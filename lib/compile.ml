open Printf
open Pretty
open Phases
open Exprs
open Types
open Errors
open Lexing
open Llvm
open Stdint
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

type 'a name_envt = (string * 'a) list

type 'a tag_envt = (tag * 'a) list

type 'a envt = 'a StringMap.t

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)

let t_i32 = TyCon (Int I32)

let t_bool = TyCon Bool

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

let rec find_tag ls (i : tag) =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Tag %d not found" i))
  | (y, v) :: rest ->
      if y = i then
        v
      else
        find_tag rest i
;;

let predicates_of_generic_bind g =
  match g with
  | GBName (name, preds, tag) -> preds
;;

let name_of_generic_bind g =
  match g with
  | GBName (name, preds, tag) -> name
;;

type scope_info = sourcespan * int option * int option

let built_in_types = StringSet.of_list ["i32"; "bool"]

(* =====================================================================
   TYPE CLASSES, SECTION A: errors, global tables, front-end stubs.
   Everything in sections A, B and C is either a stub (failwith "TODO") or
   unused by the existing pipeline until you wire it in, so the compiler
   behaves exactly as before. See typeclasses_outline.ml for the design.
   ===================================================================== *)

(* Suggested additions to errors.ml (I haven't seen it; adapt to its style). *)
(* exception NoInstance of string * sourcespan
(* rendered predicate. Raised when a wanted is neither given nor matched by an
   instance. When the predicate mentions a skolem, the message should suggest
   adding the bound, e.g. "add `T: Add` to f". *)
exception AmbiguousType of string * sourcespan
exception DuplicateClass of string * sourcespan * sourcespan
exception UnknownClass of string * sourcespan
exception OverlappingInstance of string * sourcespan * sourcespan
exception MissingMethod of string * string * sourcespan   (* instance, method *)
exception ExtraMethod of string * string * sourcespan
exception CyclicSuperclass of string * sourcespan *)

let class_table : (string, sourcespan class_info) Hashtbl.t = Hashtbl.create 8
(* class name -> info *)

let instance_table : (string, sourcespan instance_info list) Hashtbl.t = Hashtbl.create 8
(* class name -> all instances of that class. This replaces your commented-out
   `classes` / `instances`. Concrete `sourcespan` instead of `'a` avoids weak
   type variables on a top-level Hashtbl. *)

type method_impl =
  | ImplDecl of sourcespan decl (* checked + elaborated user-written DFun *)
  | ImplPrim1 of prim1 (* built-in instance: emit this primitive *)
  | ImplPrim2 of prim2

let method_impl_table : (string * string, method_impl) Hashtbl.t = Hashtbl.create 32
(* (instance_id, method name) -> implementation *)

let default_method_table : (string * string, sourcespan decl) Hashtbl.t = Hashtbl.create 16
(* (class name, method name) -> default body, stored as a DFun *)

let reset_class_state () : unit =
  (* Clear all four tables. Call at the start of type_synth so repeated
   compilations in one process (tests!) don't see each other's classes. *)
  Hashtbl.clear class_table;
  Hashtbl.clear instance_table;
  Hashtbl.clear method_impl_table;
  Hashtbl.clear default_method_table
;;

(* REAL (needed by is_well_formed / infer_prog so they stay exhaustive). *)
let partition_decls (ds : 'a decl list) : 'a decl list * 'a decl list * 'a decl list =
  List.fold_right
    (fun d (cs, is, fs) ->
      match d with
      | DClass _ -> (d :: cs, is, fs)
      | DInstance _ -> (cs, d :: is, fs)
      | DFun _ -> (cs, is, d :: fs) )
    ds ([], [], [])
;;

(* (classes, instances, funs), each in source order. *)

(* Flip to true once the Add/Sub/.. classes, the built-in instances and
   monomorphize work. Until then desugar leaves Plus, Minus, ... as EPrim2 and
   infer_exp keeps its hard-coded schemes. *)
let desugar_overloaded_ops : bool ref = ref false

let overloaded_prim1 (op : prim1) : (string * string) option =
  (* Neg |-> Some ("Neg", "neg"); everything else None. *)
  match op with
  | Neg -> Some ("Neg", "neg")
  | _ -> None
;;

let overloaded_prim2 (op : prim2) : (string * string) option =
  (* Plus |-> ("Add","add"), Minus |-> ("Sub","sub"), Times |-> ("Mul","mul"),
   Divide |-> ("Div","div"), Eq |-> ("Eq","eq"), Greater |-> ("Ord","gt"),
   GreaterEq |-> ("Ord","ge"), Less |-> ("Ord","lt"), LessEq |-> ("Ord","le").
   None for And / Or / CheckSize. In desugar's helpE:
       EPrim2(op, l, r, tag) with Some (_, m)  ==>  EApp(EId(m, tag), [l'; r'], FictolFunc, tag)
   and the same for EPrim1 with overloaded_prim1. wf runs BEFORE desugar, so it
   never sees these synthetic EIds. *)
  let res =
    match op with
    | Plus -> ("Add", "add")
    | Minus -> ("Sub", "sub")
    | Times -> ("Mul", "mul")
    | Divide -> ("Div", "div")
    | Eq -> ("Eq", "eq")
    | Greater -> ("Ord", "gt")
    | GreaterEq -> ("Ord", "ge")
    | Less -> ("Ord", "lt")
    | LessEq -> ("Ord", "le")
    | _ -> ("", "")
  in
  match res with
  | "", "" -> None
  | res -> Some res
;;

let wf_class_decl (d : sourcespan decl) : exn list = failwith "TODO"
(* wf for DClass: duplicate method names within the class, duplicate params,
   superclass / bound classes exist (UnknownClass), default bodies are
   well-formed expressions in a scope containing the method args. *)

let wf_instance_decl (d : sourcespan decl) : exn list = failwith "TODO"
(* wf for DInstance: the class exists with the right arity, the methods are
   well-formed DFuns (reuse wf_D), and the instance generics are distinct. *)

let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  let rec string_list_from_bind bind =
    match bind with
    | BName (name, _, _, tag) -> [(name, tag)]
    (* | BTuple (binds, _) -> List.concat (List.map string_list_from_bind binds) *)
    | BBlank _ -> []
  and binding_errs (scope_env, shadow_env, err_lst) x body_err =
    let adding_to_env = string_list_from_bind x in
    (* try
      let dups =
        let names = adding_to_env in
        List.map
          (fun (s, loc) ->
            let existing = List.assoc s shadow_env in
            DuplicateId (s, loc, existing) )
          names
      in *)
    (* (adding_to_env @ scope_env, adding_to_env @ shadow_env, err_lst @ dups @ body_err) *)
    (adding_to_env @ scope_env, adding_to_env @ shadow_env, err_lst @ body_err)
  (* with Not_found -> (adding_to_env @ scope_env, adding_to_env @ shadow_env, err_lst @ body_err) *)
  and blank_typ_in_bind_errs bind =
    match bind with
    | BName (name, _, typ, loc) -> (
      match typ with
      | TyBlank _ -> [NoTypeAnnotation (name, loc)]
      | _ -> [] )
    | _ -> [NotYetImplemented "unsupported binding type"]
  and wf_E_list e_lst env =
    let results = List.map (fun e -> wf_E e env) e_lst in
    List.fold_left List.append [] results
  and wf_E e env =
    match e with
    | ELiteral (LitBool _, _) -> []
    | ELiteral (LitInt (n, _), loc) ->
        if
          Int128.of_uint128 n > Int128.of_int32 Int32.max_int
          || Int128.of_uint128 n < Int128.of_int32 Int32.min_int
        then
          [Overflow (Int128.of_uint128 n, loc)]
        else
          []
    | EId (x, loc) -> (
      try
        ignore (List.assoc x env);
        []
      with Not_found -> [UnboundId (x, loc)] )
    | EPrim1 (_, e, _) -> wf_E e env
    | EPrim2 (_, l, r, _) -> wf_E_list [l; r] env
    | EIf (c, t, f, _) -> wf_E_list [c; t; f] env
    | ELet (binds, body, _) ->
        let env2, _, err_lst =
          List.fold_left
            (fun (scope_env, shadow_env, err_lst) (x, e, _) ->
              binding_errs (scope_env, shadow_env, err_lst) x (wf_E e scope_env) )
            (env, [], []) binds
        in
        err_lst @ wf_E body env2
    (* | EApp (_, args, Native, _) -> wf_E_list args env *)
    | EApp (EId (name, id_loc), args, _, loc) ->
        let fun_err = wf_E (EId (name, id_loc)) env in
        fun_err @ wf_E_list args env
    | EApp (closure, args, _, loc) ->
        (* let fun_err = wf_E closure env in
        fun_err @ wf_E_list args env *)
        [Unsupported ("Calling closures is not yet supported", loc)]
    | ESeq (e1, e2, _) -> wf_E e1 env @ wf_E e2 env
    | ETyApp (e, _, _) -> wf_E e env
  and wf_D d env (* other parameters may be needed here *) =
    match d with
    | DFun (_, generics, args, body, ct, typ, _) ->
        let env2, _, args_err_lst =
          List.fold_left
            (fun (scope_env, shadow_env, args_err_lst) (x, loc) ->
              try
                let existing = List.assoc x shadow_env in
                let err = DuplicateId (x, loc, existing) in
                ((x, loc) :: scope_env, (x, loc) :: shadow_env, args_err_lst @ [err])
              with Not_found -> ((x, loc) :: scope_env, (x, loc) :: shadow_env, args_err_lst) )
            (env, [], [])
            (List.concat (List.map string_list_from_bind args))
        in
        let typ_err_lst = List.map blank_typ_in_bind_errs args |> List.concat in
        let err_lst = args_err_lst @ typ_err_lst @ wf_E body env2 in
        err_lst
    | DClass _ | DInstance _ -> []
  and wf_D_list decls env =
    let full_env = get_new_env decls in
    let method_scope = get_method_names decls in
    List.concat
      (List.mapi
         (fun i d ->
           match d with
           | DFun (name, generics, _, _, ct, typ, loc) -> (
               (* every function name except this decl's own *)
               let others = List.filteri (fun j _ -> j <> i) decls in
               let new_env = get_new_env others @ method_scope in
               let err_lst = wf_D d (full_env @ method_scope @ env) in
               try
                 let existing = List.assoc name new_env in
                 let err = DuplicateFun (name, loc, existing) in
                 [err] @ err_lst
               with Not_found -> err_lst )
           | DClass _ -> wf_class_decl d
           | DInstance _ -> wf_instance_decl d )
         decls )
  and get_new_env decls =
    match decls with
    | DFun (name, generics, _, _, ct, typ, loc) :: rest -> (name, loc) :: get_new_env rest
    | _ :: rest -> get_new_env rest
    | [] -> []
  and get_method_names decls =
    (* class methods are global functions, so they are in scope everywhere *)
    List.concat_map
      (fun d ->
        match d with
        | DClass (_, _, _, sigs, _) -> List.map (fun s -> (s.ms_name, s.ms_span)) sigs
        | _ -> [] )
      decls
  in
  match p with
  | Program (decls, loc) -> (
      let rec helpP decls err_lst =
        (* let env = get_new_env decls in *)
        wf_D_list decls [] @ err_lst
      in
      let err_lst = helpP decls [] in
      match err_lst with
      | [] -> Ok p
      | _ -> Error err_lst )
;;

let desugar (p : sourcespan program) : sourcespan program =
  (* let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s_?#%d" name !next
  in *)
  let rec helpBE bind =
    let b, e, btag = bind in
    let e = helpE e in
    match b with
    (* | BTuple (binds, ttag) -> (
      match e with
      | EId _ -> expandTuple binds ttag e
      | _ ->
          let newname = gensym "tup" in
          (BName (newname, false, ttag), e, btag) :: expandTuple binds ttag (EId (newname, ttag)) ) *)
    | _ -> [(b, e, btag)]
  (* and expandTuple binds tag source : sourcespan binding list =
    let tupleBind i b =
      match b with
      | BBlank _ -> []
      | BName (_, _, btag) ->
          [(b, EGetItem (source, ENumber (Int64.of_int i), tag), btag)]
      | BTuple (binds, tag) ->
          let newname = gensym "tup" in
          let newexpr = EId (newname, tag) in
          ( BName (newname, false, tag),
            EGetItem (source, ENumber (Int64.of_int i), tag),
            tag )
          :: expandTuple binds tag newexpr
    in
    let size_check =
      EPrim2 (CheckSize, source, ENumber (Int64.of_int (List.length binds)))
    in
    let size_check_bind = (BBlank dummy_span, size_check) in
    size_check_bind :: List.flatten (List.mapi tupleBind binds) *)
  and helpG g = List.map helpD g
  and helpD d =
    match d with
    | DFun (name, generics, args, body, call_type, typ, tag) ->
        DFun (name, generics, args, helpE body, call_type, typ, tag)
    | DClass (name, params, supers, sigs, tag) ->
        DClass
          ( name,
            params,
            supers,
            List.map (fun s -> {s with ms_default= Option.map helpE s.ms_default}) sigs,
            tag )
    | DInstance (generics, head, methods, tag) ->
        DInstance (generics, head, List.map helpD methods, tag)
  and helpE e =
    match e with
    | ESeq (e1, e2, tag) -> ELet ([(BBlank tag, helpE e1, tag)], helpE e2, tag)
    | EId (x, tag) -> EId (x, tag)
    | ELiteral (n, tag) -> ELiteral (n, tag)
    | EPrim1 (op, body, tag) -> (
      match op with
      | _ when !desugar_overloaded_ops && Option.is_some (overloaded_prim1 op) ->
          let _, m = Option.get (overloaded_prim1 op) in
          EApp (EId (m, tag), [helpE body], FictolFunc, tag)
      | Not -> EIf (helpE body, ELiteral (LitBool false, tag), ELiteral (LitBool true, tag), tag)
      | Add1 | Sub1 | Print | PrintStack | Neg -> EPrim1 (op, helpE body, tag) )
    | EPrim2 (op, left, right, tag) -> (
      match op with
      | _ when !desugar_overloaded_ops && Option.is_some (overloaded_prim2 op) ->
          let _, m = Option.get (overloaded_prim2 op) in
          EApp (EId (m, tag), [helpE left; helpE right], FictolFunc, tag)
      | And -> EIf (helpE left, helpE right, ELiteral (LitBool false, tag), tag)
      | Or -> EIf (helpE left, ELiteral (LitBool true, tag), helpE right, tag)
      | Plus | Minus | Times | Divide | Greater | GreaterEq | Less | LessEq | Eq | CheckSize ->
          EPrim2 (op, helpE left, helpE right, tag) )
    | ELet (binds, body, tag) ->
        let newbinds = List.map helpBE binds in
        List.fold_right (fun binds body -> ELet (binds, body, tag)) newbinds (helpE body)
    (* | ELetRec (bindexps, body, tag) ->
        (* ASSUMES well-formed letrec, so only BName bindings *)
        let newbinds = List.map (fun (bind, e, tag) -> (bind, helpE e, tag)) bindexps in
        ELetRec (newbinds, helpE body, tag) *)
    | EIf (cond, thn, els, tag) -> EIf (helpE cond, helpE thn, helpE els, tag)
    | EApp (name, args, native, tag) -> EApp (helpE name, List.map helpE args, native, tag)
    | ETyApp (e, tys, tag) -> ETyApp (helpE e, tys, tag)
    (* | ELambda (binds, body, tag) ->
        let expandBind bind =
          match bind with
          | BTuple (_, btag) ->
              let newparam = gensym "tuparg" in
              (BName (newparam, false, btag), helpBE (bind, EId (newparam, btag), btag))
          | _ -> (bind, [])
        in
        let params, newbinds = List.split (List.map expandBind binds) in
        let newbody =
          List.fold_right (fun binds body -> ELet (binds, body, tag)) newbinds (helpE body)
        in
        ELambda (params, newbody, tag) *)
    (* | EString (s, tag) ->
        let num_list = List.map (fun c -> ENumber (Int64.of_int (Char.code c), tag)) (explode s) in
        let nums_linked = List.fold_right (fun n l -> ETuple ([n; l], tag)) num_list (ENil tag) in
        helpE (EApp (EId ("String", tag), [nums_linked], Snake, tag)) *)
  in
  match p with
  | Program (decls, tag) -> Program (helpG decls, tag)
;;

let rec resolve_typ_path env (typ : 'a typ) =
  match typ with
  | TyPath (path, t) -> (
    match path with
    | ["i8"] -> TyCon (Int I8)
    | ["i16"] -> TyCon (Int I16)
    | ["i32"] -> TyCon (Int I32)
    | ["i64"] -> TyCon (Int I64)
    | ["i128"] -> TyCon (Int I128)
    | ["bool"] -> TyCon Bool
    (* change to solve path eventually *)
    | [name] ->
        if List.mem name env then
          TyVar name
        else
          failwith (sprintf "cannot resolve type %s" (ExtString.String.join "::" path))
    | _ -> failwith (sprintf "cannot resolve type %s" (ExtString.String.join "::" path)) )
  | TyVar name -> TyVar name
  | TyCon name -> TyCon name
  | TyArrow (args, ret_type) ->
      TyArrow (List.map (fun arg -> resolve_typ_path env arg) args, resolve_typ_path env ret_type)
  | TyBlank t -> TyBlank t
  | TyApp (ret_typ, args) ->
      TyApp (resolve_typ_path env ret_typ, List.map (fun arg -> resolve_typ_path env arg) args)
;;

(* REAL. Use this (not resolve_typ_path) on a bound. Checking that the class
   exists belongs in is_well_formed, not here. *)
let resolve_predicate (generic_env : string list) (p : 'a predicate) : 'a predicate =
  {p with pred_args= List.map (resolve_typ_path generic_env) p.pred_args}
;;

let resolve_prog_typ_paths (p : sourcespan program) : sourcespan program =
  let rec helpP p =
    match p with
    | Program (decls, span) -> Program (List.map helpD decls, span)
  and string_list_of_generics gs =
    List.map
      (fun g ->
        match g with
        | GBName (name, _, tag) -> name )
      gs
  and helpGeneric env g =
    match g with
    | GBName (name, predicates, tag) ->
        GBName (name, List.map (resolve_predicate env) predicates, tag)
  and helpD decl = helpD_in [] decl
  and helpD_in outer decl =
    (* `outer` = type variables already in scope (instance generics for methods) *)
    match decl with
    | DFun (name, generics, args, body, call_type, typ, span) ->
        let generic_env = outer @ string_list_of_generics generics in
        let new_args = List.map (fun arg -> helpBind generic_env arg) args in
        DFun
          ( name,
            List.map (helpGeneric generic_env) generics,
            new_args,
            helpE body,
            call_type,
            resolve_typ_path generic_env typ,
            span )
    | DClass (name, params, supers, sigs, span) ->
        DClass
          ( name,
            params,
            List.map (resolve_predicate params) supers,
            List.map (helpSig params) sigs,
            span )
    | DInstance (generics, head, methods, span) ->
        let inst_env = string_list_of_generics generics in
        DInstance
          ( List.map (helpGeneric inst_env) generics,
            resolve_predicate inst_env head,
            List.map (helpD_in inst_env) methods,
            span )
  and helpSig class_env s =
    let env = class_env @ string_list_of_generics s.ms_generics in
    { s with
      ms_generics= List.map (helpGeneric env) s.ms_generics;
      ms_args= List.map (helpBind env) s.ms_args;
      ms_ret= resolve_typ_path env s.ms_ret;
      ms_default= Option.map helpE s.ms_default }
  and helpBind env bind =
    match bind with
    | BName (name, shadow, typ, span) -> BName (name, shadow, resolve_typ_path env typ, span)
    | BBlank _ -> bind
  (* | _ -> failwith "should've been desugared" *)
  and helpE expr =
    (* FIXME (existing bug): only ELet is traversed, so type paths inside EIf / EApp /
       EPrim* / ESeq are never resolved, and let annotations get an empty generic env. *)
    match expr with
    | ELet (bindings, body, span) ->
        let new_bindings =
          List.map
            (fun (bind, bind_body, span) -> (helpBind [] bind, helpE bind_body, span))
            bindings
        in
        ELet (new_bindings, helpE body, span)
    | EIf (cond, thn, els, span) -> EIf (helpE cond, helpE thn, helpE els, span)
    | EApp (closure, args, call_type, span) -> EApp (helpE closure, List.map helpE args, call_type, span)
    | ESeq (e1, e2, span) -> ESeq (helpE e1, helpE e2, span)
    | EPrim1 (op, body, span) -> EPrim1 (op, helpE body, span)
    | EPrim2 (op, l, r, span) -> EPrim2 (op, helpE l, helpE r, span)
    | _ -> expr
  in
  helpP p
;;

let rec subst_var_typ ((tyvar : string), (to_typ : 'a typ)) (in_typ : 'a typ) : 'a typ =
  match in_typ with
  | TyVar name ->
      if name = tyvar then
        to_typ
      else
        TyVar name
  | TyCon name -> TyCon name
  | TyArrow (args, ret_type) ->
      TyArrow
        ( List.map (fun arg -> subst_var_typ (tyvar, to_typ) arg) args,
          subst_var_typ (tyvar, to_typ) ret_type )
  | TyBlank t -> TyBlank t
  | TyApp (ret_typ, args) ->
      TyApp
        ( subst_var_typ (tyvar, to_typ) ret_typ,
          List.map (fun arg -> subst_var_typ (tyvar, to_typ) arg) args )
  | _ -> failwith "should have been resolved by now"
;;

let rec subst_var_typ_in_scheme
    ((tyvar : string), (to_typ : 'a typ))
    (scheme_args : string list)
    (in_typ : 'a typ) =
  match in_typ with
  | TyVar name ->
      if name = tyvar then
        if List.mem name scheme_args then
          in_typ
        else
          to_typ
      else
        in_typ
  | TyCon name -> TyCon name
  | TyArrow (args, ret_type) ->
      TyArrow
        ( List.map (fun arg -> subst_var_typ_in_scheme (tyvar, to_typ) scheme_args arg) args,
          subst_var_typ_in_scheme (tyvar, to_typ) scheme_args ret_type )
  | TyBlank t -> TyBlank t
  | TyApp (ret_typ, args) ->
      TyApp
        ( subst_var_typ_in_scheme (tyvar, to_typ) scheme_args ret_typ,
          List.map (fun arg -> subst_var_typ_in_scheme (tyvar, to_typ) scheme_args arg) args )
  | _ -> failwith "should have been resolved by now"
;;

let rec subst_var_scheme ((tyvar : string), (to_typ : 'a typ)) (in_scheme : 'a scheme) : 'a scheme =
  match in_scheme with
  | SForall (args, predicates, typ) ->
      if List.mem tyvar args then
        in_scheme
      else
        let new_typ = subst_var_typ (tyvar, to_typ) typ in
        (* let new_constraints =
          List.map (fun (cls, cty) -> (cls, subst_var_typ (tyvar, to_typ) cty)) constraints
        in *)
        let new_predicates = apply_subst_predicates [(tyvar, to_typ)] predicates in
        SForall (args, new_predicates, new_typ)

and apply_subst_typ (subst : 'a typ subst) (t : 'a typ) : 'a typ =
  List.fold_left (fun acc sub -> subst_var_typ sub acc) t subst

and apply_subst_scheme (subst : 'a typ subst) (s : 'a scheme) : 'a scheme =
  List.fold_left (fun acc sub -> subst_var_scheme sub acc) s subst

and apply_subst_typenv (subst : 'a typ subst) (env : 'a typ envt) : 'a typ envt =
  StringMap.map (fun typ -> apply_subst_typ subst typ) env

and apply_subst_schenv (subst : 'a typ subst) (env : 'a scheme envt) : 'a scheme envt =
  StringMap.map (fun typ -> apply_subst_scheme subst typ) env

and apply_subst_subst (sub1 : 'a typ subst) (sub2 : 'a typ subst) : 'a typ subst =
  List.map (fun (tyvar, to_typ) -> (tyvar, apply_subst_typ sub1 to_typ)) sub2

and apply_subst_pred (subst : 'a typ subst) (p : 'a predicate) : 'a predicate =
  {p with pred_args= List.map (apply_subst_typ subst) p.pred_args}

and apply_subst_predicates (subst : 'a typ subst) (predicates : 'a predicate list) :
    'a predicate list =
  List.map (apply_subst_pred subst) predicates
;;

let compose_subst (sub1 : 'a typ subst) (sub2 : 'a typ subst) : 'a typ subst =
  sub1 @ apply_subst_subst sub1 sub2
;;

let rec ftv_typ (t : 'a typ) : StringSet.t =
  match t with
  | TyCon _ -> StringSet.empty
  | TyVar name -> StringSet.singleton name
  | TyArrow (args, ret) ->
      List.fold_right (fun t ftvs -> StringSet.union (ftv_typ t) ftvs) args (ftv_typ ret)
  | TyApp (typ, args) ->
      List.fold_right (fun t ftvs -> StringSet.union (ftv_typ t) ftvs) args (ftv_typ typ)
  | TyBlank _ -> StringSet.empty
  | _ -> failwith "should have been resolved by now"
;;

let ftv_pred (p : 'a predicate) : StringSet.t =
  List.fold_left (fun acc t -> StringSet.union acc (ftv_typ t)) StringSet.empty p.pred_args
;;

let ftv_scheme (s : 'a scheme) : StringSet.t =
  match s with
  | SForall (args, predicates, typ) ->
      let bound = StringSet.of_list args in
      let ftv_predicates =
        List.fold_left StringSet.union StringSet.empty (List.map ftv_pred predicates)
      in
      StringSet.diff (StringSet.union (ftv_typ typ) ftv_predicates) bound
;;

let ftv_env (e : 'a scheme envt) : StringSet.t =
  let mapped = StringMap.map (fun sch -> ftv_scheme sch) e in
  StringMap.fold (fun _ value acc -> StringSet.union acc value) mapped StringSet.empty
;;

let occurs (name : string) (t : 'a typ) = StringSet.mem name (ftv_typ t)

let rec unify (t1 : 'a typ) (t2 : 'a typ) (span : sourcespan) : 'a typ subst =
  let unify_tyvar_other tyvar other =
    (* FIXME (existing bug): a failed occurs check returns [] i.e. SUCCESS. It should raise
       (but still allow TyVar a ~ TyVar a). *)
    if occurs tyvar other then
      match other with
      | TyVar(other_name) -> []
      | _ -> failwith (sprintf "Unification failure: occurs check failed at <%s>" (string_of_sourcespan span))
    else
      [(tyvar, other)]
  in
  let unify_arrows t1_args t1_ret_ty t2_args t2_ret_ty =
    let unified_args = unify_lists t1_args t2_args span in
    let t1_ret_ty = apply_subst_typ unified_args t1_ret_ty in
    let unified_rets = unify t1_ret_ty t2_ret_ty span in
    compose_subst unified_args unified_rets
  in
  match (t1, t2) with
  | TyVar name, other | other, TyVar name -> unify_tyvar_other name other
  | TyCon name1, TyCon name2 ->
      if name1 = name2 then
        []
      else
        failwith
          (sprintf "Unification failure at <%s>: inconsistent type constants"
             (string_of_sourcespan span) )
  | TyArrow (t1_args, t1_ret_ty), TyArrow (t2_args, t2_ret_ty)
   |TyApp (t1_ret_ty, t1_args), TyApp (t2_ret_ty, t2_args) ->
      unify_arrows t1_args t1_ret_ty t2_args t2_ret_ty
  | _ -> failwith (sprintf "Unification failure at <%s>" (string_of_sourcespan span))

and unify_lists (ts1 : 'a typ list) (ts2 : 'a typ list) (span : sourcespan) : 'a typ subst =
  match (ts1, ts2) with
  | first1 :: rest1, first2 :: rest2 ->
      let sub = unify first1 first2 span in
      let rest1 = List.map (apply_subst_typ sub) rest1 in
      let rest2 = List.map (apply_subst_typ sub) rest2 in
      let new_sub = unify_lists rest1 rest2 span in
      compose_subst sub new_sub
  | [], [] -> []
  | _, _ -> failwith "unify_lists: mismatched list lengths"
;;

let unifiable (p1 : 'a predicate) (p2 : 'a predicate) : bool =
  try
    let _ = unify_lists p1.pred_args p2.pred_args dummy_span in
    true
  with _ -> false
;;

let gensym_typ =
  let count = ref 0 in
  let next () =
    count := !count + 1;
    !count
  in
  fun str -> sprintf "%s_%d" str (next ())
;;

let instantiate (s : 'a scheme) : 'a predicate list * 'a typ =
  match s with
  | SForall (args, predicates, typ) ->
      let sub = List.map (fun s -> (s, TyVar (gensym_typ "T"))) args in
      let res_typ = apply_subst_typ sub typ in
      let res_constraints = apply_subst_predicates sub predicates in
      (res_constraints, res_typ)
;;

let instantiate_for_decl (s : 'a scheme) : (string * 'a typ) list * 'a predicate list * 'a typ =
  match s with
  | SForall (args, predicates, typ) ->
      let sub = List.map (fun v -> (v, TyVar (gensym_typ "T"))) args in
      (sub, apply_subst_predicates sub predicates, apply_subst_typ sub typ)
;;

let get_return_typ (typ : 'a typ) =
  match typ with
  | TyArrow (_, ret_typ) -> ret_typ
  | _ -> failwith "Expected arrow type"
;;

(* =====================================================================
   TYPE CLASSES, SECTION B: predicate utilities, classes, instances,
   solving. Placed after instantiate_for_decl so gensym_typ is available.
   ===================================================================== *)

(* REAL: Pretty.string_of_pred printed a typ and I can't see Pretty, so this
   file defines its own (shadowing Pretty's). *)
let rec show_typ (t : 'a typ) : string =
  match t with
  | TyVar n -> n
  | TyCon (Int I8) -> "i8"
  | TyCon (Int I16) -> "i16"
  | TyCon (Int I32) -> "i32"
  | TyCon (Int I64) -> "i64"
  | TyCon (Int I128) -> "i128"
  | TyCon Bool -> "bool"
  | TyCon (Skolem n) -> n
  | TyArrow (args, ret) ->
      sprintf "(%s) -> %s" (String.concat ", " (List.map show_typ args)) (show_typ ret)
  | TyBlank _ -> "_"
  | TyApp (f, args) -> sprintf "%s<%s>" (show_typ f) (String.concat ", " (List.map show_typ args))
  | TyPath (path, _) -> String.concat "::" path
;;

let string_of_pred (p : 'a predicate) : string =
  String.concat " " (p.pred_class :: List.map show_typ p.pred_args)
;;

let apply_subst_wanted (subst : 'a typ subst) (w : 'a wanted) : 'a wanted =
  {w_pred= apply_subst_pred subst w.w_pred; w_span= w.w_span}
;;

let apply_subst_wanteds (subst : 'a typ subst) (ws : 'a wanted list) : 'a wanted list =
  List.map (apply_subst_wanted subst) ws
;;

(* Substitute inside w.w_pred; keep w.w_span. *)

let pred_equal (p1 : 'a predicate) (p2 : 'a predicate) : bool =
  (* Same class name and pairwise-equal args after untagTyp. Do NOT use plain
   `=` on predicates: TyBlank / TyPath carry source spans and would compare
   unequal. (Your commented check_instance_exists used `=`.) *)
  p1.pred_class = p2.pred_class
  && List.combine p1.pred_args p2.pred_args
     |> List.for_all (fun (t1, t2) -> untagTyp t1 = untagTyp t2)
;;

let fresh_subst (vars : string list) : 'a typ subst =
  (* Map each v to TyVar (gensym_typ v). Used to rename instance variables apart
   before an overlap check, and to instantiate schemes. *)
  List.map (fun s -> (s, TyVar (gensym_typ s))) vars
;;

let has_meta_vars (p : 'a predicate) : bool =
  (* True iff ftv_pred p is non-empty. Skolems are TyCon, so every TyVar still
   present in a WANTED is an unresolved unification variable. solve_wanted uses
   this to tell "stuck, maybe solvable later" from "definitely unsatisfiable". *)
  not (StringSet.is_empty (ftv_pred p))
;;

let lookup_class (name : string) : sourcespan class_info =
  (* Hashtbl.find_opt on class_table; raise UnknownClass (needs a span argument
   in practice) if absent. *)
  match Hashtbl.find_opt class_table name with
  | Some ci -> ci
  | _ -> failwith ("Unknown class " ^ name)
;;

let get_bind_typs binds =
    List.map
      (fun bind ->
        match bind with
        | BName (name, _, typ, tag) -> typ
        | _ -> failwith "unsupported binding type" )
      binds
;;

let class_info_of_decl (d : sourcespan decl) : sourcespan class_info =
  (* DClass -> class_info. For each method_sig build a method_info:
   m_generics = ms_generics; m_typ = TyArrow(types of ms_args, ms_ret);
   m_has_default = (ms_default <> None). Pure; no table writes. *)
  let method_info_of_method_sig ms =
    let typ = TyArrow (get_bind_typs ms.ms_args, ms.ms_ret) in
    { m_name= ms.ms_name;
      m_generics= ms.ms_generics;
      m_typ= typ;
      m_has_default=
        ( match ms.ms_default with
        | Some _ -> true
        | None -> false ) }
  in
  match d with
  | DClass (name, params, superclasses, methods, tag) ->
      { class_name= name;
        class_params= params;
        class_superclasses= superclasses;
        class_methods= List.map method_info_of_method_sig methods;
        class_span= tag }
  | _ -> failwith "Cannot get class info of non class def"
;;

let scheme_of_method (cls : 'a class_info) (m : 'a method_info) : 'a scheme =
  (* The scheme of the method viewed as a top-level function:
     SForall( cls.class_params @ names of m.m_generics,
              {cls.class_name; map TyVar cls.class_params}  ::  bounds of m.m_generics,
              m.m_typ )
   The CLASS predicate comes first, and the quantified variables list the class
   params first, then method generics. instantiate / ETyApp / monomorphize all
   depend on this order. Example:
       add : forall Self. Add Self => (Self, Self) -> Self. *)
  SForall
    ( cls.class_params @ List.map name_of_generic_bind m.m_generics,
      {pred_class= cls.class_name; pred_args= List.map (fun s -> TyVar s) cls.class_params}
      :: List.concat (List.map predicates_of_generic_bind m.m_generics),
      m.m_typ )
;;

let register_class (d : sourcespan decl) : unit =
  (* Phase 1 of 2 for classes. Raise DuplicateClass if the name is taken, else
   insert class_info_of_decl d into class_table, and store each method default
   (rebuilt as a DFun with call_type FictolFunc) in default_method_table under
   (class, method). Does NOT validate anything that refers to other classes,
   because a superclass may be declared later in the file. *)
  let method_sig_to_dfun ms =
    match ms.ms_default with
    | Some (ms_default) -> 
      DFun(ms.ms_name, ms.ms_generics, ms.ms_args, ms_default, FictolFunc, ms.ms_ret, ms.ms_span)
    | None -> failwith (sprintf "Cannot convert method %s without a body" ms.ms_name)
  in
  match d with
  | DClass (name, params, superclasses, methods, span) ->
      if Hashtbl.mem class_table name then
        failwith (sprintf "Duplicate class at <%s>" (string_of_sourcespan span))
      else
        let cls_info = (class_info_of_decl d) in
        Hashtbl.add class_table name cls_info;
        List.iter
        (fun method_sig ->
          match method_sig.ms_default with
          | Some _ -> Hashtbl.add default_method_table (name, method_sig.ms_name) (method_sig_to_dfun method_sig)
          | None -> ())
        methods;
        Hashtbl.add instance_table name []
  | _ -> failwith "Cannot register non class"
;;

let validate_classes () : unit =
  (* Sorted by source position so errors are reported deterministically
     (Hashtbl iteration order is arbitrary). *)
  let all_classes =
    Hashtbl.to_seq_values class_table
    |> List.of_seq
    |> List.sort (fun a b -> compare a.class_span b.class_span)
  in
  (* A predicate used as a superclass or as a method bound must name a
     registered class and give it the right number of arguments. Looks in
     class_table directly so it doesn't depend on lookup_class. *)
  let check_pred_registered (cls : sourcespan class_info) (p : sourcespan predicate) : unit =
    match Hashtbl.find_opt class_table p.pred_class with
    | None -> failwith (sprintf "Validate classes failure: unknown class %s at <%s>" p.pred_class (string_of_sourcespan cls.class_span))
    | Some target ->
        let expected = List.length target.class_params in
        let actual = List.length p.pred_args in
        if expected <> actual then
          failwith
            (sprintf "class %s takes %d argument(s) but is given %d in `%s` (in class %s)"
               p.pred_class expected actual (string_of_pred p) cls.class_name)
  in
  (* Superclass arguments may only mention this class's own parameters. *)
  let check_superclass_vars (cls : sourcespan class_info) : unit =
    let params = StringSet.of_list cls.class_params in
    List.iter
      (fun p ->
        let stray = StringSet.diff (ftv_pred p) params in
        if not (StringSet.is_empty stray) then
          failwith
            (sprintf "superclass `%s` of class %s mentions %s, which is not a parameter of the class"
               (string_of_pred p) cls.class_name
               (String.concat ", " (StringSet.elements stray))) )
      cls.class_superclasses
  in
  (* Cycle detection. `path` is the chain of classes currently being explored,
     so reaching one again is a cycle (a diamond A<B,C<D is NOT one).
     `finished` memoises classes already proven acyclic, which avoids
     re-walking shared ancestors. Run only after check_pred_registered has
     passed for every class, so every superclass is in class_table. *)
  let finished : (string, unit) Hashtbl.t = Hashtbl.create 16 in
  let rec search (path : StringSet.t) (cls : sourcespan class_info) : unit =
    if StringSet.mem cls.class_name path then
      failwith (sprintf "Validate classes failure: cyclic superclass %s at <%s>" cls.class_name (string_of_sourcespan cls.class_span))
    else if not (Hashtbl.mem finished cls.class_name) then begin
      let path' = StringSet.add cls.class_name path in
      List.iter
        (fun (p : sourcespan predicate) ->
          match Hashtbl.find_opt class_table p.pred_class with
          | Some super -> search path' super
          | None -> () )
        cls.class_superclasses;
      Hashtbl.add finished cls.class_name ()
    end
  in
  (* Per-method checks. *)
  let check_methods (cls : sourcespan class_info) : unit =
    let params = StringSet.of_list cls.class_params in
    List.iter
      (fun (m : sourcespan method_info) ->
        (* method generics must not shadow class params; their bounds must be valid *)
        List.iter
          (fun (GBName (g, bounds, _)) ->
            if StringSet.mem g params then
              failwith
                (sprintf "type parameter %s of method %s shadows a parameter of class %s" g
                   m.m_name cls.class_name);
            List.iter (check_pred_registered cls) bounds )
          m.m_generics;
        (* the method type must mention every class param, otherwise no call
           can determine which instance to use *)
        let missing = StringSet.diff params (ftv_typ m.m_typ) in
        if not (StringSet.is_empty missing) then
          failwith
            (sprintf "method %s of class %s is ambiguous: its type does not mention %s"
               m.m_name cls.class_name
               (String.concat ", " (StringSet.elements missing))) )
      cls.class_methods
  in
  (* Method names are global functions, so they must be unique across ALL
     classes (built-ins included). A clash with a TOP-LEVEL FUNCTION is not
     visible from here; is_well_formed reports that as DuplicateFun, because
     get_method_names puts method names into its scope. *)
  let method_owner : (string, string) Hashtbl.t = Hashtbl.create 32 in
  let check_unique_methods (cls : sourcespan class_info) : unit =
    List.iter
      (fun (m : sourcespan method_info) ->
        match Hashtbl.find_opt method_owner m.m_name with
        | Some owner when owner = cls.class_name ->
            failwith (sprintf "method %s is declared twice in class %s" m.m_name cls.class_name)
        | Some owner ->
            failwith
              (sprintf "method %s of class %s is already defined by class %s" m.m_name
                 cls.class_name owner)
        | None -> Hashtbl.add method_owner m.m_name cls.class_name )
      cls.class_methods
  in
  List.iter
    (fun cls ->
      List.iter (check_pred_registered cls) cls.class_superclasses;
      check_superclass_vars cls )
    all_classes;
  List.iter (search StringSet.empty) all_classes;
  List.iter check_methods all_classes;
  List.iter check_unique_methods all_classes

let find_method (name : string) : (sourcespan class_info * sourcespan method_info) option =
  (* Search class_table for a method called `name`. Used by monomorphize to tell
   a class method from an ordinary generic function, and by wf to treat method
   names as in scope. *)
  let all_classes = List.of_seq (Hashtbl.to_seq class_table) in
  let rec helper (lst : (string * 'a class_info) list) :
      (sourcespan class_info * sourcespan method_info) option =
    match lst with
    | (_, first_cls) :: rest -> (
      match List.find_opt (fun m -> m.m_name = name) first_cls.class_methods with
      | Some m -> Some (first_cls, m)
      | _ -> helper rest )
    | [] -> None
  in
  helper all_classes
;;

let method_env () : sourcespan scheme envt =
  (* For every class and every method, add m_name |-> scheme_of_method cls m.
   This map is the INITIAL value environment: type_synth passes it to the
   inference code instead of StringMap.empty, so `EId "add"` finds a scheme. *)
  let _, all_classes = List.split (List.of_seq (Hashtbl.to_seq class_table)) in
  List.fold_left
    (fun acc cls ->
      List.fold_left
        (fun acc method_info ->
          StringMap.add method_info.m_name (scheme_of_method cls method_info) acc )
        acc cls.class_methods )
    StringMap.empty all_classes
;;

let rec superclass_closure (p : 'a predicate) : 'a predicate list =
  (* p itself plus every transitive superclass, instantiated. For p = C [t1..tn]:
   substitute class_params |-> [t1..tn] into each of class(C).class_superclasses,
   and recurse on each result. Terminates because validate_classes proved the
   graph acyclic. Example: superclass_closure {Ord;[i32]} = [Ord i32; Eq i32].
   This is Haskell's `bySuper`. *)
  let cls = lookup_class p.pred_class in
  let args = p.pred_args in
  let params = cls.class_params in
  let superclasses = cls.class_superclasses in
  (* for each superclass -> create pred that is class name, substituted args for each param
  recurse on that pred.*)
  let instantiated_superclasses =
    List.map (apply_subst_pred (List.combine params args)) superclasses
  in
  List.concat (List.map superclass_closure instantiated_superclasses)
;;

let name_of_dfun d =
  match d with
  | DFun (name, _, _, _, _, _, _) -> name
  | _ -> failwith "Cannot get name of non DFun"
;;

let instance_info_of_decl (d : sourcespan decl) : sourcespan instance_info =
  (* DInstance(generics, head, methods, span) -> instance_info:
     instance_vars    = names of generics
     instance_context = concatenation of the generics' bounds
     instance_methods = names of the DFuns in `methods`
     instance_id      = fresh unique string, e.g. gensym "Add_i32"
   Pure. *)
  match d with
  | DInstance (generics, head, method_decls, span) ->
      { instance_vars= List.map name_of_generic_bind generics;
        instance_context= List.concat (List.map predicates_of_generic_bind generics);
        instance_methods= List.map name_of_dfun method_decls;
        instance_span= span;
        instance_head= head;
        instance_id=
          head.pred_class ^ "##" ^ ExtString.String.join "#" (List.map show_typ head.pred_args) }
  | _ -> failwith "Cannot get instance info of non instance decl"
;;

let overlaps (i1 : 'a instance_info) (i2 : 'a instance_info) : bool =
  (* Rename each instance's variables apart with fresh_subst, THEN call your
   existing `unifiable` on the two heads. Without renaming, `impl<T> C for
   Pair<T, T>` and `impl<U> C for Pair<U, i32>` are compared with shared
   variable names and give wrong answers. Requires the unify occurs-check fix
   (see PART 3 notes). *)
  let i1_subst = fresh_subst i1.instance_vars in
  let i1_subbed_head = apply_subst_pred i1_subst i1.instance_head in
  let i2_subst = fresh_subst i2.instance_vars in
  let i2_subbed_head = apply_subst_pred i2_subst i2.instance_head in
  unifiable i1_subbed_head i2_subbed_head
;;

let register_instance (inst : sourcespan instance_info) : unit =
(* Validate then insert into instance_table. Checks:
   - the class exists and List.length head args = List.length class_params;
   - no existing instance of the class `overlaps` this one (OverlappingInstance);
   - every variable in instance_context also occurs in the head;
   - every method in instance_methods belongs to the class (ExtraMethod), and
     every class method without a default is present (MissingMethod).
   Does NOT check method bodies or superclass obligations; those need ALL
   instances registered first (see check_instance). *)
  let class_exists (inst) : sourcespan class_info =
    let cls_name = inst.instance_head.pred_class in
    match Hashtbl.find_opt class_table cls_name with
    | Some (cls) -> 
      if (List.length inst.instance_head.pred_args) = (List.length cls.class_params) then 
        cls
      else
        failwith ("Class param arity mismatch")
    | None -> failwith (sprintf "No class %s found" cls_name)
  in
  let no_overlap (cls_name) (inst) : unit =
    let existing = Hashtbl.find instance_table cls_name in
    List.iter
    (fun inst_item ->
      if overlaps inst inst_item then
        failwith (sprintf "Overlapping instances %s and %s" inst.instance_id inst_item.instance_id))
    existing
  in
  let context_and_params_check (inst) : unit =
    let context_vars = 
      List.fold_left
      (fun acc pred ->
        StringSet.union acc (ftv_pred pred))
      StringSet.empty inst.instance_context
    in
    let head_vars = (ftv_pred inst.instance_head) in
    if StringSet.is_empty (StringSet.diff context_vars head_vars) then
      ()
    else
      failwith (sprintf "Mismatched variable usage in instance context and instance head for %s" inst.instance_id)
  in
  let class_info_required_method_names (cls) : StringSet.t =
    List.filter (fun method_info -> method_info.m_has_default) cls.class_methods
    |>
    List.map
    (fun method_info ->
      method_info.m_name)
    |> StringSet.of_list
  in
  let methods_belong (cls) (inst) : unit =
    let required_methods = class_info_required_method_names cls in
    let implemented_methods = StringSet.of_list inst.instance_methods in
    if StringSet.is_empty (StringSet.diff required_methods implemented_methods) then
      ()
    else
      failwith (sprintf "%s does not implement the required methods" inst.instance_id)
  in
  let validate_instance (inst : sourcespan instance_info) : unit =
    let cls = class_exists inst in
    no_overlap cls.class_name inst;
    context_and_params_check inst;
    methods_belong cls inst;
    let existing = Hashtbl.find instance_table cls.class_name in
    Hashtbl.replace instance_table cls.class_name (inst :: existing)
  in
  validate_instance inst
;;

let rec match_typ (pat_vars : StringSet.t) (pat : 'a typ) (target : 'a typ) (acc : 'a typ subst) :
    'a typ subst option =
  match pat, target with
  | TyVar(v), _ when StringSet.mem v pat_vars -> 
    let existing = List.filter (fun (tyvar, typ) -> tyvar = v) acc in (
    match existing with
    | [] -> Some ((v, target) :: acc)
    | (tyvar, typ) :: _ ->
      if (untagTyp target) = (untagTyp typ) then
        Some (acc)
      else
        None)
  | TyVar(v), TyVar(t) when (not (StringSet.mem v pat_vars)) && (v = t) -> Some (acc)
  | TyCon(c), _ when (untagTyp target) = (untagTyp pat) -> Some (acc)
  | TyArrow(pat_args, pat_ret), TyArrow(target_args, target_ret)
  | TyApp(pat_ret, pat_args), TyApp(target_ret, target_args) ->
    let maybe_sub = (match_typ pat_vars pat_ret target_ret acc) in
    let arity_match = ((List.length pat_args) = (List.length target_args)) in
    (match maybe_sub with
    | Some (sub) when arity_match -> 
      match_typ_list pat_vars pat_args target_args sub
    | _ -> None)
  | _ -> None

and match_typ_list (pat_vars: StringSet.t) (pat_lst : 'a typ list) (target_lst : 'a typ list) (acc : 'a typ subst) =
  List.fold_left 
  (fun acc_sub (p, t) -> 
    match acc_sub with
    | Some(acc_sub) -> match_typ pat_vars p t acc_sub
    | None -> None)
  (Some(acc)) (List.combine pat_lst target_lst)

(* ONE-WAY MATCHING, not unification: find a substitution for the variables in
   pat_vars that makes `pat` equal to `target`, extending `acc`.
   - pat is TyVar v with v in pat_vars: if v is already in acc, require the bound
     type to equal target (pred_equal-style, via untagTyp); else bind v |-> target.
   - pat is TyVar v NOT in pat_vars: succeed iff target is the same TyVar.
   - TyCon: equal constructors. TyArrow / TyApp: same arity, recurse.
   - Variables inside `target` are NEVER bound, so TyCon i32 does not match
     TyVar T_5. That is the point: a wanted `Add T_5` must not pick an instance
     until T_5 is known. Return None on any mismatch. *)

let match_pred (pat_vars : StringSet.t) (pat : 'a predicate) (target : 'a predicate) :
    'a typ subst option =
  if pat.pred_class = target.pred_class then
    match_typ_list pat_vars pat.pred_args target.pred_args []
  else
    None
;;

(* Same class name, same arity, then fold match_typ over the argument pairs,
   threading the accumulator so repeated variables stay consistent. *)

let find_instance (p : sourcespan predicate) :
    (sourcespan instance_info * sourcespan typ subst) option =
  let all_instances = Hashtbl.find instance_table p.pred_class in
  let rec helper instances =
    match instances with
    | [] -> None
    | first :: rest -> (
      match match_pred (StringSet.of_list first.instance_vars) first.instance_head p with
      | Some (sub) -> Some ((first, sub))
      | None -> helper rest
    )
  in
  helper all_instances
;;

(* Look up instance_table[p.pred_class]; return the first instance whose
   head matches p (match_pred (set of inst.instance_vars) inst.instance_head p)
   together with the resulting substitution. Overlap was rejected at
   registration, so at most one can match. None means no match, whether the
   predicate is stuck on unknowns or truly unsatisfiable; solve_wanted decides
   which (via has_meta_vars). Haskell calls this `byInst`. *)

let given_closure (givens : 'a predicate list) : 'a predicate list =
  List.map superclass_closure givens |> List.concat
(* concat_map superclass_closure givens. With givens [Ord T] the closure is
   [Ord T; Eq T], so a wanted `Eq T` is solved without a separate Eq bound. *)

let rec solve_wanted (givens : 'a predicate list) (w : sourcespan wanted) : sourcespan wanted list =
  match List.filter (fun pred -> pred_equal w.w_pred pred) (given_closure givens) with
  | [] -> (
    match find_instance w.w_pred with
    | Some ((inst, sub)) -> (solve_wanteds givens (List.map (fun pred -> { w_pred = apply_subst_pred sub pred; w_span = w.w_span }) inst.instance_context))
    | None ->
      if has_meta_vars w.w_pred then [w] else failwith "Solve wanted failure: no instance"
  )
  | _ :: _ -> []
(* Try to discharge ONE wanted. Returns the residual wanteds that remain stuck;
   [] means fully solved. Raises NoInstance when definitely unsatisfiable.
   Precondition: the caller already applied the final substitution to w.
     1. If w.w_pred is pred_equal to some member of (given_closure givens),
        return [].
     2. Else match (find_instance w.w_pred) with
        | Some (inst, s) -> make a new wanted (same span) for each predicate in
           inst.instance_context with s applied, and return
           solve_wanteds givens of those. (Recursion is how
           `Show [Pair i32]` becomes `Show (Pair i32)`, then `Show i32`.)
        | None -> if has_meta_vars w.w_pred then [w]   (* stuck *)
                  else raise (NoInstance ...)            (* no instance and
                                                            nothing can change *)
   Haskell's `entail` + `simplify` in one function. *)

and solve_wanteds (givens : 'a predicate list) (ws : sourcespan wanted list) :
    sourcespan wanted list =
  List.concat (List.map (solve_wanted givens) ws)
;;

(* concat_map (solve_wanted givens) ws. *)

let entails (givens : sourcespan predicate list) (p : sourcespan predicate) : bool =
  try
    match solve_wanted givens {w_pred = p; w_span = dummy_span} with
    | [] -> true
    | _ -> false
  with
  | _ -> false
(* Boolean wrapper: true iff solve_wanted givens {p; dummy_span} returns []
   without raising (catch NoInstance, treat any residual as false). Use for the
   superclass-obligation check, where there is no meaningful span or error. *)

let rec skolemize_typ typ =
  match typ with
  | TyVar name -> (TyCon (Skolem (name)))
  | TyArrow (args, ret_type) -> TyArrow (List.map skolemize_typ args, skolemize_typ ret_type)
  | TyApp (generic_type, generic_param_types) ->
      TyApp (skolemize_typ generic_type, List.map skolemize_typ generic_param_types)
  | _ -> typ

let rec unskolemize_typ typ =
  match typ with
  | TyCon (Skolem (name)) -> TyVar name
  | TyArrow (args, ret_type) -> TyArrow (List.map unskolemize_typ args, unskolemize_typ ret_type)
  | TyApp (generic_type, generic_param_types) ->
      TyApp (unskolemize_typ generic_type, List.map unskolemize_typ generic_param_types)
  | _ -> typ

let skolemize_pred pred =
  { pred_class = pred.pred_class; pred_args = List.map skolemize_typ pred.pred_args}

let check_superclass_obligations (inst : sourcespan instance_info) : unit =
  let cls = lookup_class inst.instance_head.pred_class in
  let superclasses = cls.class_superclasses in
  let subst = List.combine cls.class_params inst.instance_head.pred_args in
  List.iter
  (fun superclass ->
    let s = apply_subst_pred subst superclass in
    let instance_vars_sub = List.map (fun v -> (v, TyCon (Skolem (v)))) inst.instance_vars in
    let res = entails (List.map (apply_subst_pred instance_vars_sub) inst.instance_context) (apply_subst_pred instance_vars_sub s) in
    if res then () else failwith "Check superclass obligations failure: no instance")
  superclasses
(* For `impl Ord for X`, the instance `Eq X` must exist (Haskell's superclass
   rule). For each superclass S of the class (over class_params), substitute
   class_params |-> inst.instance_head.pred_args and require
   `entails inst.instance_context S'`. FIRST replace instance_vars with
   TyCon(Skolem v) in both the context and S', because here the instance
   variables are rigid, not unknowns. Raise NoInstance otherwise. Call this
   after ALL instances are registered. *)

let scheme_of_decl (d : 'a decl) : 'a scheme =
  match d with
  | DFun (name, generics, args, _, _, ret_typ, _) ->
    let arg_tvs =
              List.map
                (fun arg ->
                  match arg with
                  | BName (_, _, typ, _) -> typ
                  | _ -> failwith "Unsupported binding type" )
                args
            in
    SForall(
      (List.map name_of_generic_bind generics),
      (List.concat (List.map predicates_of_generic_bind generics)),
      (TyArrow (arg_tvs, ret_typ))
    )
  | _ -> failwith "Cannot get scheme of non DFun"
(* DFun(name, generics, args, _, _, ret, _) ->
     SForall( names of generics,
              concat of the bounds in generics,
              TyArrow(annotated arg types, ret) ).
   Only DFun is legal; the args must be BName with an annotation (wf already
   enforces this). This replaces the `guesses` code in infer_group, which
   re-derived the quantified variables from ftv_typ; here they are exactly the
   declared generics. *)

let skolemize (s : 'a scheme) : 'a typ subst * 'a predicate list * 'a typ =
  match s with
  | SForall (args, predicates, typ) ->
      let sub = List.map (fun v -> (v, TyCon (Skolem v))) args in
      (sub, apply_subst_predicates sub predicates, apply_subst_typ sub typ)
(* Like instantiate_for_decl, but each quantified variable v is replaced by
   the rigid TyCon(Skolem v) instead of a fresh unification variable.
   Returns (v |-> skolem substitution, GIVENS = the scheme's predicates with
   the substitution applied, the skolemised type). Used when CHECKING a body.
   instantiate_for_decl stays for USE sites. *)

let instance_method_scheme (inst : 'a instance_info) (cls : 'a class_info) (m : 'a method_info) :
    'a scheme =
  let cls = lookup_class inst.instance_head.pred_class in
  SForall (
    inst.instance_vars @ (List.map name_of_generic_bind m.m_generics),
    inst.instance_context @ (List.concat (List.map predicates_of_generic_bind m.m_generics)),
    apply_subst_typ (List.combine cls.class_params inst.instance_head.pred_args) m.m_typ
  )
;;

(* The expected scheme for method m as implemented in inst:
     SForall( inst.instance_vars @ names of m.m_generics,
              inst.instance_context @ m's own bounds,
              m.m_typ with class_params |-> inst.instance_head.pred_args )
   For `impl Add for i32`, add gets `(i32, i32) -> i32` and no context. The
   class predicate itself is NOT a given: we are defining the instance. *)

(* Default method check uses scheme_of_method directly: its given is the
   class predicate `C Self` (plus superclasses via given_closure), which is
   exactly what a default body may assume. *)

let rec infer_exp (env : sourcespan scheme envt) (e : sourcespan expr) :
    sourcespan typ subst * sourcespan typ * sourcespan predicate list =
  let infer_app_typ
      (sch_subst : 'a subst)
      (sch_predicates : sourcespan predicate list)
      (sch_inst : sourcespan typ)
      (args : sourcespan expr list)
      env
      span : sourcespan typ subst * sourcespan typ * sourcespan predicate list =
    let new_env, new_subst, typs, arg_predicates =
      List.fold_left
        (fun (acc_env, acc_subst, acc_typs, acc_preds) arg ->
          let arg_subst, arg_typ, arg_preds = infer_exp acc_env arg in
          let final_subst = compose_subst acc_subst arg_subst in
          let new_env = apply_subst_schenv final_subst acc_env in
          (new_env, final_subst, acc_typs @ [arg_typ], acc_preds @ arg_preds) )
        (env, sch_subst, [], []) args
    in
    let arg_typs = List.map (apply_subst_typ new_subst) typs in
    let ret_typ = TyVar (gensym_typ "appresult") in
    let app_ty = apply_subst_typ new_subst (TyArrow (arg_typs, ret_typ)) in
    let result_subst = unify sch_inst app_ty span in
    (* (printf "result subst:\n%s\n" (ExtString.String.join "\n" (List.map (fun (s, typ) -> (sprintf "%s:%s" s (string_of_typ typ))) result_subst))); *)
    let final_subst = compose_subst new_subst result_subst in
    let ret_typ = apply_subst_typ final_subst ret_typ in
    let all_predicates = apply_subst_predicates final_subst (sch_predicates @ arg_predicates) in
    (final_subst, ret_typ, all_predicates)
  in
  match e with
  | ELiteral (LitBool _, _) -> ([], t_bool, [])
  | ELiteral (LitInt (n, suffix), loc) -> (
    match suffix with
    | IntSuffix width -> ([], TyCon (Int width), []) )
  | EId (x, loc) ->
      let cs, t = instantiate (StringMap.find x env) in
      ([], t, cs)
  | EPrim1 (op, e, loc) ->
      let sch =
        match op with
        | Print | PrintStack ->
            let new_typ = gensym_typ "prim1operand" in
            SForall ([new_typ], [], TyArrow ([TyVar new_typ], TyVar new_typ))
        | Add1 | Sub1 | Neg -> SForall ([], [], TyArrow ([t_i32], t_i32))
        | Not -> SForall ([], [], TyArrow ([t_bool], t_bool))
      in
      let sch_cs, sch_inst = instantiate sch in
      infer_app_typ [] sch_cs sch_inst [e] env loc
  | EPrim2 (op, l, r, loc) ->
      let sch =
        match op with
        | Plus ->
            let t = gensym_typ "addoperand" in
            SForall
              ( [t],
                [{pred_class= "Add"; pred_args= [TyVar t]}],
                TyArrow ([TyVar t; TyVar t], TyVar t) )
        | Minus | Times | Divide -> SForall ([], [], TyArrow ([t_i32; t_i32], t_i32))
        | Greater | GreaterEq | Less | LessEq -> SForall ([], [], TyArrow ([t_i32; t_i32], t_bool))
        | Eq ->
            let new_ty = gensym_typ "eqoperand" in
            SForall ([new_ty], [], TyArrow ([TyVar new_ty; TyVar new_ty], t_bool))
        | And | Or -> SForall ([], [], TyArrow ([t_bool; t_bool], t_bool))
        | _ -> failwith "unsupported"
      in
      let sch_cs, sch_inst = instantiate sch in
      infer_app_typ [] sch_cs sch_inst [l; r] env loc
  | EIf (c, t, f, span) ->
      let c_subst, c_typ, c_cs = infer_exp env c in
      let env = apply_subst_schenv c_subst env in
      let t_subst, t_typ, t_cs = infer_exp env t in
      let env = apply_subst_schenv t_subst env in
      let f_subst, f_typ, f_cs = infer_exp env f in
      let subst_so_far = compose_subst (compose_subst c_subst t_subst) f_subst in
      let c_typ = apply_subst_typ subst_so_far c_typ in
      let t_typ = apply_subst_typ subst_so_far t_typ in
      let f_typ = apply_subst_typ subst_so_far f_typ in
      let unif_subst1 = unify c_typ t_bool span in
      let unif_subst2 = unify t_typ f_typ span in
      let final_subst = compose_subst (compose_subst subst_so_far unif_subst1) unif_subst2 in
      let final_typ = apply_subst_typ final_subst t_typ in
      let all_constraints = apply_subst_predicates final_subst (c_cs @ t_cs @ f_cs) in
      (final_subst, final_typ, all_constraints)
  | ELet (binds, body, span) ->
      let new_env, new_subst, bind_cs =
        List.fold_left
          (fun (acc_env, acc_subst, acc_cs) (x, e, _) ->
            let b_subst, b_typ, b_cs = infer_exp acc_env e in
            let subst_so_far = compose_subst acc_subst b_subst in
            let new_env = apply_subst_schenv subst_so_far acc_env in
            let b_typ = apply_subst_typ subst_so_far b_typ in
            (* (printf "b_typ: %s\n" (string_of_typ b_typ));
            (printf "subst so far:\n%s\n" (ExtString.String.join "\n" (List.map (fun (s, typ) -> (sprintf "%s:%s" s (string_of_typ typ))) subst_so_far))); *)
            match x with
            | BName (name, _, typ, _) ->
                let typ = match typ with | TyBlank _ -> (TyVar (gensym_typ name)) | _ -> typ in
                let unified_subst = unify typ b_typ span in
                let final_subst = compose_subst subst_so_far unified_subst in
                (StringMap.add name (SForall ([], [], b_typ)) new_env, final_subst, acc_cs @ b_cs)
            | _ -> (new_env, subst_so_far, acc_cs @ b_cs) )
          (env, [], []) binds
      in
      let body_subst, body_typ, body_cs = infer_exp new_env body in
      let final_subst = compose_subst new_subst body_subst in
      let final_typ = apply_subst_typ final_subst body_typ in
      let all_constraints = apply_subst_predicates final_subst (bind_cs @ body_cs) in
      (final_subst, final_typ, all_constraints)
  | EApp (closure, args, _, loc) ->
      let clo_subst, clo_typ, clo_cs = infer_exp env closure in
      let env = apply_subst_schenv clo_subst env in
      infer_app_typ clo_subst clo_cs clo_typ args env loc
  | _ -> failwith "bad"
;;

let string_of_pred_list (pred_list : 'a predicate list) =
  ExtString.String.join "\n" (List.map string_of_pred pred_list)
;;

let generalize (env : 'a scheme envt) (predicates : 'a predicate list) (t : 'a typ) : 'a scheme =
  let quantified = StringSet.diff (ftv_typ t) (ftv_env env) in
  let kept, discharge_now =
    List.partition
      (fun pred ->
        let ftv_p = ftv_pred pred in
        (* (printf "freevars in %s:\n%s\n" (string_of_typ t) (ExtString.String.join "\n" (List.map (sprintf "%s") (StringSet.elements ftv_pred)))); *)
        not (StringSet.is_empty (StringSet.inter ftv_p quantified)) )
      predicates
  in
  (* printf "preds to keep:\n%s\n" (string_of_pred_list kept);
  printf "preds to discharge:\n%s\n" (string_of_pred_list discharge_now); *)
  (* List.iter check_instance_exists discharge_now; *)
  SForall (StringSet.elements quantified, kept, t)
;;

let name_of_bind b =
  match b with
  | BName (x, _, _, _) -> x
  | _ -> failwith "invalid bind form"
;;

let infer_decl env (decl : sourcespan decl) :
    sourcespan typ subst * sourcespan typ * sourcespan predicate list =
  match decl with
  | DFun (name, generics, args, body, call_type, typ, tag) -> (
      let sub, _, fun_typ = instantiate_for_decl (StringMap.find name env) in
      (* let declared_bounds (gen_name : string) : string list =
      (match List.find_opt (fun (orig, fty) -> match fty with
                             | TyVar(f, _) -> f = gen_name
                             | _ -> false) sub
      with
      | Some (orig, _) ->
        (match List.find_opt (fun (GBName(n, _, _)) -> n = orig) generics with
         | Some (GBName(_, bounds, _)) -> bounds
         | None -> [])
      | None -> [])
    in *)
      match fun_typ with
      | TyArrow (arg_typs, ret_typ) ->
          let body_env =
            List.fold_left2
              (fun acc arg t -> StringMap.add (name_of_bind arg) (SForall ([], [], t)) acc)
              env args arg_typs
          in
          let body_subst, body_typ, body_cs = infer_exp body_env body in
          let ret_typ = apply_subst_typ body_subst ret_typ in
          let unified_subst = unify body_typ ret_typ tag in
          let final_subst = compose_subst body_subst unified_subst in
          let final_typ = apply_subst_typ final_subst fun_typ in
          let final_cs = apply_subst_predicates final_subst body_cs in
          (final_subst, final_typ, final_cs)
      | _ -> failwith "expected arrow type for decl" )
  | _ -> failwith "infer_decl: expected a DFun"
;;

let infer_group env (group : sourcespan decl list) : sourcespan scheme envt =
  let guesses =
    List.map
      (fun decl ->
        match decl with
        | DFun (name, generics, args, body, call_type, typ, tag) ->
            let arg_tvs =
              List.map
                (fun arg ->
                  match arg with
                  | BName (_, _, typ, _) -> typ
                  | _ -> failwith "Unsupported binding type" )
                args
            in
            ( name,
              TyArrow (arg_tvs, typ),
              List.concat
                (List.map
                   (fun g ->
                     match g with
                     | GBName (_, predicates, _) -> predicates )
                   generics ) )
        | _ -> failwith "infer_group: expected a DFun" )
      group
  in
  let mono_env =
    List.fold_left
      (fun acc (name, typ, preds) ->
        StringMap.add name (SForall (StringSet.elements (ftv_typ typ), preds, typ)) acc )
      env guesses
  in
  let group_subst, results =
    List.fold_left
      (fun (subst_so_far, results_so_far) decl ->
        let s, t, cs = infer_decl (apply_subst_schenv subst_so_far mono_env) decl in
        let name =
          match decl with
          | DFun (name, _, _, _, _, _, _) -> name
          | _ -> failwith "infer_group: expected a DFun"
        in
        (compose_subst subst_so_far s, (name, t, cs) :: results_so_far) )
      ([], []) group
  in
  let outer_env = apply_subst_schenv group_subst env in
  List.fold_left
    (fun acc (name, t, cs) ->
      let final_typ = apply_subst_typ group_subst t in
      let final_cs = apply_subst_predicates group_subst cs in
      (* printf "for func %s:\n" name; *)
      StringMap.add name (generalize outer_env final_cs final_typ) acc )
    outer_env results
;;

let infer_prog (env : sourcespan scheme envt) (p : sourcespan program) : sourcespan program =
  match p with
  | Program (decls, tag) ->
      let _, _, funs = partition_decls decls in
      let _ = infer_group env funs in
      p
;;

(* =====================================================================
   TYPE CLASSES, SECTION C: elaborating type checker, built-ins,
   monomorphisation, new driver. When ready, replace infer_exp, infer_decl,
   infer_group, infer_prog and type_synth with the versions below
   (infer_exp_elab, check_decl, infer_prog_elab, type_synth_tc), delete the old
   ones, and rename.
   ===================================================================== *)

let rec map_types_in_expr (f : 'a typ -> 'a typ) (e : 'a expr) : 'a expr =
  let map_types_in_bind f b =
    match b with
    | BName (name, shadow, typ, tag) -> BName(name, shadow, (f typ), tag)
    | _ -> failwith "Unsupported binding type"
  in
  match e with
  | ESeq (e1, e2, tag) -> ESeq (map_types_in_expr f e1, map_types_in_expr f e2, tag)
  | ELet (bindings, body, tag) ->
    let new_bindings = List.map (fun (bind, bound_body, tag) ->
      ((map_types_in_bind f bind), (map_types_in_expr f bound_body), tag))
    bindings in
    ELet (new_bindings, map_types_in_expr f body, tag)
  | EPrim1 (op, body, tag) -> EPrim1 (op, map_types_in_expr f body, tag)
  | EPrim2 (op, l, r, tag) -> EPrim2 (op, map_types_in_expr f l, map_types_in_expr f r, tag)
  | EIf (cond, thn, els, tag) -> EIf (map_types_in_expr f cond, map_types_in_expr f thn, map_types_in_expr f els, tag)
  | EApp (closure, args, call_type, tag) ->
    EApp (map_types_in_expr f closure, List.map (map_types_in_expr f) args, call_type, tag)
  | ETyApp (body, tys, tag) ->
    ETyApp (map_types_in_expr f body, List.map f tys, tag)
  | _ -> e
(* Rebuild e applying f to every typ it contains: the annotations in BName
   binds inside ELet and the type-argument lists in ETyApp. Recurse through
   every expr constructor. This is the one traversal everything else is built
   from. *)

let apply_subst_expr (s : 'a typ subst) (e : 'a expr) : 'a expr =
  map_types_in_expr (apply_subst_typ s) e
(* map_types_in_expr (apply_subst_typ s). Used (a) to apply the final inference
   substitution to the ETyApp nodes (resolving the placeholders inserted
   during inference), and (b) by monomorphize to plug concrete types in for
   generic variables. *)
;;

let wanted_from_pred span pred =
  { w_pred = pred; w_span = span }
;;

let rec infer_exp_elab (env : sourcespan scheme envt) (e : sourcespan expr) :
    sourcespan typ subst * sourcespan typ * sourcespan wanted list * sourcespan expr =
  let infer_app_typ
      (make_expr)
      (sch_subst : 'a subst)
      (sch_wanteds : sourcespan wanted list)
      (sch_inst : sourcespan typ)
      (args : sourcespan expr list)
      env
      span : sourcespan typ subst * sourcespan typ * sourcespan wanted list * sourcespan expr =
    let new_env, new_subst, typs, arg_wanteds, new_args =
      List.fold_left
        (fun (acc_env, acc_subst, acc_typs, acc_wanteds, new_args) arg ->
          let arg_subst, arg_typ, arg_wanteds, new_arg = infer_exp_elab acc_env arg in
          let final_subst = compose_subst acc_subst arg_subst in
          let new_env = apply_subst_schenv final_subst acc_env in
          (new_env, final_subst, acc_typs @ [arg_typ], acc_wanteds @ arg_wanteds, new_args @ [new_arg]) )
        (env, sch_subst, [], [], []) args
    in
    let arg_typs = List.map (apply_subst_typ new_subst) typs in
    let ret_typ = TyVar (gensym_typ "appresult") in
    let app_ty = apply_subst_typ new_subst (TyArrow (arg_typs, ret_typ)) in
    let result_subst = unify sch_inst app_ty span in
    (* (printf "result subst:\n%s\n" (ExtString.String.join "\n" (List.map (fun (s, typ) -> (sprintf "%s:%s" s (string_of_typ typ))) result_subst))); *)
    let final_subst = compose_subst new_subst result_subst in
    let ret_typ = apply_subst_typ final_subst ret_typ in
    let all_predicates = apply_subst_wanteds final_subst (sch_wanteds @ arg_wanteds) in
    (final_subst, ret_typ, all_predicates, (make_expr new_args))
  in
  match e with
  | ELiteral (LitBool _, _) -> ([], t_bool, [], e)
  | ELiteral (LitInt (n, suffix), loc) -> (
    match suffix with
    | IntSuffix width -> ([], TyCon (Int width), [], e) )
  | EId (x, loc) ->
      let sub, preds, typ = instantiate_for_decl (StringMap.find x env) in
      let wanteds = List.map (wanted_from_pred loc) preds in
      let new_id = (
        match sub with
        | [] -> e
        | _ :: _ -> ETyApp(EId(x, loc), (List.map snd sub), loc)
      ) in
      ([], typ, wanteds, new_id)
  | EPrim1 (op, e, loc) ->
      let make_expr_args args = (
        match args with
        | [] -> failwith "what"
        | first :: _ -> EPrim1 (op, first, loc)
      ) in
      let sch =
        match op with
        | Print
        | PrintStack -> 
          let new_typ = gensym_typ "prim1operand" in
          SForall ([new_typ], [], TyArrow ([TyVar new_typ], TyVar new_typ))
        (* | Add1 | Sub1 | Neg -> SForall ([], [], TyArrow ([t_i32], t_i32)) *)
        | Not -> SForall ([], [], TyArrow ([t_bool], t_bool))
        | _ -> failwith "unsupported"
      in
      let sch_cs, sch_inst = instantiate sch in
      infer_app_typ make_expr_args [] (List.map (wanted_from_pred loc) sch_cs) sch_inst [e] env loc
  | EPrim2 (op, l, r, loc) ->
      let make_expr_args args = (
        match args with
        | first :: second :: _ -> EPrim2 (op, first, second, loc)
        | _ -> failwith "what"
      ) in
      let sch =
        match op with
        (* | Plus ->
            let t = gensym_typ "addoperand" in
            SForall
              ( [t],
                [{pred_class= "Add"; pred_args= [TyVar t]}],
                TyArrow ([TyVar t; TyVar t], TyVar t) )
        | Minus | Times | Divide -> SForall ([], [], TyArrow ([t_i32; t_i32], t_i32))
        | Greater | GreaterEq | Less | LessEq -> SForall ([], [], TyArrow ([t_i32; t_i32], t_bool))
        | Eq ->
            let new_ty = gensym_typ "eqoperand" in
            SForall ([new_ty], [], TyArrow ([TyVar new_ty; TyVar new_ty], t_bool)) *)
        | And | Or -> SForall ([], [], TyArrow ([t_bool; t_bool], t_bool))
        | _ -> failwith "unsupported"
      in
      let sch_cs, sch_inst = instantiate sch in
      infer_app_typ make_expr_args [] (List.map (wanted_from_pred loc) sch_cs) sch_inst [l; r] env loc
  | EIf (c, t, f, loc) ->
      let c_subst, c_typ, c_cs, new_cond = infer_exp_elab env c in
      let env = apply_subst_schenv c_subst env in
      let t_subst, t_typ, t_cs, new_true = infer_exp_elab env t in
      let env = apply_subst_schenv t_subst env in
      let f_subst, f_typ, f_cs, new_false = infer_exp_elab env f in
      let subst_so_far = compose_subst (compose_subst c_subst t_subst) f_subst in
      let c_typ = apply_subst_typ subst_so_far c_typ in
      let t_typ = apply_subst_typ subst_so_far t_typ in
      let f_typ = apply_subst_typ subst_so_far f_typ in
      let unif_subst1 = unify c_typ t_bool loc in
      let unif_subst2 = unify t_typ f_typ loc in
      let final_subst = compose_subst (compose_subst subst_so_far unif_subst1) unif_subst2 in
      let final_typ = apply_subst_typ final_subst t_typ in
      let all_constraints = apply_subst_wanteds final_subst (c_cs @ t_cs @ f_cs) in
      (final_subst, final_typ, all_constraints, EIf (new_cond, new_true, new_false, loc))
  | ELet (binds, body, let_loc) ->
      let new_env, new_subst, bind_cs, new_bindings =
        List.fold_left
          (fun (acc_env, acc_subst, acc_cs, acc_bindings) (x, e, bloc) ->
            let b_subst, b_typ, b_cs, new_e = infer_exp_elab acc_env e in
            let subst_so_far = compose_subst acc_subst b_subst in
            let new_env = apply_subst_schenv subst_so_far acc_env in
            let b_typ = apply_subst_typ subst_so_far b_typ in
            (* (printf "b_typ: %s\n" (string_of_typ b_typ));
            (printf "subst so far:\n%s\n" (ExtString.String.join "\n" (List.map (fun (s, typ) -> (sprintf "%s:%s" s (string_of_typ typ))) subst_so_far))); *)
            match x with
            | BName (name, shadow, typ, loc) ->
                let typ = match typ with | TyBlank _ -> (TyVar (gensym_typ name)) | _ -> typ in
                let unified_subst = unify typ b_typ loc in
                let final_subst = compose_subst subst_so_far unified_subst in
                (
                  StringMap.add name (SForall ([], [], b_typ)) new_env, 
                  final_subst, 
                  acc_cs @ b_cs, 
                  acc_bindings @ [(BName(name, shadow, b_typ, loc), new_e, bloc)])
            | x -> (new_env, subst_so_far, acc_cs @ b_cs, acc_bindings @ [(x, new_e, bloc)]) )
          (env, [], [], []) binds
      in
      let body_subst, body_typ, body_cs, new_body = infer_exp_elab new_env body in
      let final_subst = compose_subst new_subst body_subst in
      let final_typ = apply_subst_typ final_subst body_typ in
      let all_constraints = apply_subst_wanteds final_subst (bind_cs @ body_cs) in
      (final_subst, final_typ, all_constraints, ELet(new_bindings, new_body, let_loc))
  | EApp (closure, args, call_type, loc) ->
      let clo_subst, clo_typ, clo_wanted, new_clo_expr = infer_exp_elab env closure in
      let env = apply_subst_schenv clo_subst env in
      let make_expr new_args = EApp (new_clo_expr, new_args, call_type, loc) in
      infer_app_typ make_expr clo_subst clo_wanted clo_typ args env loc
  | _ -> failwith "bad"
;;

(* CHANGED SIGNATURE: the predicate list becomes `sourcespan wanted list`, and a
   fourth component is added: the ELABORATED expression. What to change in
   each case:
   - EId x: `let (sub, preds, t) = instantiate_for_decl (StringMap.find x env)`.
     Return ([], t, wanteds from preds tagged with loc,
             if sub = [] then EId x else ETyApp(EId x, List.map snd sub, loc)).
     Raise a normal error (not Not_found) if x is unbound.
   - EPrim1 / EPrim2: remove the hard-coded `Add` TyApp scheme and the
     Eq / Minus / Times / Greater... schemes for operators that now belong to
     classes. Those operators are rewritten to method calls by desugar (see
     3.7), so they never reach inference as EPrim2. Print/Not/And/Or etc. keep
     their prim schemes and are rebuilt unchanged in the output expr.
   - infer_app_typ: now accumulates wanteds and elaborated args as well.
   - EIf / ELet / ESeq / EApp: thread the 4th component through, and
     concatenate wanteds exactly as you now concatenate predicate lists.
   - Apply substitutions to the wanteds with apply_subst_wanted wherever you
     currently apply apply_subst_predicates.
   - `| _ -> failwith "bad"` must handle ETyApp (error: input should not
     contain it). *)

let check_decl (env : sourcespan scheme envt) (scheme : sourcespan scheme) (d : sourcespan decl) :
    sourcespan decl =
  let (skolem_subst, givens, fun_typ) = skolemize scheme in
  match d with
  | DFun(name, generic_binds, args, body, call_type, ret_typ, loc) -> (
    match fun_typ with
    | TyArrow(fun_args, fun_ret_typ) ->
      let new_body = apply_subst_expr skolem_subst body in
      let arg_typs = get_bind_typs args in
      let stated_typ = TyArrow(arg_typs, ret_typ) in
      let _ = unify stated_typ fun_typ loc in
      let body_env =
      List.fold_left2
        (fun acc arg t -> StringMap.add (name_of_bind arg) (SForall ([], [], t)) acc)
        env args fun_args
      in
      let (body_subst, new_body_typ, body_wanteds, new_new_body) = infer_exp_elab body_env new_body in
      let inferred_ret_typ = apply_subst_typ body_subst fun_ret_typ in
      let unified_subst = unify new_body_typ inferred_ret_typ loc in
      let final_subst = compose_subst body_subst unified_subst in
      let final_wanteds = apply_subst_wanteds final_subst body_wanteds in
      let residual = solve_wanteds givens final_wanteds in (
        match residual with
        | [] -> ()
        | _ -> failwith "Check decl failure: ambiguous type"
      );
      let new_new_new_body = map_types_in_expr unskolemize_typ (apply_subst_expr final_subst new_new_body) in
      DFun (name, generic_binds, args, new_new_new_body, call_type, ret_typ, loc)
    | _ -> failwith "Check decl failure: scheme type was not TyArrow"
  )
  | _ -> failwith "Check decl failure: cannot check non DFun"
;;

(* REPLACES infer_decl. Generalised so the scheme is a PARAMETER instead of
   being looked up by name; then one routine checks ordinary functions
   (scheme = scheme_of_decl d), instance methods (instance_method_scheme) and
   class default methods (scheme_of_method). Steps:
   1. (sk, givens, fun_typ) = skolemize scheme. fun_typ must be a TyArrow whose
      arity equals the number of declared args.
   2. Apply `sk` to the body and to the annotations (apply_subst_expr), so
      annotations like `let y: T = ...` become the skolem and not a flexible TyVar.
   3. For each declared arg annotation, unify it with the skolemised arg type from
      the scheme (matters for instance methods, where the user re-states the
      signature; harmless for plain DFuns).
   4. body_env = env + each arg |-> SForall([], [], its skolemised type).
   5. (s, body_typ, wanteds, body') = infer_exp body_env body.
   6. unify (apply s body_typ) (apply s ret) at the decl span; compose the
      substitutions as before.
   7. wanteds' = List.map (apply_subst_wanted final) wanteds;
      residual = solve_wanteds givens wanteds'. If residual <> [], raise
      AmbiguousType: a type variable is only constrained by a class and never
      fixed by an argument or return type.
   8. body'' = unskolemize applied via map_types_in_expr to
      (apply_subst_expr final body'). Return the DFun with body'' in place of
      the old body, everything else unchanged.
   No substitution leaks out: schemes are closed, so nothing needs threading
   between declarations. *)

let find_method_info cls d =
    match d with
    | DFun (name, _, _, _, _, _, _) -> 
      let result = List.filter (fun method_info -> method_info.m_name = name) cls.class_methods in (
        match result with
        | [found_info] -> found_info
        | _ -> failwith "Find method info failure: no method found"
      )
    | _ -> failwith "Find method info failure: given non DFun"
;;

let check_instance (env : sourcespan scheme envt) (d : sourcespan decl) : sourcespan decl =
  match d with
  | DInstance(generic_binds, instance_head, method_decls, loc) ->
    let cls = lookup_class instance_head.pred_class in
    let maybe_instance_info = find_instance instance_head in (
      match maybe_instance_info with
      | Some((instance_info, subst)) -> 
        check_superclass_obligations instance_info;
        let elaborated_decls = 
          List.map
          (fun decl ->
            let method_info = find_method_info cls decl in
            (method_info.m_name, check_decl env (instance_method_scheme instance_info cls method_info) decl))
          method_decls
        in
        List.iter
        (fun (name, decl) ->
          Hashtbl.add method_impl_table (instance_info.instance_id, name) (ImplDecl (decl)))
        elaborated_decls;
        DInstance(generic_binds, instance_head, snd (List.split elaborated_decls), loc)
      | None -> failwith "Check instance failure: no instance found??"
    )
  | _ -> failwith "Check instance failure: cannot check non DInstance"
(* d is a DInstance. Run after ALL classes and instances are registered.
   1. Look up the instance_info and the class.
   2. check_superclass_obligations.
   3. For each method DFun in the instance: find the matching method_info
      (else ExtraMethod); check_decl env (instance_method_scheme inst cls m) it;
      store the ELABORATED DFun in method_impl_table as
      ((instance_id, name), ImplDecl d').
   4. Return the DInstance rebuilt with the elaborated methods. *)

let method_sig_of_decl d =
  match d with
  | DFun (name, generic_binds, args, body, call_type, ret_typ, loc) ->
    {
      ms_name = name;
      ms_generics = generic_binds;
      ms_args = args;
      ms_ret = ret_typ;
      ms_default = Some(body);
      ms_span = loc
    }
  | _ -> failwith "Method sig of decl failure: cannot convert non DFun to method sig"
;;
let check_class_defaults (env: sourcespan scheme envt) (d : sourcespan decl) : sourcespan decl =
  match d with
  | DClass (name, params, superclasses, method_sigs, loc) ->
    let cls = lookup_class name in
    let methods_with_defaults = List.filter (fun method_info ->
      method_info.m_has_default)
    cls.class_methods in
    let elaborated_methods =
      List.map (fun method_info ->
        let default_decl = Hashtbl.find default_method_table (name, method_info.m_name) in
        (method_info.m_name, check_decl env (scheme_of_method cls method_info) default_decl))
      methods_with_defaults
    in
    List.iter
    (fun (method_name, decl) ->
      Hashtbl.replace default_method_table (name, method_name) decl)
    elaborated_methods;
    DClass (name, params, superclasses, List.map method_sig_of_decl (snd (List.split elaborated_methods)), loc)
  | _ -> failwith "Check class defaults: given non DClass"
(* d is a DClass. For each method with a default body, check_decl env
   (scheme_of_method cls m) default_fun, replace the entry in
   default_method_table with the elaborated DFun, and return the DClass with
   the elaborated defaults. The only given is `C Self` (plus superclasses), so
   a default may call other methods of the same class but nothing else. *)

let infer_prog_elab (env : sourcespan scheme envt) (p : sourcespan program) : sourcespan program =
  failwith "TODO"
;;

(* REPLACES infer_prog and infer_group; it now returns the ELABORATED program
   instead of `p` unchanged.
   1. Let funs = the DFuns. env' = env + (name |-> scheme_of_decl d) for each,
      so recursion and mutual recursion just work (no dependency analysis and
      no monomorphic-recursion guess, because every signature is explicit).
   2. check_decl env' (scheme_of_decl d) d for every DFun.
   3. check_instance / check_class_defaults for the other decls.
   4. Rebuild Program(decls', tag).
   `generalize` is no longer called for top-level functions. Keep it only if
   you later let functions omit their annotations. *)

let register_builtins () : unit = failwith "TODO"
(* Called once at the start of type_synth (replaces the commented-out block).
   Registers:
     class Add / Sub / Mul / Div  (Self): add/sub/mul/div : (Self, Self) -> Self
     class Neg (Self): neg : Self -> Self
     class Eq (Self): eq : (Self, Self) -> bool
     class Ord (Self): superclass Eq Self; gt/ge/lt/le : (Self, Self) -> bool
   and instances for each width in [I8; I16; I32; I64; I128] (Eq also for Bool),
   each with instance_vars = [] and instance_context = []. Also fill
   method_impl_table with ImplPrim2 Plus / Minus / ... and ImplPrim1 Neg, so
   that monomorphize can turn the call back into the primitive your code
   generator already knows. Build the class_infos by hand (or write tiny
   helpers); there is no source text for them. If you want only i32 at first,
   register just I32. *)

type mono_resolution =
  | ResolvedDecl of sourcespan decl * sourcespan typ subst
  (* a DFun body to specialise, plus the substitution for its type variables *)
  | ResolvedPrim1 of prim1
  | ResolvedPrim2 of prim2

type mono_state =
  { requested: (string, unit) Hashtbl.t; (* mangled names already queued *)
    worklist: (string * sourcespan typ list) Queue.t; (* generic fn name, concrete type args *)
    mutable emitted: sourcespan decl list (* finished concrete DFuns *) }

let mangle_name (base : string) (type_args : sourcespan typ list) : string = failwith "TODO"
(* A deterministic, collision-free symbol, e.g. mangle_name "id" [i32] =
   "id$i32". Must be injective on (base, args) and a legal LLVM symbol; escape
   or encode TyArrow / TyApp. Used as both the new decl name and the call
   target, and as the key into `requested`. *)

let resolve_method_call (meth : string) (type_args : sourcespan typ list) : mono_resolution =
  failwith "TODO"
;;

(* `type_args` are CONCRETE (no TyVar). Steps:
   1. (cls, m) = find_method meth. Split type_args into the first
      (List.length cls.class_params) class args and the remaining method args.
   2. pred = {cls.class_name; class args}. (inst, s) = find_instance pred; it
      must exist, because type checking proved it.
   3. Look up method_impl_table (inst.instance_id, meth):
        - ImplPrim1 / ImplPrim2 p  -> ResolvedPrim1 / ResolvedPrim2 p
        - ImplDecl d -> ResolvedDecl (d, s extended with the d's own generics
          |-> remaining method args, positionally).
      If the instance does not define the method, use default_method_table
      (cls.class_name, meth) with the substitution class_params |-> class args
      (+ method args). A default body that calls other methods of Self gets
      resolved again when it is itself monomorphised. *)

let specialize_decl (d : sourcespan decl) (s : sourcespan typ subst) (new_name : string) :
    sourcespan decl =
  failwith "TODO"
;;

(* Copy a DFun with: name = new_name, generics = [], arg and return type
   annotations substituted, and body = apply_subst_expr s body. The result
   has no type variables left. *)

let rec monomorphize_expr (st : mono_state) (e : sourcespan expr) : sourcespan expr =
  failwith "TODO"
;;

(* Structural traversal. The interesting cases:
   - EApp(ETyApp(EId f, tys, _), args, ct, loc), args monomorphised first:
       if f is a class method: match resolve_method_call f tys with
         | ResolvedPrim2 p -> EPrim2(p, a, b, loc)
         | ResolvedPrim1 p -> EPrim1(p, a, loc)
         | ResolvedDecl (d, s) -> name = mangle_name (decl name) tys; enqueue a
           specialisation (d, s, name) unless already in `requested`;
           EApp(EId(name, loc), args', FictolFunc, loc)
       else (ordinary generic function): name = mangle_name f tys; enqueue
         (f, tys); EApp(EId(name, loc), args', ct, loc).
   - A bare ETyApp that is not directly applied (a generic function or method
     used as a first-class value) is unsupported today (no closures): raise
     Unsupported.
   - If a TyVar is still present in tys, raise an internal compiler error. *)

let monomorphize (p : sourcespan program) : sourcespan program = failwith "TODO"
(* New phase after type checking.
   1. Seed: monomorphize_expr every NON-generic DFun (generics = []); keep it.
   2. Drain the worklist: for each (name, tys) not yet emitted, specialise the
      generic DFun (substitute generics |-> tys), monomorphize its body (which
      may enqueue more), emit it.
   3. Output Program(concrete DFuns only, tag). All DClass / DInstance and
      all generic DFuns disappear, so later phases and the code generator never
      see type classes. Polymorphic recursion through a type-changing call (f<T>
      calling f<List<T>>) never terminates; once you have parameterised types,
      add a depth limit. *)

let type_synth_tc (p : sourcespan program) : sourcespan program fallible =
  try
    match p with
    | Program (decls, tag) ->
      reset_class_state();
      register_builtins();
      let (classes, instances, funs) = partition_decls decls in
      List.iter register_class classes;
      validate_classes();
      List.iter (fun d -> register_instance (instance_info_of_decl d)) instances;
      let env = method_env () in
      let new_p = infer_prog_elab env p in
      Ok new_p
  with
    e -> Error [e]
    

(* The order is essential:
     reset_class_state ();
     register_builtins ();
     let (classes, instances, funs) = partition_decls decls in
     List.iter register_class classes;                 (* names + defaults *)
     validate_classes ();                              (* needs all classes *)
     List.iter (fun d -> register_instance (instance_info_of_decl d)) instances;
       (* heads only; ALL instances must be known before any body is checked *)
     let env = method_env () in
     let p' = infer_prog env p in                      (* runs check_instance and
                                                          check_class_defaults too *)
     Ok p'
   keep your `try ... with e -> Error [e]` around it. Also make sure
   check_superclass_obligations runs for built-in and user instances alike. *)

(* In compile_to_string, after the type_checked phase:
     |> add_err_phase type_checked type_synth
     |> add_phase monomorphized monomorphize        (* new phase name in Phases *)
     |> add_phase result compile_prog
*)

let type_synth (p : sourcespan program) : sourcespan program fallible =
  try Ok (infer_prog StringMap.empty p) with e -> Error [e]
;;

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let compile_prog (prog : sourcespan program) : string = sprintf "%s" (string_of_program prog)

let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase type_names_resolved resolve_prog_typ_paths
  |> add_err_phase type_checked type_synth
  (* when ready: type_synth_tc here, then
     |> add_phase monomorphized monomorphize   (* new phase name in Phases *) *)
  |> add_phase result compile_prog
;;
(* prog *)
(* |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase result compile_prog *)

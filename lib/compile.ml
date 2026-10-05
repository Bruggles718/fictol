open Printf
open Pretty
open Phases
open Exprs
open Types
open Errors
open Lexing
open Llvm
open Stdint
open Fictol_stubs
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

type 'a name_envt = (string * 'a) list

type 'a tag_envt = (tag * 'a) list

type 'a envt = 'a StringMap.t

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)

(* After type checking, every node of the AST carries its source span AND its type:
   `typed_tag expr`, `typed_tag decl`, `typed_tag program`. The AST is already
   parameterised over its tag, so exprs.ml does not change. What each tag's type means:
     - expression nodes: the type of that expression (for ETyApp and the EId inside it,
       the instantiated type of the identifier; for EApp, the result type);
     - BName binders: the binder's type;   - DFun: the function's TyArrow type;
     - everything else (BBlank, generic binders, DClass, DInstance, Program, ...):
       TyBlank, because there is no useful type. *)
type typed_tag = sourcespan * typ

let blank_tag (loc : sourcespan) : typed_tag = (loc, TyBlank loc)

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
let method_impl_table : (string * string, typed_tag method_impl) Hashtbl.t = Hashtbl.create 32
(* (instance_id, method name) -> implementation *)

let default_method_table : (string * string, sourcespan decl) Hashtbl.t = Hashtbl.create 16
(* (class name, method name) -> default body, stored as a DFun *)

let typed_default_method_table : (string * string, typed_tag decl) Hashtbl.t = Hashtbl.create 16
(* Same keys, but the TYPE-CHECKED bodies (filled by check_class_defaults). This is what
   monomorphisation reads; default_method_table keeps the untyped input that
   check_class_defaults consumes. method_impl_table is also typed: it is only filled
   by check_instance, after checking. *)

let reset_class_state () : unit =
  (* Clear all four tables. Call at the start of type_synth so repeated
   compilations in one process (tests!) don't see each other's classes. *)
  Hashtbl.clear class_table;
  Hashtbl.clear instance_table;
  Hashtbl.clear method_impl_table;
  Hashtbl.clear default_method_table;
  Hashtbl.clear typed_default_method_table
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
let desugar_overloaded_ops : bool ref = ref true

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

let add_builtins (p : sourcespan program) : sourcespan program =
  let widths = [I8; I16; I32; I64] in
  let uwidths = [U8; U16; U32; U64] in
  let int_types = List.map (fun w -> TyCon (Int w)) widths in
  let int_types = int_types @ (List.map (fun w -> TyCon (UInt w)) uwidths) in
  let bool_type = TyCon Bool in
  let self = TyVar "Self" in
  let params_self = ["Self"] in
  let make_arg name typ = BName (name, false, typ, dummy_span) in
  let make_prim2_method name ret_typ =
    { ms_name= name;
      ms_generics= [];
      ms_args= [make_arg "a" self; make_arg "b" self];
      ms_ret= ret_typ;
      ms_default= None;
      ms_span= dummy_span }
  in
  let make_prim1_method name ret_typ =
    { ms_name= name;
      ms_generics= [];
      ms_args= [make_arg "a" self];
      ms_ret= ret_typ;
      ms_default= None;
      ms_span= dummy_span }
  in
  let make_math_method name = make_prim2_method name self in
  let make_superclass name typs = {pred_class= name; pred_args= typs} in
  let make_class name params superclasses methods =
    DClass (name, params, superclasses, methods, dummy_span)
  in
  let math_classes =
    List.map
      (fun (cls_name, method_name) ->
        make_class cls_name params_self [] [make_math_method method_name] )
      ( List.map overloaded_prim2 [Plus; Minus; Times; Divide]
      |> List.map (fun maybe_op ->
          match maybe_op with
          | Some res -> res
          | None -> failwith "seriously what??" ) )
  in
  let neg_class = make_class "Neg" params_self [] [make_prim1_method "neg" self] in
  let eq_class = make_class "Eq" params_self [] [make_prim2_method "eq" bool_type] in
  let ord_class =
    make_class "Ord" params_self
      [make_superclass "Eq" [self]]
      [ make_prim2_method "gt" bool_type;
        make_prim2_method "ge" bool_type;
        make_prim2_method "lt" bool_type;
        make_prim2_method "le" bool_type ]
  in
  let built_in_classes = math_classes @ [eq_class; ord_class; neg_class] in
  let name_to_prim2_op name =
    match name with
    | "add" -> Plus
    | "sub" -> Minus
    | "mul" -> Times
    | "div" -> Divide
    | "eq" -> Eq
    | "gt" -> Greater
    | "ge" -> GreaterEq
    | "lt" -> Less
    | "le" -> LessEq
    | _ -> failwith "not prim2, what??"
  in
  let name_to_prim1_op name =
    match name with
    | "neg" -> Neg
    | _ -> failwith "not prim1, what??"
  in
  let inst_prim_for_typ cls typ =
    match cls with
    | DClass (name, params, superclasses, method_sigs, dummy_span) ->
        let method_impls =
          List.map
            (fun method_sig ->
              try
                let prim_op = name_to_prim2_op method_sig.ms_name in
                ImplPrim2 prim_op
              with _ ->
                let prim_op = name_to_prim1_op method_sig.ms_name in
                ImplPrim1 prim_op )
            method_sigs
        in
        DInstance ([], {pred_class= name; pred_args= [typ]}, method_impls, dummy_span)
    | _ -> failwith "not class, what??"
  in
  let instances =
    List.map
      (fun (cls, typs) -> List.map (fun typ -> inst_prim_for_typ cls typ) typs)
      (List.map (fun cls -> (cls, int_types)) built_in_classes)
    |> List.concat
  in
  let eq_bool_instance = inst_prim_for_typ eq_class bool_type in
  match p with
  | Program (decls, loc) -> Program (built_in_classes @ instances @ [eq_bool_instance] @ decls, loc)
;;

let wf_class_decl (d : sourcespan decl) : exn list = []
(* wf for DClass: duplicate method names within the class, duplicate params,
   superclass / bound classes exist (UnknownClass), default bodies are
   well-formed expressions in a scope containing the method args. *)

let wf_instance_decl (d : sourcespan decl) : exn list = []
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
          n > Uint64.max_int
        then
          [Overflow (n, loc)]
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
    | EApp (EId (name, id_loc), args, loc) ->
        let fun_err = wf_E (EId (name, id_loc)) env in
        fun_err @ wf_E_list args env
    | EApp (closure, args, loc) ->
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
  and helpImplD impl_d =
    match impl_d with
    | ImplDecl decl -> ImplDecl (helpD decl)
    | ImplPrim1 _ | ImplPrim2 _ -> impl_d
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
        DInstance (generics, head, List.map helpImplD methods, tag)
  and helpE e =
    match e with
    | ESeq (e1, e2, tag) -> ELet ([(BBlank tag, helpE e1, tag)], helpE e2, tag)
    | EId (x, tag) -> EId (x, tag)
    | ELiteral (n, tag) -> ELiteral (n, tag)
    | EPrim1 (op, body, tag) -> (
      match op with
      | _ when !desugar_overloaded_ops && Option.is_some (overloaded_prim1 op) ->
          let _, m = Option.get (overloaded_prim1 op) in
          EApp (EId (m, tag), [helpE body], tag)
      | Not -> EIf (helpE body, ELiteral (LitBool false, tag), ELiteral (LitBool true, tag), tag)
      | Add1 | Sub1 | Print | PrintStack | Neg -> EPrim1 (op, helpE body, tag) )
    | EPrim2 (op, left, right, tag) -> (
      match op with
      | _ when !desugar_overloaded_ops && Option.is_some (overloaded_prim2 op) ->
          let _, m = Option.get (overloaded_prim2 op) in
          EApp (EId (m, tag), [helpE left; helpE right], tag)
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
    | EApp (name, args, tag) -> EApp (helpE name, List.map helpE args, tag)
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

let rec resolve_typ_path env (typ : typ) =
  match typ with
  | TyPath (path, t) -> (
    match path with
    | ["i8"] -> TyCon (Int I8)
    | ["i16"] -> TyCon (Int I16)
    | ["i32"] -> TyCon (Int I32)
    | ["i64"] -> TyCon (Int I64)
    | ["u8"] -> TyCon (UInt U8)
    | ["u16"] -> TyCon (UInt U16)
    | ["u32"] -> TyCon (UInt U32)
    | ["u64"] -> TyCon (UInt U64)
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
  | TyArrow (args, ret_type, call_type) ->
      TyArrow
        ( List.map (fun arg -> resolve_typ_path env arg) args,
          resolve_typ_path env ret_type,
          call_type )
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
  and helpImplD_in outer impl_d =
    match impl_d with
    | ImplDecl decl -> ImplDecl (helpD_in outer decl)
    | ImplPrim1 _ | ImplPrim2 _ -> impl_d
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
            helpE generic_env body,
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
            List.map (helpImplD_in inst_env) methods,
            span )
  and helpSig class_env s =
    let env = class_env @ string_list_of_generics s.ms_generics in
    { s with
      ms_generics= List.map (helpGeneric env) s.ms_generics;
      ms_args= List.map (helpBind env) s.ms_args;
      ms_ret= resolve_typ_path env s.ms_ret;
      ms_default= Option.map (helpE env) s.ms_default }
  and helpBind env bind =
    match bind with
    | BName (name, shadow, typ, span) -> BName (name, shadow, resolve_typ_path env typ, span)
    | BBlank _ -> bind
  (* | _ -> failwith "should've been desugared" *)
  and helpE env expr =
    match expr with
    | ELet (bindings, body, span) ->
        let new_bindings =
          List.map
            (fun (bind, bind_body, span) -> (helpBind env bind, helpE env bind_body, span))
            bindings
        in
        ELet (new_bindings, helpE env body, span)
    | EIf (cond, thn, els, span) -> EIf (helpE env cond, helpE env thn, helpE env els, span)
    | EApp (closure, args, span) -> EApp (helpE env closure, List.map (helpE env) args, span)
    | ESeq (e1, e2, span) -> ESeq (helpE env e1, helpE env e2, span)
    | EPrim1 (op, body, span) -> EPrim1 (op, helpE env body, span)
    | EPrim2 (op, l, r, span) -> EPrim2 (op, helpE env l, helpE env r, span)
    | _ -> expr
  in
  helpP p
;;

let rec subst_var_typ ((tyvar : string), (to_typ : typ)) (in_typ : typ) : typ =
  match in_typ with
  | TyVar name ->
      if name = tyvar then
        to_typ
      else
        TyVar name
  | TyCon name -> TyCon name
  | TyArrow (args, ret_type, call_type) ->
      TyArrow
        ( List.map (fun arg -> subst_var_typ (tyvar, to_typ) arg) args,
          subst_var_typ (tyvar, to_typ) ret_type,
          call_type )
  | TyBlank t -> TyBlank t
  | TyApp (ret_typ, args) ->
      TyApp
        ( subst_var_typ (tyvar, to_typ) ret_typ,
          List.map (fun arg -> subst_var_typ (tyvar, to_typ) arg) args )
  | _ -> failwith "should have been resolved by now"
;;

let rec subst_var_typ_in_scheme
    ((tyvar : string), (to_typ : typ))
    (scheme_args : string list)
    (in_typ : typ) =
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
  | TyArrow (args, ret_type, call_type) ->
      TyArrow
        ( List.map (fun arg -> subst_var_typ_in_scheme (tyvar, to_typ) scheme_args arg) args,
          subst_var_typ_in_scheme (tyvar, to_typ) scheme_args ret_type,
          call_type )
  | TyBlank t -> TyBlank t
  | TyApp (ret_typ, args) ->
      TyApp
        ( subst_var_typ_in_scheme (tyvar, to_typ) scheme_args ret_typ,
          List.map (fun arg -> subst_var_typ_in_scheme (tyvar, to_typ) scheme_args arg) args )
  | _ -> failwith "should have been resolved by now"
;;

let rec subst_var_scheme ((tyvar : string), (to_typ : typ)) (in_scheme : 'a scheme) : 'a scheme =
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

and apply_subst_typ (subst : typ subst) (t : typ) : typ =
  List.fold_left (fun acc sub -> subst_var_typ sub acc) t subst

and apply_subst_scheme (subst : typ subst) (s : 'a scheme) : 'a scheme =
  List.fold_left (fun acc sub -> subst_var_scheme sub acc) s subst

and apply_subst_typenv (subst : typ subst) (env : typ envt) : typ envt =
  StringMap.map (fun typ -> apply_subst_typ subst typ) env

and apply_subst_schenv (subst : typ subst) (env : 'a scheme envt) : 'a scheme envt =
  StringMap.map (fun typ -> apply_subst_scheme subst typ) env

and apply_subst_subst (sub1 : typ subst) (sub2 : typ subst) : typ subst =
  List.map (fun (tyvar, to_typ) -> (tyvar, apply_subst_typ sub1 to_typ)) sub2

and apply_subst_pred (subst : typ subst) (p : 'a predicate) : 'a predicate =
  {p with pred_args= List.map (apply_subst_typ subst) p.pred_args}

and apply_subst_predicates (subst : typ subst) (predicates : 'a predicate list) : 'a predicate list
    =
  List.map (apply_subst_pred subst) predicates
;;

let compose_subst (sub1 : typ subst) (sub2 : typ subst) : typ subst =
  sub1 @ apply_subst_subst sub1 sub2
;;

let rec ftv_typ (t : typ) : StringSet.t =
  match t with
  | TyCon _ -> StringSet.empty
  | TyVar name -> StringSet.singleton name
  | TyArrow (args, ret, call_type) ->
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

let occurs (name : string) (t : typ) = StringSet.mem name (ftv_typ t)

let rec unify (t1 : typ) (t2 : typ) (span : sourcespan) : typ subst =
  let unify_tyvar_other tyvar other =
    if occurs tyvar other then
      match other with
      | TyVar other_name when other_name = tyvar -> []
      | _ ->
          failwith
            (sprintf "Unification failure: occurs check failed at <%s>" (string_of_sourcespan span))
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
          (sprintf "Unification failure at <%s>: inconsistent type constants %s and %s"
             (string_of_sourcespan span) (string_of_typ t1) (string_of_typ t2) )
  | TyArrow (t1_args, t1_ret_ty, t1_call_type), TyArrow (t2_args, t2_ret_ty, t2_call_type)
    when t1_call_type = t2_call_type -> unify_arrows t1_args t1_ret_ty t2_args t2_ret_ty
  | TyApp (t1_ret_ty, t1_args), TyApp (t2_ret_ty, t2_args) ->
      unify_arrows t1_args t1_ret_ty t2_args t2_ret_ty
  | _ -> failwith (sprintf "Unification failure at <%s>" (string_of_sourcespan span))

and unify_lists (ts1 : typ list) (ts2 : typ list) (span : sourcespan) : typ subst =
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

let instantiate (s : 'a scheme) : 'a predicate list * typ =
  match s with
  | SForall (args, predicates, typ) ->
      let sub = List.map (fun s -> (s, TyVar (gensym_typ "T"))) args in
      let res_typ = apply_subst_typ sub typ in
      let res_constraints = apply_subst_predicates sub predicates in
      (res_constraints, res_typ)
;;

let instantiate_for_decl (s : 'a scheme) : (string * typ) list * 'a predicate list * typ =
  match s with
  | SForall (args, predicates, typ) ->
      let sub = List.map (fun v -> (v, TyVar (gensym_typ "T"))) args in
      (sub, apply_subst_predicates sub predicates, apply_subst_typ sub typ)
;;

let get_return_typ (typ : typ) =
  match typ with
  | TyArrow (_, ret_typ, call_type) -> ret_typ
  | _ -> failwith (sprintf "Expected arrow type, got %s" (string_of_typ typ))
;;

(* =====================================================================
   TYPE CLASSES, SECTION B: predicate utilities, classes, instances,
   solving. Placed after instantiate_for_decl so gensym_typ is available.
   ===================================================================== *)


(* let string_of_pred (p : 'a predicate) : string =
  String.concat " " (p.pred_class :: List.map show_typ p.pred_args)
;; *)

let apply_subst_wanted (subst : typ subst) (w : 'a wanted) : 'a wanted =
  {w_pred= apply_subst_pred subst w.w_pred; w_span= w.w_span}
;;

let apply_subst_wanteds (subst : typ subst) (ws : 'a wanted list) : 'a wanted list =
  List.map (apply_subst_wanted subst) ws
;;

(* Substitute inside w.w_pred; keep w.w_span. *)

let rec typ_equal (t1 : typ) (t2 : typ) : bool =
  match (t1, t2) with
  | TyVar v1, TyVar v2 -> v1 = v2
  | TyCon k1, TyCon k2 -> k1 = k2
  | TyArrow (args1, ret1, call_type1), TyArrow (args2, ret2, call_type2) ->
      call_type1 = call_type2
      && List.length args1 = List.length args2
      && List.for_all2 typ_equal args1 args2
      && typ_equal ret1 ret2
  | TyApp (f1, args1), TyApp (f2, args2) ->
      List.length args1 = List.length args2
      && typ_equal f1 f2
      && List.for_all2 typ_equal args1 args2
  | TyPath (path1, _), TyPath (path2, _) -> path1 = path2
  | TyBlank _, TyBlank _ -> true
  | _ -> false
;;

let pred_equal (p1 : 'a predicate) (p2 : 'a predicate) : bool =
  p1.pred_class = p2.pred_class
  && List.length p1.pred_args = List.length p2.pred_args
  && List.for_all2 typ_equal p1.pred_args p2.pred_args
;;

let fresh_subst (vars : string list) : typ subst =
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
    let typ = TyArrow (get_bind_typs ms.ms_args, ms.ms_ret, FictolFunc) in
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
    | Some ms_default ->
        DFun (ms.ms_name, ms.ms_generics, ms.ms_args, ms_default, FictolFunc, ms.ms_ret, ms.ms_span)
    | None -> failwith (sprintf "Cannot convert method %s without a body" ms.ms_name)
  in
  match d with
  | DClass (name, params, superclasses, methods, span) ->
      if Hashtbl.mem class_table name then
        failwith (sprintf "Duplicate class at <%s>" (string_of_sourcespan span))
      else
        let cls_info = class_info_of_decl d in
        Hashtbl.add class_table name cls_info;
        List.iter
          (fun method_sig ->
            match method_sig.ms_default with
            | Some _ ->
                Hashtbl.add default_method_table (name, method_sig.ms_name)
                  (method_sig_to_dfun method_sig)
            | None -> () )
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
    | None ->
        failwith
          (sprintf "Validate classes failure: unknown class %s at <%s>" p.pred_class
             (string_of_sourcespan cls.class_span) )
    | Some target ->
        let expected = List.length target.class_params in
        let actual = List.length p.pred_args in
        if expected <> actual then
          failwith
            (sprintf "class %s takes %d argument(s) but is given %d in `%s` (in class %s)"
               p.pred_class expected actual (string_of_pred p) cls.class_name )
  in
  (* Superclass arguments may only mention this class's own parameters. *)
  let check_superclass_vars (cls : sourcespan class_info) : unit =
    let params = StringSet.of_list cls.class_params in
    List.iter
      (fun p ->
        let stray = StringSet.diff (ftv_pred p) params in
        if not (StringSet.is_empty stray) then
          failwith
            (sprintf
               "superclass `%s` of class %s mentions %s, which is not a parameter of the class"
               (string_of_pred p) cls.class_name
               (String.concat ", " (StringSet.elements stray)) ) )
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
      failwith
        (sprintf "Validate classes failure: cyclic superclass %s at <%s>" cls.class_name
           (string_of_sourcespan cls.class_span) )
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
                (sprintf "type parameter %s of method %s shadows a parameter of class %s" g m.m_name
                   cls.class_name );
            List.iter (check_pred_registered cls) bounds )
          m.m_generics;
        (* the method type must mention every class param, otherwise no call
           can determine which instance to use *)
        let missing = StringSet.diff params (ftv_typ m.m_typ) in
        if not (StringSet.is_empty missing) then
          failwith
            (sprintf "method %s of class %s is ambiguous: its type does not mention %s" m.m_name
               cls.class_name
               (String.concat ", " (StringSet.elements missing)) ) )
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
                 cls.class_name owner )
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
;;

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
  let cls = lookup_class p.pred_class in
  let params = cls.class_params in
  let subst = List.combine params p.pred_args in
  let instantiated_superclasses = List.map (apply_subst_pred subst) cls.class_superclasses in
  p :: List.concat (List.map superclass_closure instantiated_superclasses)
;;

let name_of_impldecl_dfun impl_d =
  match impl_d with
  | ImplDecl (DFun (name, _, _, _, _, _, _)) -> name
  | ImplPrim1 op -> (
    match overloaded_prim1 op with
    | Some (_, name) -> name
    | None -> failwith (sprintf "Cannot get decl name of prim1 %s" (string_of_op1 op)) )
  | ImplPrim2 op -> (
    match overloaded_prim2 op with
    | Some (_, name) -> name
    | None -> failwith (sprintf "Cannot get decl name of prim1 %s" (string_of_op2 op)) )
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
  | DInstance (generics, head, method_impls, span) ->
      { instance_vars= List.map name_of_generic_bind generics;
        instance_context= List.concat (List.map predicates_of_generic_bind generics);
        instance_methods= List.map name_of_impldecl_dfun method_impls;
        instance_span= span;
        instance_head= head;
        instance_id=
          head.pred_class ^ "##" ^ ExtString.String.join "#" (List.map string_of_typ head.pred_args)
      }
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
  let class_exists inst : sourcespan class_info =
    let cls_name = inst.instance_head.pred_class in
    match Hashtbl.find_opt class_table cls_name with
    | Some cls ->
        if List.length inst.instance_head.pred_args = List.length cls.class_params then
          cls
        else
          failwith "Class param arity mismatch"
    | None -> failwith (sprintf "No class %s found" cls_name)
  in
  let no_overlap cls_name inst : unit =
    let existing = Hashtbl.find instance_table cls_name in
    List.iter
      (fun inst_item ->
        if overlaps inst inst_item then
          failwith
            (sprintf "Overlapping instances %s and %s" inst.instance_id inst_item.instance_id) )
      existing
  in
  let context_and_params_check inst : unit =
    let context_vars =
      List.fold_left
        (fun acc pred -> StringSet.union acc (ftv_pred pred))
        StringSet.empty inst.instance_context
    in
    let head_vars = ftv_pred inst.instance_head in
    if StringSet.is_empty (StringSet.diff context_vars head_vars) then
      ()
    else
      failwith
        (sprintf "Mismatched variable usage in instance context and instance head for %s"
           inst.instance_id )
  in
  let class_info_required_method_names cls : StringSet.t =
    List.filter (fun method_info -> not method_info.m_has_default) cls.class_methods
    |> List.map (fun method_info -> method_info.m_name)
    |> StringSet.of_list
  in
  let methods_belong cls inst : unit =
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

let rec match_typ (pat_vars : StringSet.t) (pat : typ) (target : typ) (acc : typ subst) :
    typ subst option =
  match (pat, target) with
  | TyVar v, _ when StringSet.mem v pat_vars -> (
      let existing = List.filter (fun (tyvar, typ) -> tyvar = v) acc in
      match existing with
      | [] -> Some ((v, target) :: acc)
      | (tyvar, typ) :: _ ->
          if typ_equal target typ then
            Some acc
          else
            None )
  | TyVar v, TyVar t when (not (StringSet.mem v pat_vars)) && v = t -> Some acc
  | TyCon c, _ when typ_equal target pat -> Some acc
  | TyArrow (pat_args, pat_ret, pat_call_type), TyArrow (target_args, target_ret, target_call_type)
    when pat_call_type = target_call_type -> (
      let maybe_sub = match_typ pat_vars pat_ret target_ret acc in
      let arity_match = List.length pat_args = List.length target_args in
      match maybe_sub with
      | Some sub when arity_match -> match_typ_list pat_vars pat_args target_args sub
      | _ -> None )
  | TyApp (pat_ret, pat_args), TyApp (target_ret, target_args) -> (
      let maybe_sub = match_typ pat_vars pat_ret target_ret acc in
      let arity_match = List.length pat_args = List.length target_args in
      match maybe_sub with
      | Some sub when arity_match -> match_typ_list pat_vars pat_args target_args sub
      | _ -> None )
  | _ -> None

and match_typ_list
    (pat_vars : StringSet.t)
    (pat_lst : typ list)
    (target_lst : typ list)
    (acc : typ subst) =
  List.fold_left
    (fun acc_sub (p, t) ->
      match acc_sub with
      | Some acc_sub -> match_typ pat_vars p t acc_sub
      | None -> None )
    (Some acc) (List.combine pat_lst target_lst)
;;

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
    typ subst option =
  if pat.pred_class = target.pred_class then
    match_typ_list pat_vars pat.pred_args target.pred_args []
  else
    None
;;

(* Same class name, same arity, then fold match_typ over the argument pairs,
   threading the accumulator so repeated variables stay consistent. *)

let find_instance (p : sourcespan predicate) : (sourcespan instance_info * typ subst) option =
  let all_instances = Hashtbl.find instance_table p.pred_class in
  let rec helper instances =
    match instances with
    | [] -> None
    | first :: rest -> (
      match match_pred (StringSet.of_list first.instance_vars) first.instance_head p with
      | Some sub -> Some (first, sub)
      | None -> helper rest )
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
  List.concat (List.map superclass_closure givens)
;;

(* concat_map superclass_closure givens. With givens [Ord T] the closure is
   [Ord T; Eq T], so a wanted `Eq T` is solved without a separate Eq bound. *)

let rec solve_wanted (givens : 'a predicate list) (w : sourcespan wanted) : sourcespan wanted list =
  if List.exists (fun pred -> pred_equal w.w_pred pred) (given_closure givens) then
    []
  else
    match List.filter (fun pred -> pred_equal w.w_pred pred) (given_closure givens) with
    | [] -> (
      match find_instance w.w_pred with
      | Some (inst, sub) ->
          solve_wanteds givens
            (List.map
               (fun pred -> {w_pred= apply_subst_pred sub pred; w_span= w.w_span})
               inst.instance_context )
      | None ->
          if has_meta_vars w.w_pred then
            [w]
          else
            failwith
              (sprintf "Solve wanted failure: no instance %s. Add constraint at <%s>"
                 (string_of_pred w.w_pred) (string_of_sourcespan w.w_span) ) )
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
    match solve_wanted givens {w_pred= p; w_span= dummy_span} with
    | [] -> true
    | _ -> false
  with _ -> false
;;

(* Boolean wrapper: true iff solve_wanted givens {p; dummy_span} returns []
   without raising (catch NoInstance, treat any residual as false). Use for the
   superclass-obligation check, where there is no meaningful span or error. *)

let rec skolemize_typ typ =
  match typ with
  | TyVar name -> TyCon (Skolem name)
  | TyArrow (args, ret_type, call_type) ->
      TyArrow (List.map skolemize_typ args, skolemize_typ ret_type, call_type)
  | TyApp (generic_type, generic_param_types) ->
      TyApp (skolemize_typ generic_type, List.map skolemize_typ generic_param_types)
  | _ -> typ
;;

let rec unskolemize_typ typ =
  match typ with
  | TyCon (Skolem name) -> TyVar name
  | TyArrow (args, ret_type, call_type) ->
      TyArrow (List.map unskolemize_typ args, unskolemize_typ ret_type, call_type)
  | TyApp (generic_type, generic_param_types) ->
      TyApp (unskolemize_typ generic_type, List.map unskolemize_typ generic_param_types)
  | _ -> typ
;;

let skolemize_pred pred =
  {pred_class= pred.pred_class; pred_args= List.map skolemize_typ pred.pred_args}
;;

let check_superclass_obligations (inst : sourcespan instance_info) : unit =
  let cls = lookup_class inst.instance_head.pred_class in
  let superclasses = cls.class_superclasses in
  let subst = List.combine cls.class_params inst.instance_head.pred_args in
  List.iter
    (fun superclass ->
      let s = apply_subst_pred subst superclass in
      let instance_vars_sub = List.map (fun v -> (v, TyCon (Skolem v))) inst.instance_vars in
      let res =
        entails
          (List.map (apply_subst_pred instance_vars_sub) inst.instance_context)
          (apply_subst_pred instance_vars_sub s)
      in
      if res then
        ()
      else
        failwith "Check superclass obligations failure: no instance" )
    superclasses
;;

(* For `impl Ord for X`, the instance `Eq X` must exist (Haskell's superclass
   rule). For each superclass S of the class (over class_params), substitute
   class_params |-> inst.instance_head.pred_args and require
   `entails inst.instance_context S'`. FIRST replace instance_vars with
   TyCon(Skolem v) in both the context and S', because here the instance
   variables are rigid, not unknowns. Raise NoInstance otherwise. Call this
   after ALL instances are registered. *)

let scheme_of_decl (d : 'a decl) : 'a scheme =
  match d with
  | DFun (name, generics, args, _, call_type, ret_typ, _) ->
      let arg_tvs =
        List.map
          (fun arg ->
            match arg with
            | BName (_, _, typ, _) -> typ
            | _ -> failwith "Scheme of decl failure: Unsupported binding type" )
          args
      in
      SForall
        ( List.map name_of_generic_bind generics,
          List.concat (List.map predicates_of_generic_bind generics),
          TyArrow (arg_tvs, ret_typ, call_type) )
  | _ -> failwith "Scheme of decl failure: Cannot get scheme of non DFun"
;;

(* DFun(name, generics, args, _, _, ret, _) ->
     SForall( names of generics,
              concat of the bounds in generics,
              TyArrow(annotated arg types, ret) ).
   Only DFun is legal; the args must be BName with an annotation (wf already
   enforces this). This replaces the `guesses` code in infer_group, which
   re-derived the quantified variables from ftv_typ; here they are exactly the
   declared generics. *)

let skolemize (s : 'a scheme) : typ subst * 'a predicate list * typ =
  match s with
  | SForall (args, predicates, typ) ->
      let sub = List.map (fun v -> (v, TyCon (Skolem v))) args in
      (sub, apply_subst_predicates sub predicates, apply_subst_typ sub typ)
;;

(* Like instantiate_for_decl, but each quantified variable v is replaced by
   the rigid TyCon(Skolem v) instead of a fresh unification variable.
   Returns (v |-> skolem substitution, GIVENS = the scheme's predicates with
   the substitution applied, the skolemised type). Used when CHECKING a body.
   instantiate_for_decl stays for USE sites. *)

let instance_method_scheme (inst : 'a instance_info) (cls : 'a class_info) (m : 'a method_info) :
    'a scheme =
  SForall
    ( inst.instance_vars @ List.map name_of_generic_bind m.m_generics,
      inst.instance_context @ List.concat (List.map predicates_of_generic_bind m.m_generics),
      apply_subst_typ (List.combine cls.class_params inst.instance_head.pred_args) m.m_typ )
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

let string_of_pred_list (pred_list : 'a predicate list) =
  ExtString.String.join "\n" (List.map string_of_pred pred_list)
;;

let name_of_bind b =
  match b with
  | BName (x, _, _, _) -> x
  | _ -> failwith "invalid bind form"
;;

(* =====================================================================
   TYPE CLASSES, SECTION C: elaborating type checker, built-ins,
   monomorphisation, new driver. When ready, replace infer_exp, infer_decl,
   infer_group, infer_prog and type_synth with the versions below
   (infer_exp_elab, check_decl, infer_prog_elab, type_synth_tc), delete the old
   ones, and rename.
   ===================================================================== *)

let map_types_in_bind f b =
  match b with
  | BName (name, shadow, typ, tag) -> BName (name, shadow, f typ, tag)
  | BBlank _ -> b
;;

let rec map_types_in_expr (f : typ -> typ) (e : 'a expr) : 'a expr =
  match e with
  | ESeq (e1, e2, tag) -> ESeq (map_types_in_expr f e1, map_types_in_expr f e2, tag)
  | ELet (bindings, body, tag) ->
      let new_bindings =
        List.map
          (fun (bind, bound_body, tag) ->
            (map_types_in_bind f bind, map_types_in_expr f bound_body, tag) )
          bindings
      in
      ELet (new_bindings, map_types_in_expr f body, tag)
  | EPrim1 (op, body, tag) -> EPrim1 (op, map_types_in_expr f body, tag)
  | EPrim2 (op, l, r, tag) -> EPrim2 (op, map_types_in_expr f l, map_types_in_expr f r, tag)
  | EIf (cond, thn, els, tag) ->
      EIf (map_types_in_expr f cond, map_types_in_expr f thn, map_types_in_expr f els, tag)
  | EApp (closure, args, tag) ->
      EApp (map_types_in_expr f closure, List.map (map_types_in_expr f) args, tag)
  | ETyApp (body, tys, tag) -> ETyApp (map_types_in_expr f body, List.map f tys, tag)
  | _ -> e
;;

(* Rebuild e applying f to every typ it contains: the annotations in BName
   binds inside ELet and the type-argument lists in ETyApp. Recurse through
   every expr constructor. This is the one traversal everything else is built
   from. *)

let apply_subst_expr (s : typ subst) (e : 'a expr) : 'a expr =
  map_types_in_expr (apply_subst_typ s) e
;;

(* map_types_in_expr (apply_subst_typ s). Used (a) to apply the final inference
   substitution to the ETyApp nodes (resolving the placeholders inserted
   during inference), and (b) by monomorphize to plug concrete types in for
   generic variables. *)

(* ---------------------------------------------------------------------
   Typed-tag utilities.
   --------------------------------------------------------------------- *)

let tag_of_expr (e : 'a expr) : 'a =
  match e with
  | ESeq (_, _, t)
   |ELet (_, _, t)
   |EPrim1 (_, _, t)
   |EPrim2 (_, _, _, t)
   |EIf (_, _, _, t)
   |ELiteral (_, t)
   |EId (_, t)
   |EApp (_, _, t)
   |ETyApp (_, _, t) -> t
;;

let type_of_expr (e : typed_tag expr) : typ = snd (tag_of_expr e)

let span_of_expr (e : typed_tag expr) : sourcespan = fst (tag_of_expr e)

(* Rebuild an AST piece with every tag mapped by f. The tag type parameter changes, so
   predicates (whose 'a is phantom) are rebuilt too. *)
let map_tags_pred (p : 'a predicate) : 'b predicate =
  {pred_class= p.pred_class; pred_args= p.pred_args}
;;

let map_tags_bind (f : 'a -> 'b) (b : 'a bind) : 'b bind =
  match b with
  | BBlank tag -> BBlank (f tag)
  | BName (name, shadow, typ, tag) -> BName (name, shadow, typ, f tag)
;;

let map_tags_generic (f : 'a -> 'b) (g : 'a generic_bind) : 'b generic_bind =
  match g with
  | GBName (name, preds, tag) -> GBName (name, List.map map_tags_pred preds, f tag)
;;

let rec map_tags_expr (f : 'a -> 'b) (e : 'a expr) : 'b expr =
  let go = map_tags_expr f in
  match e with
  | ESeq (e1, e2, tag) -> ESeq (go e1, go e2, f tag)
  | ELet (bindings, body, tag) ->
      ELet
        ( List.map (fun (b, bound, btag) -> (map_tags_bind f b, go bound, f btag)) bindings,
          go body,
          f tag )
  | EPrim1 (op, body, tag) -> EPrim1 (op, go body, f tag)
  | EPrim2 (op, l, r, tag) -> EPrim2 (op, go l, go r, f tag)
  | EIf (c, t, el, tag) -> EIf (go c, go t, go el, f tag)
  | ELiteral (lit, tag) -> ELiteral (lit, f tag)
  | EId (x, tag) -> EId (x, f tag)
  | EApp (fn, args, tag) -> EApp (go fn, List.map go args, f tag)
  | ETyApp (body, tys, tag) -> ETyApp (go body, tys, f tag)
;;

let map_tags_method_sig (f : 'a -> 'b) (ms : 'a method_sig) : 'b method_sig =
  { ms_name= ms.ms_name;
    ms_generics= List.map (map_tags_generic f) ms.ms_generics;
    ms_args= List.map (map_tags_bind f) ms.ms_args;
    ms_ret= ms.ms_ret;
    ms_default= Option.map (map_tags_expr f) ms.ms_default;
    ms_span= f ms.ms_span }
;;

let rec map_tags_decl (f : 'a -> 'b) (d : 'a decl) : 'b decl =
  match d with
  | DFun (name, generics, args, body, call_type, ret_typ, tag) ->
      DFun
        ( name,
          List.map (map_tags_generic f) generics,
          List.map (map_tags_bind f) args,
          map_tags_expr f body,
          call_type,
          ret_typ,
          f tag )
  | DClass (name, params, supers, sigs, tag) ->
      DClass
        (name, params, List.map map_tags_pred supers, List.map (map_tags_method_sig f) sigs, f tag)
  | DInstance (generics, head, impls, tag) ->
      DInstance
        ( List.map (map_tags_generic f) generics,
          map_tags_pred head,
          List.map (map_tags_impl f) impls,
          f tag )

and map_tags_impl (f : 'a -> 'b) (impl : 'a method_impl) : 'b method_impl =
  match impl with
  | ImplDecl d -> ImplDecl (map_tags_decl f d)
  | ImplPrim1 op -> ImplPrim1 op
  | ImplPrim2 op -> ImplPrim2 op
;;

let map_tags_program (f : 'a -> 'b) (p : 'a program) : 'b program =
  match p with
  | Program (decls, tag) -> Program (List.map (map_tags_decl f) decls, f tag)
;;

(* typed program -> plain program, for the pretty printer *)
let strip_types (p : typed_tag program) : sourcespan program = map_tags_program fst p

(* Untyped pieces that sit inside a typed decl. *)
let lift_bind (b : sourcespan bind) : typed_tag bind =
  match b with
  | BName (name, shadow, typ, loc) -> BName (name, shadow, typ, (loc, typ))
  | BBlank loc -> BBlank (blank_tag loc)
;;

let lift_generic (g : sourcespan generic_bind) : typed_tag generic_bind =
  map_tags_generic blank_tag g
;;

(* Apply f to every type in a typed expression: the types inside the tags, plus the
   binder annotations and ETyApp arguments (map_types_in_expr). This is the zonk
   (final substitution, unskolemize) and the specialisation (generics |-> concrete). *)
let map_typed_types (f : typ -> typ) (e : typed_tag expr) : typed_tag expr =
  map_tags_expr (fun (loc, t) -> (loc, f t)) (map_types_in_expr f e)
;;

let map_typed_bind_types (f : typ -> typ) (b : typed_tag bind) : typed_tag bind =
  map_tags_bind (fun (loc, t) -> (loc, f t)) (map_types_in_bind f b)
;;

let wanted_from_pred span pred = {w_pred= pred; w_span= span}

let call_type_of_arrow_typ typ =
  match typ with
  | TyArrow (args, ret, ct) -> ct
  | _ -> failwith "call_type_of_arrow_typ failure: given non arrow type"
;;

let rec infer_exp_elab (env : sourcespan scheme envt) (e : sourcespan expr) :
    typ subst * typ * sourcespan wanted list * typed_tag expr =
  let infer_app_typ
      (make_expr : typed_tag expr list -> typ -> typed_tag expr)
      (sch_subst : 'a subst)
      (sch_wanteds : sourcespan wanted list)
      (sch_inst : typ)
      (args : sourcespan expr list)
      env
      span : typ subst * typ * sourcespan wanted list * typed_tag expr =
    let new_env, new_subst, typs, arg_wanteds, new_args =
      List.fold_left
        (fun (acc_env, acc_subst, acc_typs, acc_wanteds, new_args) arg ->
          let arg_subst, arg_typ, arg_wanteds, new_arg = infer_exp_elab acc_env arg in
          let final_subst = compose_subst acc_subst arg_subst in
          let new_env = apply_subst_schenv final_subst acc_env in
          ( new_env,
            final_subst,
            acc_typs @ [arg_typ],
            acc_wanteds @ arg_wanteds,
            new_args @ [new_arg] ) )
        (env, sch_subst, [], [], []) args
    in
    let arg_typs = List.map (apply_subst_typ new_subst) typs in
    let ret_typ = TyVar (gensym_typ "appresult") in
    let ct = call_type_of_arrow_typ sch_inst in
    let app_ty = apply_subst_typ new_subst (TyArrow (arg_typs, ret_typ, ct)) in
    let result_subst = unify sch_inst app_ty span in
    (* (printf "result subst:\n%s\n" (ExtString.String.join "\n" (List.map (fun (s, typ) -> (sprintf "%s:%s" s (string_of_typ typ))) result_subst))); *)
    let final_subst = compose_subst new_subst result_subst in
    let ret_typ = apply_subst_typ final_subst ret_typ in
    let all_predicates = apply_subst_wanteds final_subst (sch_wanteds @ arg_wanteds) in
    (final_subst, ret_typ, all_predicates, make_expr new_args ret_typ)
  in
  match e with
  | ELiteral (LitBool b, loc) -> ([], t_bool, [], ELiteral (LitBool b, (loc, t_bool)))
  | ELiteral (LitInt (n, suffix), loc) -> (
    match suffix with
    | IntSuffix width ->
        let t = TyCon (Int width) in
        ([], t, [], ELiteral (LitInt (n, suffix), (loc, t)))
    | UIntSuffix width ->
       let t = TyCon (UInt width) in
        ([], t, [], ELiteral (LitInt (n, suffix), (loc, t))))
  | EId (x, loc) ->
      let sub, preds, typ = instantiate_for_decl (StringMap.find x env) in
      let wanteds = List.map (wanted_from_pred loc) preds in
      let id_tag = (loc, typ) in
      let new_id =
        match sub with
        | [] -> EId (x, id_tag)
        | _ :: _ -> ETyApp (EId (x, id_tag), List.map snd sub, id_tag)
      in
      ([], typ, wanteds, new_id)
  | EPrim1 (op, e, loc) ->
      let make_expr_args args ret_typ =
        match args with
        | [] -> failwith "what"
        | first :: _ -> EPrim1 (op, first, (loc, ret_typ))
      in
      let sch =
        match op with
        | Print | PrintStack ->
            let new_typ = gensym_typ "prim1operand" in
            SForall ([new_typ], [], TyArrow ([TyVar new_typ], TyVar new_typ, Prim))
        (* | Add1 | Sub1 | Neg -> SForall ([], [], TyArrow ([t_i32], t_i32)) *)
        | Not -> SForall ([], [], TyArrow ([t_bool], t_bool, Prim))
        | _ -> failwith (sprintf "unsupported prim1 %s" (string_of_op1 op))
      in
      let sch_cs, sch_inst = instantiate sch in
      infer_app_typ make_expr_args [] (List.map (wanted_from_pred loc) sch_cs) sch_inst [e] env loc
  | EPrim2 (op, l, r, loc) ->
      let make_expr_args args ret_typ =
        match args with
        | first :: second :: _ -> EPrim2 (op, first, second, (loc, ret_typ))
        | _ -> failwith "what"
      in
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
        | And | Or -> SForall ([], [], TyArrow ([t_bool; t_bool], t_bool, Prim))
        | _ -> failwith (sprintf "unsupported prim2 %s" (string_of_op2 op))
      in
      let sch_cs, sch_inst = instantiate sch in
      infer_app_typ make_expr_args []
        (List.map (wanted_from_pred loc) sch_cs)
        sch_inst [l; r] env loc
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
      ( final_subst,
        final_typ,
        all_constraints,
        EIf (new_cond, new_true, new_false, (loc, final_typ)) )
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
                let typ =
                  match typ with
                  | TyBlank _ -> TyVar (gensym_typ name)
                  | _ -> typ
                in
                let unified_subst = unify typ b_typ loc in
                let final_subst = compose_subst subst_so_far unified_subst in
                ( StringMap.add name (SForall ([], [], b_typ)) new_env,
                  final_subst,
                  acc_cs @ b_cs,
                  acc_bindings @ [(BName (name, shadow, b_typ, (loc, b_typ)), new_e, (bloc, b_typ))]
                )
            | x ->
                ( new_env,
                  subst_so_far,
                  acc_cs @ b_cs,
                  acc_bindings @ [(lift_bind x, new_e, (bloc, b_typ))] ) )
          (env, [], [], []) binds
      in
      let body_subst, body_typ, body_cs, new_body = infer_exp_elab new_env body in
      let final_subst = compose_subst new_subst body_subst in
      let final_typ = apply_subst_typ final_subst body_typ in
      let all_constraints = apply_subst_wanteds final_subst (bind_cs @ body_cs) in
      (final_subst, final_typ, all_constraints, ELet (new_bindings, new_body, (let_loc, final_typ)))
  | EApp (closure, args, loc) ->
      let clo_subst, clo_typ, clo_wanted, new_clo_expr = infer_exp_elab env closure in
      let env = apply_subst_schenv clo_subst env in
      let make_expr new_args ret_typ = EApp (new_clo_expr, new_args, (loc, ret_typ)) in
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
    typed_tag decl =
  let skolem_subst, givens, fun_typ = skolemize scheme in
  match d with
  | DFun (name, generic_binds, args, body, call_type, ret_typ, loc) -> (
    match fun_typ with
    | TyArrow (fun_args, fun_ret_typ, ct) ->
        let new_body = apply_subst_expr skolem_subst body in
        let arg_typs = get_bind_typs args in
        let stated_typ = TyArrow (arg_typs, ret_typ, call_type) in
        let _ = unify stated_typ fun_typ loc in
        let body_env =
          List.fold_left2
            (fun acc arg t -> StringMap.add (name_of_bind arg) (SForall ([], [], t)) acc)
            env args fun_args
        in
        let body_subst, new_body_typ, body_wanteds, new_new_body =
          infer_exp_elab body_env new_body
        in
        let inferred_ret_typ = apply_subst_typ body_subst fun_ret_typ in
        let unified_subst = unify new_body_typ inferred_ret_typ loc in
        let final_subst = compose_subst body_subst unified_subst in
        let final_wanteds = apply_subst_wanteds final_subst body_wanteds in
        let residual = solve_wanteds givens final_wanteds in
        ( match residual with
        | [] -> ()
        | _ -> failwith "Check decl failure: ambiguous type" );
        (* zonk: the final substitution, then skolems back to the generics' TyVars, in
           every tag type, binder annotation and ETyApp argument *)
        let zonk t = unskolemize_typ (apply_subst_typ final_subst t) in
        let typed_body = map_typed_types zonk new_new_body in
        DFun
          ( name,
            List.map lift_generic generic_binds,
            List.map lift_bind args,
            typed_body,
            call_type,
            ret_typ,
            (loc, TyArrow (arg_typs, ret_typ, call_type)) )
    | _ -> failwith "Check decl failure: scheme type was not TyArrow" )
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
  let name = name_of_impldecl_dfun d in
  let result = List.filter (fun method_info -> method_info.m_name = name) cls.class_methods in
  match result with
  | [found_info] -> found_info
  | _ -> failwith "Find method info failure: no method found"
;;

let check_impl_decl env scheme impl_d : typed_tag method_impl =
  match impl_d with
  | ImplDecl decl -> ImplDecl (check_decl env scheme decl)
  | ImplPrim1 op -> ImplPrim1 op
  | ImplPrim2 op -> ImplPrim2 op
;;

let check_instance (env : sourcespan scheme envt) (d : sourcespan decl) : typed_tag decl =
  match d with
  | DInstance (generic_binds, instance_head, method_impls, loc) -> (
      let cls = lookup_class instance_head.pred_class in
      let maybe_instance_info = find_instance instance_head in
      match maybe_instance_info with
      | Some (instance_info, subst) ->
          check_superclass_obligations instance_info;
          let elaborated_impls =
            List.map
              (fun impl ->
                let method_info = find_method_info cls impl in
                ( method_info.m_name,
                  check_impl_decl env (instance_method_scheme instance_info cls method_info) impl ) )
              method_impls
          in
          List.iter
            (fun (name, impl) ->
              Hashtbl.add method_impl_table (instance_info.instance_id, name) impl )
            elaborated_impls;
          DInstance
            ( List.map lift_generic generic_binds,
              map_tags_pred instance_head,
              snd (List.split elaborated_impls),
              blank_tag loc )
      | None -> failwith "Check instance failure: no instance found??" )
  | _ -> failwith "Check instance failure: cannot check non DInstance"
;;

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
      { ms_name= name;
        ms_generics= generic_binds;
        ms_args= args;
        ms_ret= ret_typ;
        ms_default= Some body;
        ms_span= loc }
  | _ -> failwith "Method sig of decl failure: cannot convert non DFun to method sig"
;;

let check_class_defaults (env : sourcespan scheme envt) (d : sourcespan decl) : typed_tag decl =
  match d with
  | DClass (name, params, superclasses, method_sigs, loc) ->
      let cls = lookup_class name in
      let methods_with_defaults =
        List.filter (fun method_info -> method_info.m_has_default) cls.class_methods
      in
      let elaborated_methods =
        List.map
          (fun method_info ->
            let default_decl = Hashtbl.find default_method_table (name, method_info.m_name) in
            (method_info.m_name, check_decl env (scheme_of_method cls method_info) default_decl) )
          methods_with_defaults
      in
      (* the typed bodies go in their own table; default_method_table keeps the untyped input *)
      List.iter
        (fun (method_name, decl) ->
          Hashtbl.replace typed_default_method_table (name, method_name) decl )
        elaborated_methods;
      (* methods with a default get their elaborated body; the others are just re-tagged *)
      let typed_sigs =
        List.map
          (fun ms ->
            match List.assoc_opt ms.ms_name elaborated_methods with
            | Some typed_default -> method_sig_of_decl typed_default
            | None -> map_tags_method_sig blank_tag ms )
          method_sigs
      in
      DClass (name, params, List.map map_tags_pred superclasses, typed_sigs, blank_tag loc)
  | _ -> failwith "Check class defaults: given non DClass"
;;

(* d is a DClass. For each method with a default body, check_decl env
   (scheme_of_method cls m) default_fun, replace the entry in
   default_method_table with the elaborated DFun, and return the DClass with
   the elaborated defaults. The only given is `C Self` (plus superclasses), so
   a default may call other methods of the same class but nothing else. *)

let name_of_dfun d =
  match d with
  | DFun (name, _, _, _, _, _, _) -> name
  | _ -> failwith "Name of DFun failure: given non DFun"
;;

let infer_prog_elab (env : sourcespan scheme envt) (p : sourcespan program) : typed_tag program =
  match p with
  | Program (decls, loc) ->
      let classes, instances, funs = partition_decls decls in
      let new_env =
        List.fold_left
          (fun acc_env decl -> StringMap.add (name_of_dfun decl) (scheme_of_decl decl) acc_env)
          env funs
      in
      let new_funs = List.map (fun decl -> check_decl new_env (scheme_of_decl decl) decl) funs in
      let new_instances = List.map (fun inst -> check_instance new_env inst) instances in
      let new_classes = List.map (fun cls -> check_class_defaults new_env cls) classes in
      Program (new_classes @ new_instances @ new_funs, blank_tag loc)
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

type mono_resolution =
  | ResolvedDecl of typed_tag decl * typ subst
  | ResolvedPrim1 of prim1
  | ResolvedPrim2 of prim2

type mono_request =
  { template: typed_tag decl;
    subst: typ subst;
    new_name: string }

type mono_state =
  { requested: (string, unit) Hashtbl.t;
    worklist: mono_request Queue.t;
    mutable emitted: typed_tag decl list }

let rec typ_to_symbol (t : typ) : string =
  match t with
  | TyVar name -> name
  | TyCon tykind -> string_of_tykind tykind
  | TyArrow (ty_lst, ret_ty, call_type) ->
      "$"
      ^ ExtString.String.join "$" (List.map string_of_typ ty_lst)
      ^ "$arrow$$"
      ^ string_of_typ ret_ty
  | TyBlank _ -> "blank"
  | TyApp (generic_ty, generic_param_ty_lst) ->
      string_of_typ generic_ty
      ^ "$"
      ^ ExtString.String.join ", " (List.map string_of_typ generic_param_ty_lst)
      ^ "$"
  | TyPath (path, _) -> "::" ^ ExtString.String.join "::" path
;;

let mangle_name (base : string) (type_args : typ list) : string =
  List.fold_left (fun acc typ -> acc ^ "_" ^ typ_to_symbol typ) base type_args
;;

let resolve_method_call (meth : string) (type_args : typ list) : mono_resolution =
  let ice msg = failwith (sprintf "Resolve method call failure: %s" msg) in
  let split_at n l =
    let rec go n acc l =
      match l with
      | x :: rest when n > 0 -> go (n - 1) (x :: acc) rest
      | _ -> (List.rev acc, l)
    in
    go n [] l
  in
  let resolved_decl (decl : typed_tag decl) (method_args : typ list) (subst : typ subst) :
      mono_resolution =
    match decl with
    | DFun (name, generic_binds, _, _, _, _, _) ->
        let names = List.map name_of_generic_bind generic_binds in
        if List.length names <> List.length method_args then
          ice
            (sprintf "%s has %d type parameter(s) but was given %d method type argument(s)" name
               (List.length names) (List.length method_args) );
        ResolvedDecl (decl, List.combine names method_args @ subst)
    | _ -> ice "expected a DFun"
  in
  if List.exists (fun t -> not (StringSet.is_empty (ftv_typ t))) type_args then
    ice
      (sprintf "type arguments of %s are not concrete: %s" meth
         (String.concat ", " (List.map string_of_typ type_args)) );
  match find_method meth with
  | None -> ice (sprintf "method %s not found" meth)
  | Some (cls, _) ->
      let class_arg_count = List.length cls.class_params in
      let class_args, method_args = split_at class_arg_count type_args in
      if List.length class_args <> class_arg_count then
        ice
          (sprintf "method %s of class %s needs %d class type argument(s), got %d" meth
             cls.class_name class_arg_count (List.length type_args) );
      let pred = {pred_class= cls.class_name; pred_args= class_args} in
      begin match find_instance pred with
      | None -> ice (sprintf "no instance %s" (string_of_pred pred))
      | Some (inst, inst_subst) ->
        begin match Hashtbl.find_opt method_impl_table (inst.instance_id, meth) with
        | Some (ImplPrim1 op) -> ResolvedPrim1 op
        | Some (ImplPrim2 op) -> ResolvedPrim2 op
        | Some (ImplDecl d) -> resolved_decl d method_args inst_subst
        | None ->
          begin match Hashtbl.find_opt typed_default_method_table (cls.class_name, meth) with
          | Some d -> resolved_decl d method_args (List.combine cls.class_params class_args)
          | None ->
              ice
                (sprintf "instance %s does not define %s and class %s has no default"
                   inst.instance_id meth cls.class_name )
          end
        end
      end
;;

let specialize_decl (d : typed_tag decl) (s : typ subst) (new_name : string) : typed_tag decl =
  let sub = apply_subst_typ s in
  match d with
  | DFun (name, generic_binds, args, body, call_type, ret_typ, (loc, fun_typ)) ->
      DFun
        ( new_name,
          [],
          List.map (map_typed_bind_types sub) args,
          map_typed_types sub body,
          call_type,
          sub ret_typ,
          (loc, sub fun_typ) )
  | _ -> failwith "Specialize decl failure: given non DFun"
;;

let monomorphize (p : typed_tag program) : typed_tag program =
  match p with
  | Program (decls, tag) ->
      let _, _, funs = partition_decls decls in
      let st = {requested= Hashtbl.create 32; worklist= Queue.create (); emitted= []} in
      (* Find a top-level generic function. *)
      let find_function_template name =
        match
          List.find_opt
            (fun d ->
              match d with
              | DFun (dname, _, _, _, _, _, _) -> dname = name
              | _ -> false )
            funs
        with
        | Some d -> d
        | None -> failwith (sprintf "Monomorphize failure: could not find function %s" name)
      in
      let enqueue (template : typed_tag decl) (subst : typ subst) (new_name : string) =
        if not (Hashtbl.mem st.requested new_name) then begin
          Hashtbl.add st.requested new_name ();
          Queue.add {template; subst; new_name} st.worklist
        end
      in
      let rec monomorphize_expr (e : typed_tag expr) : typed_tag expr =
        match e with
        (* Generic function/method call. *)
        | EApp (ETyApp (EId (f_name, id_loc), tys, _), args, loc) ->
            (* Every type argument must be concrete by this point. *)
            List.iter
              (fun typ ->
                if not (StringSet.is_empty (ftv_typ typ)) then
                  raise
                    (InternalCompilerError
                       (sprintf "Found TyVar in monomorphize_expr: %s" (string_of_typ typ)) ) )
              tys;
            let args = List.map monomorphize_expr args in
            begin match find_method f_name with
            (* ---------------------------------------------------------
                 Type-class method
                 --------------------------------------------------------- *)
            | Some (_, _) ->
              begin match resolve_method_call f_name tys with
              | ResolvedPrim1 op -> EPrim1 (op, List.nth args 0, loc)
              | ResolvedPrim2 op -> EPrim2 (op, List.nth args 0, List.nth args 1, loc)
              | ResolvedDecl (d, subst) ->
                  let new_name = mangle_name (name_of_dfun d) tys in
                  (* DO NOT try to find `d` in `funs`.
                           `d` may live inside a DInstance. *)
                  enqueue d subst new_name;
                  EApp (EId (new_name, id_loc), args, loc)
              end
            (* ---------------------------------------------------------
                 Ordinary generic function
                 --------------------------------------------------------- *)
            | None ->
                let template = find_function_template f_name in
                let generic_binds =
                  match template with
                  | DFun (_, gs, _, _, _, _, _) -> gs
                  | _ -> failwith "Monomorphize failure: template is not a DFun"
                in
                let generic_names = List.map name_of_generic_bind generic_binds in
                if List.length generic_names <> List.length tys then
                  failwith
                    (sprintf "Monomorphize failure: %s expects %d type argument(s), got %d" f_name
                       (List.length generic_names) (List.length tys) );
                let subst = List.combine generic_names tys in
                let new_name = mangle_name f_name tys in
                enqueue template subst new_name;
                EApp (EId (new_name, id_loc), args, loc)
            end
        | EApp (closure, args, loc) ->
            EApp (monomorphize_expr closure, List.map monomorphize_expr args, loc)
        | ELet (bindings, body, loc) ->
            let new_bindings =
              List.map (fun (x, b, binding_loc) -> (x, monomorphize_expr b, binding_loc)) bindings
            in
            ELet (new_bindings, monomorphize_expr body, loc)
        | EIf (cond, thn, els, loc) ->
            EIf (monomorphize_expr cond, monomorphize_expr thn, monomorphize_expr els, loc)
        | EId _ | ELiteral _ -> e
        | _ -> failwith "Monomorphize failure: unsupported expression"
      in
      (* Non-generic functions are roots of the specialization graph.
         Generic functions themselves are templates and aren't emitted
         unless something actually calls them. *)
      let roots =
        List.filter_map
          (fun d ->
            match d with
            | DFun (name, [], args, body, call_type, ret_typ, loc) ->
                let new_body = monomorphize_expr body in
                Some (DFun (name, [], args, new_body, call_type, ret_typ, loc))
            | DFun (_, _generic_binds, _, _, _, _, _) -> None
            | _ -> None )
          funs
      in
      (* Generate requested specializations. *)
      while not (Queue.is_empty st.worklist) do
        let request = Queue.take st.worklist in
        let specialised = specialize_decl request.template request.subst request.new_name in
        match specialised with
        | DFun (name, generics, args, body, call_type, ret_typ, loc) ->
            let new_body = monomorphize_expr body in
            st.emitted <-
              DFun (name, generics, args, new_body, call_type, ret_typ, loc) :: st.emitted
        | _ -> failwith "Monomorphize failure: specialization was not a DFun"
      done;
      Program (roots @ List.rev st.emitted, tag)
;;

let type_synth_tc (p : sourcespan program) : typed_tag program fallible =
  try
    match p with
    | Program (decls, tag) ->
        reset_class_state ();
        (* register_builtins (); *)
        let classes, instances, funs = partition_decls decls in
        List.iter register_class classes;
        validate_classes ();
        List.iter (fun d -> register_instance (instance_info_of_decl d)) instances;
        let env = method_env () in
        let new_p = infer_prog_elab env p in
        Ok new_p
  with e -> Error [e]
;;

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

let tag_prog (p : 'a program) : (tag * typ) program =
  let next = ref 0 in
  let tag (span, typ) =
    next := !next + 1;
    (!next, typ)
  in
  map_tags_program tag p
;;

let rename_and_tag (p : (tag * typ) program) : (tag * typ) program =
  let rec rename env p =
    match p with
    | Program (decls, tag) -> Program (List.map (helpD env) decls, tag)
  and helpD env decl =
    match decl with
    | DFun (name, [], args, body, call_type, ret_typ, (tag, typ)) ->
        let newArgs, env' = helpBS env args in
        DFun (name, [], newArgs, helpE env' body, call_type, ret_typ, (tag, typ))
    | _ -> failwith "Rename and tag: Found non DFun after monomorphization?? Is that allowed?? Idk"
  and helpB env b =
    match b with
    | BBlank _ -> (b, env)
    | BName (name, allow_shadow, b_typ, (tag, typ)) ->
        let name' = sprintf "%s_%d" name tag in
        (BName (name', allow_shadow, b_typ, (tag, typ)), (name, name') :: env)
  and helpBS env (bs : (tag * typ) bind list) =
    match bs with
    | [] -> ([], env)
    | b :: bs ->
        let b', env' = helpB env b in
        let bs', env'' = helpBS env' bs in
        (b' :: bs', env'')
  and helpBG env (bindings : (tag * typ) binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE env e in
        let bindings', env'' = helpBG env' bindings in
        ((b', e', a) :: bindings', env'')
  and helpE env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE env e1, helpE env e2, tag)
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE env arg, tag)
    | EPrim2 (op, left, right, tag) -> EPrim2 (op, helpE env left, helpE env right, tag)
    | EIf (c, t, f, tag) -> EIf (helpE env c, helpE env t, helpE env f, tag)
    | ELiteral _ -> e
    | EId (name, tag) -> ( try EId (find env name, tag) with InternalCompilerError _ -> e )
    | EApp (func, args, tag) ->
        (* Figure out a way to determine call type. 
      Maybe build a global env of externs, and a global env of top level functions,
      and if its not in either then it's extern?
      But that doesn't work because how do I know what func is?
      maybe i have to resolve it later...
      WAIT! I can check the type of the expr func and determine if it's a closure or a regular arrow type.
      That tells me if it's a function or a closure. If arrow type, check a global extern env. If not found,
      FictolFunc. If found, extern of that type.
      WAIT AGAIN! This doesn't work because I don't have a name to look up in the env. func could be anything.
      Can I rely on well-formedness to prove any invariants? 
      Should the call type be encoded in the arrow type?
      
      OK heres what to do:
      after rename and ANF, each func will have a unique id and be called from that unique id, and I can
      know the call type from that. I'm not sure how this will work across function boundaries though.
      maybe don't have raw function pointers at all, only allow passing around explicit closures?*)
        let func = helpE env func in
        EApp (func, List.map (helpE env) args, tag)
    | ELet (binds, body, tag) ->
        let binds', env' = helpBG env binds in
        let body' = helpE env' body in
        ELet (binds', body', tag)
    | _ -> failwith "Rename and tag: unsupported expr"
  in
  rename [] p
;;

type 'a anf_bind =
  | BSeq of 'a cexpr * typ
  | BLet of string * typ * 'a cexpr

let anf (p : (tag * typ) program) : typ aprogram =
  let rec helpP (p : (tag * typ) program) : typ aprogram =
    match p with
    | Program (decls, (tag, typ)) -> AProgram (List.map helpD decls, typ)
  and helpD d =
    match d with
    | DFun (name, [], args, body, call_type, ret_typ, (tag, typ)) ->
        let new_args =
          List.map
            (fun arg ->
              match arg with
              | BName (b_name, _, b_typ, _) -> (b_name, b_typ)
              | _ -> failwith "anf: unsupported binding" )
            args
        in
        AFun (name, new_args, helpA body, call_type, ret_typ, typ)
    | _ -> failwith "anf: invalid decl"
  and helpC (e : (tag * typ) expr) : typ cexpr * typ anf_bind list =
    match e with
    | EPrim1 (op, arg, (tag, typ)) ->
        let arg_imm, arg_setup = helpI arg in
        (CPrim1 (op, arg_imm, typ), arg_setup)
    | EPrim2 (op, left, right, (tag, typ)) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (CPrim2 (op, left_imm, right_imm, typ), left_setup @ right_setup)
    | EIf (cond, _then, _else, (tag, typ)) ->
        let cond_imm, cond_setup = helpI cond in
        (CIf (cond_imm, helpA _then, helpA _else, typ), cond_setup)
    | ELet ([], body, _) -> helpC body
    | ELet ((BBlank _, exp, (tag, typ)) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq (exp_ans, typ)] @ body_setup)
    | ELet ((BName (bind, _, typ, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, typ, exp_ans)] @ body_setup)
    (* | ELet ((BTuple _, _, _) :: _, _, _) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away") *)
    | EApp (func, args, (tag, typ)) ->
        let func_ans, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        (CApp (func_ans, new_args, typ), func_setup @ List.concat new_setup)
    | ESeq (e1, e2, (tag, typ)) ->
        let e1_ans, e1_setup = helpC e1 in
        let e2_ans, e2_setup = helpC e2 in
        (e2_ans, e1_setup @ [BSeq (e1_ans, typ)] @ e2_setup)
    | _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : (tag * typ) expr) : typ immexpr * typ anf_bind list =
    match e with
    | ELiteral (litval, (tag, typ)) -> (ImmLiteral (litval, typ), [])
    | EId (name, (tag, typ)) -> (ImmId (name, typ), [])
    | ESeq (e1, e2, _) ->
        let _, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        (e2_imm, e1_setup @ e2_setup)
    | EPrim1 (op, arg, (tag, typ)) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, typ), arg_setup @ [BLet (tmp, typ, CPrim1 (op, arg_imm, typ))])
    | EPrim2 (op, left, right, (tag, typ)) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        ( ImmId (tmp, typ),
          left_setup @ right_setup @ [BLet (tmp, typ, CPrim2 (op, left_imm, right_imm, typ))] )
    | EIf (cond, _then, _else, (tag, typ)) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        ( ImmId (tmp, typ),
          cond_setup @ [BLet (tmp, typ, CIf (cond_imm, helpA _then, helpA _else, typ))] )
    | EApp (func, args, (tag, typ)) ->
        let tmp = sprintf "app_%d" tag in
        let new_func, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        ( ImmId (tmp, typ),
          func_setup @ List.concat new_setup @ [BLet (tmp, typ, CApp (new_func, new_args, typ))] )
    | ELet ([], body, _) -> helpI body
    | ELet ((BBlank _, exp, (tag, typ)) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq (exp_ans, typ)] @ body_setup)
    | ELet ((BName (bind, _, typ, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, typ, exp_ans)] @ body_setup)
    | _ -> failwith "anf: unsupported expr"
  and helpA e : typ aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq (exp, typ) -> ASeq (exp, body, typ)
        | BLet (name, typ, exp) -> ALet (name, exp, body, typ) )
      ans_setup (ACExpr ans)
  in
  helpP p
;;

let map_tags_immexpr (f : 'a -> 'b) (e : 'a immexpr) : 'b immexpr =
  match e with
  | ImmLiteral (lit, tag) -> ImmLiteral (lit, f tag)
  | ImmId (name, tag) -> ImmId (name, f tag)
;;

let map_tags_abind (f : 'a -> 'b) ((name, tag) : 'a abind) : 'b abind = (name, f tag)

let rec map_tags_cexpr (f : 'a -> 'b) (c : 'a cexpr) : 'b cexpr =
  let imm = map_tags_immexpr f in
  match c with
  | CIf (cond, then_, else_, tag) ->
      CIf (imm cond, map_tags_aexpr f then_, map_tags_aexpr f else_, f tag)
  | CPrim1 (op, arg, tag) -> CPrim1 (op, imm arg, f tag)
  | CPrim2 (op, left, right, tag) -> CPrim2 (op, imm left, imm right, f tag)
  | CApp (fn, args, tag) -> CApp (imm fn, List.map imm args, f tag)
  | CImmExpr e -> CImmExpr (imm e)

and map_tags_aexpr (f : 'a -> 'b) (a : 'a aexpr) : 'b aexpr =
  match a with
  | ASeq (first, rest, tag) -> ASeq (map_tags_cexpr f first, map_tags_aexpr f rest, f tag)
  | ALet (name, bound, body, tag) ->
      ALet (name, map_tags_cexpr f bound, map_tags_aexpr f body, f tag)
  | ACExpr c -> ACExpr (map_tags_cexpr f c)
;;

let map_tags_adecl (f : 'a -> 'b) (d : 'a adecl) : 'b adecl =
  match d with
  | AFun (name, args, body, call_type, ret_typ, tag) ->
      AFun (name, List.map (map_tags_abind f) args, map_tags_aexpr f body, call_type, ret_typ, f tag)
;;

let map_tags_aprogram (f : 'a -> 'b) (p : 'a aprogram) : 'b aprogram =
  match p with
  | AProgram (decls, tag) -> AProgram (List.map (map_tags_adecl f) decls, f tag)
;;

let tag_of_immexpr (e : 'a immexpr) : 'a =
  match e with
  | ImmLiteral (_, tag) | ImmId (_, tag) -> tag
;;

let tag_of_cexpr (c : 'a cexpr) : 'a =
  match c with
  | CIf (_, _, _, tag) | CPrim1 (_, _, tag) | CPrim2 (_, _, _, tag) | CApp (_, _, tag) -> tag
  | CImmExpr e -> tag_of_immexpr e
;;

let tag_of_aexpr (a : 'a aexpr) : 'a =
  match a with
  | ASeq (_, _, tag) | ALet (_, _, _, tag) -> tag
  | ACExpr c -> tag_of_cexpr c
;;

let tag_of_adecl (d : 'a adecl) : 'a =
  match d with
  | AFun (_, _, _, _, _, tag) -> tag
;;

let tag_of_aprogram (p : 'a aprogram) : 'a =
  match p with
  | AProgram (_, tag) -> tag
;;

let tag_of_abind ((_, tag) : 'a abind) : 'a = tag

let atag_prog p =
  let next = ref 0 in
  let tag typ =
    next := !next + 1;
    (!next, typ)
  in
  map_tags_aprogram tag p
;;

let typ_to_llvm_typ context typ =
  match typ with
  | TyCon tykind -> (
    match tykind with
    | Int I8 -> i8_type context
    | Int I16 -> i16_type context
    | Int I32 -> i32_type context
    | Int I64 -> i64_type context
    | UInt U8 -> i8_type context
    | UInt U16 -> i16_type context
    | UInt U32 -> i32_type context
    | UInt U64 -> i64_type context
    | Bool -> i1_type context
    | _ -> failwith "Typ to llvm typ failure: unsupported tykind" )
  | _ -> failwith "cannot convert non TyCon to llvm"
;;

let get_tycon_tykind typ =
  match typ with
  | TyCon tykind -> tykind
  | _ -> failwith "Cannot get tykind of non tycon"
;;

let typ_to_llvm_signed typ =
  match typ with
  | TyCon (Int _) -> true
  | TyCon (UInt _) -> false
  | _ -> failwith "non int cannot be signed or unsigned Unsupported"
;;

let typ_to_llvm_fn_type context typ =
  match typ with
  | TyArrow (args, ret, call_type) ->
      function_type (typ_to_llvm_typ context ret) (Array.of_list (List.map (typ_to_llvm_typ context) args))
  | _ -> failwith "expected a function type"
;;

let gensym_compile =
  let next = ref 0 in
  fun name ->
    next := !next + 1;
    sprintf "%s_%d" name !next
;;

let call_type_to_llvm_call_conv ct =
  match ct with
  | Extern "C" -> Llvm.CallConv.c
  | _ -> 18 (* tailcc *)
;;

let rec compile_afun context builder env (f : 'a adecl) : unit =
  match f with
  | AFun (name, binds, body, call_type, ret_typ, (tag, typ)) ->
      let llvm_fun = find env name in
      let args_env = List.combine (List.map fst binds) (Array.to_list (params llvm_fun)) in
      let bb = append_block context "entry" llvm_fun in
      position_at_end bb builder;
      (* the tail-mode compile emits a ret on every path, so there is no build_ret here *)
      ( match call_type with
      | Extern _ ->
          let compiled_body = compile_aexpr context builder (args_env @ env) body llvm_fun in
          let _ = build_ret compiled_body builder in
          ()
      | _ -> compile_aexpr_tail context builder (args_env @ env) body llvm_fun );
      Llvm_analysis.assert_valid_function llvm_fun

and forward_declare_func the_module context (f : 'a adecl) : string * llvalue =
  match f with
  | AFun (name, binds, body, call_type, ret_typ, (tag, typ)) ->
      let llvm_args =
        Array.of_list (List.map (fun (_, (_, b_typ)) -> typ_to_llvm_typ context b_typ) binds)
      in
      (* the real return type, not void *)
      let func_type = function_type (typ_to_llvm_typ context ret_typ) llvm_args in
      let llvm_fun = declare_function name func_type the_module in
      Llvm.set_function_call_conv (call_type_to_llvm_call_conv call_type) llvm_fun;
      (name, llvm_fun)

(* ---------- non-tail position: produces a value ---------- *)

and compile_aexpr context builder env (e : 'a aexpr) llvm_fun : llvalue =
  match e with
  | ACExpr c -> compile_cexpr context builder  env c llvm_fun
  | ALet (name, bound, body, _) ->
      let v = compile_cexpr context builder env bound llvm_fun in
      compile_aexpr context builder ((name, v) :: env) body llvm_fun
  | ASeq (first, rest, _) ->
      let _ = compile_cexpr context builder env first llvm_fun in
      compile_aexpr context builder env rest llvm_fun

and compile_cexpr context builder env (c : 'a cexpr) llvm_fun : llvalue =
  match c with
  | CImmExpr imm -> compile_immexpr context env imm
  | CPrim2 (op, left, right, (_, typ)) ->
      let l = compile_immexpr context env left in
      let r = compile_immexpr context env right in
      let _, ltyp = tag_of_immexpr left in
      let _, rtyp = tag_of_immexpr right in
      (prim2_to_llvm_op op ltyp rtyp) l r (gensym_compile "cprim2") builder
  | CPrim1 (op, body, (_, typ)) ->
      let b = compile_immexpr context env body in
      (prim1_to_llvm_op op typ) b (gensym_compile "cprim1") builder
  | CApp (closure, args, _) ->
      let _, closure_typ = tag_of_immexpr closure in
      let call_type = call_type_of_arrow_typ closure_typ in
      compile_call context builder env closure args call_type
  | CIf (cond, thn, els, _) ->
      let cond_imm = compile_immexpr context env cond in
      let if_name = gensym_compile "if" in
      let thn_bb = append_block context (if_name ^ "_then") llvm_fun in
      let els_bb = append_block context (if_name ^ "_else") llvm_fun in
      let merge_bb = append_block context (if_name ^ "_end") llvm_fun in
      let _ = build_cond_br cond_imm thn_bb els_bb builder in
      position_at_end thn_bb builder;
      let thn_val = compile_aexpr context builder env thn llvm_fun in
      let thn_end = insertion_block builder in
      (* the block the branch ENDED in *)
      let _ = build_br merge_bb builder in
      position_at_end els_bb builder;
      let els_val = compile_aexpr context builder env els llvm_fun in
      let els_end = insertion_block builder in
      let _ = build_br merge_bb builder in
      position_at_end merge_bb builder;
      build_phi [(thn_val, thn_end); (els_val, els_end)] (if_name ^ "_result") builder

(* ---------- tail position: emits `ret` on every path, returns unit ---------- *)

and compile_aexpr_tail context builder env (e : 'a aexpr) llvm_fun : unit =
  match e with
  | ACExpr c -> compile_cexpr_tail context builder env c llvm_fun
  | ALet (name, bound, body, _) ->
      let v = compile_cexpr context builder env bound llvm_fun in
      (* the bound value is NOT in tail position *)
      compile_aexpr_tail context builder ((name, v) :: env) body llvm_fun
  | ASeq (first, rest, _) ->
      let _ = compile_cexpr context builder env first llvm_fun in
      compile_aexpr_tail context builder env rest llvm_fun

and compile_cexpr_tail context builder env (c : 'a cexpr) llvm_fun : unit =
  match c with
  | CApp (closure, args, _) ->
      let _, closure_typ = tag_of_immexpr closure in
      let call_type = call_type_of_arrow_typ closure_typ in
      let call = compile_call context builder env closure args call_type in
      (* set_musttail call; *)
      ( match call_type with
      | Extern _ -> ()
      | _ -> Llvm.set_tail_call true call; set_musttail call );
      (* nothing may sit between the call and this ret *)
      let _ = build_ret call builder in
      ()
  | CIf (cond, thn, els, _) ->
      let cond_imm = compile_immexpr context env cond in
      let if_name = gensym_compile "if" in
      let thn_bb = append_block context (if_name ^ "_then") llvm_fun in
      let els_bb = append_block context (if_name ^ "_else") llvm_fun in
      let _ = build_cond_br cond_imm thn_bb els_bb builder in
      (* no merge block: each branch ends in its own ret *)
      position_at_end thn_bb builder;
      compile_aexpr_tail context builder env thn llvm_fun;
      position_at_end els_bb builder;
      compile_aexpr_tail context builder env els llvm_fun
  | CImmExpr _ | CPrim1 _ | CPrim2 _ ->
      let v = compile_cexpr context builder env c llvm_fun in
      let _ = build_ret v builder in
      ()

(* shared by both modes; only the tail version sets the tail marker *)
and compile_call context builder env closure args call_type : llvalue =
  let callee = compile_immexpr context env closure in
  let llvm_args = Array.of_list (List.map (compile_immexpr context env) args) in
  (* the FUNCTION type, taken from the callee's own type so it matches its declaration *)
  let fn_type = typ_to_llvm_fn_type context (snd (tag_of_immexpr closure)) in
  let call = build_call fn_type callee llvm_args (gensym_compile "app") builder in
  Llvm.set_instruction_call_conv (call_type_to_llvm_call_conv call_type) call;
  call

and compile_immexpr context env (e : 'a immexpr) : llvalue =
  match e with
  | ImmId (name, (tag, typ)) -> find env name
  | ImmLiteral (LitInt (n, suffix), (tag, typ)) ->
      const_of_int64 (typ_to_llvm_typ context typ) (Uint64.to_int64 n) (typ_to_llvm_signed typ)
  | ImmLiteral (LitBool true, (tag, typ)) -> const_int (i1_type context) 1
  | ImmLiteral (LitBool false, (tag, typ)) -> const_int (i1_type context) 0

and prim2_to_llvm_op op ltyp rtyp =
  let ltykind = get_tycon_tykind ltyp in
  let rtykind = get_tycon_tykind rtyp in
  match (op, ltykind, rtykind) with
  | Plus, Int _, Int _ | Plus, UInt _, UInt _-> build_add
  | Minus, Int _, Int _ | Minus, UInt _, UInt _ -> build_sub
  | Times, Int _, Int _ | Times, UInt _, UInt _-> build_mul
  | Divide, Int _, Int _ -> build_sdiv
  | Divide, UInt _, UInt _ -> build_udiv
  | Eq, Int _, Int _ | Eq, Bool, Bool | Eq, UInt _, UInt _ -> build_icmp Icmp.Eq
  | Greater, Int _, Int _ -> build_icmp Icmp.Sgt
  | GreaterEq, Int _, Int _ -> build_icmp Icmp.Sge
  | Less, Int _, Int _ -> build_icmp Icmp.Slt
  | LessEq, Int _, Int _ -> build_icmp Icmp.Sle
  | Greater, UInt _, UInt _ -> build_icmp Icmp.Ugt
  | GreaterEq, UInt _, UInt _ -> build_icmp Icmp.Uge
  | Less, UInt _, UInt _ -> build_icmp Icmp.Ult
  | LessEq, UInt _, UInt _ -> build_icmp Icmp.Ule
  | _ ->
      failwith
        (sprintf "unsupported prim2 to llvm op %s for typs %s %s" (string_of_op2 op)
           (string_of_typ ltyp) (string_of_typ rtyp) )

and prim1_to_llvm_op op typ =
  let tykind = get_tycon_tykind typ in
  match (op, tykind) with
  | Neg, _ -> build_neg
  | Not, _ -> build_not
  | _ ->
      failwith
        (sprintf "unsupported prim2 to llvm op %s for typ %s" (string_of_op1 op) (string_of_typ typ))
;;

let compile_prog context the_module builder (prog : (tag * typ) aprogram) : string =
  match prog with
  | AProgram (decls, (tag, typ)) ->
      let llvm_funs_env = List.map (forward_declare_func the_module context) decls in
      List.iter (compile_afun context builder llvm_funs_env) decls;
      string_of_llmodule the_module
;;

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let compile_to_string (module_name : string) (prog : sourcespan program pipeline) : string pipeline =
  let context = global_context () in
  let the_module = create_module context module_name in
  let builder = builder context in
  prog
  |> add_err_phase well_formed (fun p -> is_well_formed (add_builtins p))
  |> add_phase desugared desugar
  |> add_phase type_names_resolved resolve_prog_typ_paths
  (* |> add_err_phase type_checked type_synth *)
  (* when ready: type_synth_tc here, then
     |> add_phase monomorphized monomorphize   (* new phase name in Phases *) *)
  |> add_err_phase type_checked type_synth_tc
  |> add_phase monomorphized monomorphize
  |> add_phase tagged tag_prog
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag_prog (anf p))
  |> add_phase result (compile_prog context the_module builder)
;;
(* prog *)
(* |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase result compile_prog *)

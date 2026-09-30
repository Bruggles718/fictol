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
let t_i32 = TyCon(Int(I32), dummy_span)
let t_bool = TyCon(Bool, dummy_span)

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

type scope_info = sourcespan * int option * int option

let built_in_types = StringSet.of_list ["i32"; "bool"]

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
    | BName(name, _, typ, loc) ->
      (
        match typ with
        | TyBlank _ -> [(NoTypeAnnotation(name, loc))]
        | _ -> []
      )
    | _ -> [(NotYetImplemented ("unsupported binding type"))]
  and wf_E_list e_lst env =
    let results = List.map (fun e -> wf_E e env) e_lst in
    List.fold_left List.append [] results
  and wf_E e env =
    match e with
    | ELiteral(LitBool(_), _) -> []
    | ELiteral (LitInt(n, _), loc) ->
        if (Int128.of_uint128 n) > (Int128.of_int32 Int32.max_int) || (Int128.of_uint128 n) < (Int128.of_int32 Int32.min_int) then
          [Overflow ((Int128.of_uint128 n), loc)]
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
    | EApp (EId(name, id_loc), args, _, loc) ->
        let fun_err = wf_E (EId(name, id_loc)) env in
        fun_err @ wf_E_list args env
    | EApp (closure, args, _, loc) ->
        (* let fun_err = wf_E closure env in
        fun_err @ wf_E_list args env *)
        [Unsupported ("Calling closures is not yet supported", loc)]
    | ESeq (e1, e2, _) -> wf_E e1 env @ wf_E e2 env
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
        let typ_err_lst =
          List.map
          blank_typ_in_bind_errs
          args
          |> List.concat
        in
        let err_lst = args_err_lst @ typ_err_lst @ wf_E body env2 in
        err_lst
  and wf_D_list decls env =
    let full_env = get_new_env decls in
    List.concat
      (List.mapi
         (fun i d ->
           match d with
           | DFun (name, generics, _, _, ct, typ, loc) -> (
               let seq_env = full_env |> List.to_seq in
               let new_env =
                 Seq.append (Seq.take i seq_env) (Seq.drop (i + 1) seq_env) |> List.of_seq
               in
               let err_lst = wf_D d (full_env @ env) in
               try
                 let existing = List.assoc name new_env in
                 let err = DuplicateFun (name, loc, existing) in
                 [err] @ err_lst
               with Not_found -> err_lst )
          )
         decls )
  and get_new_env decls =
    match decls with
    | DFun (name, generics, _, _, ct, typ, loc) :: rest -> (name, loc) :: get_new_env rest
    | [] -> []
  in
  match p with
  | Program (decls, loc) -> (
      let rec helpP decls err_lst =
        (* let env = get_new_env decls in *)
        (wf_D_list decls [] @ err_lst)
      in
      let err_lst = helpP (decls) [] in
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
          [(b, EGetItem (source, ENumber (Int64.of_int i, dummy_span), tag), btag)]
      | BTuple (binds, tag) ->
          let newname = gensym "tup" in
          let newexpr = EId (newname, tag) in
          ( BName (newname, false, tag),
            EGetItem (source, ENumber (Int64.of_int i, dummy_span), tag),
            tag )
          :: expandTuple binds tag newexpr
    in
    let size_check =
      EPrim2 (CheckSize, source, ENumber (Int64.of_int (List.length binds), dummy_span), dummy_span)
    in
    let size_check_bind = (BBlank dummy_span, size_check, dummy_span) in
    size_check_bind :: List.flatten (List.mapi tupleBind binds) *)
  and helpG g = List.map helpD g
  and helpD d =
    match d with
    | DFun (name, generics, args, body, call_type, typ, tag) ->
      DFun (name, generics, args, helpE body, call_type, typ, tag)
  and helpE e =
    match e with
    | ESeq (e1, e2, tag) -> ELet ([(BBlank tag, helpE e1, tag)], helpE e2, tag)
    | EId (x, tag) -> EId (x, tag)
    | ELiteral (n, tag) -> ELiteral (n, tag)
    | EPrim1 (op, body, tag) -> (
      match op with
      | Not -> EIf (helpE body, ELiteral (LitBool(false), tag), ELiteral (LitBool(true), tag), tag)
      | Add1 | Sub1 | Print | PrintStack | Neg ->
          EPrim1 (op, helpE body, tag) )
    | EPrim2 (op, left, right, tag) -> (
      match op with
      | And ->
          EIf
            ( helpE left,
              helpE right,
              ELiteral (LitBool(false), tag),
              tag )
      | Or ->
          EIf
            ( helpE left,
              ELiteral (LitBool(true), tag),
              helpE right,
              tag )
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
  | Program (decls, tag) ->
    Program (helpG decls, tag)
;;

let rec resolve_typ_path (env) (typ : 'a typ) =
  match typ with
  | TyPath (path, t) -> 
    (
      match path with
      | ["i8"]   -> TyCon(Int I8,  t)
      | ["i16"]  -> TyCon(Int I16, t)
      | ["i32"]  -> TyCon(Int I32, t)
      | ["i64"]  -> TyCon(Int I64, t)
      | ["i128"] -> TyCon(Int I128, t)
      | ["bool"] -> TyCon(Bool, t)
      (* change to solve path eventually *)
      | [name] -> 
        if List.mem name env then
          TyVar(name, t)
        else
          failwith (sprintf "cannot resolve type %s" (ExtString.String.join "::" path))
      | _ -> failwith (sprintf "cannot resolve type %s" (ExtString.String.join "::" path))
    )
  | TyVar (name, t) -> TyVar(name, t)
  | TyCon (name, t) -> TyCon(name, t)
  | TyArrow (args, ret_type, t) -> TyArrow(List.map (fun arg -> (resolve_typ_path env arg)) args, (resolve_typ_path env ret_type), t)
  | TyBlank(t) -> TyBlank(t)
  | TyApp (ret_typ, args, t) -> TyApp((resolve_typ_path env ret_typ), List.map (fun arg -> (resolve_typ_path env arg)) args, t)

let resolve_prog_typ_paths (p : sourcespan program) : sourcespan program =
  let rec helpP p =
    (match p with
    | Program (decls, span) ->
      Program (List.map helpD decls, span))
  and string_list_of_generics gs =
    List.map 
    (fun g ->
      match g with
      | GBName(name, _, tag) -> name)
    gs
  and helpGeneric env g =
    match g with
    | GBName(name, predicates, tag) ->
      GBName(name,
        List.map (fun pred -> {pred_class = pred.pred_class; pred_args = (List.map (resolve_typ_path env) pred.pred_args)}) predicates,
        tag)
  and helpD decl =
    match decl with
    | DFun(name, generics, args, body, call_type, typ, span) ->
      let generic_env = (string_list_of_generics generics) in
      let new_args =
        List.map
        (fun arg ->
          helpBind generic_env arg)
        args in
      DFun(name, (List.map (helpGeneric generic_env) generics), new_args, helpE body, call_type, resolve_typ_path generic_env typ, span)
  and helpBind env bind =
    match bind with
    | BName(name, shadow, typ, span) -> BName(name, shadow, resolve_typ_path env typ, span)
    | BBlank _ -> bind
    (* | _ -> failwith "should've been desugared" *)
  and helpE expr =
    match expr with
    | ELet(bindings, body, span) ->
      let new_bindings =
        List.map
        (fun (bind, bind_body, span) ->
          (helpBind [] bind, helpE bind_body, span))
        bindings in
      ELet(new_bindings, helpE body, span)
    | _ -> expr
  in
  helpP p

let rec subst_var_typ ((tyvar : string), (to_typ : 'a typ)) (in_typ : 'a typ) : 'a typ =
  match in_typ with
  | TyVar (name, t) -> 
    (
      if name = tyvar then
        to_typ
      else
        (TyVar(name, t))
    )
  | TyCon (name, t) -> TyCon(name, t)
  | TyArrow (args, ret_type, t) -> TyArrow(List.map (fun arg -> (subst_var_typ (tyvar, to_typ) arg)) args, (subst_var_typ (tyvar, to_typ) ret_type), t)
  | TyBlank(t) -> TyBlank(t)
  | TyApp (ret_typ, args, t) -> TyApp((subst_var_typ (tyvar, to_typ) ret_typ), List.map (fun arg -> (subst_var_typ (tyvar, to_typ) arg)) args, t)
  | _ -> failwith "should have been resolved by now"

let rec subst_var_typ_in_scheme ((tyvar : string), (to_typ : 'a typ)) (scheme_args : string list) (in_typ : 'a typ) =
  match in_typ with
  | TyVar (name, t) -> 
    (
      if name = tyvar then
        if (List.mem name scheme_args) then
          in_typ
        else 
          to_typ
      else
        in_typ
    )
  | TyCon (name, t) -> TyCon(name, t)
  | TyArrow (args, ret_type, t) -> TyArrow(List.map (fun arg -> (subst_var_typ_in_scheme (tyvar, to_typ) scheme_args arg)) args, (subst_var_typ_in_scheme (tyvar, to_typ) scheme_args ret_type), t)
  | TyBlank(t) -> TyBlank(t)
  | TyApp (ret_typ, args, t) -> TyApp((subst_var_typ_in_scheme (tyvar, to_typ) scheme_args ret_typ), List.map (fun arg -> (subst_var_typ_in_scheme (tyvar, to_typ) scheme_args arg)) args, t)
  | _ -> failwith "should have been resolved by now"


let rec subst_var_scheme ((tyvar : string), (to_typ : 'a typ)) (in_scheme : 'a scheme) : 'a scheme =
  match in_scheme with
  | SForall(args, predicates, typ, t) -> 
      if List.mem tyvar args then
        in_scheme
      else
        let new_typ = subst_var_typ (tyvar, to_typ) typ in
        (* let new_constraints =
          List.map (fun (cls, cty) -> (cls, subst_var_typ (tyvar, to_typ) cty)) constraints
        in *)
        let new_predicates = apply_subst_predicates [(tyvar, to_typ)] predicates in
        SForall(args, new_predicates, new_typ, t)

and apply_subst_typ    (subst : 'a typ subst) (t : 'a typ) : 'a typ = 
  List.fold_left (fun acc sub -> subst_var_typ sub acc) t subst
    
and apply_subst_scheme (subst : 'a typ subst) (s : 'a scheme) : 'a scheme = 
  List.fold_left (fun acc sub -> subst_var_scheme sub acc) s subst

and apply_subst_typenv (subst : 'a typ subst) (env : 'a typ envt) : 'a typ envt = 
  StringMap.map (fun (typ) -> apply_subst_typ subst typ) env
and apply_subst_schenv (subst : 'a typ subst) (env : 'a scheme envt) : 'a scheme envt =
  StringMap.map (fun (typ) -> apply_subst_scheme subst typ) env
and apply_subst_subst (sub1 : 'a typ subst) (sub2 : 'a typ subst) : 'a typ subst =
  List.map (fun (tyvar, to_typ) -> (tyvar, (apply_subst_typ sub1 to_typ))) sub2

and apply_subst_predicates (subst : 'a typ subst) (predicates : 'a predicate list)
    : 'a predicate list =
  List.map (fun pred -> {pred_class = pred.pred_class; pred_args=(List.map (apply_subst_typ subst) pred.pred_args)}) predicates 

let compose_subst (sub1 : 'a typ subst) (sub2 : 'a typ subst) : 'a typ subst =
  sub1 @ (apply_subst_subst sub1 sub2)

let rec ftv_typ (t : 'a typ) : StringSet.t =
  match t with
  | TyCon _ -> StringSet.empty
  | TyVar(name, _) -> StringSet.singleton name
  | TyArrow(args, ret, _) ->
    List.fold_right (fun t ftvs -> StringSet.union (ftv_typ t) ftvs)
                    args
                    (ftv_typ ret)
  | TyApp(typ, args, _) ->
    List.fold_right (fun t ftvs -> StringSet.union (ftv_typ t) ftvs)
                    args
                    (ftv_typ typ)
  | TyBlank _ -> StringSet.empty
  | _ -> failwith "should have been resolved by now"
;;
let ftv_scheme (s : 'a scheme) : StringSet.t =
  match s with
  | SForall(args, predicates, typ, _) ->
    let bound = StringSet.of_list args in
    let ftv_predicates =
      List.fold_left
        (fun acc pred -> StringSet.union acc (List.fold_left StringSet.union StringSet.empty (List.map ftv_typ pred.pred_args)))
        StringSet.empty predicates
    in
    StringSet.diff (StringSet.union (ftv_typ typ) ftv_predicates) bound
let ftv_env (e : 'a scheme envt) : StringSet.t =
  let mapped = StringMap.map (fun (sch) -> ftv_scheme sch) e in
  StringMap.fold (fun _ value acc -> StringSet.union acc value) mapped StringSet.empty

let occurs (name : string) (t : 'a typ) =
  StringSet.mem name (ftv_typ t)

let rec unify (t1 : 'a typ) (t2 : 'a typ) (span: sourcespan) : 'a typ subst =
  let unify_tyvar_other tyvar other =
    if occurs tyvar other then
      []
    else
      [(tyvar, other)]
  in
  let unify_arrows t1_args t1_ret_ty t2_args t2_ret_ty =
    let unified_args = unify_lists t1_args t2_args span in
    let t1_ret_ty = apply_subst_typ unified_args t1_ret_ty in
    let unified_rets = unify t1_ret_ty t2_ret_ty span in
    compose_subst unified_args unified_rets
  in
  match t1, t2 with
  | TyVar(name, _), other
  | other, TyVar(name, _) -> unify_tyvar_other name other
  | TyCon(name1, _), TyCon(name2, _) -> 
    if name1 = name2 then
      []
    else
      failwith (sprintf "Unification failure at <%s>: inconsistent type constants" (string_of_sourcespan span))
  | TyArrow(t1_args, t1_ret_ty, t1_tag), TyArrow(t2_args, t2_ret_ty, t2_tag)
  | TyApp(t1_ret_ty, t1_args, t1_tag), TyApp(t2_ret_ty, t2_args, t2_tag) ->
    unify_arrows t1_args t1_ret_ty t2_args t2_ret_ty
  | _ -> failwith (sprintf "Unification failure at <%s>" (string_of_sourcespan span))
and unify_lists (ts1: 'a typ list) (ts2: 'a typ list) (span: sourcespan) : 'a typ subst =
    match ts1, ts2 with
    | first1 :: rest1, first2 :: rest2 ->
      let sub = unify first1 first2 span in
      let rest1 = List.map (apply_subst_typ sub) rest1 in
      let rest2 = List.map (apply_subst_typ sub) rest2 in
      let new_sub = unify_lists rest1 rest2 span in
      compose_subst sub new_sub
    | [], [] -> []
    | _, _ -> failwith "unify_lists: mismatched list lengths"
;;

let classes   : (string, 'a class_info) Hashtbl.t = Hashtbl.create 8
let instances : (string, 'a instance_info list) Hashtbl.t = Hashtbl.create 8

let unifiable (p1 : 'a predicate) (p2 : 'a predicate) : bool =
  try
    let _ = unify_lists p1.pred_args p2.pred_args dummy_span in
    true
  with _ -> false

let register_instance (cls : string) (inst : 'a instance_info) =
  let existing =
    match Hashtbl.find_opt instances cls with
    | Some insts -> insts
    | None -> []
  in
  if List.exists (fun i -> unifiable i.instance_head inst.instance_head) existing then
    failwith (Printf.sprintf "overlapping instances for %s" cls)
  else
    Hashtbl.replace instances cls ( inst :: existing)

let check_instance_exists (pred : 'a predicate) =
  match Hashtbl.find_opt instances pred.pred_class with
  | Some insts when List.exists (fun i -> i.instance_head = pred) insts -> ()
  | _ -> failwith (Printf.sprintf "no instance of %s" (string_of_pred pred))

let gensym_typ =
    let count = ref 0 in
    let next () =
      count := !count + 1;
      !count
    in fun str -> sprintf "%s_%d" str (next ())
;;
let instantiate (s : 'a scheme) : 'a predicate list * 'a typ =
  match s with
  | SForall(args, predicates, typ, tag) ->
    let sub = List.map (fun s -> (s, (TyVar(gensym_typ "T", tag)))) args in
    let res_typ = apply_subst_typ sub typ in
    let res_constraints = apply_subst_predicates sub predicates in
    (res_constraints, res_typ)

let instantiate_for_decl (s : 'a scheme)
    : (string * 'a typ) list * 'a predicate list * 'a typ =
  match s with
  | SForall(args, predicates, typ, _tag) -> 
  let sub = List.map (fun v -> (v, TyVar(gensym_typ "T", dummy_span))) args in
  (sub, apply_subst_predicates sub predicates, apply_subst_typ sub typ)

let get_return_typ (typ : 'a typ) =
  match typ with
  | TyArrow(_, ret_typ, _) -> ret_typ
  | _ -> failwith "Expected arrow type"


let rec infer_exp (env : sourcespan scheme envt) (e : sourcespan expr)
    : (sourcespan typ subst * sourcespan typ * sourcespan predicate list) =
  let infer_app_typ (sch_subst : 'a subst) (sch_predicates : sourcespan predicate list)
                     (sch_inst : sourcespan typ) (args : sourcespan expr list) (env) (span)
      : (sourcespan typ subst * sourcespan typ * sourcespan predicate list) =
    let (new_env, new_subst, typs, arg_predicates) =
      List.fold_left
        (fun (acc_env, acc_subst, acc_typs, acc_preds) arg ->
          let (arg_subst, arg_typ, arg_preds) = infer_exp acc_env arg in
          let final_subst = compose_subst acc_subst arg_subst in
          let new_env = apply_subst_schenv final_subst acc_env in
          (new_env, final_subst, acc_typs @ [arg_typ], acc_preds @ arg_preds))
        (env, sch_subst, [], []) args
    in
    let arg_typs = List.map (apply_subst_typ new_subst) typs in
    let ret_typ = TyVar(gensym_typ "appresult", dummy_span) in
    let app_ty = apply_subst_typ new_subst (TyArrow(arg_typs, ret_typ, dummy_span)) in
    let result_subst = unify sch_inst app_ty span in
    (printf "result subst:\n%s\n" (ExtString.String.join "\n" (List.map (fun (s, typ) -> (sprintf "%s:%s" s (string_of_typ typ))) result_subst)));
    let final_subst = compose_subst new_subst result_subst in
    let ret_typ = apply_subst_typ final_subst ret_typ in
    let all_predicates = apply_subst_predicates final_subst (sch_predicates @ arg_predicates) in
    (final_subst, ret_typ, all_predicates)
  in
  match e with
  | ELiteral(LitBool(_), _) -> ([], t_bool, [])
  | ELiteral (LitInt(n, suffix), loc) ->
      (match suffix with
       | IntSuffix(width) -> ([], TyCon(Int(width), dummy_span), []))
  | EId (x, loc) ->
      let (cs, t) = instantiate (StringMap.find x env) in
      ([], t, cs)
  | EPrim1 (op, e, loc) ->
      let sch = (
        match op with
        | Print | PrintStack ->
          let new_typ = gensym_typ "prim1operand" in
          SForall([new_typ], [], TyArrow([TyVar(new_typ, dummy_span)], TyVar(new_typ, dummy_span), dummy_span), dummy_span)
        | Add1 | Sub1 | Neg -> SForall([], [], TyArrow([t_i32], t_i32, dummy_span), dummy_span)
        | Not -> SForall([], [], TyArrow([t_bool], t_bool, dummy_span), dummy_span)
      ) in
      let (sch_cs, sch_inst) = instantiate sch in
      infer_app_typ [] sch_cs sch_inst [e] env loc
  | EPrim2 (op, l, r, loc) ->
      let sch = (
        match op with
        | Plus ->
          let t = gensym_typ "addoperand" in
          SForall([t], [{pred_class = "Add"; pred_args = [(TyVar(t, dummy_span))]}],
                  TyArrow([TyVar(t, dummy_span); TyVar(t, dummy_span)], TyVar(t, dummy_span), dummy_span),
                  dummy_span)
        | Minus | Times | Divide -> SForall([], [], TyArrow([t_i32; t_i32], t_i32, dummy_span), dummy_span)
        | Greater | GreaterEq | Less | LessEq -> SForall([], [], TyArrow([t_i32; t_i32], t_bool, dummy_span), dummy_span)
        | Eq ->
          let new_ty = gensym_typ "eqoperand" in
          SForall([new_ty], [], TyArrow([TyVar(new_ty, dummy_span); TyVar(new_ty, dummy_span)], t_bool, dummy_span), dummy_span)
        | And | Or -> SForall([], [], TyArrow([t_bool; t_bool], t_bool, dummy_span), dummy_span)
        | _ -> failwith "unsupported"
      ) in
      let (sch_cs, sch_inst) = instantiate sch in
      infer_app_typ [] sch_cs sch_inst [l; r] env loc
  | EIf(c, t, f, span) ->
    let (c_subst, c_typ, c_cs) = infer_exp env c in
    let env = apply_subst_schenv c_subst env in
    let (t_subst, t_typ, t_cs) = infer_exp env t in
    let env = apply_subst_schenv t_subst env in
    let (f_subst, f_typ, f_cs) = infer_exp env f in
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
      let (new_env, new_subst, bind_cs) =
        List.fold_left
          (fun (acc_env, acc_subst, acc_cs) (x, e, _) ->
            let (b_subst, b_typ, b_cs) = infer_exp acc_env e in
            let subst_so_far = compose_subst acc_subst b_subst in
            let new_env = apply_subst_schenv subst_so_far acc_env in
            let b_typ = apply_subst_typ subst_so_far b_typ in
            (printf "b_typ: %s\n" (string_of_typ b_typ));
            (printf "subst so far:\n%s\n" (ExtString.String.join "\n" (List.map (fun (s, typ) -> (sprintf "%s:%s" s (string_of_typ typ))) subst_so_far)));
            (match x with
             | BName(name, _, typ, _) ->
               let unified_subst = unify typ b_typ span in
               let final_subst = compose_subst subst_so_far unified_subst in
               (StringMap.add name (SForall([], [], b_typ, dummy_span)) new_env,
                final_subst, acc_cs @ b_cs)
             | _ -> (new_env, subst_so_far, acc_cs @ b_cs)))
          (env, [], []) binds
      in
      let (body_subst, body_typ, body_cs) = infer_exp new_env body in
      let final_subst = compose_subst new_subst body_subst in
      let final_typ = apply_subst_typ final_subst body_typ in
      let all_constraints = apply_subst_predicates final_subst (bind_cs @ body_cs) in
      (final_subst, final_typ, all_constraints)
  | EApp (closure, args, _, loc) ->
      let (clo_subst, clo_typ, clo_cs) = infer_exp env closure in
      let env = apply_subst_schenv clo_subst env in
      infer_app_typ clo_subst clo_cs clo_typ args env loc
  | _ -> failwith "bad"

and try_solve_pred pred =
  try
    solve_pred_fail pred
  with
    | exn-> ()

and solve_pred_fail pred =
  List.iter 
    (fun cty ->
      match cty with
      | TyVar(vname, _) -> failwith "don't solve yet"
        
      | concrete -> ())
    pred.pred_args;
    check_instance_exists pred

let generalize (env : 'a scheme envt) (predicates : 'a predicate list) (t : 'a typ) : 'a scheme =
  let quantified = StringSet.diff (ftv_typ t) (ftv_env env) in
  let kept, discharge_now =
    List.partition
      (fun pred -> 
        let ftv_pred = (List.fold_left StringSet.union StringSet.empty (List.map ftv_typ pred.pred_args)) in
        (printf "freevars in %s:\n%s\n" (string_of_typ t) (ExtString.String.join "\n" (List.map (sprintf "%s") (StringSet.elements ftv_pred))));
        not (StringSet.is_empty (StringSet.inter ftv_pred quantified)))
      predicates
  in
  List.iter check_instance_exists discharge_now;
  SForall(StringSet.elements quantified, kept, t, dummy_span)

let name_of_bind b =
  match b with
  | BName(x, _, _, _) -> x
  | _ -> failwith "invalid bind form"

let infer_decl env (decl: sourcespan decl)
    : (sourcespan typ subst * sourcespan typ * sourcespan predicate list) =
  match decl with
  | DFun (name, generics, args, body, call_type, typ, tag) ->
    let (sub, _, fun_typ) = instantiate_for_decl (StringMap.find name env) in
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
    (match fun_typ with
     | TyArrow(arg_typs, ret_typ, _) ->
        let body_env =
          List.fold_left2
            (fun acc arg t -> StringMap.add (name_of_bind arg) (SForall([], [], t, dummy_span)) acc)
            env args arg_typs in
        let (body_subst, body_typ, body_cs) = infer_exp body_env body in
        let ret_typ = apply_subst_typ body_subst ret_typ in
        let unified_subst = unify body_typ ret_typ tag in
        let final_subst = compose_subst body_subst unified_subst in
        let final_typ = apply_subst_typ final_subst fun_typ in
        let final_cs = apply_subst_predicates final_subst body_cs in
        List.iter try_solve_pred final_cs;
        (* List.iter check_instance_exists final_cs; *)
        (final_subst, final_typ, final_cs)
     | _ -> failwith "expected arrow type for decl")

let infer_group env (group : sourcespan decl list) : sourcespan scheme envt =
  let guesses =
    List.map
      (fun decl -> match decl with
        | DFun(name, generics, args, body, call_type, typ, tag) ->
          let arg_tvs = List.map (fun arg -> match arg with
            | BName (_, _, typ, _) -> typ
            | _ -> failwith "Unsupported binding type") args in
          (name, TyArrow(arg_tvs, typ, dummy_span), dummy_span,
          List.concat (List.map 
            (fun g ->
              match g with
              | GBName(_, predicates, _) -> predicates) generics)))
      group in
  let mono_env =
    List.fold_left
      (fun acc (name, typ, _, preds) -> StringMap.add name (SForall(StringSet.to_list (ftv_typ typ), preds, typ, dummy_span)) acc)
      env guesses in
  let (group_subst, results) =
    List.fold_left
      (fun (subst_so_far, results_so_far) decl ->
        let (s, t, cs) = infer_decl (apply_subst_schenv subst_so_far mono_env) decl in
        let name = match decl with DFun(name, _, _, _, _, _, _) -> name in
        (compose_subst subst_so_far s, (name, t, cs) :: results_so_far))
      ([], []) group in
  let outer_env = apply_subst_schenv group_subst env in
  List.fold_left
    (fun acc (name, t, cs) ->
      let final_typ = apply_subst_typ group_subst t in
      let final_cs = apply_subst_predicates group_subst cs in
      StringMap.add name (generalize outer_env final_cs final_typ) acc)
    outer_env results

let infer_prog (env : sourcespan scheme envt)
  (p : sourcespan program) : sourcespan program =
  match p with
  | Program(decls, tag) ->
    let _ = infer_group env decls in
    p


let type_synth (p : sourcespan program) : sourcespan program fallible =
  Hashtbl.add classes "Add" { class_name = "Add"; class_params = [GBName("Self", [], dummy_span)]; class_superclasses = []; class_methods = ["add", TyArrow([TyVar("Self",dummy_span); TyVar("Self",dummy_span)], TyVar("Self",dummy_span), dummy_span)] };
  List.iter (fun w -> register_instance "Add" 
  {instance_head = {pred_class = "Add"; pred_args = [(TyCon(Int w, dummy_span))]}; instance_context = []})
    [I8; I16; I32; I64; I128];
  try
    Ok(infer_prog StringMap.empty p)
  with e -> Error([e])
;;

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let compile_prog (prog: sourcespan program) : string =
  sprintf "%s" (string_of_program prog)
;;

let compile_to_string (prog : sourcespan program pipeline) : string pipeline
    =
  prog
  |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase type_names_resolved resolve_prog_typ_paths
  |> add_err_phase type_checked type_synth
  |> add_phase result compile_prog
  (* prog *)
  (* |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase result compile_prog *)
;;
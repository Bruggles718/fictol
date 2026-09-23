open Printf
open Pretty
open Phases
open Exprs
open Errors
open Lexing
open Llvm
open Stdint
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

type 'a name_envt = (string * 'a) list

type 'a tag_envt = (tag * 'a) list

type 'a envt = 'a StringMap.t

type 'a type_envt = 'a typ envt
type 'a scheme_envt = 'a scheme envt

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
  and wf_E_list e_lst env =
    let results = List.map (fun e -> wf_E e env) e_lst in
    List.fold_left List.append [] results
  and wf_E e env =
    match e with
    | ELiteral(LitBool(_), _) -> []
    | ELiteral (LitInt(n), loc) ->
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
    | DFun (_, args, body, ct, typ, _) ->
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
        let err_lst = args_err_lst @ wf_E body env2 in
        err_lst
  and wf_D_list decls env =
    let full_env = get_new_env decls in
    List.concat
      (List.mapi
         (fun i d ->
           match d with
           | DFun (name, _, _, ct, typ, loc) -> (
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
    | DFun (name, _, _, ct, typ, loc) :: rest -> (name, loc) :: get_new_env rest
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
  | TyArrow (args, ret_type) -> TyArrow(List.map (fun arg -> (subst_var_typ (tyvar, to_typ) arg)) args, (subst_var_typ (tyvar, to_typ) ret_type))
  | TyBlank(t) -> TyBlank(t)
  | TyApp (ret_typ, args) -> TyApp((subst_var_typ (tyvar, to_typ) ret_typ), List.map (fun arg -> (subst_var_typ (tyvar, to_typ) arg)) args)

let rec subst_var_scheme ((tyvar : string), (to_typ : 'a typ)) (in_scheme : 'a scheme) : 'a scheme =
  match in_scheme with
  | SForall(args, typ, t) -> 


(* let rec type_check_prog (prog: sourcespan program) : sourcespan program fallible =
  match prog with
  | Program(decls, _) ->
    let env = get_decls_type_env decls in
    let errs = type_check_decl_list env decls in
    match errs with
    | [] -> Ok prog
    | _ -> Error errs

and type_check_decl_list env decls =
  match decls with
  | first :: rest -> (type_check_decl env first) @ (type_check_decl_list env rest)
  | [] -> []

and get_binds_type_env binds =
  let filtered = 
    List.filter 
    (fun b -> 
      match b with
      | BName _ -> true
      | BBlank _ -> false)
    binds
  in
  List.map
  (fun b -> 
    match b with
    | BName(name, _, typ, _) -> (name, typ)
    | BBlank _ -> raise (InternalCompilerError ("Shouldn't be blank")))
  filtered
and type_check_decl env decl = 
  match decl with
  | DFun(name, binds, body, _, typ, _) -> 
    let (errs, result_typ) = type_check_exp ((get_binds_type_env binds ) @ env) body typ in
    errs
and type_check_exp env exp typ = 
  match exp, typ with
  | _, TyBlank loc -> ([CannotInferType("cannot infer type!")], (TyBlank(loc)))
  | ELiteral(LitInt(n), _), TyCon("i32", _) -> ([], typ)
  | ELiteral(LitBool(b), _), TyCon("bool", _) -> ([], typ)
  | EId(name, loc), expected_typ -> 
    let id_typ = untagTyp (find env name) in
    let expected_typ_untagged = untagTyp expected_typ in
    if id_typ = expected_typ_untagged then
      ([], typ)
    else
      ([InconsistentType(sprintf "inconsistent type at %s" (string_of_sourcespan loc))], typ)
  | EPrim2(Plus, lhs, rhs, loc), TyCon("i32", _)
  | EPrim2(Minus, lhs, rhs, loc), TyCon("i32", _)
  | EPrim2(Times, lhs, rhs, loc), TyCon("i32", _)
  | EPrim2(Divide, lhs, rhs, loc), TyCon("i32", _)
  | EPrim2(And, lhs, rhs, loc), TyCon("bool", _)
  | EPrim2(Or, lhs, rhs, loc), TyCon("bool", _) ->
    let (errs_lhs, typ_lhs) = (type_check_exp env lhs typ) in
    let (errs_rhs, typ_rhs) = (type_check_exp env rhs typ) in
    (errs_lhs @ errs_rhs, typ)
  | EPrim2(Greater, lhs, rhs, loc), TyCon("bool", ty_loc)
  | EPrim2(GreaterEq, lhs, rhs, loc), TyCon("bool", ty_loc)
  | EPrim2(Less, lhs, rhs, loc), TyCon("bool", ty_loc)
  | EPrim2(LessEq, lhs, rhs, loc), TyCon("bool", ty_loc) ->
    let (errs_lhs, typ_lhs) = (type_check_exp env lhs (TyCon("i32", loc))) in
    let (errs_rhs, typ_rhs) = (type_check_exp env rhs (TyCon("i32", loc))) in
    (errs_lhs @ errs_rhs, typ)
  | ELet(bindings, body, loc), expected_typ ->
      let bindings_errs = type_check_bindings env bindings in
      let binds = List.map (fun (bind, _, _) -> bind) bindings in
      let binds_type_env = get_binds_type_env binds in
      let (errs_body, typ_body) = type_check_exp (binds_type_env @ env) body expected_typ in
      (bindings_errs @ errs_body, typ_body)
  | EApp(EId(name, id_loc), args, ct, loc), expected_typ ->
    let func_typ = (find env name) in
    let (errs_args, _) = (
      match func_typ with
      | TyArrow(arg_typs, ret_typ) -> 
        (List.combine args arg_typs)
        |> List.map (fun (arg, typ) ->
          type_check_exp env arg typ)
        |> List.split
      | _ -> ([[InconsistentType(sprintf "cannot call non-arrow type at %s" (string_of_sourcespan id_loc))]], [])
      ) in
    (List.concat errs_args, expected_typ)
  | EIf(cond, thn, els, loc), expected_typ ->
    let (errs_cond, typ_cond) = (type_check_exp env cond typ) in
    let (errs_thn, typ_thn) = (type_check_exp env thn typ) in
    let (errs_els, typ_els) = (type_check_exp env els typ) in
    (errs_cond @ errs_thn @ errs_els, typ)
  | _, TyCon(_, loc) -> ([CannotInferType(sprintf "cannot infer type at %s" (string_of_sourcespan loc))], typ)
  | _, _ -> ([CannotInferType("cannot infer type!")], typ)

and type_check_bindings env bindings =
  match bindings with
  | (BName(name, _, typ, _), body, _) :: rest -> (fst (type_check_exp env body typ)) @ (type_check_bindings ((name, typ) :: env) rest)
  | _ -> [] 
and get_decls_type_env decls =
  match decls with
  | DFun (name, binds, _, _, typ, _) :: rest -> 
      let bind_types = List.map get_bind_type binds in
      [(name, TyArrow(bind_types, typ))] @ (get_decls_type_env rest)
  | [] -> []

and get_bind_type b =
  match b with
  | BBlank loc -> TyCon("Any", loc)
  | BName (name, _, typ, _) -> typ *)



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
  (* |> add_err_phase type_checked type_check_prog *)
  |> add_phase result compile_prog
  (* prog *)
  (* |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase result compile_prog *)
;;
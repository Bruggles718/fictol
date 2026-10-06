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
open Compiler_common

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
        if n > Uint64.max_int then
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
    | DFun (fun_name, generics, args, body, ct, typ, fun_loc) ->
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
        let ret_typ_err =
          match typ with
          | TyBlank _ -> [NoTypeAnnotation (fun_name ^ " return type", fun_loc)]
          | _ -> []
        in
        let err_lst = args_err_lst @ typ_err_lst @ ret_typ_err @ wf_E body env2 in
        err_lst
    | DClass _ | DInstance _ -> []
  (* wf for DInstance: the class exists with the right arity, the methods are
   well-formed DFuns (reuse wf_D), and the instance generics are distinct. *)
  and wf_instance_decl (d : sourcespan decl) env : exn list =
    match d with
    | DInstance (generic_binds, head, method_impls, loc) ->
      let existing_method_names = Hashtbl.create 8 in
      let method_impl_errs = List.concat (
        List.map
        (fun mi ->
          match mi with
          | ImplDecl(DFun(name, generics, args, body, call_type, ret_typ, dloc)) ->
            let dup_err = (if Hashtbl.mem existing_method_names name then
              [DuplicateFun(name, dloc, Hashtbl.find existing_method_names name)]
            else
              []) in
            let decl_errs = wf_D (DFun(name, generics, args, body, call_type, ret_typ, dloc)) env in
            dup_err @ decl_errs
          | ImplDecl(_) -> [Unsupported ("Non-function method def found", loc)]
          | _ -> [])
        method_impls
      ) in
      method_impl_errs
    | _ -> failwith "well-formed instance decl failure: given non instance"
  (* wf for DClass: duplicate method names within the class, duplicate params,
   superclass / bound classes exist (UnknownClass), default bodies are
   well-formed expressions in a scope containing the method args. *)
  and wf_class_decl (d : sourcespan decl) env superclass_env : exn list =
    match d with
    | DClass (name, params, superclasses, method_sigs, loc) ->
        let _, dup_params_errs =
          List.fold_left
            (fun (scope_env, args_err_lst) x ->
              try
                let existing = List.assoc x scope_env in
                let err = DuplicateId (x, loc, existing) in
                ((x, loc) :: scope_env, args_err_lst @ [err])
              with Not_found -> ((x, loc) :: scope_env, args_err_lst) )
            (env, []) params
        in
        let dup_method_errs =
          List.concat
            (List.map
               (fun method_sig ->
                 try
                   let span = List.assoc method_sig.ms_name env in
                   [DuplicateFun (method_sig.ms_name, method_sig.ms_span, span)]
                 with Not_found -> [] )
               method_sigs )
        in
        let method_body_errs =
          List.concat
            (List.map
               (fun ms ->
                 match ms.ms_default with
                 | Some body ->
                     wf_D
                       (DFun
                          ( ms.ms_name,
                            ms.ms_generics,
                            ms.ms_args,
                            body,
                            FictolFunc,
                            ms.ms_ret,
                            ms.ms_span ) )
                       env
                 | None -> [] )
               method_sigs )
        in
        let superclass_errs =
          List.map
            (fun pred ->
              try
                let params_len, sup_loc = List.assoc pred.pred_class superclass_env in
                if params_len = List.length params then
                  []
                else
                  [Arity (params_len, List.length params, loc)]
              with Not_found -> [UnboundId (pred.pred_class, loc)] )
            superclasses
          |> List.concat
        in
        dup_params_errs @ superclass_errs @ dup_method_errs @ method_body_errs
    | _ -> failwith "well-formed class decl failure: given non class"
  and wf_D_list decls env =
    let full_env = get_new_env decls in
    let dup_method_errs, method_scope = get_method_names decls in
    let dup_class_errs = get_dup_class_errs decls in
    let class_env = get_class_env decls in
    dup_class_errs
    @ dup_method_errs
    @ List.concat
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
             | DClass _ -> wf_class_decl d env class_env
             | DInstance _ -> wf_instance_decl d env )
           decls )
  and get_new_env decls =
    match decls with
    | DFun (name, generics, _, _, ct, typ, loc) :: rest -> (name, loc) :: get_new_env rest
    | _ :: rest -> get_new_env rest
    | [] -> []
  and get_dup_class_errs decls =
    let existing_class_names = Hashtbl.create 8 in
    List.concat
      (List.map
         (fun d ->
           match d with
           | DClass (name, _, _, _, loc) ->
               if Hashtbl.mem existing_class_names name then
                 let other_loc = Hashtbl.find existing_class_names name in
                 [DuplicateFun (name, loc, other_loc)]
               else (
                 Hashtbl.replace existing_class_names name loc;
                 []
               )
           | _ -> [] )
         decls )
  and get_class_env decls =
    List.map
      (fun d ->
        match d with
        | DClass (name, params, _, _, loc) -> [(name, (List.length params, loc))]
        | _ -> [] )
      decls
    |> List.concat
  and get_method_names decls =
    (* class methods are global functions, so they are in scope everywhere *)
    let existing_method_names = Hashtbl.create 8 in
    let errs_names =
      List.concat_map
        (fun d ->
          match d with
          | DClass (_, _, _, sigs, _) ->
              List.map
                (fun s ->
                  let errs =
                    if Hashtbl.mem existing_method_names s.ms_name then
                      let other_loc = Hashtbl.find existing_method_names s.ms_name in
                      [DuplicateFun (s.ms_name, s.ms_span, other_loc)]
                    else (
                      Hashtbl.replace existing_method_names s.ms_name s.ms_span;
                      []
                    )
                  in
                  (errs, (s.ms_name, s.ms_span)) )
                sigs
          | _ -> [] )
        decls
    in
    let errs, env = List.split errs_names in
    (List.concat errs, env)
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

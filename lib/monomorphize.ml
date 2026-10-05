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
open Typecheck

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


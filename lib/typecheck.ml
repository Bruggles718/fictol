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

let rec resolve_typ_path env (typ : typ) =
  match typ with
  | TyPath (path, t) -> (
    match path with
    (* change to solve path eventually *)
    | [name] ->
        let found_opt = List.assoc_opt name env in
        if Option.is_some found_opt then
          (Option.get found_opt, [])
        else
          (typ, [UnknownType typ])
    | _ -> (typ, [UnknownType typ]) )
  | TyVar name -> (TyVar name, [])
  | TyCon name -> (TyCon name, [])
  | TyArrow (args, ret_typ, call_type) ->
      let args_typs_errs = List.map (fun arg -> resolve_typ_path env arg) args in
      let arg_typs, arg_errs = List.split args_typs_errs in
      let ret_typ, ret_errs = resolve_typ_path env ret_typ in
      let errs = List.concat arg_errs @ ret_errs in
      (TyArrow (arg_typs, ret_typ, call_type), errs)
  | TyBlank t -> (TyBlank t, [])
  | TyApp (ret_typ, args) ->
      let args_typs_errs = List.map (fun arg -> resolve_typ_path env arg) args in
      let arg_typs, arg_errs = List.split args_typs_errs in
      let ret_typ, ret_errs = resolve_typ_path env ret_typ in
      let errs = List.concat arg_errs @ ret_errs in
      (TyApp (ret_typ, arg_typs), errs)
;;

(* REAL. Use this (not resolve_typ_path) on a bound. Checking that the class
   exists belongs in is_well_formed, not here. *)
let resolve_predicate (generic_env : (string * typ) list) (p : 'a predicate) =
  let args_typs_errs = List.map (fun arg -> resolve_typ_path generic_env arg) p.pred_args in
  let arg_typs, arg_errs = List.split args_typs_errs in
  ({p with pred_args= arg_typs}, List.concat arg_errs)
;;

let resolve_prog_typ_paths (p : sourcespan program) : sourcespan program fallible =
  let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s_%d" name !next
  in
  let builtin_types =
  [
    ("i8",   TyCon (Int I8));
    ("i16",  TyCon (Int I16));
    ("i32",  TyCon (Int I32));
    ("i64",  TyCon (Int I64));
    ("u8",   TyCon (UInt U8));
    ("u16",  TyCon (UInt U16));
    ("u32",  TyCon (UInt U32));
    ("u64",  TyCon (UInt U64));
    ("bool", TyCon Bool);
    ("ref",  TyCon Reference);
    ("region", TyCon Region);
    ("Static", TyApp (TyCon Region, [TyCon (RegionName "Static")]))
  ] in
  let rec helpP p =
    match p with
    | Program (decls, span) ->
        let new_decls, errs = List.split (List.map (helpD_in builtin_types) decls) in
        (Program (new_decls, span), List.concat errs)
  (* and string_list_of_generics gs =
    List.map
      (fun g ->
        match g with
        | GBName (name, _, tag) -> name )
      gs *)
  and env_of_generics gs =
    List.map
      (fun g ->
        match g with
        | GBName (name, _, tag) -> (name, TyVar name) )
      gs
  and helpGeneric env g =
    match g with
    | GBName (name, predicates, tag) ->
        let preds, errs = List.split (List.map (resolve_predicate env) predicates) in
        (GBName (name, preds, tag), List.concat errs)
  (* and helpD decl = helpD_in [] decl *)
  and helpImplD_in outer impl_d =
    match impl_d with
    | ImplDecl decl ->
        let new_decl, errs = helpD_in outer decl in
        (ImplDecl new_decl, errs)
    | ImplPrim1 _ | ImplPrim2 _ -> (impl_d, [])
  and helpD_in outer decl =
    (* `outer` = type variables already in scope (instance generics for methods) *)
    match decl with
    | DFun (name, generics, args, body, call_type, typ, span) ->
        let generic_env = outer @ env_of_generics generics in
        let new_args, args_errs =
          List.split (List.map (fun arg -> helpBind generic_env arg) args)
        in
        let gens, gen_errs = List.split (List.map (helpGeneric generic_env) generics) in
        let ret_typ, ret_errs = resolve_typ_path generic_env typ in
        let new_body, body_errs = helpE generic_env body in
        ( DFun (name, gens, new_args, new_body, call_type, ret_typ, span),
          List.concat gen_errs @ List.concat args_errs @ ret_errs @ body_errs )
    | DClass (name, params, supers, sigs, span) ->
        let params_env = outer @ List.map (fun param -> (param, TyVar param)) params in
        let new_supers, super_errs = List.split (List.map (resolve_predicate params_env) supers) in
        let new_sigs, sig_errs = List.split (List.map (helpSig params_env) sigs) in
        ( DClass (name, params, new_supers, new_sigs, span),
          List.concat super_errs @ List.concat sig_errs )
    | DInstance (generics, head, methods, span) ->
        let inst_env = outer @ env_of_generics generics in
        let new_gens, gen_errs = List.split (List.map (helpGeneric inst_env) generics) in
        let new_head, head_errs = resolve_predicate inst_env head in
        let new_impls, impl_errs = List.split (List.map (helpImplD_in inst_env) methods) in
        ( DInstance (new_gens, new_head, new_impls, span),
          List.concat gen_errs @ head_errs @ List.concat impl_errs )
  and helpSig class_env s =
    let env = class_env @ env_of_generics s.ms_generics in
    let new_gens, gen_errs = List.split (List.map (helpGeneric env) s.ms_generics) in
    let new_args, arg_errs = List.split (List.map (helpBind env) s.ms_args) in
    let new_ret, ret_errs = resolve_typ_path env s.ms_ret in
    let new_default, default_errs =
      match s.ms_default with
      | Some default ->
          let new_default, default_errs = helpE env default in
          (Some new_default, default_errs)
      | None -> (None, [])
    in
    ( {s with ms_generics= new_gens; ms_args= new_args; ms_ret= new_ret; ms_default= new_default},
      List.concat gen_errs @ List.concat arg_errs @ ret_errs @ default_errs )
  and helpBind env bind =
    match bind with
    | BName (name, shadow, typ, span) ->
        let new_typ, typ_errs = resolve_typ_path env typ in
        (BName (name, shadow, new_typ, span), typ_errs)
    | BBlank _ -> (bind, [])
  (* | _ -> failwith "should've been desugared" *)
  and helpE env expr =
    match expr with
    | ELet (bindings, body, span) ->
        let new_bindings, binding_errs =
          List.split
            (List.map
               (fun (bind, bind_body, span) ->
                 let new_bind, bind_errs = helpBind env bind in
                 let new_body, body_errs = helpE env bind_body in
                 ((new_bind, new_body, span), bind_errs @ body_errs) )
               bindings )
        in
        let new_body, body_errs = helpE env body in
        (ELet (new_bindings, new_body, span), List.concat binding_errs @ body_errs)
    | EIf (cond, thn, els, span) ->
        let new_cond, cond_errs = helpE env cond in
        let new_thn, thn_errs = helpE env thn in
        let new_els, els_errs = helpE env els in
        (EIf (new_cond, new_thn, new_els, span), cond_errs @ thn_errs @ els_errs)
    | EApp (closure, args, span) ->
        let new_closure, closure_errs = helpE env closure in
        let new_args, arg_err_lists = List.split (List.map (helpE env) args) in
        (EApp (new_closure, new_args, span), closure_errs @ List.concat arg_err_lists)
    | ESeq (e1, e2, span) ->
        let new_e1, errs1 = helpE env e1 in
        let new_e2, errs2 = helpE env e2 in
        (ESeq (new_e1, new_e2, span), errs1 @ errs2)
    | EPrim1 (op, body, span) ->
        let new_body, errs = helpE env body in
        (EPrim1 (op, new_body, span), errs)
    | EPrim2 (op, l, r, span) ->
        let new_l, l_errs = helpE env l in
        let new_r, r_errs = helpE env r in
        (EPrim2 (op, new_l, new_r, span), l_errs @ r_errs)
    | EBorrow (borrowed_expr, ref_name, region, body, span) ->
        let new_borrowed_expr, be_errs = helpE env borrowed_expr in
        let new_reg_name = (gensym region) in
        let new_env = (region, TyApp (TyCon Region, [TyCon (RegionName new_reg_name)])) :: env in
        let new_body, body_errs = helpE new_env body in
        (EBorrow (new_borrowed_expr, ref_name, new_reg_name, new_body, span), be_errs @ body_errs)
    | EReference (body, span) ->
        let new_body, body_errs = helpE env body in
        (EReference (new_body, span), body_errs)
    | _ -> (expr, [])
  in
  let prog, errs = helpP p in
  match errs with
  | [] -> Ok prog
  | _ -> Error errs
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
          (sprintf "Unification failure: inconsistent type constants %s and %s at <%s>"
             (string_of_typ t1) (string_of_typ t2) (string_of_sourcespan span) )
  | TyArrow (t1_args, t1_ret_ty, t1_call_type), TyArrow (t2_args, t2_ret_ty, t2_call_type)
    when t1_call_type = t2_call_type -> unify_arrows t1_args t1_ret_ty t2_args t2_ret_ty
  | TyApp (t1_ret_ty, t1_args), TyApp (t2_ret_ty, t2_args) ->
      unify_arrows t1_args t1_ret_ty t2_args t2_ret_ty
  | _ ->
      failwith
        (sprintf "Unification failure: cannot unify %s and %s at <%s>" (string_of_typ t1)
           (string_of_typ t2) (string_of_sourcespan span) )

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

let get_return_typ (typ : typ) =
  match typ with
  | TyArrow (_, ret_typ, call_type) -> ret_typ
  | _ -> failwith (sprintf "Expected arrow type, got %s" (string_of_typ typ))
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
        failwith
          (sprintf "Check superclass obligations failure: no instance of %s"
             (string_of_pred superclass) ) )
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
  | EBorrow (_, _, _, _, t) -> t
  | EReference (_, t) -> t
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
  | EBorrow (borrowed_expr, ref_name, region, body, tag) ->
      EBorrow (go borrowed_expr, ref_name, region, go body, f tag)
  | EReference (body, tag) -> EReference (go body, f tag)
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

let find_method_info cls d =
  let name = name_of_impldecl_dfun d in
  let result = List.filter (fun method_info -> method_info.m_name = name) cls.class_methods in
  match result with
  | [found_info] -> found_info
  | _ -> failwith "Find method info failure: no method found"
;;

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

let name_of_dfun d =
  match d with
  | DFun (name, _, _, _, _, _, _) -> name
  | _ -> failwith "Name of DFun failure: given non DFun"
;;

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

let type_synth_tc (p : sourcespan program) : typed_tag program fallible =
  let gensym_typ =
    let count = ref 0 in
    let next () =
      count := !count + 1;
      !count
    in
    fun str -> sprintf "%s_%d" str (next ())
  in
  let instantiate (s : 'a scheme) : 'a predicate list * typ =
    match s with
    | SForall (args, predicates, typ) ->
        let sub = List.map (fun s -> (s, TyVar (gensym_typ "T"))) args in
        let res_typ = apply_subst_typ sub typ in
        let res_constraints = apply_subst_predicates sub predicates in
        (res_constraints, res_typ)
  in
  let instantiate_for_decl (s : 'a scheme) : (string * typ) list * 'a predicate list * typ =
    match s with
    | SForall (args, predicates, typ) ->
        let sub = List.map (fun v -> (v, TyVar (gensym_typ "T"))) args in
        (sub, apply_subst_predicates sub predicates, apply_subst_typ sub typ)
  in
  (* =====================================================================
   TYPE CLASSES, SECTION B: predicate utilities, classes, instances,
   solving. Placed after instantiate_for_decl so gensym_typ is available.
   ===================================================================== *)
  (* let string_of_pred (p : 'a predicate) : string =
  String.concat " " (p.pred_class :: List.map show_typ p.pred_args)
;; *)
  let fresh_subst (vars : string list) : typ subst =
    (* Map each v to TyVar (gensym_typ v). Used to rename instance variables apart
   before an overlap check, and to instantiate schemes. *)
    List.map (fun s -> (s, TyVar (gensym_typ s))) vars
  in
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
  in
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
  in
  (* =====================================================================
   TYPE CLASSES, SECTION C: elaborating type checker, built-ins,
   monomorphisation, new driver. When ready, replace infer_exp, infer_decl,
   infer_group, infer_prog and type_synth with the versions below
   (infer_exp_elab, check_decl, infer_prog_elab, type_synth_tc), delete the old
   ones, and rename.
   ===================================================================== *)
  let rec gen_blanks_in_typ typ =
    match typ with
    | TyApp (ret_typ, args) -> TyApp (gen_blanks_in_typ ret_typ, List.map gen_blanks_in_typ args)
    | TyArrow (args, ret_typ, call_type) ->
        TyArrow (List.map gen_blanks_in_typ args, gen_blanks_in_typ ret_typ, call_type)
    | TyBlank _ -> TyVar (gensym_typ "T")
    | _ -> typ
  in
  let rec infer_exp_elab (env : sourcespan scheme envt) (e : sourcespan expr) :
      typ subst * typ * sourcespan wanted list * typed_tag expr =
    match e with
    | ELiteral (LitBool b, loc) -> ([], t_bool, [], ELiteral (LitBool b, (loc, t_bool)))
    | ELiteral (LitInt (n, suffix), loc) -> (
      match suffix with
      | IntSuffix width ->
          let t = TyCon (Int width) in
          ([], t, [], ELiteral (LitInt (n, suffix), (loc, t)))
      | UIntSuffix width ->
          let t = TyCon (UInt width) in
          ([], t, [], ELiteral (LitInt (n, suffix), (loc, t))) )
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
        infer_app_typ make_expr_args []
          (List.map (wanted_from_pred loc) sch_cs)
          sch_inst [e] env loc
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
                  let new_typ =
                    match b_typ with
                    | TyApp (TyCon Reference, _) -> typ
                    | _ -> gen_blanks_in_typ typ
                  in
                  (* let new_typ = gen_blanks_in_typ typ in *)
                  let unified_subst = unify new_typ b_typ loc in
                  let final_subst = compose_subst subst_so_far unified_subst in
                  ( StringMap.add name (SForall ([], [], b_typ)) new_env,
                    final_subst,
                    acc_cs @ b_cs,
                    acc_bindings
                    @ [(BName (name, shadow, b_typ, (loc, b_typ)), new_e, (bloc, b_typ))] )
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
        ( final_subst,
          final_typ,
          all_constraints,
          ELet (new_bindings, new_body, (let_loc, final_typ)) )
    | EApp (closure, args, loc) ->
        let clo_subst, clo_typ, clo_wanted, new_clo_expr = infer_exp_elab env closure in
        let env = apply_subst_schenv clo_subst env in
        let make_expr new_args ret_typ = EApp (new_clo_expr, new_args, (loc, ret_typ)) in
        infer_app_typ make_expr clo_subst clo_wanted clo_typ args env loc
    | EReference (body, loc) ->
        let body_subst, body_typ, body_wanteds, new_body_expr = infer_exp_elab env body in
        let ref_typ =
          TyApp (TyCon Reference, [body_typ; TyApp (TyCon Region, [TyVar (gensym_typ "RN")])])
        in
        let final_typ = apply_subst_typ body_subst ref_typ in
        let final_constraints = apply_subst_wanteds body_subst body_wanteds in
        (* EReference(new_body_expr, (loc, )) in *)
        (body_subst, final_typ, final_constraints, EReference (new_body_expr, (loc, final_typ)))
    | _ -> failwith (sprintf "cannot type check %s" (string_of_expr e))
  and infer_app_typ
      (make_expr : typed_tag expr list -> typ -> typed_tag expr)
      (sch_subst : typ subst)
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
  in
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
  let check_impl_decl env scheme impl_d : typed_tag method_impl =
    match impl_d with
    | ImplDecl decl -> ImplDecl (check_decl env scheme decl)
    | ImplPrim1 op -> ImplPrim1 op
    | ImplPrim2 op -> ImplPrim2 op
  in
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
                    check_impl_decl env (instance_method_scheme instance_info cls method_info) impl
                  ) )
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
  in
  (* d is a DInstance. Run after ALL classes and instances are registered.
   1. Look up the instance_info and the class.
   2. check_superclass_obligations.
   3. For each method DFun in the instance: find the matching method_info
      (else ExtraMethod); check_decl env (instance_method_scheme inst cls m) it;
      store the ELABORATED DFun in method_impl_table as
      ((instance_id, name), ImplDecl d').
   4. Return the DInstance rebuilt with the elaborated methods. *)
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
  in
  (* d is a DClass. For each method with a default body, check_decl env
   (scheme_of_method cls m) default_fun, replace the entry in
   default_method_table with the elaborated DFun, and return the DClass with
   the elaborated defaults. The only given is `C Self` (plus superclasses), so
   a default may call other methods of the same class but nothing else. *)
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
  in
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

open Printf
open Errors
open Types
open Terms
open Exprs
open Typecheck
open Compiler_common
open Pretty

let rec tm_free_vars tm =
  match tm with
  | TmVar (x, tag) -> [ x ]
  | TmApp (m, n, tag) -> tm_free_vars m @ tm_free_vars n
  | TmLambda (x, a, m, _, tag) -> tm_free_vars a @ List.filter (( <> ) x) (tm_free_vars m)
  | TmThunk (m, _, tag) -> 
    (tm_free_vars m)
  | TmPi (x, a, preds, m, _, tag) -> 
    let ftv_predicates =
        List.concat (List.map ftv_tmpred preds)
      in
    ftv_predicates @ tm_free_vars a @ List.filter (( <> ) x) (tm_free_vars m)
  | TmIf (cond, thn, els, tag) -> tm_free_vars cond @ tm_free_vars thn @ tm_free_vars els
  | TmUniverse _ | TmLiteral _ -> []

and ftv_tmpred (p : 'a tmpredicate) : (string list) =
  List.fold_left (fun acc t -> (tm_free_vars t) @ acc) [] p.pred_args
;;

let rec binders tm =
  match tm with
  | TmApp (m, n, tag) -> binders m @ binders n
  | TmLambda (x, a, m, _, tag) -> [x] @ binders a @ (binders m)
  | TmThunk (m, _, tag) -> (binders m)
  | TmPi (x, a, preds, m,_, tag) -> [x] @ binders a @ (List.concat (List.map binders_tmpred preds)) @ (binders m)
  | TmIf (cond, thn, els, tag) -> binders cond @ binders thn @ binders els
  | TmUniverse _ | TmLiteral _ | TmVar _ -> []

and binders_tmpred p =
  List.fold_left (fun acc t -> (binders t) @ acc) [] p.pred_args

let all_vars tm = tm_free_vars tm @ binders tm

let rec freshen (banlist : string list) (base : string) =
  if List.mem base banlist then freshen banlist (base ^ "'") else base



let rec subst x m tm =
  match tm with
  | TmVar (y, tag) when x = y -> m
  | TmApp (m', n, tag) -> TmApp(subst x m m', subst x m n, tag)
  | TmLambda (y, a, n, call_type, tag) when x = y -> TmLambda (y, subst x m a, n, call_type, tag)
  | TmLambda (y, a, n, call_type, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst x m (rename (freshen banlist y) tm)
  | TmLambda (y, a, n, call_type, tag) -> TmLambda (y, subst x m a, subst x m n, call_type, tag)
  | TmPi (y, a, preds, n, call_type, tag) when x = y -> TmPi (y, subst x m a, List.map (subst_tmpred x m) preds, n, call_type, tag)
  | TmPi (y, a, preds, n, call_type, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst x m (rename (freshen banlist y) tm)
  | TmPi (y, a, preds, n, call_type, tag) -> TmPi (y, subst x m a, List.map (subst_tmpred x m) preds, subst x m n, call_type, tag)
  | TmThunk (n, call_type, tag) -> TmThunk (subst x m n, call_type, tag)
  | TmIf (cond, thn, els, tag) -> TmIf(subst x m cond, subst x m thn, subst x m els, tag)
  | TmLiteral _ | TmVar _ | TmUniverse _ -> tm

and subst_tmpred x m pred =
  { pred_class=pred.pred_class; pred_args=(List.map (subst x m) pred.pred_args) }

and rename x' binder =
  match binder with
  | TmLambda (x, a, m, call_type, tag) -> TmLambda (x', a, (subst x (TmVar (x',tag)) m), call_type, tag)
  | TmPi (x, a, preds, m, call_type, tag) -> TmPi (x', a, List.map (subst_tmpred x (TmVar(x', tag))) preds, (subst x (TmVar (x',tag)) m), call_type, tag)
  | _ -> raise (InternalCompilerError("rename term failure: Given non binder"))
  
let rec alpha_eq tm1 tm2 =
  match tm1, tm2 with
  | TmVar(x, _), TmVar(y, _) -> x = y
  | TmApp(a1, b1, _), TmApp(a2, b2, _) -> alpha_eq a1 a2 && alpha_eq b1 b2
  | TmLambda(x1, a1, m1, call_type1, _), TmLambda(x2, a2, m2, call_type2, _) when x1 = x2 ->
    call_type1 = call_type2 && alpha_eq a1 a2 && alpha_eq m1 m2
  | TmPi(x1, a1, preds1, m1, call_type1, _), TmPi(x2, a2, preds2, m2, call_type2, _) when x1 = x2 ->
    let eq_preds = (List.map (fun (p1, p2) -> alpha_eq_preds p1 p2) (List.combine preds1 preds2)) in
    let eq_preds_folded = List.fold_left (fun acc result -> result && acc) true eq_preds in
    call_type1 = call_type2 && alpha_eq a1 a2 && eq_preds_folded && alpha_eq m1 m2
  | TmLambda(x1, a1, m1, _, _), TmLambda(x2, a2, m2, _, _) ->
    let banlist = all_vars m1 @ all_vars m2 in
    let fresh_x = freshen banlist x1 in
    alpha_eq (rename fresh_x tm1) (rename fresh_x tm2)
  | TmThunk (m1, _, _), TmThunk (m2, _, _) ->
    alpha_eq m1 m2
  | TmPi(x1, a1, preds1, m1, _, _), TmPi(x2, a2, preds2, m2, _, _) ->
    let banlist = all_vars m1 @ all_vars m2 in
    let fresh_x = freshen banlist x1 in
    alpha_eq (rename fresh_x tm1) (rename fresh_x tm2)
  | TmIf(cond1, thn1, els1, _), TmIf(cond2, thn2, els2, _) ->
    alpha_eq cond1 cond2 && alpha_eq thn1 thn2 && alpha_eq els1 els2
  | TmLiteral(l1, _), TmLiteral(l2, _) ->
    l1 = l2
  | TmUniverse(lvl1), TmUniverse(lvl2) -> lvl1 = lvl2
  | _, _ -> false

and alpha_eq_preds pred1 pred2 =
  let terms_eq = List.map (fun (t1, t2) -> alpha_eq t1 t2) (List.combine pred1.pred_args pred2.pred_args) in
  let all_terms_eq = List.fold_left (fun acc result -> result && acc) true terms_eq in
  pred1.pred_class = pred2.pred_class && all_terms_eq

let rec eval tm =
  match tm with
  | TmApp (m, n, tag) -> eval_app (eval m) (eval n) tag
  | TmLambda (x, a, m, call_type, tag) -> TmLambda (x, eval a, eval m, call_type, tag)
  | TmPi (x, a, preds, m, call_type, tag) -> TmPi (x, eval a, List.map eval_pred preds, eval m, call_type, tag)
  | TmThunk (m, call_type, tag) -> TmThunk (eval m, call_type, tag)
  | TmIf (cond, thn, els, tag) -> TmIf(eval cond, eval thn, eval els, tag)
  | TmLiteral _ | TmVar _ | TmUniverse _ -> tm

and eval_pred pred =
  { pred_class = pred.pred_class; pred_args = List.map eval pred.pred_args }

and eval_app m n tag =
  match m with
  | TmLambda(x, a, m, _, tag) -> eval (subst x n m)
  | _ -> TmApp (m, n, tag)


type 'a context = (string * 'a term) list

type span_term_pair = (sourcespan * (sourcespan term))

let rec pi args body ct tag =
  match args with
  | (name, tm, preds) :: rest -> TmPi (name, tm, preds, pi rest body ct tag, ct, tag)
  | [] -> body

let rec lam args body ct tag =
  match args with
  | (name, tm) :: rest -> TmLambda (name, tm, lam rest body ct tag, ct, tag)
  | [] -> body

let type_synth_terms (p: sourcespan program) =

  let rec gensym =
      let next = ref 0 in
      fun name ->
        next := !next + 1;
        sprintf "%s_%d" name !next
  in
  let rec fresh_subst (vars : string list) : typ subst =
    (* Map each v to TyVar (gensym_typ v). Used to rename instance variables apart
   before an overlap check, and to instantiate schemes. *)
    List.map (fun s -> (s, TyVar (gensym s))) vars
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
  let rec infer_type_term (ctx) (tm) : (sourcespan term * sourcespan tmwanted list * span_term_pair term) =
    let ref_typ tm region =
      TmApp(TmApp(TmVar("ref", dummy_span), tm, dummy_span), TmVar(region, dummy_span), dummy_span)
    in
    match tm with
    | TmUniverse lvl -> 
      let typ = TmUniverse (lvl + 1) in
      (typ, [], TmUniverse(lvl))
    | TmLiteral (LitString s, loc) ->
      let typ = ref_typ (TmVar("char", dummy_span)) ("Static") in
      (typ, [], TmLiteral(LitString s, (loc, typ)))
    | TmLiteral (LitChar c, loc) ->
      let typ = TmVar("char", dummy_span) in
      (typ, [], TmLiteral(LitChar c, (loc, typ)))
    | TmLiteral (LitBool b, loc) ->
      let typ = TmVar("bool", dummy_span) in
      (typ, [], TmLiteral(LitBool b, (loc, typ)))
    | TmLiteral (LitInt (n, suffix), loc) ->
      let inttyp = (
        match suffix with
        | IntSuffix width -> Int width
        | UIntSuffix width -> UInt width
      ) in
      let typstr = string_of_tykind inttyp in
      let typ = TmVar(typstr, dummy_span) in
      (typ, [], TmLiteral(LitInt(n, suffix), (loc, typ)))
    | TmVar (x, loc) -> 
      let typ = eval (List.assoc x ctx) in
      let (typ_typ, typ_wanteds, new_typ) = infer_type_term ctx typ in
      (typ, typ_wanteds, (TmVar(x, (loc, typ))))
    | TmLambda (x, a, m, call_type, loc) ->
      let (a_typ, a_wanteds, new_a) = infer_type_term ctx a in
      let (m_typ, m_wanteds, new_m) = infer_type_term ((x, a) :: ctx) m in
      let lam_typ = TmPi(x, a, [], m_typ, call_type, loc) in
      let _ = infer_type_term ctx lam_typ in
      let evaluated_lam_typ = eval lam_typ in
      (evaluated_lam_typ, a_wanteds @ m_wanteds, TmLambda(x, new_a, new_m, call_type, (loc, evaluated_lam_typ)))
    | TmThunk (m, call_type, loc) ->
      let (m_typ, m_wanteds, new_m) = infer_universe ctx m in
      (m_typ, m_wanteds, TmThunk(new_m, call_type, (loc, m_typ)))
    | TmPi (x, a, preds, m, call_type, loc) ->
      let (_, a_wanteds, new_a) = infer_universe ctx a in
      let (pred_wanteds, new_preds) = List.split (List.map (infer_tmpred ctx) preds) in
      let (m_typ, m_wanteds, new_m) = infer_universe ctx m in
      (m_typ, a_wanteds @ List.concat pred_wanteds @ m_wanteds, TmPi(x, new_a, new_preds, new_m, call_type, (loc, m_typ)))
    | TmApp (m, n, loc) ->
      infer_app_term ctx m n
    | TmIf (cond, thn, els, loc) ->
      let (cond_typ, cond_wanteds, new_cond) = infer_type_term ctx cond in
      let (thn_typ, thn_wanteds, new_thn) = infer_type_term ctx thn in
      let (els_typ, els_wanteds, new_els) = infer_type_term ctx els in
      (if alpha_eq cond_typ (TmVar("bool", dummy_span)) then
        ()
      else
        failwith "cond is not bool");
      (if alpha_eq thn_typ els_typ then () else failwith "if branches must have same types");
      (thn_typ, cond_wanteds @ thn_wanteds @ els_wanteds, (TmIf(new_cond, new_thn, new_els, (loc, thn_typ))))


  and infer_app_term (ctx) m n =
    match infer_type_term ctx m with
    | (TmPi (x, a, preds, m, call_type, loc), m_wanteds, new_m) ->
      let (n_typ, n_wanteds, new_n) = infer_type_term ctx n in
      let app_typ = (
        if alpha_eq a n_typ then eval (subst x n m) else failwith "Infer app failure"
      ) in
      (app_typ, m_wanteds @ n_wanteds, TmApp(new_m, new_n, (loc, app_typ)))
    | (TmThunk (m, call_type, loc), m_wanteds, new_m) ->
      (* probably should check that n is nothing or unit or something? or maybe I need a separate term for calling a thunk *)
      let (n_typ, n_wanteds, new_n) = infer_type_term ctx n in
      let app_typ = eval m in
      (app_typ, m_wanteds @ n_wanteds, TmApp(new_m, new_n, (loc, app_typ)))
    | (m_typ, m_wanteds, new_m) ->
      failwith "Infer app failure: cannot apply arguments to non lambda"
      

  and infer_tmpred ctx pred =
    let (arg_typs, wanteds, new_args) = 
      List.fold_right (fun (arg_typ, arg_wanteds, new_arg) (res_types, res_wanteds, res_args)  ->
        (arg_typ :: res_types, arg_wanteds @ res_wanteds, new_arg :: res_args)) (List.map (infer_type_term ctx) pred.pred_args) ([], [], []) in
    (wanteds, {pred_class = pred.pred_class; pred_args = new_args})



  and infer_universe ctx t =
    match infer_type_term ctx t with
    | (TmUniverse(lvl), twanteds, new_t) -> (TmUniverse(lvl), twanteds, new_t)
    | _ -> raise (InternalCompilerError("infer universe failure: inferred non universe"))

  and term_of_typ tag (typ : typ) : 'a term =
    match typ with
    | TyVar (name) -> TmVar (name, tag)
    | TyArrow (args, ret, ct) ->
      let term_args =
        List.map
        (fun arg ->
          ((gensym "Tm"), term_of_typ tag arg, []))
        args in
      let term_ret_typ = term_of_typ tag ret in
      (
        match args with
        | [] -> TmThunk(term_ret_typ, ct, tag)
        | _ -> pi term_args term_ret_typ ct tag
      )
    | TyApp(ret, args) ->
      List.fold_right (fun arg acc ->
        TmApp(term_of_typ tag arg, acc, tag))
      (ret :: args) (TmVar(gensym "UNIT", tag))
    | _ -> ice "cannot convert type to term"


  and tmpred_of_pred tag (pred: 'a predicate) =
    { pred_class=pred.pred_class; pred_args = List.map (term_of_typ tag) pred.pred_args }
  
  and term_of_bind arg = (
          match arg with
          | BName (name, _, typ, loc) -> (name, term_of_typ loc typ, [])
          | BBlank (loc) -> ice "Unsupported binding type in decl")
  and term_of_generic_bind gen =
    match gen with
    | GBName (name, preds, loc) -> (name, TmUniverse 0, List.map (tmpred_of_pred loc) preds)

  and pi_of_decl d =
    match d with
    | DFun(name, generics, args, _, call_type, ret_typ, loc) ->
      let term_args = 
        List.map
        term_of_bind
        args in
      let term_generics =
        List.map
        term_of_generic_bind
        generics in
      let term_ret_typ = term_of_typ loc ret_typ in
      let all_term_args = (term_generics @ term_args) in
      (match all_term_args with
      | [] -> TmThunk(term_ret_typ, call_type, loc)
      | _ -> pi all_term_args term_ret_typ call_type loc)
    | DClass _ | DInstance _ -> ice "cannot get pi of non DFun"
  and pi_of_method (cls : 'a class_info) (m : 'a method_info) : 'a term =
    let m_arrow_typ_term = term_of_typ dummy_span m.m_typ in
    let generic_terms = List.map term_of_generic_bind m.m_generics in
    pi generic_terms m_arrow_typ_term (FictolFunc) dummy_span
  and term_of_expr expr = failwith "TODO"
  and lam_of_decl d =
    match d with
    | DFun(name, generics, args, Some(body), call_type, ret_typ, loc) ->
      let term_args = 
        List.map
        (fun arg ->
          match arg with
          | BName (name, _, typ, loc) -> (name, term_of_typ loc typ)
          | BBlank (loc) -> ice "Unsupported binding type in decl")
        args in
      let term_generics =
        List.map
        (fun gen ->
          match gen with
          | GBName (name, preds, loc) -> (name, TmUniverse 0))
        generics in
      (* let term_ret_typ = term_of_typ ret_typ in *)
      let all_term_args = (term_generics @ term_args) in
      (
        match all_term_args with
        | [] -> TmThunk(term_of_expr body, call_type, loc)
        | first :: rest -> lam (term_generics @ term_args) (term_of_expr body) call_type loc
      )
    | DFun _ -> ice "cannot get lam of non DFun without body"
    | DClass _ | DInstance _ -> ice "cannot get lam of non DFun"
  and check_decl ctx d =
    match d with
    | DFun(name, generics, args, Some(body), call_type, ret_typ, loc) ->
      let decl_term = lam_of_decl d in
      let expected_typ = pi_of_decl d in
      let (inferred_typ, wanteds, inferred_decl_term) = infer_type_term ctx decl_term in
      if alpha_eq inferred_typ expected_typ then
        (* solve_wanteds. if any residual, fail, ambiguous type *)
        inferred_decl_term
      else
        failwith "Check decl failure: stated type and actual type differ"
    | _ -> ice "given non dfun?"
      
  and infer_prog_term (env) (p: sourcespan program) =
    match p with
    | Program (decls, loc) ->
      let classes, instances, funs = partition_decls decls in
      let new_env =
        List.fold_left
            (fun acc_env decl -> ((name_of_dfun decl), (pi_of_decl decl)) :: acc_env)
            env funs
      in
      let new_funs = List.map (check_decl new_env) funs in
      TmProgram new_funs
      
  in
  let method_env () : (string * 'a term) list =
  (* For every class and every method, add m_name |-> scheme_of_method cls m.
   This map is the INITIAL value environment: type_synth passes it to the
   inference code instead of StringMap.empty, so `EId "add"` finds a scheme. *)
    let _, all_classes = List.split (List.of_seq (Hashtbl.to_seq class_table)) in
    List.fold_left
      (fun acc cls ->
        List.fold_left
          (fun acc method_info ->
            (method_info.m_name, (pi_of_method cls method_info)) :: acc )
          acc cls.class_methods )
      [] all_classes
  in
  try
    match p with
    | Program (decls, loc) ->
      reset_class_state ();
      let classes, instances, funs = partition_decls decls in
      List.iter register_class classes;
      validate_classes ();
      List.iter (fun d -> register_instance (instance_info_of_decl d)) instances;
      let env = method_env () in
        let new_p = infer_prog_term env p in
        Ok new_p
  with e -> Error [e]
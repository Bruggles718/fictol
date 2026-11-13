open Printf
open Errors
open Types
open Terms
open Exprs
open Compiler_common
open Pretty
open Stdint

let rec tm_free_vars tm =
  match tm with
  | TmVar (x, tag) -> [x]
  | TmApp (m, n, app_boundary, tag) -> tm_free_vars m @ tm_free_vars n
  | TmLambda (x, a, m, _, tag) | TmPi (x, a, m, _, tag) | TmLet (x, a, m, tag) ->
      tm_free_vars a @ List.filter (( <> ) x) (tm_free_vars m)
  | TmIf (cond, thn, els, tag) -> tm_free_vars cond @ tm_free_vars thn @ tm_free_vars els
  | TmPrim1 (op, body, tag) -> tm_free_vars body
  | TmPrim2 (op, lhs, rhs, tag) -> tm_free_vars lhs @ tm_free_vars rhs
  | TmUniverse _ | TmLiteral _ | TmPrimTy _ | TmMeta _ -> []
;;

let rec tm_meta_vars tm =
  match tm with
  | TmMeta (x, scope, tag) -> [x]
  | TmApp (m, n, app_boundary, tag) -> tm_free_vars m @ tm_free_vars n
  | TmLambda (x, a, m, _, tag) | TmPi (x, a, m, _, tag) | TmLet (x, a, m, tag) ->
      tm_free_vars a @ List.filter (( <> ) x) (tm_free_vars m)
  | TmIf (cond, thn, els, tag) -> tm_free_vars cond @ tm_free_vars thn @ tm_free_vars els
  | TmPrim1 (op, body, tag) -> tm_free_vars body
  | TmPrim2 (op, lhs, rhs, tag) -> tm_free_vars lhs @ tm_free_vars rhs
  | TmUniverse _ | TmLiteral _ | TmPrimTy _ | TmVar _ -> []
;;

let rec binders tm =
  match tm with
  | TmApp (m, n, app_boundary, tag) -> binders m @ binders n
  | TmLambda (x, a, m, _, tag) | TmPi (x, a, m, _, tag) | TmLet (x, a, m, tag) ->
      [x] @ binders a @ binders m
  | TmIf (cond, thn, els, tag) -> binders cond @ binders thn @ binders els
  | TmPrim1 (op, body, tag) -> binders body
  | TmPrim2 (op, lhs, rhs, tag) -> binders lhs @ binders rhs
  | TmUniverse _ | TmLiteral _ | TmVar _ | TmMeta _ | TmPrimTy _ -> []
;;

let all_vars tm = tm_free_vars tm @ binders tm

let rec freshen (banlist : string list) (base : string) =
  if List.mem base banlist then
    freshen banlist (base ^ "'")
  else
    base
;;

let rec subst_vars_in_term x m tm =
  match tm with
  | TmVar (y, tag) when x = y -> tag_term tag m
  | TmApp (m', n, app_boundary, tag) -> TmApp (subst_vars_in_term x m m', subst_vars_in_term x m n, app_boundary, tag)
  | TmLet (y, a, n, tag) when x = y -> TmLet (y, subst_vars_in_term x m a, n, tag)
  | TmLet (y, a, n, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst_vars_in_term x m (rename (freshen banlist y) tm)
  | TmLet (y, a, n, tag) -> TmLet (y, subst_vars_in_term x m a, n, tag)
  | TmLambda (y, a, n, binder_info, tag) when x = y -> TmLambda (y, subst_vars_in_term x m a, n, binder_info, tag)
  | TmLambda (y, a, n, binder_info, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst_vars_in_term x m (rename (freshen banlist y) tm)
  | TmLambda (y, a, n, binder_info, tag) -> TmLambda (y, subst_vars_in_term x m a, subst_vars_in_term x m n, binder_info, tag)
  | TmPi (y, a, n, binder_info, tag) when x = y -> TmPi (y, subst_vars_in_term x m a, n, binder_info, tag)
  | TmPi (y, a, n, binder_info, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst_vars_in_term x m (rename (freshen banlist y) tm)
  | TmPi (y, a, n, binder_info, tag) -> TmPi (y, subst_vars_in_term x m a, subst_vars_in_term x m n, binder_info, tag)
  | TmIf (cond, thn, els, tag) -> TmIf (subst_vars_in_term x m cond, subst_vars_in_term x m thn, subst_vars_in_term x m els, tag)
  | TmPrim1 (op, body, tag) -> TmPrim1 (op, subst_vars_in_term x m body, tag)
  | TmPrim2 (op, lhs, rhs, tag) -> TmPrim2 (op, subst_vars_in_term x m lhs, subst_vars_in_term x m rhs, tag)
  | TmLiteral _ | TmVar _ | TmUniverse _ | TmPrimTy _ | TmMeta _ -> tm

and rename x' binder =
  match binder with
  | TmLambda (x, a, m, binder_info, tag) ->
      TmLambda (x', a, subst_vars_in_term x (TmVar (x', tag)) m, binder_info, tag)
  | TmPi (x, a, m, binder_info, tag) -> TmPi (x', a, subst_vars_in_term x (TmVar (x', tag)) m, binder_info, tag)
  | TmLet (x, a, m, tag) -> TmLet (x', a, subst_vars_in_term x (TmVar (x', tag)) m, tag)
  | _ -> raise (InternalCompilerError "rename term failure: Given non binder")
;;

let rec subst_metas_in_term x (m: unit term) (tm: 'a term) : ('a term) =
  match tm with
  | TmMeta (y, env, tag) when x = y -> tag_term tag m
  | TmApp (m', n, app_boundary, tag) ->
      TmApp (subst_metas_in_term x m m', subst_metas_in_term x m n, app_boundary, tag)
  | TmLet (y, a, n, tag) -> TmLet (y, subst_metas_in_term x m a, n, tag)
  | TmLambda (y, a, n, binder_info, tag) ->
      TmLambda (y, subst_metas_in_term x m a, subst_metas_in_term x m n, binder_info, tag)
  | TmPi (y, a, n, binder_info, tag) ->
      TmPi (y, subst_metas_in_term x m a, subst_metas_in_term x m n, binder_info, tag)
  | TmIf (cond, thn, els, tag) ->
      TmIf
        (subst_metas_in_term x m cond, subst_metas_in_term x m thn, subst_metas_in_term x m els, tag)
  | TmPrim1 (op, body, tag) -> TmPrim1 (op, subst_metas_in_term x m body, tag)
  | TmPrim2 (op, lhs, rhs, tag) ->
      TmPrim2 (op, subst_metas_in_term x m lhs, subst_metas_in_term x m rhs, tag)
  | TmLiteral _ | TmVar _ | TmUniverse _ | TmPrimTy _ | TmMeta _ -> tm
;;

let rec alpha_eq tm1 tm2 =
  match (tm1, tm2) with
  | TmVar (x, _), TmVar (y, _) -> x = y
  | TmApp (a1, b1, app_boundary1, _), TmApp (a2, b2, app_boundary2, _) ->
      app_boundary1 = app_boundary2 && alpha_eq a1 a2 && alpha_eq b1 b2
  | TmLet (x1, a1, m1, _), TmLet (x2, a2, m2, _) when x1 = x2 -> alpha_eq a1 a2 && alpha_eq m1 m2
  | TmLambda (x1, a1, m1, binder_info1, _), TmLambda (x2, a2, m2, binder_info2, _) when x1 = x2 ->
      binder_info1 = binder_info2 && alpha_eq a1 a2 && alpha_eq m1 m2
  | TmPi (x1, a1, m1, binder_info1, _), TmPi (x2, a2, m2, binder_info2, _) when x1 = x2 ->
      binder_info1 = binder_info2 && alpha_eq a1 a2 && alpha_eq m1 m2
  | TmLet (x1, a1, m1, _), TmLet (x2, a2, m2, _) ->
      let banlist = all_vars m1 @ all_vars m2 in
      let fresh_x = freshen banlist x1 in
      alpha_eq (rename fresh_x tm1) (rename fresh_x tm2)
  | TmLambda (x1, a1, m1, _, _), TmLambda (x2, a2, m2, _, _) ->
      let banlist = all_vars m1 @ all_vars m2 in
      let fresh_x = freshen banlist x1 in
      alpha_eq (rename fresh_x tm1) (rename fresh_x tm2)
  | TmPi (x1, a1, m1, _, _), TmPi (x2, a2, m2, _, _) ->
      let banlist = all_vars m1 @ all_vars m2 in
      let fresh_x = freshen banlist x1 in
      alpha_eq (rename fresh_x tm1) (rename fresh_x tm2)
  | TmIf (cond1, thn1, els1, _), TmIf (cond2, thn2, els2, _) ->
      alpha_eq cond1 cond2 && alpha_eq thn1 thn2 && alpha_eq els1 els2
  | TmLiteral (l1, _), TmLiteral (l2, _) -> l1 = l2
  | TmUniverse (lvl1, _), TmUniverse (lvl2, _) -> lvl1 = lvl2
  | TmPrimTy (typ1, _), TmPrimTy (typ2, _) -> typ1 = typ2
  | TmPrim1 (op1, body1, _), TmPrim1 (op2, body2, _) -> op1 = op2 && alpha_eq body1 body2
  | TmPrim2 (op1, lhs1, rhs1, _), TmPrim2 (op2, lhs2, rhs2, _) ->
      op1 = op2 && alpha_eq lhs1 lhs2 && alpha_eq rhs1 rhs2
  | _, _ -> false
;;

type 'a normalize_result = {
  nr_term : 'a term;
  nr_stuck_metas : StringSet.t;
}

let empty_result term = {
  nr_term = term;
  nr_stuck_metas = StringSet.empty;
}

let merge_results term results = {
  nr_term = term;
  nr_stuck_metas =
    List.fold_left
      (fun acc result -> StringSet.union acc result.nr_stuck_metas)
      StringSet.empty
      results;
}

let rec collect_metas tm =
  match tm with
  | TmMeta (id, env, _) -> StringSet.singleton id
  | TmLambda (_, ty, body, _, _)
  | TmPi (_, ty, body, _, _) ->
      StringSet.union (collect_metas ty) (collect_metas body)
  | TmApp (fn, arg, _, _) ->
      StringSet.union (collect_metas fn) (collect_metas arg)
  | TmLet (_, value, body, _) ->
      StringSet.union (collect_metas value) (collect_metas body)
  | TmIf (cond, thn, els, _) ->
      StringSet.union (collect_metas cond)
        (StringSet.union (collect_metas thn) (collect_metas els))
  | TmPrim1 (_, body, _) ->
      collect_metas body
  | TmPrim2 (_, lhs, rhs, _) ->
      StringSet.union (collect_metas lhs) (collect_metas rhs)
  | _ -> StringSet.empty

let prim2_int_op op l r suff =
  let cmp = Uint64.compare l r in
  match op with
  | Plus -> LitInt (Uint64.add l r, suff)
  | Minus -> LitInt (Uint64.sub l r, suff)
  | Times -> LitInt (Uint64.mul l r, suff)
  | Divide ->
      if Uint64.compare r Uint64.zero = 0 then
        ice "Division by zero during constant evaluation"
      else
        LitInt (Uint64.div l r, suff)
  | Greater -> LitBool (cmp > 0)
  | GreaterEq -> LitBool (cmp >= 0)
  | Less -> LitBool (cmp < 0)
  | LessEq -> LitBool (cmp <= 0)
  | _ -> ice (sprintf "Cannot perform op %s on integers" (string_of_op2 op))
;;

let rec whnf tm =
  match tm with
  | TmLet (x, value, body, _) ->
      whnf (subst_vars_in_term x value body)

  | TmApp (fn, arg, app_boundary, tag) ->
      let fn_result = whnf fn in
      let fn' = fn_result.nr_term in
      begin match fn' with
      | TmLambda (x, _, body, _, _) ->
          let result = whnf (subst_vars_in_term x arg body) in
          {
            result with
            nr_stuck_metas =
              StringSet.union fn_result.nr_stuck_metas result.nr_stuck_metas
          }
      | TmMeta _ ->
          {
            nr_term = TmApp (fn', arg, app_boundary, tag);
            nr_stuck_metas =
              StringSet.union fn_result.nr_stuck_metas (collect_metas fn')
          }
      | _ ->
          {
            nr_term = TmApp (fn', arg, app_boundary, tag);
            nr_stuck_metas = fn_result.nr_stuck_metas
          }
      end

  | TmIf (cond, thn, els, tag) ->
      let cond_result = whnf cond in
      begin match cond_result.nr_term with
      | TmLiteral (LitBool true, _) ->
          let result = whnf thn in
          {
            result with
            nr_stuck_metas =
              StringSet.union cond_result.nr_stuck_metas result.nr_stuck_metas
          }
      | TmLiteral (LitBool false, _) ->
          let result = whnf els in
          {
            result with
            nr_stuck_metas =
              StringSet.union cond_result.nr_stuck_metas result.nr_stuck_metas
          }
      | TmMeta _ ->
          {
            nr_term = TmIf (cond_result.nr_term, thn, els, tag);
            nr_stuck_metas =
              StringSet.union cond_result.nr_stuck_metas
                (collect_metas cond_result.nr_term)
          }
      | _ ->
          {
            nr_term = TmIf (cond_result.nr_term, thn, els, tag);
            nr_stuck_metas = cond_result.nr_stuck_metas
          }
      end

  | TmPrim2 (Eq, lhs, rhs, tag) ->
      let lhs_result = whnf lhs in
      let rhs_result = whnf rhs in
      begin match lhs_result.nr_term, rhs_result.nr_term with
      | TmLiteral (l, _), TmLiteral (r, _) ->
          merge_results
            (TmLiteral (LitBool (l = r), tag))
            [lhs_result; rhs_result]
      | _ ->
          let blocked =
            StringSet.union lhs_result.nr_stuck_metas rhs_result.nr_stuck_metas
          in
          let blocked =
            match lhs_result.nr_term, rhs_result.nr_term with
            | TmMeta _, _ -> StringSet.union blocked (collect_metas lhs_result.nr_term)
            | _, TmMeta _ -> StringSet.union blocked (collect_metas rhs_result.nr_term)
            | _ -> blocked
          in
          {
            nr_term = TmPrim2 (Eq, lhs_result.nr_term, rhs_result.nr_term, tag);
            nr_stuck_metas = blocked
          }
      end

  | TmPrim2 (op, lhs, rhs, tag) ->
      let lhs_result = whnf lhs in
      let rhs_result = whnf rhs in
      begin match lhs_result.nr_term, rhs_result.nr_term with
      | TmLiteral (LitInt (n1, suff1), _),
        TmLiteral (LitInt (n2, suff2), _) when suff1 = suff2 ->
          merge_results
            (TmLiteral (prim2_int_op op n1 n2 suff1, tag))
            [lhs_result; rhs_result]
      | lhs', rhs' ->
          let blocked =
            StringSet.union lhs_result.nr_stuck_metas rhs_result.nr_stuck_metas
          in
          let blocked =
            match lhs', rhs' with
            | TmMeta _, _ -> StringSet.union blocked (collect_metas lhs')
            | _, TmMeta _ -> StringSet.union blocked (collect_metas rhs')
            | _ -> blocked
          in
          {
            nr_term = TmPrim2 (op, lhs', rhs', tag);
            nr_stuck_metas = blocked
          }
      end

  | TmPrim1 (Neg, body, tag) ->
      let result = whnf body in
      begin match result.nr_term with
      | TmLiteral (LitInt (n, suff), _) ->
          { result with nr_term = TmLiteral (LitInt (Uint64.neg n, suff), tag) }
      | TmMeta _ ->
          {
            nr_term = TmPrim1 (Neg, result.nr_term, tag);
            nr_stuck_metas =
              StringSet.union result.nr_stuck_metas (collect_metas result.nr_term)
          }
      | _ ->
          { result with nr_term = TmPrim1 (Neg, result.nr_term, tag) }
      end

  | TmPrim1 (Not, body, tag) ->
      let result = whnf body in
      begin match result.nr_term with
      | TmLiteral (LitBool b, _) ->
          { result with nr_term = TmLiteral (LitBool (not b), tag) }
      | TmMeta _ ->
          {
            nr_term = TmPrim1 (Not, result.nr_term, tag);
            nr_stuck_metas =
              StringSet.union result.nr_stuck_metas (collect_metas result.nr_term)
          }
      | _ ->
          { result with nr_term = TmPrim1 (Not, result.nr_term, tag) }
      end

  | TmPrim1 (op, body, tag) ->
      let result = whnf body in
      { result with nr_term = TmPrim1 (op, result.nr_term, tag) }

  | TmLambda _ | TmPi _
  | TmLiteral _ | TmVar _ | TmUniverse _
  | TmMeta _ | TmPrimTy _ ->
      empty_result tm

(* Update this to return info for determining Resolved or Stuck. Maybe WHNF needs updating too? *)
let rec normalize tm =
  let head = whnf tm in
  let tm = head.nr_term in
  match tm with
  | TmLambda (x, param_ty, body, binder_info, tag) ->
      let ty = normalize param_ty in
      let body = normalize body in
      merge_results
        (TmLambda (x, ty.nr_term, body.nr_term, binder_info, tag))
        [head; ty; body]
  | TmPi (x, domain, codomain, binder_info, tag) ->
      let domain = normalize domain in
      let codomain = normalize codomain in
      merge_results
        (TmPi (x, domain.nr_term, codomain.nr_term, binder_info, tag))
        [head; domain; codomain]
  | TmApp (fn, arg, app_boundary, tag) ->
      let fn = normalize fn in
      let arg = normalize arg in
      let result =
        whnf (TmApp (fn.nr_term, arg.nr_term, app_boundary, tag))
      in
      merge_results result.nr_term [head; fn; arg; result]
  | TmIf (cond, thn, els, tag) ->
      let cond = normalize cond in
      let thn = normalize thn in
      let els = normalize els in
      let result =
        whnf (TmIf (cond.nr_term, thn.nr_term, els.nr_term, tag))
      in
      merge_results result.nr_term [head; cond; thn; els; result]
  | TmPrim2 (op, lhs, rhs, tag) ->
      let lhs = normalize lhs in
      let rhs = normalize rhs in
      let result =
        whnf (TmPrim2 (op, lhs.nr_term, rhs.nr_term, tag))
      in
      merge_results result.nr_term [head; lhs; rhs; result]
  | TmPrim1 (op, body, tag) ->
      let body = normalize body in
      let result = whnf (TmPrim1 (op, body.nr_term, tag)) in
      merge_results result.nr_term [head; body; result]
  | TmLet (x, value, body, _) ->
      normalize (subst_vars_in_term x value body)
  | (TmLiteral _ | TmVar _ | TmUniverse _
    | TmMeta _ | TmPrimTy _) ->
      head

and normalize_if_reduced result =
  let reduced = whnf result.nr_term in
  let stuck_metas =
    StringSet.union result.nr_stuck_metas reduced.nr_stuck_metas
  in
  if reduced.nr_term = result.nr_term then
    { nr_term = result.nr_term; nr_stuck_metas = stuck_metas }
  else
    let normalized = normalize reduced.nr_term in
    {
      nr_term = normalized.nr_term;
      nr_stuck_metas =
        StringSet.union stuck_metas normalized.nr_stuck_metas
    }
;;

type typed_tag = (sourcespan * (sourcespan term))

type 'a residual_constraint = 
    | RCUnify of 'a term * 'a term
    | RCAuto of 'a term
    | RCWantedTC of unit term * sourcespan

(* for tracking postponed unification *)
type 'a residual =
    {
        (* terms to unify *)
        (* r_constraint: ('a term) * ('a term); *)
        r_constraint: 'a residual_constraint;
        (* metas required before further reduction *)
        r_blockers: (string list)
    }

type wanted = 
    {
        w_pred: unit term;
        w_span: sourcespan;
    }

type 'a infer_result =
    {
        inf_res_subst: (unit term subst);
        inf_res_inferred_type: (unit term);
        inf_res_residuals: (unit residual list);
        (* inf_res_wanteds: (wanted list); *)
        inf_res_elaborated_term: ('a term);
    }

let apply_subst_term (subst : unit term subst) (t : 'a term) : 'a term =
  List.fold_left (fun acc (x, m) -> subst_metas_in_term x m acc) t subst

let apply_subst_env (subst : unit term subst) (env : unit term envt) : unit term envt =
  StringMap.map (fun typ -> (apply_subst_term subst typ)) env

let apply_subst_subst (sub1 : unit term subst) (sub2 : unit term subst) : unit term subst =
  List.map (fun (tyvar, to_typ) -> (tyvar, (apply_subst_term sub1 to_typ))) sub2


let compose_subst (sub1 : unit term subst) (sub2 : unit term subst) : unit term subst =
  sub1 @ apply_subst_subst sub1 sub2


let occurs (name : string) (t : 'a term) = List.mem name (tm_meta_vars t)

let rec unify (tm1 : unit term) (tm2 : unit term) (span : sourcespan) : (unit term subst * unit residual list) =
    let unify_meta_other meta_name meta_scope other =
        if occurs meta_name other then
            match other with
            | TmMeta (other_name, other_scope, other_tag) when other_name = meta_name -> []
            | _ ->
                failwith (sprintf "Unification failure at <%s>:\noccurs check failed " (string_of_sourcespan span))
        else
            let ftv = tm_free_vars other in
            let not_in_scope = List.filter (fun var_name ->
                    not (StringMap.mem var_name meta_scope)) ftv in
            match not_in_scope with
            | [] -> [(meta_name, other)]
            | _ -> failwith 
                (sprintf 
                "Unification failure at <%s>:\nmeta variable %s cannot be substituted with variables outside of it's scope." 
                (string_of_sourcespan span) meta_name)
    in
    let tm1_norm_res = normalize tm1 in
    let tm2_norm_res = normalize tm2 in
    match tm1_norm_res.nr_stuck_metas, tm2_norm_res.nr_stuck_metas with
    | stuck1, stuck2 when not ((StringSet.is_empty stuck1) || (StringSet.is_empty stuck2)) -> 
        [], [{r_constraint = RCUnify(tm1_norm_res.nr_term, tm2_norm_res.nr_term); r_blockers = (StringSet.to_list (StringSet.union stuck1 stuck2))}]
    | _ -> (
            let ntm1, ntm2 = tm1_norm_res.nr_term, tm2_norm_res.nr_term in
            match ntm1, ntm2 with
            | TmMeta (name, scope, tag), other | other, TmMeta (name, scope, tag) ->
                let subst = unify_meta_other name scope other in
                subst, []
            | _, _ when alpha_eq ntm1 ntm2 -> [], []
            | TmApp(t1_ret, t1_arg, app_boundary1, tag1), TmApp(t2_ret, t2_arg, app_boundary2, tag2)
            when app_boundary1 = app_boundary2 ->
                let ret_subst, ret_residuals = unify (t1_ret) (t2_ret) span in
                let arg_subst, arg_residuals = unify (t1_arg) (t2_arg) span in
                compose_subst ret_subst arg_subst, ret_residuals @ arg_residuals
            | TmPi(x1, a1, m1, binder_info1, tag1), TmPi(x2, a2, m2, binder_info2, tag2) 
            | TmLambda(x1, a1, m1, binder_info1, tag1), TmLambda(x2, a2, m2, binder_info2, tag2) 
            when binder_info1 = binder_info2 ->
                let arg_subst, arg_residuals = unify (a1) (a2) span in
                let ret_subst, ret_residuals = unify (m1) (m2) span in
                compose_subst arg_subst ret_subst, arg_residuals @ ret_residuals
            (* TODO: other terms *)
            | _, _ -> failwith (sprintf "Unification failure at <%s>:\ncannot unify %s and %s" (string_of_sourcespan span) "<tm1>" "<tm2>")
    )

let rec solve_auto (meta: 'a term) (typ: unit term) (span : sourcespan) : (unit term subst * unit residual list) =
    failwith "TODO"
    (* 
        extract meta env. 
        search env for anything bound with the exact type "typ".
        search enum and struct constructors recursively.
        search functions in the environment recursively that return the exact type "typ".
    *)



let type_synth_terms (p: sourcespan program) =
    let gensym =
        let next = ref 0 in
        fun name ->
        next := !next + 1;
        sprintf "%s_%d" name !next
    in
    (* IDEA: 
        getting the Pi type of a function should remove the implicit arguments and subst them with fresh meta variables *)
    (* IDEA: 
        elaboration should lower methods whose impl is a prim. Also, I think change prim methods
        to not be callable by name. Prevent writing "add(5, 7)" directly. Perhaps losing some
        ergonomics in some cases, but makes this system much stronger and easier to reason about.*)
    (* IDEA:
        Consider adding a "context" to a TmMeta. Need to avoid locals escaping their scope in types.
        Think about what this representation should be. *)
    (* IDEA:
        Make a TmBorrow, and when doing type inference on the body, add (Reg: Region) to the env.
        For TmIf, when checking the true branch, add (p: So(cond)) to the env.
        This way, extra values can be available for type inference without any extra syntactic sugar
        or runtime erasure. It all just happens during the type inference. I'm a genius btw. *)
    (* IDEA:
        add Constraint as a type of piinfo, separate from Auto.
        Constraints will always be last?
        infer_type_elab when coming across a Pi type with a constraint will remove it
        from the type and try to solve the wanted. If stuck, we add it to the wanted list.
        Need to come up with a way to track stuck autos. Stuck implicits are tracked with
        residuals, but stuck autos need a way to defer as well.
        Maybe also replace the scope of TmMeta with a StringMap so it is actually just an
        environment. When proof solving occurs, it can look for values in the env that existed
        when the meta was created. *)
    (* IDEA:
        make Pi types contain information about how many arguments are left or possibly
        just whether it is the last argument or not. This is because with mixed ordering 
        of implicit, explicit, auto, and constraints, it may not be possible to tell
        from a TmApp alone where the boundaries lie.*)
    (* Thoughts:
        Something about the way that infer_type_app_elab works just doesn't sit right with me.
        Rather than a separate insert_implicit_args, it should be able to handle the implicit args.
        I think there should be some kind of replacement for "normalize" when the return type is
        computed. Perhaps that's where the recursive call should be? Maybe it should depend on the
        app_boundary? It needs some way of handling when there are trailing constraints or implicit args.
        This is getting really frustrating. *)
    let rec infer_type_elab (env: unit term envt) (tm: 'a term) : 'b infer_result =
        match tm with
        | TmLiteral(LitBool(b), tag) ->
            let inferred_type = TmPrimTy(Bool, ()) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_elaborated_term = TmLiteral(LitBool(b), (tag, inferred_type))
            }
        | TmLiteral(LitChar(c), tag) ->
            let inferred_type = TmPrimTy(Char, ()) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_elaborated_term = TmLiteral(LitChar(c), (tag, inferred_type))
            }
        | TmLiteral(LitInt(n, suffix), tag) ->
            let inferred_type = (
                match suffix with
                | IntSuffix width ->
                    TmPrimTy(Int width, ())
                | UIntSuffix width ->
                    TmPrimTy(UInt width, ()))
            in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_elaborated_term = TmLiteral(LitInt(n, suffix), (tag, inferred_type))
            }
        | TmLiteral(LitString(s), tag) ->
            let str_len = String.length s in
            let str_len_lit = TmLiteral(LitInt(Uint64.of_int str_len, UIntSuffix(U64)), ()) in
            let span_var = TmVar("span", ()) in
            let t_char = TmPrimTy(Char, ()) in
            let region = TmVar("Static", ()) in
            let str_typ = TmApp(TmApp(TmApp(span_var, t_char, Continue, ()), str_len_lit, Continue, ()), region, End, ()) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = str_typ; 
                inf_res_residuals = [];
                inf_res_elaborated_term = TmLiteral(LitString(s), (tag, str_typ))
            }
        | TmUniverse(lvl, tag) ->
            let inferred_type = TmUniverse(lvl + 1, ()) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_elaborated_term = TmUniverse(lvl, (tag, inferred_type))
            }
        | TmPrimTy(typ, tag) ->
            let inferred_type = TmUniverse(0, ()) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_elaborated_term = TmPrimTy(typ, (tag, inferred_type))
            }
        | TmVar(name, tag) ->
            let inferred_type = (StringMap.find name env) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_elaborated_term = TmVar(name, (tag, inferred_type))
            }
        | TmApp(called, arg, app_boundary, tag) ->
            let inf_res_called = infer_type_elab env called in
            let new_env = apply_subst_env inf_res_called.inf_res_subst env in
            infer_type_app_elab new_env inf_res_called arg app_boundary tag
        | _ -> failwith "Unsupported term"
    and infer_type_app_elab env called_inf_res arg app_boundary (span: sourcespan) =
        let rec implicit_helper env fn_inf_res =
            let fn_type = normalize fn_inf_res.inf_res_inferred_type in
            match fn_type.nr_term with
            | TmPi (bound_name, bound_type, return_typ, binder_info, _)
                when (binder_info.bi_piinfo = Implicit) ->
                let fresh_meta = TmMeta (gensym "?m", env, (span)) in
                let new_inf_res = helper env fn_inf_res fresh_meta span in
                let new_env = apply_subst_env new_inf_res.inf_res_subst env in
                new_env, new_inf_res
            | TmPi (bound_name, bound_type, return_typ, binder_info, _)
                when (binder_info.bi_piinfo = Auto) ->
                let fresh_meta = TmMeta (gensym "?m", env, (span)) in
                let new_inf_res = helper env fn_inf_res fresh_meta span in
                let new_env = apply_subst_env new_inf_res.inf_res_subst env in
                let new_bound_type = apply_subst_term new_inf_res.inf_res_subst bound_type in
                let new_subst, new_residuals = solve_auto fresh_meta new_bound_type span in
                let new_inf_res = {
                    new_inf_res with
                    inf_res_subst = compose_subst new_inf_res.inf_res_subst new_subst;
                    inf_res_residuals = new_residuals @ new_inf_res.inf_res_residuals
                } in
                let new_new_env = apply_subst_env new_inf_res.inf_res_subst new_env in
                new_new_env, new_inf_res
            | _ -> ice "impossible"
        and collect_tail_implicits env (fn_inf_res: (sourcespan * unit term) infer_result) =
            let fn_type = normalize fn_inf_res.inf_res_inferred_type in
            match fn_type.nr_term with
            | TmPi (bound_name, bound_type, return_typ, binder_info, _)
                when (binder_info.bi_piinfo = Explicit) ->
                failwith (sprintf "arity mismatch at <%s>:\nNot enough args" (string_of_sourcespan span))
            | TmPi (bound_name, bound_type, return_typ, binder_info, _)
                when (binder_info.bi_piinfo = Implicit) ->
                let new_env, new_inf_res = implicit_helper env fn_inf_res in
                collect_tail_implicits new_env new_inf_res
            | TmPi (bound_name, bound_type, return_typ, binder_info, _)
                when (binder_info.bi_piinfo = Auto) ->
                let new_env, new_inf_res = implicit_helper env fn_inf_res in
                collect_tail_implicits new_env new_inf_res
            | TmPi (bound_name, bound_type, return_typ, binder_info, _)
                when (binder_info.bi_piinfo = Constraint) ->
                (* run wanted solver here *)
                (* return with this pi removed *)
                failwith "TODO"
            | _ -> fn_inf_res
        and insert_implicit_arg env (fn_inf_res: (sourcespan * unit term) infer_result) =
            let fn_type = normalize fn_inf_res.inf_res_inferred_type in
            match fn_type.nr_term with
            | TmPi (bound_name, bound_type, return_typ, binder_info, _)
                when (binder_info.bi_piinfo = Implicit) ->
                let new_env, new_inf_res = implicit_helper env fn_inf_res in
                insert_implicit_arg new_env new_inf_res
            | TmPi (bound_name, bound_type, return_typ, binder_info, _)
                when (binder_info.bi_piinfo = Auto) ->
                let new_env, new_inf_res = implicit_helper env fn_inf_res in
                insert_implicit_arg new_env new_inf_res
            | _ -> env, fn_inf_res
        and helper env (called_inf_res: (sourcespan * unit term) infer_result) arg span =
            match called_inf_res.inf_res_inferred_type with
            | TmPi(bound_name, typ_of_bound_name, return_typ, binder_info, tag) ->
                let arg_inf_res = infer_type_elab env arg in
                let arg_typ = (
                    apply_subst_term called_inf_res.inf_res_subst
                    (apply_subst_term
                        arg_inf_res.inf_res_subst
                        arg_inf_res.inf_res_inferred_type)
                ) in
                let new_typ_of_bound_name = apply_subst_term arg_inf_res.inf_res_subst
                    (apply_subst_term called_inf_res.inf_res_subst typ_of_bound_name) in
                let subst, residuals = unify (arg_typ) (new_typ_of_bound_name) span in
                let new_subst, new_residuals = 
                    compose_subst called_inf_res.inf_res_subst (compose_subst arg_inf_res.inf_res_subst subst),
                    called_inf_res.inf_res_residuals @ arg_inf_res.inf_res_residuals @ residuals 
                in
                let new_ret_typ = apply_subst_term new_subst return_typ in
                let arg_term = apply_subst_term new_subst arg_inf_res.inf_res_elaborated_term in
                let result_type = subst_vars_in_term bound_name (untag_term arg_term) new_ret_typ in
                let result_nr_res = normalize result_type in
                let result_type = result_nr_res.nr_term in
                let elaborated_term =
                    TmApp (
                        apply_subst_term new_subst called_inf_res.inf_res_elaborated_term,
                        arg_term,
                        binder_info.bi_app_boundary,
                        (span, result_type)
                    ) in
                {
                    inf_res_subst = new_subst;
                    inf_res_inferred_type = result_type;
                    inf_res_residuals = new_residuals;
                    inf_res_elaborated_term = elaborated_term;
                }
            | _ -> failwith "Expected callable, given unsupported type"
        in
        let new_env, called_inf_res = insert_implicit_arg env called_inf_res in
        let res_inf_res = helper new_env called_inf_res arg span in
        let new_new_env = apply_subst_env res_inf_res.inf_res_subst new_env in
        match app_boundary with
        | Continue -> res_inf_res
        | End -> collect_tail_implicits new_new_env res_inf_res
    in
    ()


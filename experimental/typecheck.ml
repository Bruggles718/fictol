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
  | TmVar (y, tag) when x = y -> m
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

let rec subst_metas_in_term x m tm =
  match tm with
  | TmMeta (y, env, tag) when x = y -> m
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

let tag_term (tag : 'a) (tm : unit term) : 'a term =
  match tm with
  | TmUniverse (level, _) -> TmUniverse (level, tag)
  | TmPi (name, domain, codomain, binder_info, _) ->
      TmPi (name, domain, codomain, binder_info, tag)
  | TmLambda (name, domain, body, binder_info, _) ->
      TmLambda (name, domain, body, binder_info, tag)
  | TmLet (name, value, body, _) ->
      TmLet (name, value, body, tag)
  | TmApp (fn, arg, app_boundary, _) ->
      TmApp (fn, arg, app_boundary, tag)
  | TmPrim1 (op, arg, _) -> TmPrim1 (op, arg, tag)
  | TmPrim2 (op, lhs, rhs, _) -> TmPrim2 (op, lhs, rhs, tag)
  | TmIf (cond, then_branch, else_branch, _) ->
      TmIf (cond, then_branch, else_branch, tag)
  | TmLiteral (lit, _) -> TmLiteral (lit, tag)
  | TmPrimTy (typ, _) -> TmPrimTy (typ, tag)
  | TmVar (name, _) -> TmVar (name, tag)
  | TmMeta (name, context, _) -> TmMeta (name, context, tag)

let rec untag_term (tm : 'a term) : unit term =
  match tm with
  | TmUniverse (level, _) ->
      TmUniverse (level, ())
  | TmPi (name, domain, codomain, binder_info, _) ->
      TmPi
        (name, untag_term domain, untag_term codomain, binder_info, ())
  | TmLambda (name, domain, body, binder_info, _) ->
      TmLambda
        (name, untag_term domain, untag_term body, binder_info, ())
  | TmLet (name, value, body, _) ->
      TmLet (name, untag_term value, untag_term body, ())
  | TmApp (fn, arg, app_boundary, _) ->
      TmApp (untag_term fn, untag_term arg, app_boundary, ())
  | TmPrim1 (op, arg, _) ->
      TmPrim1 (op, untag_term arg, ())
  | TmPrim2 (op, lhs, rhs, _) ->
      TmPrim2 (op, untag_term lhs, untag_term rhs, ())
  | TmIf (cond, then_branch, else_branch, _) ->
      TmIf
        (untag_term cond, untag_term then_branch, untag_term else_branch, ())
  | TmLiteral (lit, _) ->
      TmLiteral (lit, ())
  | TmPrimTy (typ, _) ->
      TmPrimTy (typ, ())
  | TmVar (name, _) ->
      TmVar (name, ())
  | TmMeta (name, context, _) ->
      TmMeta (name, context, ())

let tag_of_term (tm : 'a term) : 'a =
  match tm with
  | TmUniverse (_, tag)
  | TmPi (_, _, _, _, tag)
  | TmLambda (_, _, _, _, tag)
  | TmLet (_, _, _, tag)
  | TmApp (_, _, _, tag)
  | TmPrim1 (_, _, tag)
  | TmPrim2 (_, _, _, tag)
  | TmIf (_, _, _, tag)
  | TmLiteral (_, tag)
  | TmPrimTy (_, tag)
  | TmVar (_, tag)
  | TmMeta (_, _, tag) -> tag

type typed_tag = (sourcespan * (sourcespan term))

(* for tracking postponed unification *)
type 'a residual =
    {
        (* terms to unify *)
        r_constraint: ('a term * 'a term);
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
        inf_res_wanteds: (wanted list);
        inf_res_elaborated_term: ('a term);
    }

let type_synth_terms (p: sourcespan program) = failwith "TODO"
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
    (* let rec infer_term_elab (env : sourcespan term envt) (e : sourcespan term) :
      sourcespan term subst * sourcespan term * sourcespan term list * (typed_tag) term = *)
    let rec infer_type_elab (env: unit term envt) (tm: sourcespan term) : 'a infer_result =
        match tm with
        | TmLiteral(LitBool(b), tag) ->
            let inferred_type = TmPrimTy(Bool, ()) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_wanteds = []; 
                inf_res_elaborated_term = TmLiteral(LitBool(b), (tag, inferred_type))
            }
        | TmLiteral(LitChar(c), tag) ->
            let inferred_type = TmPrimTy(Char, ()) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_wanteds = []; 
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
                inf_res_wanteds = []; 
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
                inf_res_wanteds = []; 
                inf_res_elaborated_term = TmLiteral(LitString(s), (tag, str_typ))
            }
        | TmUniverse(lvl, tag) ->
            let inferred_type = TmUniverse(lvl + 1, ()) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_wanteds = []; 
                inf_res_elaborated_term = TmUniverse(lvl, (tag, inferred_type))
            }
        | TmPrimTy(typ, tag) ->
            let inferred_type = TmUniverse(0, ()) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_wanteds = []; 
                inf_res_elaborated_term = TmPrimTy(typ, (tag, inferred_type))
            }
        | TmVar(name, tag) ->
            let inferred_type = (StringMap.find name env) in
            {
                inf_res_subst = []; 
                inf_res_inferred_type = inferred_type; 
                inf_res_residuals = [];
                inf_res_wanteds = []; 
                inf_res_elaborated_term = TmVar(name, (tag, inferred_type))
            }
        | _ -> failwith "Unsupported term"
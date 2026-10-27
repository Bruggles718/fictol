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

let rec subst x m tm =
  match tm with
  | TmVar (y, tag) when x = y -> m
  | TmApp (m', n, app_boundary, tag) -> TmApp (subst x m m', subst x m n, app_boundary, tag)
  | TmLet (y, a, n, tag) when x = y -> TmLet (y, subst x m a, n, tag)
  | TmLet (y, a, n, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst x m (rename (freshen banlist y) tm)
  | TmLet (y, a, n, tag) -> TmLet (y, subst x m a, n, tag)
  | TmLambda (y, a, n, call_type, tag) when x = y -> TmLambda (y, subst x m a, n, call_type, tag)
  | TmLambda (y, a, n, call_type, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst x m (rename (freshen banlist y) tm)
  | TmLambda (y, a, n, call_type, tag) -> TmLambda (y, subst x m a, subst x m n, call_type, tag)
  | TmPi (y, a, n, call_type, tag) when x = y -> TmPi (y, subst x m a, n, call_type, tag)
  | TmPi (y, a, n, call_type, tag) when List.mem y (tm_free_vars m) ->
      let banlist = tm_free_vars m @ all_vars n in
      subst x m (rename (freshen banlist y) tm)
  | TmPi (y, a, n, call_type, tag) -> TmPi (y, subst x m a, subst x m n, call_type, tag)
  | TmIf (cond, thn, els, tag) -> TmIf (subst x m cond, subst x m thn, subst x m els, tag)
  | TmPrim1 (op, body, tag) -> TmPrim1 (op, subst x m body, tag)
  | TmPrim2 (op, lhs, rhs, tag) -> TmPrim2 (op, subst x m lhs, subst x m rhs, tag)
  | TmLiteral _ | TmVar _ | TmUniverse _ | TmPrimTy _ | TmMeta _ -> tm

and rename x' binder =
  match binder with
  | TmLambda (x, a, m, call_type, tag) ->
      TmLambda (x', a, subst x (TmVar (x', tag)) m, call_type, tag)
  | TmPi (x, a, m, call_type, tag) -> TmPi (x', a, subst x (TmVar (x', tag)) m, call_type, tag)
  | TmLet (x, a, m, tag) -> TmLet (x', a, subst x (TmVar (x', tag)) m, tag)
  | _ -> raise (InternalCompilerError "rename term failure: Given non binder")
;;

let rec subst_metas_in_term x m tm =
  match tm with
  | TmMeta (y, tag) when x = y -> m
  | TmApp (m', n, app_boundary, tag) ->
      TmApp (subst_metas_in_term x m m', subst_metas_in_term x m n, app_boundary, tag)
  | TmLet (y, a, n, tag) -> TmLet (y, subst_metas_in_term x m a, n, tag)
  | TmLambda (y, a, n, call_type, tag) ->
      TmLambda (y, subst_metas_in_term x m a, subst_metas_in_term x m n, call_type, tag)
  | TmPi (y, a, n, call_type, tag) ->
      TmPi (y, subst_metas_in_term x m a, subst_metas_in_term x m n, call_type, tag)
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
  | TmLambda (x1, a1, m1, call_type1, _), TmLambda (x2, a2, m2, call_type2, _) when x1 = x2 ->
      call_type1 = call_type2 && alpha_eq a1 a2 && alpha_eq m1 m2
  | TmPi (x1, a1, m1, call_type1, _), TmPi (x2, a2, m2, call_type2, _) when x1 = x2 ->
      call_type1 = call_type2 && alpha_eq a1 a2 && alpha_eq m1 m2
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
  | TmUniverse lvl1, TmUniverse lvl2 -> lvl1 = lvl2
  | TmPrimTy (typ1, _), TmPrimTy (typ2, _) -> typ1 = typ2
  | TmPrim1 (op1, body1, _), TmPrim1 (op2, body2, _) -> op1 = op2 && alpha_eq body1 body2
  | TmPrim2 (op1, lhs1, rhs1, _), TmPrim2 (op2, lhs2, rhs2, _) ->
      op1 = op2 && alpha_eq lhs1 lhs2 && alpha_eq rhs1 rhs2
  | _, _ -> false
;;

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
  (* Zeta reduction. *)
  | TmLet (x, value, body, _) -> whnf (subst x value body)
  (* Reduce the function position, but not the argument. *)
  | TmApp (fn, arg, app_boundary, tag) ->
      let fn' = whnf fn in
      begin match fn' with
      (* Beta reduction. Notice that [arg] is not reduced first. *)
      | TmLambda (x, _, body, _, _) -> whnf (subst x arg body)
      | _ -> TmApp (fn', arg, app_boundary, tag)
      end
  (* Reduce only the condition. *)
  | TmIf (cond, thn, els, tag) ->
      let cond' = whnf cond in
      begin match cond' with
      | TmLiteral (LitBool true, _) -> whnf thn
      | TmLiteral (LitBool false, _) -> whnf els
      | _ -> TmIf (cond', thn, els, tag)
      end
  (* Equality computes only when both operands become literals. *)
  | TmPrim2 (Eq, lhs, rhs, tag) ->
      let lhs' = whnf lhs in
      let rhs' = whnf rhs in
      begin match (lhs', rhs') with
      | TmLiteral (l, _), TmLiteral (r, _) ->
        begin match equal_literals l r with
        | Some result -> TmLiteral (LitBool result, tag)
        | None -> TmPrim2 (Eq, lhs', rhs', tag)
        end
      | _ -> TmPrim2 (Eq, lhs', rhs', tag)
      end
  (* Integer operations must expose their operands before computing. *)
  | TmPrim2 (op, lhs, rhs, tag) ->
      let lhs' = whnf lhs in
      let rhs' = whnf rhs in
      begin match (lhs', rhs') with
      | TmLiteral (LitInt (n1, suff1), _), TmLiteral (LitInt (n2, suff2), _) when suff1 = suff2 ->
          TmLiteral (prim2_int_op op n1 n2 suff1, tag)
      | _ -> TmPrim2 (op, lhs', rhs', tag)
      end
  | TmPrim1 (Neg, body, tag) ->
      let body' = whnf body in
      begin match body' with
      | TmLiteral (LitInt (n, suff), _) -> TmLiteral (LitInt (Uint64.neg n, suff), tag)
      | _ -> TmPrim1 (Neg, body', tag)
      end
  | TmPrim1 (Not, body, tag) ->
      let body' = whnf body in
      begin match body' with
      | TmLiteral (LitBool b, _) -> TmLiteral (LitBool (not b), tag)
      | _ -> TmPrim1 (Not, body', tag)
      end
  | TmPrim1 (op, body, tag) -> TmPrim1 (op, whnf body, tag)
  (* A lambda is already in WHNF. *)
  | TmLambda _ -> tm
  (* A Pi type is already in WHNF. *)
  | TmPi _ -> tm
  (* Neutral and atomic terms are already in WHNF. *)
  | TmLiteral _ | TmVar _ | TmUniverse _ | TmMeta _ | TmPrimTy _ -> tm
;;

let rec normalize tm =
  match whnf tm with
  | TmLambda (x, param_ty, body, call_type, tag) ->
      TmLambda (x, normalize param_ty, normalize body, call_type, tag)
  | TmPi (x, domain, codomain, call_type, tag) ->
      TmPi (x, normalize domain, normalize codomain, call_type, tag)
  | TmApp (fn, arg, app_boundary, tag) ->
      let fn' = normalize fn in
      let arg' = normalize arg in
      let result = TmApp (fn', arg', app_boundary, tag) in
      normalize_if_reduced result
  | TmIf (cond, thn, els, tag) ->
      let cond' = normalize cond in
      let thn' = normalize thn in
      let els' = normalize els in
      let result = TmIf (cond', thn', els', tag) in
      normalize_if_reduced result
  | TmPrim2 (op, lhs, rhs, tag) ->
      let lhs' = normalize lhs in
      let rhs' = normalize rhs in
      let result = TmPrim2 (op, lhs', rhs', tag) in
      normalize_if_reduced result
  | TmPrim1 (op, body, tag) ->
      let body' = normalize body in
      let result = TmPrim1 (op, body', tag) in
      normalize_if_reduced result
  (* WHNF should always eliminate lets, but handling one here makes the
     function robust if whnf's behavior later changes. *)
  | TmLet (x, value, body, _) -> normalize (subst x value body)
  | (TmLiteral _ | TmVar _ | TmUniverse _ | TmMeta _ | TmPrimTy _) as tm -> tm

and normalize_if_reduced tm =
  let tm' = whnf tm in
  if tm' = tm then
    tm
  else
    normalize tm'
;;

let conv lhs rhs =
  alpha_eq (normalize lhs) (normalize rhs)
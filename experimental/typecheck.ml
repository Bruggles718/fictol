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
  | TmVar (x, tag) -> [ x ]
  | TmApp (m, n, app_boundary, tag) -> tm_free_vars m @ tm_free_vars n
  | TmLambda (x, a, m, _, tag) | TmPi (x, a, m, _, tag) | TmLet (x, a, m, tag) -> tm_free_vars a @ List.filter (( <> ) x) (tm_free_vars m)
  | TmIf (cond, thn, els, tag) -> tm_free_vars cond @ tm_free_vars thn @ tm_free_vars els
  | TmPrim1 (op, body, tag) ->
    tm_free_vars body
  | TmPrim2 (op, lhs, rhs, tag) ->
    tm_free_vars lhs @ tm_free_vars rhs
  | TmUniverse _ | TmLiteral _ | TmPrimTy _ | TmMeta _ -> []

let rec binders tm =
  match tm with
  | TmApp (m, n, app_boundary, tag) -> binders m @ binders n
  | TmLambda (x, a, m, _, tag) | TmPi (x, a, m,_, tag) | TmLet (x, a, m, tag) -> [x] @ binders a @ (binders m)
  | TmIf (cond, thn, els, tag) -> binders cond @ binders thn @ binders els
  | TmPrim1 (op, body, tag) ->
    binders body
  | TmPrim2 (op, lhs, rhs, tag) ->
    binders lhs @ binders rhs
  | TmUniverse _ | TmLiteral _ | TmVar _ | TmMeta _ | TmPrimTy _ -> []

let all_vars tm = tm_free_vars tm @ binders tm

let rec freshen (banlist : string list) (base : string) =
  if List.mem base banlist then freshen banlist (base ^ "'") else base

let rec subst x m tm =
  match tm with
  | TmVar (y, tag) when x = y -> m
  | TmApp (m', n, app_boundary, tag) -> TmApp(subst x m m', subst x m n, app_boundary, tag)
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
  | TmPrim1 (op, body, tag) ->
    TmPrim1 (op, subst x m body, tag)
  | TmPrim2 (op, lhs, rhs, tag) ->
    TmPrim2 (op, subst x m lhs, subst x m rhs, tag)
  | TmLiteral _ | TmVar _ | TmUniverse _ | TmPrimTy _ | TmMeta _ -> tm


and rename x' binder =
  match binder with
  | TmLambda (x, a, m, call_type, tag) -> TmLambda (x', a, (subst x (TmVar (x',tag)) m), call_type, tag)
  | TmPi (x, a, m, call_type, tag) -> TmPi (x', a, (subst x (TmVar (x',tag)) m), call_type, tag)
  | TmLet(x, a, m, tag) -> TmLet (x', a, (subst x (TmVar (x',tag)) m), tag)
  | _ -> raise (InternalCompilerError("rename term failure: Given non binder"))
  
let rec subst_metas_in_term x m tm =
  match tm with
  | TmMeta (y, tag) when x = y -> m
  | TmApp (m', n, app_boundary, tag) -> TmApp(subst_metas_in_term x m m', subst_metas_in_term x m n, app_boundary, tag)
  | TmLet (y, a, n, tag) -> TmLet (y, subst_metas_in_term x m a, n, tag)
  | TmLambda (y, a, n, call_type, tag) -> TmLambda (y, subst_metas_in_term x m a, subst_metas_in_term x m n, call_type, tag)
  | TmPi (y, a, n, call_type, tag) -> TmPi (y, subst_metas_in_term x m a, subst_metas_in_term x m n, call_type, tag)
  | TmIf (cond, thn, els, tag) -> TmIf (subst_metas_in_term x m cond, subst_metas_in_term x m thn, subst_metas_in_term x m els, tag)
  | TmPrim1 (op, body, tag) ->
    TmPrim1 (op, subst_metas_in_term x m body, tag)
  | TmPrim2 (op, lhs, rhs, tag) ->
    TmPrim2 (op, subst_metas_in_term x m lhs, subst_metas_in_term x m rhs, tag)
  | TmLiteral _ | TmVar _ | TmUniverse _ | TmPrimTy _ | TmMeta _ -> tm

let rec alpha_eq tm1 tm2 =
  match tm1, tm2 with
  | TmVar(x, _), TmVar(y, _) -> x = y
  | TmApp(a1, b1, app_boundary1, _), TmApp(a2, b2, app_boundary2, _) -> app_boundary1 = app_boundary2 && alpha_eq a1 a2 && alpha_eq b1 b2
  | TmLet(x1, a1, m1, _), TmLet(x2, a2, m2, _) when x1 = x2 ->
    alpha_eq a1 a2 && alpha_eq m1 m2
  | TmLambda(x1, a1, m1, call_type1, _), TmLambda(x2, a2, m2, call_type2, _) when x1 = x2 ->
    call_type1 = call_type2 && alpha_eq a1 a2 && alpha_eq m1 m2
  | TmPi(x1, a1, m1, call_type1, _), TmPi(x2, a2, m2, call_type2, _) when x1 = x2 ->
    call_type1 = call_type2 && alpha_eq a1 a2 && alpha_eq m1 m2
  | TmLet(x1, a1, m1, _), TmLet(x2, a2, m2, _) ->
    let banlist = all_vars m1 @ all_vars m2 in
    let fresh_x = freshen banlist x1 in
    alpha_eq (rename fresh_x tm1) (rename fresh_x tm2)
  | TmLambda(x1, a1, m1, _, _), TmLambda(x2, a2, m2, _, _) ->
    let banlist = all_vars m1 @ all_vars m2 in
    let fresh_x = freshen banlist x1 in
    alpha_eq (rename fresh_x tm1) (rename fresh_x tm2)
  | TmPi(x1, a1, m1, _, _), TmPi(x2, a2, m2, _, _) ->
    let banlist = all_vars m1 @ all_vars m2 in
    let fresh_x = freshen banlist x1 in
    alpha_eq (rename fresh_x tm1) (rename fresh_x tm2)
  | TmIf(cond1, thn1, els1, _), TmIf(cond2, thn2, els2, _) ->
    alpha_eq cond1 cond2 && alpha_eq thn1 thn2 && alpha_eq els1 els2
  | TmLiteral(l1, _), TmLiteral(l2, _) ->
    l1 = l2
  | TmUniverse(lvl1), TmUniverse(lvl2) -> lvl1 = lvl2
  | TmPrimTy(typ1, _), TmPrimTy(typ2, _) -> typ1 = typ2
  | TmPrim1(op1, body1, _), TmPrim1(op2, body2, _) ->
    op1 = op2 && alpha_eq body1 body2
  | TmPrim2(op1, lhs1, rhs1, _), TmPrim2(op2, lhs2, rhs2, _) ->
    op1 = op2 && alpha_eq lhs1 lhs2 && alpha_eq rhs1 rhs2
  | _, _ -> false

let prim2_int_op op l r suff = 
  match op with
  | Plus -> LitInt(Uint64.add l r, suff)
  | Minus -> LitInt(Uint64.sub l r, suff)
  | Times -> LitInt(Uint64.mul l r, suff)
  | Divide -> LitInt(Uint64.div l r, suff)
  | Greater -> LitBool(l > r)
  | GreaterEq -> LitBool(l >= r)
  | Less -> LitBool(l < r)
  | LessEq -> LitBool(l <= r)
  | _ -> ice (sprintf "Cannot perform op %s on integers" (string_of_op2 op))

let rec eval tm =
  match tm with
  | TmApp (m, n, app_boundary, tag) -> eval_app (reduce m) (reduce n) app_boundary tag
  | TmLet (x, a, m, tag) -> reduce (subst x a m)
  | TmLambda (x, a, m, call_type, tag) -> TmLambda (x, reduce a, reduce m, call_type, tag)
  | TmPi (x, a, m, call_type, tag) -> TmPi (x, reduce a, reduce m, call_type, tag)
  | TmIf (cond, thn, els, tag) -> 
    let reduced_cond = reduce cond in
    (
      match reduced_cond with
      | TmLiteral(LitBool(true), _) -> reduce thn
      | TmLiteral(LitBool(false), _) -> reduce els
      | _ -> TmIf(reduced_cond, reduce thn, reduce els, tag)
    )
  | TmPrim2 (Eq, lhs, rhs, tag) ->
    TmLiteral(LitBool(lhs = rhs), tag)
  | TmPrim2 (op, TmLiteral(LitInt(n1, suff1), _), TmLiteral(LitInt(n2, suff2), _), tag) when suff1 = suff2 ->
    TmLiteral(prim2_int_op op n1 n2 suff1, tag)
  | TmPrim2 (op, lhs, rhs, tag) -> (TmPrim2(op, reduce lhs, reduce rhs, tag))
  | TmPrim1 (Neg, TmLiteral(LitInt(n, suff), _), tag) ->
    TmLiteral(LitInt(Uint64.neg n, suff), tag)
  | TmPrim1 (Not, TmLiteral(LitBool(b), _), tag) ->
    TmLiteral(LitBool(not b), tag)
  | TmPrim1 (op, body, tag) -> (TmPrim1(op, reduce body, tag) )
  | TmLiteral _ | TmVar _ | TmUniverse _ | TmMeta _ | TmPrimTy _ -> tm

and eval_app m n app_boundary tag =
  match m with
  | TmLambda(x, a, body, _, tag) -> reduce (subst x n body)
  | _ -> TmApp (m, n, app_boundary, tag)

and reduce tm =
  let evaluated = eval tm in
  if evaluated = tm then 
    evaluated 
  else
    eval evaluated
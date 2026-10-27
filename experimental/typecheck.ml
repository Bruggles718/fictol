open Printf
open Errors
open Types
open Terms
open Exprs
open Compiler_common
open Pretty

let rec tm_free_vars tm =
  match tm with
  | TmVar (x, tag) -> [ x ]
  | TmApp (m, n, tag) -> tm_free_vars m @ tm_free_vars n
  | TmLambda (x, a, m, _, tag) | TmPi (x, a, m, _, tag) | TmLet (x, a, m, tag) -> tm_free_vars a @ List.filter (( <> ) x) (tm_free_vars m)
  | TmIf (cond, thn, els, tag) -> tm_free_vars cond @ tm_free_vars thn @ tm_free_vars els
  | TmPrim1 (op, body, tag) ->
    tm_free_vars body
  | TmPrim2 (op, lhs, rhs, tag) ->
    tm_free_vars lhs @ tm_free_vars rhs
  | TmUniverse _ | TmLiteral _ | TmPrimTy _ | TmMeta _ -> []

let rec binders tm =
  match tm with
  | TmApp (m, n, tag) -> binders m @ binders n
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
  | TmApp (m', n, tag) -> TmApp(subst x m m', subst x m n, tag)
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
  | TmApp (m', n, tag) -> TmApp(subst_metas_in_term x m m', subst_metas_in_term x m n, tag)
  | TmLet (y, a, n, tag) -> TmLet (y, subst x m a, n, tag)
  | TmLambda (y, a, n, call_type, tag) -> TmLambda (y, subst_metas_in_term x m a, subst_metas_in_term x m n, call_type, tag)
  | TmPi (y, a, n, call_type, tag) -> TmPi (y, subst_metas_in_term x m a, subst_metas_in_term x m n, call_type, tag)
  | TmIf (cond, thn, els, tag) -> TmIf (subst_metas_in_term x m cond, subst_metas_in_term x m thn, subst_metas_in_term x m els, tag)
  | TmPrim1 (op, body, tag) ->
    TmPrim1 (op, subst_metas_in_term x m body, tag)
  | TmPrim2 (op, lhs, rhs, tag) ->
    TmPrim2 (op, subst_metas_in_term x m lhs, subst_metas_in_term x m rhs, tag)
  | TmLiteral _ | TmVar _ | TmUniverse _ | TmPrimTy _ | TmMeta _ -> tm
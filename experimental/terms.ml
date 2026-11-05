open Types
open Exprs

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)
type 'a envt = 'a StringMap.t

type app_boundary =
  | Continue
  | End


type binder_info =
  {
    bi_call_type: call_type;
    bi_piinfo: piinfo;
    bi_app_boundary: app_boundary;
  }

type 'a term =
  | TmUniverse of int * 'a
  | TmPi of string * 'a term * 'a term * binder_info * 'a
  | TmLambda of string * 'a term * 'a term * binder_info * 'a
  | TmLet of string * 'a term * 'a term * 'a
  | TmApp of 'a term * 'a term * app_boundary * 'a
  | TmPrim1 of prim1 * 'a term * 'a
  | TmPrim2 of prim2 * 'a term * 'a term * 'a
  | TmIf of 'a term * 'a term * 'a term * 'a
  | TmLiteral of lit * 'a
  | TmPrimTy of typ * 'a
  | TmVar of string * 'a
  | TmMeta of string * unit term envt * 'a

and 'a term_method_impl =
  | TImplDecl of 'a term
  | TImplPrim1 of prim1 (* built-in instance: emit this primitive *)
  | TImplPrim2 of prim2

type 'a method_info =
  { m_name: string;
    m_typ: 'a term;
    (* a TyArrow that may mention the class parameters, e.g. for class Add with
     params ["Self"]: (Self, Self) -> Self *)
    m_has_default: bool }

type 'a class_info =
  { class_name: string;
    class_params: string list; (* ["Self"], or ["a"; "b"] for multi-param *)
    class_superclasses: 'a term list;
    (* over class_params, e.g. class Ord has [ {Eq; [Self]} ] *)
    class_methods: 'a method_info list;
    class_span: 'a }
(* Your commented-out class_info, tidied: methods are stored as
   (generics, type) and the FULL scheme is derived on demand by
   scheme_of_method. Only signatures live here; bodies stay in the AST (DClass)
   and in default_method_table. *)

type 'a instance_info =
  { instance_id: string;
    (* Unique name, e.g. "Add_i32" or "Show_Pair_1". Key into method_impl_table;
     basis for mangled names after monomorphisation. *)
    instance_vars: string list;
    (* Type variables bound by the instance; these are the PATTERN variables when
     matching a wanted predicate against instance_head. *)
    instance_head: 'a term;
    instance_context: 'a term list;
    (* the `T: Show` part of `impl<T: Show> Show for Pair<T>` *)
    instance_methods: string list;
    (* names of the methods this instance defines itself; the rest must have
     defaults in the class *)
    instance_span: 'a }

type 'a subst = (string * 'a) list

let rec tag_term (tag : 'a) (tm : 'b term) : 'a term =
  match tm with
  | TmUniverse (level, _) -> TmUniverse (level, tag)
  | TmPi (name, domain, codomain, binder_info, _) ->
      TmPi
        (name, tag_term tag domain, tag_term tag codomain, binder_info, tag)
  | TmLambda (name, domain, body, binder_info, _) ->
      TmLambda
        (name, tag_term tag domain, tag_term tag body, binder_info, tag)
  | TmLet (name, value, body, _) ->
      TmLet (name, tag_term tag value, tag_term tag body, tag)
  | TmApp (fn, arg, app_boundary, _) ->
      TmApp (tag_term tag fn, tag_term tag arg, app_boundary, tag)
  | TmPrim1 (op, arg, _) ->
      TmPrim1 (op, tag_term tag arg, tag)
  | TmPrim2 (op, lhs, rhs, _) ->
      TmPrim2 (op, tag_term tag lhs, tag_term tag rhs, tag)
  | TmIf (cond, then_branch, else_branch, _) ->
      TmIf
        (tag_term tag cond,
         tag_term tag then_branch,
         tag_term tag else_branch,
         tag)
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

let rec map_term (f : 'a term -> 'b term) (tm : 'a term) : 'b term =
  let tm' =
    match tm with
    | TmUniverse (level, tag) ->
        TmUniverse (level, tag)
    | TmPi (name, domain, codomain, binder_info, tag) ->
        TmPi (name, map_term f domain, map_term f codomain, binder_info, tag)
    | TmLambda (name, domain, body, binder_info, tag) ->
        TmLambda (name, map_term f domain, map_term f body, binder_info, tag)
    | TmLet (name, value, body, tag) ->
        TmLet (name, map_term f value, map_term f body, tag)
    | TmApp (fn, arg, app_boundary, tag) ->
        TmApp (map_term f fn, map_term f arg, app_boundary, tag)
    | TmPrim1 (op, arg, tag) ->
        TmPrim1 (op, map_term f arg, tag)
    | TmPrim2 (op, lhs, rhs, tag) ->
        TmPrim2 (op, map_term f lhs, map_term f rhs, tag)
    | TmIf (cond, then_branch, else_branch, tag) ->
        TmIf
          (map_term f cond, map_term f then_branch, map_term f else_branch, tag)
    | TmLiteral (lit, tag) ->
        TmLiteral (lit, tag)
    | TmPrimTy (typ, tag) ->
        TmPrimTy (typ, tag)
    | TmVar (name, tag) ->
        TmVar (name, tag)
    | TmMeta (name, context, tag) ->
        TmMeta (name, context, tag)
  in
  f tm'
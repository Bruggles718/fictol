open Types
open Exprs

module StringSet = Set.Make (String)

type app_boundary =
  | Continue
  | End


type binder_info =
  {
    bi_call_type: call_type;
    bi_piinfo: piinfo;
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
  | TmMeta of string * StringSet.t * 'a

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
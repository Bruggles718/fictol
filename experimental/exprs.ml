open Stdint
open Types

type sourcespan = Lexing.position * Lexing.position

type tag = int

type prim1 =
  | Not
  | Neg
  | Deref
  | Ref

type prim2 =
  | Plus
  | Minus
  | Times
  | Divide
  | And
  | Or
  | Greater
  | GreaterEq
  | Less
  | LessEq
  | Eq

and 'a bind =
  | BBlank of 'a
  | BName of string * 'a expr option * 'a

and piinfo =
  | Implicit
  | Explicit
  | Auto

and 'a fun_param =
  | FPName of string * 'a expr * piinfo * 'a

and 'a binding = 'a bind * 'a expr * 'a

and int_suffix =
  | IntSuffix of signed_int_width
  | UIntSuffix of unsigned_int_width

and lit =
  | LitInt of uint64 * int_suffix
  | LitString of string
  | LitChar of char
  (* | Float of float * 'a *)
  | LitBool of bool

and 'a expr =
  | ESeq of 'a expr * 'a expr * 'a
  (* | ETuple of 'a expr list * 'a
  | EGetItem of 'a expr * 'a expr * 'a
  | ESetItem of 'a expr * 'a expr * 'a expr * 'a *)
  | ELet of 'a binding list * 'a expr * 'a
  | EPrim1 of prim1 * 'a expr * 'a
  | EPrim2 of prim2 * 'a expr * 'a expr * 'a
  | EIf of 'a expr * 'a expr * 'a expr * 'a
  | ELiteral of lit * 'a
  (* | ENil of 'a *)
  | EId of string * 'a
  | EApp of 'a expr * 'a expr list * 'a
  (* | ELambda of 'a bind list * 'a expr * 'a *)
  (* | ELetRec of 'a binding list * 'a expr * 'a *)
  (* | EString of string * 'a *)
  (* | ETyApp of 'a expr * typ list * 'a *)
  | EBorrow of 'a expr * string * string * 'a expr * 'a
    (* expr to borrow, name to bind it as, name of region, body, tag *)

(* and 'a method_sig =
  { ms_name: string;
    ms_generics: 'a generic_bind list;
    ms_args: 'a bind list;
    ms_ret: typ;
    ms_default: 'a expr option; (* Some body when the class gives a default *)
    ms_span: 'a } *)

and 'a fun_sig =
  {
    fname: string;
    fparams: 'a fun_param list;
    fbody: 'a expr option;
    fcall_type: call_type;
    fret_type: 'a expr;
    ftag: 'a;
  }

type 'a decl =
  | DFun of 'a fun_sig
  | DClass of string * string list * 'a expr list * 'a fun_sig list * 'a
  | DInstance of 'a fun_param list * 'a expr * 'a method_impl list * 'a

and 'a method_impl =
  | ImplDecl of 'a decl (* checked + elaborated user-written DFun *)
  | ImplPrim1 of prim1 (* built-in instance: emit this primitive *)
  | ImplPrim2 of prim2

type 'a program = Program of 'a decl list * 'a

(* I need to investigate a bit more and determine what method_info should actually contain under dependent types *)
(* Also, should all of this have terms instead of exprs? needs more thought as well. *)

(* type 'a method_info =
  { m_name: string;
    m_generics: 'a generic_bind list;
    (* the method's OWN type parameters and bounds (beyond the class's) *)
    m_typ: typ;
    (* a TyArrow that may mention the class parameters, e.g. for class Add with
     params ["Self"]: (Self, Self) -> Self *)
    m_has_default: bool }

type 'a class_info =
  { class_name: string;
    class_params: string list; (* ["Self"], or ["a"; "b"] for multi-param *)
    class_superclasses: 'a expr list;
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
    instance_head: 'a expr;
    instance_context: 'a expr list;
    (* the `T: Show` part of `impl<T: Show> Show for Pair<T>` *)
    instance_methods: string list;
    (* names of the methods this instance defines itself; the rest must have
     defaults in the class *)
    instance_span: 'a } *)

(* type 'a immexpr =
  (* immediate expressions *)
  | ImmLiteral of lit * 'a
  | ImmId of string * 'a
(* | ImmNil of 'a *)

and 'a abind = string * 'a

and 'a cexpr =
  (* compound expressions *)
  | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
  | CPrim1 of prim1 * 'a immexpr * 'a
  | CPrim2 of prim2 * 'a immexpr * 'a immexpr * 'a
  | CApp of 'a immexpr * 'a immexpr list * 'a
  | CImmExpr of 'a immexpr
(* for when you just need an immediate value *)
(* | CTuple of 'a immexpr list * 'a
  | CGetItem of 'a immexpr * 'a immexpr * 'a
  | CSetItem of 'a immexpr * 'a immexpr * 'a immexpr * 'a
  | CLambda of string list * 'a aexpr * 'a *)

and 'a aexpr =
  (* anf expressions *)
  | ASeq of 'a cexpr * 'a aexpr * 'a
  | ALet of string * 'a cexpr * 'a aexpr * 'a
  (* | ALetRec of (string * 'a cexpr) list * 'a aexpr * 'a *)
  | ACExpr of 'a cexpr

and 'a adecl = AFun of string * 'a abind list * 'a aexpr option * call_type * typ * 'a

and 'a aprogram = AProgram of 'a adecl list * 'a *)

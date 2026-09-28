open Stdint
open Types

type tag = int

type sourcespan = Lexing.position * Lexing.position

type prim1 =
  | Add1
  | Sub1
  | Print
  | Not
  | PrintStack
  | Neg

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
  | CheckSize

and 'a bind =
  | BBlank of 'a
  | BName of string * bool * 'a typ * 'a
  (* | BTuple of 'a bind list * 'a *)

and 'a binding = 'a bind * 'a expr * 'a

and call_type =
  | Extern of string
  | FictolFunc
  | FictolClosure
  | Unknown

and int_suffix =
  | IntSuffix of signed_int_width

and lit = 
  | LitInt of uint128 * int_suffix
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
  | EApp of 'a expr * 'a expr list * call_type * 'a
  (* | ELambda of 'a bind list * 'a expr * 'a *)
  (* | ELetRec of 'a binding list * 'a expr * 'a *)
  (* | EString of string * 'a *)

type 'a decl =
  | DFun of string * 'a bind list * 'a expr * call_type * 'a typ * 'a

type 'a program = Program of 'a decl list * 'a

(* type 'a immexpr =
  (* immediate expressions *)
  | ImmInt32 of int32 * 'a
  | ImmBool of bool * 'a
  | ImmId of string * 'a
  (* | ImmNil of 'a *)

and 'a cexpr =
  (* compound expressions *)
  | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
  | CPrim1 of prim1 * 'a immexpr * 'a
  | CPrim2 of prim2 * 'a immexpr * 'a immexpr * 'a
  | CApp of 'a immexpr * 'a immexpr list * call_type * 'a
  | CImmExpr of 'a immexpr (* for when you just need an immediate value *)
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

and 'a adecl =
  | AFun of string * 'a bind list * 'a aexpr * 'a *)

(* and 'a aprogram = AProgram of 'a adecl list * 'a *)
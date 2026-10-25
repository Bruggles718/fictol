open Types
open Exprs

type 'a term =
  | TmUniverse of int
  | TmPi of string * 'a term * 'a term * call_type * 'a
  | TmLambda of string * 'a term * 'a term * call_type * 'a
  | TmLet of string * 'a term * 'a term * 'a
  | TmApp of 'a term * 'a term * 'a
  | TmPrim1 of prim1 * 'a term * 'a
  | TmPrim2 of prim2 * 'a term * 'a term * 'a
  | TmIf of 'a term * 'a term * 'a term * 'a
  | TmLiteral of lit * 'a
  | TmPrimTy of typ * 'a
  | TmVar of string * 'a
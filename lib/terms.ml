open Types
open Exprs

type 'a term =
  | TmUniverse of int
  | TmPi of string * 'a term * 'a tmpredicate list * 'a term * call_type * 'a
  | TmLambda of string * 'a term * 'a term * call_type * 'a
  | TmApp of 'a term * 'a term * 'a
  | TmSeq of 'a term * 'a term * 'a
  | TmLet of string * 'a term * 'a term * 'a
  | TmPrim1 of prim1 * 'a term * 'a
  | TmPrim2 of prim2 * 'a term * 'a term * 'a
  | TmIf of 'a term * 'a term * 'a term * 'a
  | TmLiteral of lit * 'a
  | TmVar of string * 'a
  | TmGetReference of 'a term * 'a

and 'a tmpredicate =
  { pred_class: string;
    pred_args: 'a term list }

and 'a tmwanted =
  { w_pred: 'a tmpredicate;
    w_span: 'a (* where the constraint came from, for error messages *) }
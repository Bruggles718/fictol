open Types
open Exprs

(* I think this needs to be extended to have prims again, but not lets.
I also need metavariables. I also think I need a way to distinguish between
regular arguments and implicit arguments. *)
type 'a term =
  | TmUniverse of int
  | TmPi of string * 'a term * 'a tmpredicate list * 'a term * call_type * 'a
  | TmLambda of string * 'a term * 'a term * call_type * 'a
  | TmThunk of 'a term * call_type * 'a
  | TmApp of 'a term * 'a term * 'a
  | TmIf of 'a term * 'a term * 'a term * 'a
  | TmLiteral of lit * 'a
  | TmVar of string * 'a

and 'a tmpredicate =
  { pred_class: string;
    pred_args: 'a term list }

and 'a tmwanted =
  { w_pred: 'a tmpredicate;
    w_span: 'a (* where the constraint came from, for error messages *) }

and 'a tmprogram = TmProgram of 'a term list
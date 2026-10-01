open Printf
open Exprs
open Pretty
open Stdint

(* TODO: Define any additional exceptions you want *)
exception ParseError of string (* parse-error message *)

exception UnboundId of string * sourcespan (* name, where used *)

exception UnboundFun of string * sourcespan (* name of fun, where used *)

exception DuplicateId of string * sourcespan * sourcespan (* name, where used, where defined *)

exception DuplicateFun of string * sourcespan * sourcespan (* name, where used, where defined *)

(* value, where used *)
exception Overflow of int128 * sourcespan

exception Arity of int * int * sourcespan (* intended arity, actual arity, where called *)

exception NotYetImplemented of string (* TODO: Message to show *)

exception Unsupported of string * sourcespan

exception InternalCompilerError of string (* Major failure: message to show *)

exception NoTypeAnnotation of string * sourcespan

exception CannotInferType of string

exception InconsistentType of string

(* name binding, where defined *)
(* exception LetRecNonFunction of sourcespan bind * sourcespan  *)

(* name, where defined, actual typ *)
(* exception ShouldBeFunction of string * sourcespan  *)

exception
  DeclArity of string * int * int * sourcespan (* name, num args, num types, where defined *)

let known_compiletime_exn exn =
  match exn with
  | ParseError _
   |NotYetImplemented _
   |InternalCompilerError _
   |Overflow _
   |UnboundId _
   |UnboundFun _
   |DuplicateId _
   |DuplicateFun _
   |Unsupported _
   |CannotInferType _
   |InconsistentType _
   |NoTypeAnnotation _
   |Arity _ -> true
  | _ -> false
;;

let print_error exn =
  match exn with
  | ParseError msg -> msg
  | NotYetImplemented msg -> "Not yet implemented: " ^ msg
  | Unsupported (msg, loc) -> sprintf "Unsupported: %s at <%s>" msg (string_of_sourcespan loc)
  | InternalCompilerError msg -> "Internal Compiler Error: " ^ msg
  | UnboundId (x, loc) ->
      sprintf "The identifier %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
  | UnboundFun (x, loc) ->
      sprintf "The function name %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
  | DuplicateId (x, loc, existing) ->
      sprintf "The identifier %s, redefined at <%s>, duplicates one at <%s>" x
        (string_of_sourcespan loc) (string_of_sourcespan existing)
  | DuplicateFun (x, loc, existing) ->
      sprintf "The function name %s, redefined at <%s>, duplicates one at <%s>" x
        (string_of_sourcespan loc) (string_of_sourcespan existing)
  | Overflow (num, loc) ->
      sprintf "The number literal %s, used at <%s>, is not supported in this language"
        (Int128.to_string num) (string_of_sourcespan loc)
  | Arity (expected, actual, loc) ->
      sprintf "The function called at <%s> expected an arity of %d, but received %d arguments"
        (string_of_sourcespan loc) expected actual
  | DeclArity (name, num_args, num_types, loc) ->
      sprintf "The function %s, defined at %s, has %d arguments but only %d types provided" name
        (string_of_sourcespan loc) num_args num_types
  | CannotInferType msg -> "Cannot infer type: " ^ msg
  | InconsistentType msg -> "Inconsistent type: " ^ msg
  | NoTypeAnnotation (x, loc) ->
      sprintf "Type annotation required for %s at <%s>" x (string_of_sourcespan loc)
  | _ -> sprintf "%s" (Printexc.to_string exn)
;;

(* Stringifies a list of compilation errors *)
let print_errors (exns : exn list) : string list = List.map print_error exns

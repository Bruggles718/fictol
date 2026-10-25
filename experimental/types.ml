type sourcespan = Lexing.position * Lexing.position

type call_type =
  | Extern of string
  | FictolFunc
  | FictolClosure
  | Prim
  | Unknown

type signed_int_width =
  | I8
  | I16
  | I32
  | I64

type unsigned_int_width =
  | U8
  | U16
  | U32
  | U64

type typ =
  | Int of signed_int_width
  | UInt of unsigned_int_width
  | Bool
  | Char
  | Region
  | Unit

(* type 'a predicate =
  { pred_class: string;
    pred_args: typ list }
(* UNCHANGED, but now actually used. `Add i32` is
   { pred_class = "Add"; pred_args = [TyCon (Int I32)] }.
   This replaces your `TyApp(TyVar "Add", [TyVar t])` encoding. *)

type 'a generic_bind = GBName of string * 'a predicate list * 'a
(* CHANGED: the middle field used to be `typ list`. Each bound is now a full
   predicate whose FIRST argument is the generic itself:
       fun f<T: Add + Eq>(..)
         ==> GBName("T", [ {Add;[T]}; {Eq;[T]} ], tag)
   (T written as TyPath(["T"], tag) by the parser, turned into TyVar by
   resolve_prog_typ_paths). Multi-parameter bounds put extra arguments after T. *)

type 'a scheme = SForall of string list * 'a predicate list * typ
(* CHANGED: the context is `'a predicate list` instead of `typ list`. *)

type 'a subst = (string * 'a) list

type 'a wanted =
  { w_pred: 'a predicate;
    w_span: 'a (* where the constraint came from, for error messages *) }
(* NEW. A predicate the type checker still has to justify, tagged with the
   source location that generated it ("no instance Add bool at line 7"). *)

 *)

(* let rec untagTyp t =
  match t with
  | TyVar name -> TyVar name
  | TyCon name -> TyCon name
  | TyArrow (args, ret_type) -> TyArrow (List.map untagTyp args, untagTyp ret_type)
  | TyBlank _ -> TyBlank ()
  | TyApp (generic_type, generic_param_types) ->
      TyApp (untagTyp generic_type, List.map untagTyp generic_param_types)
  | TyPath (path, _) -> TyPath (path, ())
;; *)

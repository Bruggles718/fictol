type signed_int_width =
  | I8
  | I16
  | I32
  | I64
  | I128

type tykind =
  | Int of signed_int_width
  | Bool
  | Skolem of string
(* NEW. A rigid type constant standing for a generic parameter while that
     function's body is being checked. `Skolem "T"` unifies only with
     `Skolem "T"`. Because your unify already says "TyCon a ~ TyCon b iff
     a = b", skolems need NO new unify code. Using the generic's own name
     (not a gensym) makes it trivial to turn a skolem back into `TyVar "T"`
     afterwards (see unskolemize_typ). Add a case for it wherever you match on
     tykind (pretty printer, codegen). *)

type 'a typ =
  | TyVar of string
  | TyCon of tykind
  | TyArrow of 'a typ list * 'a typ
  | TyBlank of 'a
  | TyApp of 'a typ * 'a typ list
  | TyPath of string list * 'a

type 'a predicate =
  { pred_class: string;
    pred_args: 'a typ list }
(* UNCHANGED, but now actually used. `Add i32` is
   { pred_class = "Add"; pred_args = [TyCon (Int I32)] }.
   This replaces your `TyApp(TyVar "Add", [TyVar t])` encoding. *)

type 'a generic_bind = GBName of string * 'a predicate list * 'a
(* CHANGED: the middle field used to be `'a typ list`. Each bound is now a full
   predicate whose FIRST argument is the generic itself:
       fun f<T: Add + Eq>(..)
         ==> GBName("T", [ {Add;[T]}; {Eq;[T]} ], tag)
   (T written as TyPath(["T"], tag) by the parser, turned into TyVar by
   resolve_prog_typ_paths). Multi-parameter bounds put extra arguments after T. *)

type 'a scheme = SForall of string list * 'a predicate list * 'a typ
(* CHANGED: the context is `'a predicate list` instead of `'a typ list`. *)

type 'a subst = (string * 'a) list

type 'a wanted =
  { w_pred: 'a predicate;
    w_span: 'a (* where the constraint came from, for error messages *) }
(* NEW. A predicate the type checker still has to justify, tagged with the
   source location that generated it ("no instance Add bool at line 7"). *)

type 'a method_info =
  { m_name: string;
    m_generics: 'a generic_bind list;
    (* the method's OWN type parameters and bounds (beyond the class's) *)
    m_typ: 'a typ;
    (* a TyArrow that may mention the class parameters, e.g. for class Add with
     params ["Self"]: (Self, Self) -> Self *)
    m_has_default: bool }

type 'a class_info =
  { class_name: string;
    class_params: string list; (* ["Self"], or ["a"; "b"] for multi-param *)
    class_superclasses: 'a predicate list;
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
    instance_head: 'a predicate;
    instance_context: 'a predicate list;
    (* the `T: Show` part of `impl<T: Show> Show for Pair<T>` *)
    instance_methods: string list;
    (* names of the methods this instance defines itself; the rest must have
     defaults in the class *)
    instance_span: 'a }

let rec untagTyp t =
  match t with
  | TyVar name -> TyVar name
  | TyCon name -> TyCon name
  | TyArrow (args, ret_type) -> TyArrow (List.map untagTyp args, untagTyp ret_type)
  | TyBlank _ -> TyBlank ()
  | TyApp (generic_type, generic_param_types) ->
      TyApp (untagTyp generic_type, List.map untagTyp generic_param_types)
  | TyPath (path, _) -> TyPath (path, ())
;;

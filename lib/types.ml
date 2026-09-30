type signed_int_width =
  | I8
  | I16
  | I32
  | I64
  | I128

type tykind =
  | Int of signed_int_width
  | Bool

type 'a typ =
  | TyVar of string * 'a
  | TyCon of tykind * 'a
  | TyArrow of 'a typ list * 'a typ * 'a
  | TyBlank of 'a
  | TyApp of 'a typ * 'a typ list * 'a
  | TyPath of string list * 'a

type 'a predicate = {
  pred_class : string;
  pred_args : 'a typ list;
}

type 'a generic_bind =
  | GBName of string * 'a predicate list * 'a

type 'a class_info = {
  class_name: string;
  class_params: 'a generic_bind list;
  class_superclasses : 'a predicate list;
  class_methods : (string * 'a generic_bind list * 'a typ) list;  (* method name -> signature, mentioning TyVar "Self" *)
}

type 'a instance_info = {
  (* include instance_id? *)

  instance_head : 'a predicate;
  instance_context: 'a predicate list;
  (* instance_methods: (string * 'a typ) list; *)
}

type 'a scheme =
  | SForall of string list * 'a predicate list * 'a typ * 'a

type 'a subst = (string * 'a) list
let rec untagTyp t =
  match t with
  | TyVar (name, _) -> TyVar(name, ())
  | TyCon (name,_) -> TyCon(name, ())
  | TyArrow (args, ret_type, _) -> TyArrow(List.map untagTyp args, untagTyp ret_type, ())
  | TyBlank(_) -> TyBlank(())
  | TyApp (generic_type, generic_param_types, _) -> TyApp(untagTyp generic_type, List.map untagTyp generic_param_types, ())
  | TyPath (path, _) -> TyPath(path, ())
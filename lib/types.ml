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
  | TyCon of string * 'a
  | TyArrow of 'a typ list * 'a typ * 'a
  | TyBlank of 'a
  | TyApp of 'a typ * 'a typ list * 'a

type 'a scheme =
  | SForall of string list * 'a typ * 'a

type 'a subst = (string * 'a) list
let rec untagTyp t =
  match t with
  | TyVar (name, _) -> TyVar(name, ())
  | TyCon (name,_) -> TyCon(name, ())
  | TyArrow (args, ret_type, _) -> TyArrow(List.map untagTyp args, untagTyp ret_type, ())
  | TyBlank(_) -> TyBlank(())
  | TyApp (generic_type, generic_param_types, _) -> TyApp(untagTyp generic_type, List.map untagTyp generic_param_types, ())
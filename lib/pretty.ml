open Exprs
open Format
open Lexing
open Stdint

let string_of_sourcespan ((pstart, pend) : sourcespan) : string =
  sprintf "%s, %d:%d-%d:%d" pstart.pos_fname pstart.pos_lnum
    (pstart.pos_cnum - pstart.pos_bol)
    pend.pos_lnum (pend.pos_cnum - pend.pos_bol)
;;

let string_of_position (p : position) : string =
  sprintf "%s:line %d, col %d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)
;;

let rec intersperse (elts : 'a list) (sep : 'a) : 'a list =
  match elts with
  | [] -> []
  | [elt] -> [elt]
  | elt :: rest -> elt :: sep :: intersperse rest sep
;;

let string_of_op1 op =
  match op with
  | Add1 -> "add1"
  | Sub1 -> "sub1"
  | Print -> "print"
  | PrintStack -> "printStack"
  | Not -> "!"
;;

let name_of_op1 op =
  match op with
  | Add1 -> "Add1"
  | Sub1 -> "Sub1"
  | Print -> "Print"
  | PrintStack -> "PrintStack"
  | Not -> "Not"
;;

let string_of_op2 op =
  match op with
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Divide -> "/"
  | And -> "&&"
  | Or -> "||"
  | Greater -> ">"
  | Less -> "<"
  | GreaterEq -> ">="
  | LessEq -> "<="
  | Eq -> "=="
  | CheckSize -> "check_size"
;;

let name_of_op2 op =
  match op with
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Times -> "Times"
  | Divide -> "Divide"
  | And -> "And"
  | Or -> "Or"
  | Greater -> "Greater"
  | Less -> "Less"
  | GreaterEq -> "GreaterEq"
  | LessEq -> "LessEq"
  | Eq -> "Eq"
  | CheckSize -> "CheckSize"
;;

let rec string_of_typ (t: 'a typ) : string =
  match t with
  | TyVar(name, _) | TyCon(name, _) -> name
  | TyArrow(ty_lst, ret_ty) -> "(" ^ ExtString.String.join ", " (List.map string_of_typ ty_lst) ^ ") -> " ^ (string_of_typ ret_ty)
  | TyBlank _ -> ""
  | TyApp(generic_ty, generic_param_ty_lst) ->
      (string_of_typ generic_ty) ^ 
      "<" ^ ExtString.String.join ", " (List.map string_of_typ generic_param_ty_lst) ^ ">"

let rec string_of_bind (b : 'a bind) : string =
  match b with
  | BBlank _ -> "_"
  | BName (name, allow_shadow, typ, _) ->
      ( if allow_shadow then
          "shadow "
        else
          "" )
      ^ name ^ ":" ^ (string_of_typ typ)
  (* | BTuple (binds, _) -> "(" ^ ExtString.String.join ", " (List.map string_of_bind binds) ^ ")" *)
;;

let string_of_call_type ct =
  match ct with
  | Extern(lang) -> sprintf "*'%s'" lang
  | FictolFunc -> ""
  | FictolClosure -> "#"
  | Unknown -> "?"
;;

let rec string_of_binding_with (depth : int) (print_a : 'a -> string) ((bind, expr, _) : 'a binding)
    : string =
  sprintf "%s = %s" (string_of_bind bind) (string_of_expr_with depth print_a expr)

and string_of_binding (b : 'a binding) : string = string_of_binding_with 1000 (fun _ -> "") b

and string_of_expr_with (depth : int) (print_a : 'a -> string) (e : 'a expr) : string =
  let string_of_expr = string_of_expr_with (depth - 1) print_a in
  if depth <= 0 then
    "..."
  else
    match e with
    | ESeq (e1, e2, a) -> string_of_expr e1 ^ "; " ^ string_of_expr e2
    (* | ETuple ([e], a) -> "(" ^ string_of_expr e ^ ",)" ^ print_a a
    | ETuple (exprs, a) -> "(" ^ ExtString.String.join ", " (List.map string_of_expr exprs) ^ ")"
    | EGetItem (e, idx, a) -> sprintf "%s[%s]%s" (string_of_expr e) (string_of_expr idx) (print_a a)
    | ESetItem (e, idx, newval, a) ->
        sprintf "%s[%s] := %s %s" (string_of_expr e) (string_of_expr idx) (string_of_expr newval)
          (print_a a)
    | ENumber (n, a) -> Int64.to_string n ^ print_a a
    | EBool (b, a) -> string_of_bool b ^ print_a a
    | ENil a -> "nil " ^ print_a a *)
    | ELiteral(LitInt(n), a) -> Uint128.to_string n ^ print_a a
    | ELiteral(LitBool(b), a) -> string_of_bool b ^ print_a a
    | EId (x, a) -> x ^ print_a a
    | EPrim1 (op, e, a) -> sprintf "%s(%s)%s" (string_of_op1 op) (string_of_expr e) (print_a a)
    | EPrim2 (op, left, right, a) ->
        sprintf "(%s %s %s)%s" (string_of_expr left) (string_of_op2 op) (string_of_expr right)
          (print_a a)
    | ELet (binds, body, a) ->
        let binds_strs = List.map (string_of_binding_with (depth - 1) print_a) binds in
        let binds_str = List.fold_left ( ^ ) "" (intersperse binds_strs ", ") in
        sprintf "(let %s in %s)%s" binds_str (string_of_expr body) (print_a a)
    | EIf (cond, thn, els, a) ->
        sprintf "(if %s: %s else: %s)%s" (string_of_expr cond) (string_of_expr thn)
          (string_of_expr els) (print_a a)
    | EApp (func, args, call_type, a) ->
        sprintf "(%s%s(%s))%s" (string_of_call_type call_type) (string_of_expr func)
          (ExtString.String.join ", " (List.map string_of_expr args))
          (print_a a)
    (* | ELetRec (binds, body, a) ->
        let binds_strs = List.map (string_of_binding_with (depth - 1) print_a) binds in
        let binds_str = List.fold_left ( ^ ) "" (intersperse binds_strs ", ") in
        sprintf "(let-rec %s in %s)%s" binds_str (string_of_expr body) (print_a a)
    | ELambda (binds, body, a) ->
        let binds_strs = List.map string_of_bind binds in
        let binds_str = List.fold_left ( ^ ) "" (intersperse binds_strs ", ") in
        sprintf "(lam(%s) %s)%s" binds_str (string_of_expr body) (print_a a)
    | EGetField (obj, field_name, a) ->
        sprintf "%s.%s %s" (string_of_expr obj) field_name (print_a a)
    | ESetField (obj, field_name, new_val, a) ->
        sprintf "%s.%s := %s %s" (string_of_expr obj) field_name (string_of_expr new_val)
          (print_a a)
    | EMethodApp (obj, method_name, args, a) ->
        sprintf "(%s.%s(%s))%s" (string_of_expr obj) method_name
          (ExtString.String.join ", " (List.map string_of_expr args))
          (print_a a)
    | EString (s, a) -> sprintf "\"%s\"%s" s (print_a a) *)
;;

let string_of_expr (e : 'a expr) : string = string_of_expr_with 1000 (fun _ -> "") e

let rec string_of_decl_with (depth : int) (print_a : 'a -> string) (d : 'a decl) : string =
  match d with
  | DFun (name, args, body, call_type, typ, a) ->
      sprintf "(def %s(%s)%s:\n  %s)%s" name
        (ExtString.String.join ", " (List.map string_of_bind args))
        (let typ_str = (string_of_typ typ) in
        if (String.length typ_str) <= 0 then "" else " -> " ^ typ_str)
        (string_of_expr_with (depth - 1) print_a body)
        (print_a a)
;;

let string_of_decl (d : 'a decl) : string = string_of_decl_with 1000 (fun _ -> "") d

let string_of_program_with (depth : int) (print_a : 'a -> string) (p : 'a program) : string =
  match p with
  | Program (decls, a) ->
      ExtString.String.join "\n" (List.map (string_of_decl_with depth print_a) decls)
      ^ "\n"
      ^ print_a a
;;

let string_of_program (p : 'a program) : string = string_of_program_with 1000 (fun _ -> "") p
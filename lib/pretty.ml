open Exprs
open Types
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
  | Neg -> "-"
;;

let name_of_op1 op =
  match op with
  | Add1 -> "Add1"
  | Sub1 -> "Sub1"
  | Print -> "Print"
  | PrintStack -> "PrintStack"
  | Not -> "Not"
  | Neg -> "Neg"
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

let rec string_of_tykind (t : tykind) =
  match t with
  | Region -> "region"
  | RegionName name -> name
  | Reference -> "ref"
  | Bool -> "bool"
  | Char -> "char"
  | Skolem s -> "Skolem(" ^ s ^ ")"
  | Int w -> (
    match w with
    | I8 -> "i8"
    | I16 -> "i16"
    | I32 -> "i32"
    | I64 -> "i64" )
  | UInt w -> (
    match w with
    | U8 -> "u8"
    | U16 -> "u16"
    | U32 -> "u32"
    | U64 -> "u64" )
;;

let rec string_of_typ (t : typ) : string =
  match t with
  | TyVar name -> name
  | TyCon tykind -> string_of_tykind tykind
  | TyArrow (ty_lst, ret_ty, call_type) ->
      "("
      ^ ExtString.String.join ", " (List.map string_of_typ ty_lst)
      ^ ") -> "
      ^ string_of_typ ret_ty
  | TyBlank _ -> "blank"
  | TyApp (generic_ty, generic_param_ty_lst) ->
      string_of_typ generic_ty
      ^ "<"
      ^ ExtString.String.join ", " (List.map string_of_typ generic_param_ty_lst)
      ^ ">"
  | TyPath (path, _) -> "path:" ^ ExtString.String.join "::" path
;;

let rec string_of_bind (b : 'a bind) : string =
  match b with
  | BBlank _ -> "_"
  | BName (name, allow_shadow, typ, _) ->
      ( if allow_shadow then
          "shadow "
        else
          "" )
      ^ name
      ^ ":"
      ^ string_of_typ typ
;;

(* | BTuple (binds, _) -> "(" ^ ExtString.String.join ", " (List.map string_of_bind binds) ^ ")" *)

let string_of_pred pred =
  sprintf "%s<%s>" pred.pred_class
    (ExtString.String.join ", " (List.map string_of_typ pred.pred_args))
;;

let rec string_of_generic_bind (b : 'a generic_bind) : string =
  match b with
  | GBName (name, bounds, tag) ->
      let colon =
        if List.length bounds > 0 then
          ":"
        else
          ""
      in
      name ^ colon ^ ExtString.String.join "+" (List.map string_of_pred bounds)
;;

let string_of_call_type ct =
  match ct with
  | Extern lang -> sprintf "*'%s'" lang
  | FictolFunc -> ""
  | FictolClosure -> "#"
  | Unknown -> "?"
  | Prim -> "p"
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
    | ELiteral (LitString (s), a) -> s ^ (print_a a)
    | ELiteral (LitChar (c), a) -> (String.of_char c) ^ (print_a a)
    | ELiteral (LitInt (n, suff), a) -> Uint64.to_string n ^ print_a a
    | ELiteral (LitBool b, a) -> string_of_bool b ^ print_a a
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
    | EApp (func, args, a) ->
        sprintf "(%s(%s))%s" (string_of_expr func)
          (ExtString.String.join ", " (List.map string_of_expr args))
          (print_a a)
    | ETyApp (e, typs, a) -> string_of_expr e
    | EBorrow (borrowed_expr, ref_name, region, body, a) ->
        sprintf "(borrow %s as %s for %s in %s)%s" (string_of_expr borrowed_expr) ref_name region
          (string_of_expr body) (print_a a)
    | EGetReference (body, a) -> sprintf "(reference of %s)%s" (string_of_expr body) (print_a a)
;;

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

let string_of_expr (e : 'a expr) : string = string_of_expr_with 1000 (fun _ -> "") e

let string_of_func_sig_with depth print_a name generics args (body : 'a expr option) call_type typ a
    =
  sprintf "(def %s%s(%s)%s%s)%s" name
    (let gens = ExtString.String.join ", " (List.map string_of_generic_bind generics) in
     if List.length generics > 0 then
       "<" ^ gens ^ ">"
     else
       gens )
    (ExtString.String.join ", " (List.map string_of_bind args))
    (let typ_str = string_of_typ typ in
     if String.length typ_str <= 0 then
       ""
     else
       " -> " ^ typ_str )
    ( match body with
    | Some body -> ":\n  " ^ string_of_expr_with (depth - 1) print_a body
    | None -> ";" )
    (print_a a)
;;

let rec string_of_impl_decl_with depth print_a impl_d =
  match impl_d with
  | ImplDecl decl -> string_of_decl_with depth print_a decl
  | ImplPrim1 op -> string_of_op1 op
  | ImplPrim2 op -> string_of_op2 op

and string_of_decl_with (depth : int) (print_a : 'a -> string) (d : 'a decl) : string =
  match d with
  | DFun (name, generics, args, body, call_type, typ, a) ->
      string_of_func_sig_with depth print_a name generics args (Some body) call_type typ a
  | DClass (name, params, superclasses, method_sigs, a) ->
      sprintf "(typeclass %s%s%s:\n  %s)%s" name
        (let gens = ExtString.String.join ", " params in
         if List.length params > 0 then
           "<" ^ gens ^ ">"
         else
           gens )
        (let superclasses_str =
           ExtString.String.join " + " (List.map string_of_pred superclasses)
         in
         if List.length superclasses > 0 then
           " extends " ^ superclasses_str
         else
           "" )
        (ExtString.String.join "\n  "
           (List.map
              (fun ms ->
                string_of_func_sig_with depth print_a ms.ms_name ms.ms_generics ms.ms_args
                  ms.ms_default FictolFunc ms.ms_ret ms.ms_span )
              method_sigs ) )
        (print_a a)
  | DInstance (generics, head, method_impls, a) ->
      sprintf "(instance%s %s:\n  %s)%s"
        (let gens = ExtString.String.join ", " (List.map string_of_generic_bind generics) in
         if List.length generics > 0 then
           "<" ^ gens ^ ">"
         else
           gens )
        (string_of_pred head)
        (ExtString.String.join "\n  "
           (List.map (string_of_impl_decl_with depth print_a) method_impls) )
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

let rec string_of_aexpr_with (depth : int) (print_a : 'a -> string) (e : 'a aexpr) : string =
  let string_of_aexpr = string_of_aexpr_with (depth - 1) print_a in
  let string_of_cexpr = string_of_cexpr_with (depth - 1) print_a in
  if depth <= 0 then
    "..."
  else
    match e with
    | ASeq (e1, e2, a) ->
        sprintf "(%s ; %s)%s" (string_of_cexpr e1) (string_of_aexpr e2) (print_a a)
    | ALet (x, e, b, a) ->
        sprintf "(alet %s = %s in %s)%s" x (string_of_cexpr e) (string_of_aexpr b) (print_a a)
    | ACExpr c -> string_of_cexpr c

and string_of_adecl_with depth print_a decl =
  match decl with
  | AFun (name, args, body, call_type, ret_typ, a) ->
      let binds = List.map (fun (b_name, b_a) -> sprintf "%s%s" b_name (print_a b_a)) args in
      sprintf "(def %s(%s)%s:\n  %s)%s" name
        (ExtString.String.join ", " binds)
        (let typ_str = string_of_typ ret_typ in
         if String.length typ_str <= 0 then
           ""
         else
           " -> " ^ typ_str )
        (string_of_aexpr_with (depth - 1) print_a body)
        (print_a a)

and string_of_cexpr_with (depth : int) (print_a : 'a -> string) (c : 'a cexpr) : string =
  let string_of_aexpr = string_of_aexpr_with (depth - 1) print_a in
  let string_of_immexpr = string_of_immexpr_with print_a in
  if depth <= 0 then
    "..."
  else
    match c with
    | CGetReference (body, a) -> sprintf "(reference of %s)%s" (string_of_immexpr body) (print_a a)
    | CPrim1 (op, e, a) -> sprintf "%s(%s)%s" (string_of_op1 op) (string_of_immexpr e) (print_a a)
    | CPrim2 (op, left, right, a) ->
        sprintf "(%s %s %s)%s" (string_of_immexpr left) (string_of_op2 op) (string_of_immexpr right)
          (print_a a)
    | CIf (cond, thn, els, a) ->
        sprintf "(if %s: %s else: %s)%s" (string_of_immexpr cond) (string_of_aexpr thn)
          (string_of_aexpr els) (print_a a)
    | CApp (func, args, a) ->
        sprintf "(%s(%s))%s" (string_of_immexpr func)
          (ExtString.String.join ", " (List.map string_of_immexpr args))
          (print_a a)
    | CImmExpr i -> string_of_immexpr i

and string_of_immexpr_with (print_a : 'a -> string) (i : 'a immexpr) : string =
  match i with
  | ImmLiteral (LitString (s), a) -> s ^ (print_a a)
  | ImmLiteral (LitChar (c), a) -> (String.of_char c) ^ (print_a a)
  | ImmLiteral (LitInt (n, suff), a) -> Uint64.to_string n ^ print_a a
  | ImmLiteral (LitBool b, a) -> string_of_bool b ^ print_a a
  | ImmId (x, a) -> x ^ print_a a

and string_of_aprogram_with (depth : int) (print_a : 'a -> string) (p : 'a aprogram) : string =
  match p with
  | AProgram (decls, a) ->
      ExtString.String.join "\n" (List.map (string_of_adecl_with depth print_a) decls) ^ print_a a
;;

let string_of_aexpr ?(depth = 100) (e : 'a aexpr) : string =
  string_of_aexpr_with depth (fun _ -> "") e
;;

let string_of_cexpr ?(depth = 100) (c : 'a cexpr) : string =
  string_of_cexpr_with depth (fun _ -> "") c
;;

let string_of_immexpr (i : 'a immexpr) : string = string_of_immexpr_with (fun _ -> "") i

let string_of_aprogram ?(depth = 100) (p : 'a aprogram) : string =
  string_of_aprogram_with depth (fun _ -> "") p
;;

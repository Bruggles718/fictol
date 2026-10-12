open Printf
open Pretty
open Phases
open Exprs
open Types
open Errors
open Lexing
open Llvm
open Stdint
open Fictol_stubs
open Printf
open Pretty
open Phases
open Exprs
open Types
open Errors
open Lexing
open Llvm
open Stdint
open Fictol_stubs
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

type 'a name_envt = (string * 'a) list

type 'a tag_envt = (tag * 'a) list

type 'a envt = 'a StringMap.t

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)

(* After type checking, every node of the AST carries its source span AND its type:
   `typed_tag expr`, `typed_tag decl`, `typed_tag program`. The AST is already
   parameterised over its tag, so exprs.ml does not change. What each tag's type means:
     - expression nodes: the type of that expression (for ETyApp and the EId inside it,
       the instantiated type of the identifier; for EApp, the result type);
     - BName binders: the binder's type;   - DFun: the function's TyArrow type;
     - everything else (BBlank, generic binders, DClass, DInstance, Program, ...):
       TyBlank, because there is no useful type. *)
type typed_tag = sourcespan * typ

let blank_tag (loc : sourcespan) : typed_tag = (loc, TyBlank loc)

let t_i32 = TyCon (Int I32)

let t_bool = TyCon Bool

let t_str =
  TyApp (TyCon Reference, [TyCon Char; TyApp (TyCon Region, [TyCon (RegionName "Static")])])
;;

let t_char = TyCon Char

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

let rec find_tag ls (i : tag) =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Tag %d not found" i))
  | (y, v) :: rest ->
      if y = i then
        v
      else
        find_tag rest i
;;

let ice msg = raise (InternalCompilerError msg)

let predicates_of_generic_bind g =
  match g with
  | GBName (name, preds, tag) -> preds
;;

let name_of_generic_bind g =
  match g with
  | GBName (name, preds, tag) -> name
;;

type scope_info = sourcespan * int option * int option

(* =====================================================================
   TYPE CLASSES, SECTION A: errors, global tables, front-end stubs.
   Everything in sections A, B and C is either a stub (ice "TODO") or
   unused by the existing pipeline until you wire it in, so the compiler
   behaves exactly as before. See typeclasses_outline.ml for the design.
   ===================================================================== *)

(* Suggested additions to errors.ml (I haven't seen it; adapt to its style). *)
(* exception NoInstance of string * sourcespan
(* rendered predicate. Raised when a wanted is neither given nor matched by an
   instance. When the predicate mentions a skolem, the message should suggest
   adding the bound, e.g. "add `T: Add` to f". *)
exception AmbiguousType of string * sourcespan
exception DuplicateClass of string * sourcespan * sourcespan
exception UnknownClass of string * sourcespan
exception OverlappingInstance of string * sourcespan * sourcespan
exception MissingMethod of string * string * sourcespan   (* instance, method *)
exception ExtraMethod of string * string * sourcespan
exception CyclicSuperclass of string * sourcespan *)

let class_table : (string, sourcespan class_info) Hashtbl.t = Hashtbl.create 8
(* class name -> info *)

let instance_table : (string, sourcespan instance_info list) Hashtbl.t = Hashtbl.create 8

(* class name -> all instances of that class. This replaces your commented-out
   `classes` / `instances`. Concrete `sourcespan` instead of `'a` avoids weak
   type variables on a top-level Hashtbl. *)
let method_impl_table : (string * string, typed_tag method_impl) Hashtbl.t = Hashtbl.create 32
(* (instance_id, method name) -> implementation *)

let default_method_table : (string * string, sourcespan decl) Hashtbl.t = Hashtbl.create 16
(* (class name, method name) -> default body, stored as a DFun *)

let typed_default_method_table : (string * string, typed_tag decl) Hashtbl.t = Hashtbl.create 16
(* Same keys, but the TYPE-CHECKED bodies (filled by check_class_defaults). This is what
   monomorphisation reads; default_method_table keeps the untyped input that
   check_class_defaults consumes. method_impl_table is also typed: it is only filled
   by check_instance, after checking. *)

let reset_class_state () : unit =
  (* Clear all four tables. Call at the start of type_synth so repeated
   compilations in one process (tests!) don't see each other's classes. *)
  Hashtbl.clear class_table;
  Hashtbl.clear instance_table;
  Hashtbl.clear method_impl_table;
  Hashtbl.clear default_method_table;
  Hashtbl.clear typed_default_method_table
;;

(* REAL (needed by is_well_formed / infer_prog so they stay exhaustive). *)
let partition_decls (ds : 'a decl list) : 'a decl list * 'a decl list * 'a decl list =
  List.fold_right
    (fun d (cs, is, fs) ->
      match d with
      | DClass _ -> (d :: cs, is, fs)
      | DInstance _ -> (cs, d :: is, fs)
      | DFun _ -> (cs, is, d :: fs) )
    ds ([], [], [])
;;

(* (classes, instances, funs), each in source order. *)

(* Flip to true once the Add/Sub/.. classes, the built-in instances and
   monomorphize work. Until then desugar leaves Plus, Minus, ... as EPrim2 and
   infer_exp keeps its hard-coded schemes. *)
let desugar_overloaded_ops : bool ref = ref true

let overloaded_prim1 (op : prim1) : (string * string) option =
  (* Neg |-> Some ("Neg", "neg"); everything else None. *)
  match op with
  | Neg -> Some ("Neg", "neg")
  | _ -> None
;;

let overloaded_prim2 (op : prim2) : (string * string) option =
  (* Plus |-> ("Add","add"), Minus |-> ("Sub","sub"), Times |-> ("Mul","mul"),
   Divide |-> ("Div","div"), Eq |-> ("Eq","eq"), Greater |-> ("Ord","gt"),
   GreaterEq |-> ("Ord","ge"), Less |-> ("Ord","lt"), LessEq |-> ("Ord","le").
   None for And / Or / CheckSize. In desugar's helpE:
       EPrim2(op, l, r, tag) with Some (_, m)  ==>  EApp(EId(m, tag), [l'; r'], FictolFunc, tag)
   and the same for EPrim1 with overloaded_prim1. wf runs BEFORE desugar, so it
   never sees these synthetic EIds. *)
  let res =
    match op with
    | Plus -> ("Add", "add")
    | Minus -> ("Sub", "sub")
    | Times -> ("Mul", "mul")
    | Divide -> ("Div", "div")
    | Eq -> ("Eq", "eq")
    | Greater -> ("Ord", "gt")
    | GreaterEq -> ("Ord", "ge")
    | Less -> ("Ord", "lt")
    | LessEq -> ("Ord", "le")
    | _ -> ("", "")
  in
  match res with
  | "", "" -> None
  | res -> Some res
;;

let add_builtins (p : sourcespan program) : sourcespan program =
  let widths = [I8; I16; I32; I64] in
  let uwidths = [U8; U16; U32; U64] in
  let int_types = List.map (fun w -> TyCon (Int w)) widths in
  let int_types = int_types @ List.map (fun w -> TyCon (UInt w)) uwidths in
  let bool_type = TyCon Bool in
  let self = TyVar "Self" in
  let params_self = ["Self"] in
  let make_arg name typ = BName (name, false, typ, dummy_span) in
  let make_prim2_method name ret_typ =
    { ms_name= name;
      ms_generics= [];
      ms_args= [make_arg "a" self; make_arg "b" self];
      ms_ret= ret_typ;
      ms_default= None;
      ms_span= dummy_span }
  in
  let make_prim1_method name ret_typ =
    { ms_name= name;
      ms_generics= [];
      ms_args= [make_arg "a" self];
      ms_ret= ret_typ;
      ms_default= None;
      ms_span= dummy_span }
  in
  let make_math_method name = make_prim2_method name self in
  let make_superclass name typs = {pred_class= name; pred_args= typs} in
  let make_class name params superclasses methods =
    DClass (name, params, superclasses, methods, dummy_span)
  in
  let math_classes =
    List.map
      (fun (cls_name, method_name) ->
        make_class cls_name params_self [] [make_math_method method_name] )
      ( List.map overloaded_prim2 [Plus; Minus; Times; Divide]
      |> List.map (fun maybe_op ->
          match maybe_op with
          | Some res -> res
          | None -> ice "seriously what??" ) )
  in
  let neg_class = make_class "Neg" params_self [] [make_prim1_method "neg" self] in
  let eq_class = make_class "Eq" params_self [] [make_prim2_method "eq" bool_type] in
  let ord_class =
    make_class "Ord" params_self
      [make_superclass "Eq" [self]]
      [ make_prim2_method "gt" bool_type;
        make_prim2_method "ge" bool_type;
        make_prim2_method "lt" bool_type;
        make_prim2_method "le" bool_type ]
  in
  let built_in_classes = math_classes @ [eq_class; ord_class; neg_class] in
  let name_to_prim2_op name =
    match name with
    | "add" -> Plus
    | "sub" -> Minus
    | "mul" -> Times
    | "div" -> Divide
    | "eq" -> Eq
    | "gt" -> Greater
    | "ge" -> GreaterEq
    | "lt" -> Less
    | "le" -> LessEq
    | _ -> ice "not prim2, what??"
  in
  let name_to_prim1_op name =
    match name with
    | "neg" -> Neg
    | _ -> ice "not prim1, what??"
  in
  let inst_prim_for_typ cls typ =
    match cls with
    | DClass (name, params, superclasses, method_sigs, dummy_span) ->
        let method_impls =
          List.map
            (fun method_sig ->
              try
                let prim_op = name_to_prim2_op method_sig.ms_name in
                ImplPrim2 prim_op
              with _ ->
                let prim_op = name_to_prim1_op method_sig.ms_name in
                ImplPrim1 prim_op )
            method_sigs
        in
        DInstance ([], {pred_class= name; pred_args= [typ]}, method_impls, dummy_span)
    | _ -> ice "not class, what??"
  in
  let instances =
    List.map
      (fun (cls, typs) -> List.map (fun typ -> inst_prim_for_typ cls typ) typs)
      (List.map (fun cls -> (cls, int_types)) built_in_classes)
    |> List.concat
  in
  let eq_bool_instance = inst_prim_for_typ eq_class bool_type in
  match p with
  | Program (decls, loc) -> Program (built_in_classes @ instances @ [eq_bool_instance] @ decls, loc)
;;

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
open Compiler_common

let add_builtins (p : sourcespan program) : sourcespan program =
  (* let widths = [I8; I16; I32; I64] in
  let uwidths = [U8; U16; U32; U64] in *)
  (* let int_types = List.map (fun w -> TyCon (Int w)) widths in
  let int_types = int_types @ List.map (fun w -> TyCon (UInt w)) uwidths in *)
  let type_type = EId("Type", dummy_span) in
  let int_types = [
    "i8"; "i16"; "i32"; "i64";
    "u8"; "u16"; "u32"; "u64";
  ] in
  let int_types = List.map (fun s -> EId(s, dummy_span)) int_types in
  (* let self = TyVar "Self" in *)
  let self = EId("Self", dummy_span) in
  let params_self = [(FPName("Self", type_type, Explicit, dummy_span))] in
  let make_arg name typ = FPName (name, typ, Explicit, dummy_span) in
  let make_prim2_method name ret_typ =
    { fname= name;
      fparams= [make_arg "a" self; make_arg "b" self];
      fbody= None;
      fret_type=self;
      fcall_type=FictolFunc;
      ftag= dummy_span }
  in
  let make_prim1_method name ret_typ =
    { fname= name;
      fparams= [make_arg "a" self];
      fbody= None;
      fret_type=self;
      fcall_type=FictolFunc;
      ftag= dummy_span }
  in
  let make_math_method name = make_prim2_method name self in
  let make_superclass name typs = EApp(EId(name, dummy_span), typs, dummy_span) in
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
  let not_class = make_class "Not" params_self [] [make_prim1_method "not" self] in
  let eq_class = make_class "Eq" params_self [] [make_prim2_method "eq" t_bool] in
  let deref_class = make_class "Deref" params_self [] [
    {
      fname = "deref";
      fparams = [(FPName("R", EId("Region", dummy_span), Implicit, dummy_span)); make_arg "a" (EApp(EId("ref", dummy_span), [self; EId("R", dummy_span)], dummy_span))];
      (* ms_args = [make_arg "a" (TyApp(TyCon(Reference), [self; (TyApp(TyCon(Region), [TyVar("T")]))]))]; *)
      fbody = None;
      fret_type = self;
      fcall_type = FictolFunc;
      ftag = dummy_span;
    }
  ] in
  let ref_class = make_class "Ref" params_self [] [
    {
      fname = "ref";
      fparams = [(FPName("R", EId("Region", dummy_span), Implicit, dummy_span)); make_arg "a" self];
      (* ms_args = [make_arg "a" (TyApp(TyCon(Reference), [self; (TyApp(TyCon(Region), [TyVar("T")]))]))]; *)
      fbody = None;
      fret_type = (EApp(EId("ref", dummy_span), [self; EId("R", dummy_span)], dummy_span));
      fcall_type = FictolFunc;
      ftag = dummy_span;
    }
  ] in
  let ord_class =
    make_class "Ord" params_self
      [make_superclass "Eq" [self]]
      [ make_prim2_method "gt" t_bool;
        make_prim2_method "ge" t_bool;
        make_prim2_method "lt" t_bool;
        make_prim2_method "le" t_bool ]
  in
  let built_in_classes = math_classes @ [eq_class; ord_class; neg_class; deref_class] in
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
    | "not" -> Not
    | "neg" -> Neg
    | "deref" -> Deref
    | "ref" -> Ref
    | _ -> ice "not prim1, what??"
  in
  let inst_prim_for_typ cls typ =
    match cls with
    | DClass (name, params, superclasses, method_sigs, dummy_span) ->
        let method_impls =
          List.map
            (fun method_sig ->
              try
                let prim_op = name_to_prim2_op method_sig.fname in
                ImplPrim2 prim_op
              with _ ->
                let prim_op = name_to_prim1_op method_sig.fname in
                ImplPrim1 prim_op )
            method_sigs
        in
        DInstance ([], make_superclass name [typ], method_impls, dummy_span)
    | _ -> ice "not class, what??"
  in
  let inst_generic_prim cls =
    let typ = EId("T", dummy_span) in
    match cls with
    | DClass (name, params, superclasses, method_sigs, dummy_span) ->
        let method_impls =
          List.map
            (fun method_sig ->
              try
                let prim_op = name_to_prim2_op method_sig.fname in
                ImplPrim2 prim_op
              with _ ->
                let prim_op = name_to_prim1_op method_sig.fname in
                ImplPrim1 prim_op )
            method_sigs
        in
        DInstance ([(FPName("T", type_type, Explicit, dummy_span))], make_superclass name [typ], method_impls, dummy_span)
    | _ -> ice "not class, what??"
  in
  let instances =
    List.map
      (fun (cls, typs) -> List.map (fun typ -> inst_prim_for_typ cls typ) typs)
      (List.map (fun cls -> (cls, int_types)) built_in_classes)
    |> List.concat
  in
  let non_numeric_classes = [eq_class; deref_class] in
  let non_numeric_typs = [t_bool; t_char] in
  let non_numeric_instances =
    List.map
      (fun (cls, typs) -> List.map (fun typ -> inst_prim_for_typ cls typ) typs)
      (List.map (fun cls -> (cls, non_numeric_typs)) non_numeric_classes)
    |> List.concat
  in
  let not_instance = inst_prim_for_typ not_class (t_bool) in
  let ref_instance = inst_generic_prim ref_class in
  match p with
  | Program (decls, loc) -> Program ([not_class; ref_class] @ built_in_classes @ instances @ non_numeric_instances @ [not_instance; ref_instance] @ decls, loc)
;;

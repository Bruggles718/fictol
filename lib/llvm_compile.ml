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
open Typecheck
open Anf

let rec typ_to_llvm_typ context typ =
  match typ with
  | TyCon tykind -> (
    match tykind with
    | Int I8 -> i8_type context
    | Int I16 -> i16_type context
    | Int I32 -> i32_type context
    | Int I64 -> i64_type context
    | UInt U8 -> i8_type context
    | UInt U16 -> i16_type context
    | UInt U32 -> i32_type context
    | UInt U64 -> i64_type context
    | Bool -> i1_type context
    | Char -> i8_type context
    | _ -> ice "Typ to llvm typ failure: unsupported tykind" )
  | TyApp (TyCon Reference, _) -> pointer_type context
  | TyArrow _ -> pointer_type context
  | _ -> ice (sprintf "cannot convert %s to llvm" (string_of_typ typ))

and typ_to_llvm_fn_type context typ =
  match typ with
  | TyArrow (args, ret, call_type) ->
      function_type (typ_to_llvm_typ context ret)
        (Array.of_list (List.map (typ_to_llvm_typ context) args))
  | _ -> ice "expected a function type"
;;

let get_tycon_tykind typ =
  match typ with
  | TyCon tykind -> tykind
  | _ -> ice "Cannot get tykind of non tycon"
;;

let typ_to_llvm_signed typ =
  match typ with
  | TyCon (Int _) -> true
  | TyCon (UInt _) -> false
  | _ -> ice "non int cannot be signed or unsigned Unsupported"
;;

let call_type_to_llvm_call_conv ct =
  match ct with
  | Extern "C" -> Llvm.CallConv.c
  | _ -> 18 (* tailcc *)
;;

let name_of_immexpr imm =
  match imm with
  | ImmId (name, _) -> name
  | _ -> ice (sprintf "cannot get name of non-id %s" (string_of_immexpr imm))
;;

let compile_prog context the_module builder (prog : (tag * typ) aprogram) : string =
  let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s_%d" name !next
  in
  let rec compile_afun env (f : 'a adecl) : unit =
    match f with
    | AFun (name, binds, body, call_type, ret_typ, (tag, typ)) -> (
        let llvm_fun = find env name in
        match body with
        | Some body ->
            (* let args_env = List.combine (List.map fst binds) (Array.to_list (params llvm_fun)) in *)
            let bb = append_block context "entry" llvm_fun in
            position_at_end bb builder;
            let args_env =
              List.map2
                (fun (name, (_, typ)) arg ->
                  let slot = build_alloca (typ_to_llvm_typ context typ) name builder in
                  ignore (build_store arg slot builder);
                  (name, slot) )
                binds
                (Array.to_list (params llvm_fun))
            in
            (* the tail-mode compile emits a ret on every path, so there is no build_ret here *)
            ( match call_type with
            | Extern _ ->
                let compiled_body = compile_aexpr (args_env @ env) body llvm_fun in
                let _ = build_ret compiled_body builder in
                ()
            | _ -> compile_aexpr_tail (args_env @ env) body llvm_fun );
            Llvm_analysis.assert_valid_function llvm_fun
        | None -> Llvm.set_linkage Llvm.Linkage.External llvm_fun )
  and forward_declare_func the_module context (f : 'a adecl) : string * llvalue =
    match f with
    | AFun (name, binds, _, call_type, ret_typ, (tag, typ)) ->
        let llvm_args =
          Array.of_list (List.map (fun (_, (_, b_typ)) -> typ_to_llvm_typ context b_typ) binds)
        in
        (* the real return type, not void *)
        let func_type = function_type (typ_to_llvm_typ context ret_typ) llvm_args in
        let llvm_fun = declare_function name func_type the_module in
        Llvm.set_function_call_conv (call_type_to_llvm_call_conv call_type) llvm_fun;
        (name, llvm_fun)
  (* ---------- non-tail position: produces a value ---------- *)
  and compile_aexpr env (e : 'a aexpr) llvm_fun : llvalue =
    match e with
    | ACExpr c -> compile_cexpr env c llvm_fun
    | ALet (name, bound, body, _) ->
        let v = compile_cexpr env bound llvm_fun in
        let _, bound_typ = tag_of_cexpr bound in
        let stack_loc = build_alloca (typ_to_llvm_typ context bound_typ) name builder in
        let _ = build_store v stack_loc builder in
        (* the bound value is NOT in tail position *)
        let new_env = (name, stack_loc) :: env in
        compile_aexpr new_env body llvm_fun
    | ASeq (first, rest, _) ->
        let _ = compile_cexpr env first llvm_fun in
        compile_aexpr env rest llvm_fun
  and compile_cexpr env (c : 'a cexpr) llvm_fun : llvalue =
    match c with
    | CImmExpr imm -> compile_immexpr env imm
    | CPrim2 (op, left, right, (tag, typ)) ->
        let l = compile_immexpr env left in
        let r = compile_immexpr env right in
        let _, ltyp = tag_of_immexpr left in
        let _, rtyp = tag_of_immexpr right in
        (prim2_to_llvm_op op ltyp rtyp) l r (sprintf "cprim2_%d" tag) builder
    | CPrim1 (op, body, (tag, typ)) ->
        let b = compile_immexpr env body in
        let _, b_typ = tag_of_immexpr body in
        (prim1_to_llvm_op op b_typ) b (sprintf "cprim1_%d" tag) builder
    | CGetReference (body, (tag, typ)) -> (
      match body with
      | ImmId (name, (tag, typ)) -> (
        match lookup_function name the_module with
        | Some _ ->
            let fn = build_alloca (pointer_type context) (gensym "fn_ptr") builder in
            let _ = build_store (find env name) fn builder in
            fn
            (* build_load (typ_to_llvm_typ context typ) fn (gensym "fn_val") builder *)
        | _ -> find env name )
      | _ -> ice "cannot reference non-id" )
    | CApp (closure, args, (tag, typ)) ->
        let _, closure_typ = tag_of_immexpr closure in
        let call_type = call_type_of_arrow_typ closure_typ in
        compile_call env closure args call_type tag
    | CIf (cond, thn, els, (tag, _)) ->
        let cond_imm = compile_immexpr env cond in
        let if_name = sprintf "if_%d" tag in
        let thn_bb = append_block context (if_name ^ "_then") llvm_fun in
        let els_bb = append_block context (if_name ^ "_else") llvm_fun in
        let merge_bb = append_block context (if_name ^ "_end") llvm_fun in
        let _ = build_cond_br cond_imm thn_bb els_bb builder in
        position_at_end thn_bb builder;
        let thn_val = compile_aexpr env thn llvm_fun in
        let thn_end = insertion_block builder in
        (* the block the branch ENDED in *)
        let _ = build_br merge_bb builder in
        position_at_end els_bb builder;
        let els_val = compile_aexpr env els llvm_fun in
        let els_end = insertion_block builder in
        let _ = build_br merge_bb builder in
        position_at_end merge_bb builder;
        build_phi [(thn_val, thn_end); (els_val, els_end)] (if_name ^ "_result") builder
  (* ---------- tail position: emits `ret` on every path, returns unit ---------- *)
  and compile_aexpr_tail env (e : 'a aexpr) llvm_fun : unit =
    match e with
    | ACExpr c -> compile_cexpr_tail env c llvm_fun
    | ALet (name, bound, body, _) ->
        let v = compile_cexpr env bound llvm_fun in
        let _, bound_typ = tag_of_cexpr bound in
        let stack_loc = build_alloca (typ_to_llvm_typ context bound_typ) name builder in
        let _ = build_store v stack_loc builder in
        (* the bound value is NOT in tail position *)
        let new_env = (name, stack_loc) :: env in
        compile_aexpr_tail new_env body llvm_fun
    | ASeq (first, rest, _) ->
        let _ = compile_cexpr env first llvm_fun in
        compile_aexpr_tail env rest llvm_fun
  and compile_cexpr_tail env (c : 'a cexpr) llvm_fun : unit =
    match c with
    | CApp (closure, args, (tag, typ)) ->
        let _, closure_typ = tag_of_immexpr closure in
        let call_type = call_type_of_arrow_typ closure_typ in
        let call = compile_call env closure args call_type tag in
        (* set_musttail call; *)
        ( match call_type with
        | Extern _ -> ()
        | _ -> Llvm.set_tail_call true call; set_musttail call );
        (* nothing may sit between the call and this ret *)
        let _ = build_ret call builder in
        ()
    | CIf (cond, thn, els, (tag, _)) ->
        let cond_imm = compile_immexpr env cond in
        let if_name = sprintf "if_%d" tag in
        let thn_bb = append_block context (if_name ^ "_then") llvm_fun in
        let els_bb = append_block context (if_name ^ "_else") llvm_fun in
        let _ = build_cond_br cond_imm thn_bb els_bb builder in
        (* no merge block: each branch ends in its own ret *)
        position_at_end thn_bb builder;
        compile_aexpr_tail env thn llvm_fun;
        position_at_end els_bb builder;
        compile_aexpr_tail env els llvm_fun
    | CImmExpr _ | CPrim1 _ | CPrim2 _ | CGetReference _ ->
        let v = compile_cexpr env c llvm_fun in
        let _ = build_ret v builder in
        ()
  (* shared by both modes; only the tail version sets the tail marker *)
  and compile_call env closure args call_type app_tag : llvalue =
    (* let callee = (
    match closure with
    | ImmId (name, (tag, typ)) -> 
      let fn = build_alloca (pointer_type context) (sprintf "fn_ptr_%d" app_tag) builder in
      let _ = build_store (find env name) fn builder in
      build_load (typ_to_llvm_typ context typ) fn (sprintf "fn_val_%d" app_tag) builder
    | _ -> ice "cannot call non-id"
  ) in *)
    let callee = compile_immexpr env closure in
    let tag, typ = tag_of_immexpr closure in
    let llvm_args = Array.of_list (List.map (compile_immexpr env) args) in
    (* the FUNCTION type, taken from the callee's own type so it matches its declaration *)
    let fn_type = typ_to_llvm_fn_type context typ in
    (* let f_value = build_alloca (pointer_type context) (sprintf "f_value_%d" app_tag) builder in *)
    (* let _ = build_store callee f_value builder in *)
    let call = build_call fn_type callee llvm_args (sprintf "app_%d" app_tag) builder in
    Llvm.set_instruction_call_conv (call_type_to_llvm_call_conv call_type) call;
    call
  and compile_immexpr env (e : 'a immexpr) : llvalue =
    match e with
    | ImmId (name, (tag, typ)) -> (
      match lookup_function name the_module with
      | Some _ ->
          let fn = build_alloca (pointer_type context) (gensym "fn_ptr") builder in
          let _ = build_store (find env name) fn builder in
          build_load (typ_to_llvm_typ context typ) fn (gensym "fn_val") builder
      | _ ->
          let stack_loc = find env name in
          build_load (typ_to_llvm_typ context typ) stack_loc name builder )
    | ImmLiteral (LitInt (n, suffix), (tag, typ)) ->
        const_of_int64 (typ_to_llvm_typ context typ) (Uint64.to_int64 n) (typ_to_llvm_signed typ)
    | ImmLiteral (LitBool true, (tag, typ)) -> const_int (i1_type context) 1
    | ImmLiteral (LitBool false, (tag, typ)) -> const_int (i1_type context) 0
    | ImmLiteral (LitString s, (tag, typ)) ->
        build_global_stringptr s (sprintf "string_literal_%d" tag) builder
    | ImmLiteral (LitChar c, (tag, typ)) -> const_int (i8_type context) (int_of_char c)
  and prim2_to_llvm_op op ltyp rtyp =
    let ltykind = get_tycon_tykind ltyp in
    let rtykind = get_tycon_tykind rtyp in
    match (op, ltykind, rtykind) with
    | Plus, Int _, Int _ | Plus, UInt _, UInt _ -> build_add
    | Minus, Int _, Int _ | Minus, UInt _, UInt _ -> build_sub
    | Times, Int _, Int _ | Times, UInt _, UInt _ -> build_mul
    | Divide, Int _, Int _ -> build_sdiv
    | Divide, UInt _, UInt _ -> build_udiv
    | Eq, Int _, Int _ | Eq, Bool, Bool | Eq, UInt _, UInt _ -> build_icmp Icmp.Eq
    | Greater, Int _, Int _ -> build_icmp Icmp.Sgt
    | GreaterEq, Int _, Int _ -> build_icmp Icmp.Sge
    | Less, Int _, Int _ -> build_icmp Icmp.Slt
    | LessEq, Int _, Int _ -> build_icmp Icmp.Sle
    | Greater, UInt _, UInt _ -> build_icmp Icmp.Ugt
    | GreaterEq, UInt _, UInt _ -> build_icmp Icmp.Uge
    | Less, UInt _, UInt _ -> build_icmp Icmp.Ult
    | LessEq, UInt _, UInt _ -> build_icmp Icmp.Ule
    | _ ->
        ice
          (sprintf "unsupported prim2 to llvm op %s for typs %s %s" (string_of_op2 op)
             (string_of_typ ltyp) (string_of_typ rtyp) )
  and prim1_to_llvm_op op typ =
    (* let tykind = get_tycon_tykind typ in *)
    match (op, typ) with
    | Neg, _ -> build_neg
    | Not, _ -> build_not
    | Deref, (TyApp(TyCon(Reference), [ref_typ; _])) -> build_load (typ_to_llvm_typ context ref_typ)
    | _ ->
        ice
          (sprintf "unsupported prim1 to llvm op %s for typ %s" (string_of_op1 op)
             (string_of_typ typ) )
  in
  match prog with
  | AProgram (decls, (tag, typ)) ->
      let env = List.map (forward_declare_func the_module context) decls in
      List.iter (compile_afun env) decls;
      string_of_llmodule the_module
;;

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
open Tag

type 'a anf_bind =
  | BSeq of 'a cexpr * typ
  | BLet of string * typ * 'a cexpr

let anf (p : (tag * typ) program) : typ aprogram =
  let rec helpP (p : (tag * typ) program) : typ aprogram =
    match p with
    | Program (decls, (tag, typ)) -> AProgram (List.map helpD decls, typ)
  and helpD d =
    match d with
    | DFun (name, [], args, body, call_type, ret_typ, (tag, typ)) ->
        let new_args =
          List.map
            (fun arg ->
              match arg with
              | BName (b_name, _, b_typ, _) -> (b_name, b_typ)
              | _ -> failwith "ANF: unsupported binding" )
            args
        in
        AFun (name, new_args, helpA body, call_type, ret_typ, typ)
    | _ -> failwith "anf: invalid decl"
  and helpC (e : (tag * typ) expr) : typ cexpr * typ anf_bind list =
    match e with
    | EGetReference (arg, (tag, typ)) ->
        let arg_imm, arg_setup = helpI arg in
        (CGetReference (arg_imm, typ), arg_setup)
    | EPrim1 (op, arg, (tag, typ)) ->
        let arg_imm, arg_setup = helpI arg in
        (CPrim1 (op, arg_imm, typ), arg_setup)
    | EPrim2 (op, left, right, (tag, typ)) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (CPrim2 (op, left_imm, right_imm, typ), left_setup @ right_setup)
    | EIf (cond, _then, _else, (tag, typ)) ->
        let cond_imm, cond_setup = helpI cond in
        (CIf (cond_imm, helpA _then, helpA _else, typ), cond_setup)
    | ELet ([], body, _) -> helpC body
    | ELet ((BBlank _, exp, (tag, typ)) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq (exp_ans, typ)] @ body_setup)
    | ELet ((BName (bind, _, typ, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, typ, exp_ans)] @ body_setup)
    (* | ELet ((BTuple _, _, _) :: _, _, _) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away") *)
    | EApp (func, args, (tag, typ)) ->
        let func_ans, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        (CApp (func_ans, new_args, typ), func_setup @ List.concat new_setup)
    | ESeq (e1, e2, (tag, typ)) ->
        let e1_ans, e1_setup = helpC e1 in
        let e2_ans, e2_setup = helpC e2 in
        (e2_ans, e1_setup @ [BSeq (e1_ans, typ)] @ e2_setup)
    | _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : (tag * typ) expr) : typ immexpr * typ anf_bind list =
    match e with
    | ELiteral (litval, (tag, typ)) -> (ImmLiteral (litval, typ), [])
    | EId (name, (tag, typ)) -> (ImmId (name, typ), [])
    | ESeq (e1, e2, _) ->
        let _, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        (e2_imm, e1_setup @ e2_setup)
    | EGetReference (arg, (tag, typ)) ->
        let tmp = sprintf "ref_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, typ), arg_setup @ [BLet (tmp, typ, CGetReference (arg_imm, typ))])
    | EPrim1 (op, arg, (tag, typ)) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, typ), arg_setup @ [BLet (tmp, typ, CPrim1 (op, arg_imm, typ))])
    | EPrim2 (op, left, right, (tag, typ)) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        ( ImmId (tmp, typ),
          left_setup @ right_setup @ [BLet (tmp, typ, CPrim2 (op, left_imm, right_imm, typ))] )
    | EIf (cond, _then, _else, (tag, typ)) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        ( ImmId (tmp, typ),
          cond_setup @ [BLet (tmp, typ, CIf (cond_imm, helpA _then, helpA _else, typ))] )
    | EApp (func, args, (tag, typ)) ->
        let tmp = sprintf "app_%d" tag in
        let new_func, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        ( ImmId (tmp, typ),
          func_setup @ List.concat new_setup @ [BLet (tmp, typ, CApp (new_func, new_args, typ))] )
    | ELet ([], body, _) -> helpI body
    | ELet ((BBlank _, exp, (tag, typ)) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq (exp_ans, typ)] @ body_setup)
    | ELet ((BName (bind, _, typ, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, typ, exp_ans)] @ body_setup)
    | _ -> failwith (sprintf "ANF: unsupported expr %s" (string_of_expr e))
  and helpA e : typ aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq (exp, typ) -> ASeq (exp, body, typ)
        | BLet (name, typ, exp) -> ALet (name, exp, body, typ) )
      ans_setup (ACExpr ans)
  in
  helpP p
;;

let map_tags_immexpr (f : 'a -> 'b) (e : 'a immexpr) : 'b immexpr =
  match e with
  | ImmLiteral (lit, tag) -> ImmLiteral (lit, f tag)
  | ImmId (name, tag) -> ImmId (name, f tag)
;;

let map_tags_abind (f : 'a -> 'b) ((name, tag) : 'a abind) : 'b abind = (name, f tag)

let rec map_tags_cexpr (f : 'a -> 'b) (c : 'a cexpr) : 'b cexpr =
  let imm = map_tags_immexpr f in
  match c with
  | CIf (cond, then_, else_, tag) ->
      CIf (imm cond, map_tags_aexpr f then_, map_tags_aexpr f else_, f tag)
  | CGetReference (arg, tag) -> CGetReference (imm arg, f tag)
  | CPrim1 (op, arg, tag) -> CPrim1 (op, imm arg, f tag)
  | CPrim2 (op, left, right, tag) -> CPrim2 (op, imm left, imm right, f tag)
  | CApp (fn, args, tag) -> CApp (imm fn, List.map imm args, f tag)
  | CImmExpr e -> CImmExpr (imm e)

and map_tags_aexpr (f : 'a -> 'b) (a : 'a aexpr) : 'b aexpr =
  match a with
  | ASeq (first, rest, tag) -> ASeq (map_tags_cexpr f first, map_tags_aexpr f rest, f tag)
  | ALet (name, bound, body, tag) ->
      ALet (name, map_tags_cexpr f bound, map_tags_aexpr f body, f tag)
  | ACExpr c -> ACExpr (map_tags_cexpr f c)
;;

let map_tags_adecl (f : 'a -> 'b) (d : 'a adecl) : 'b adecl =
  match d with
  | AFun (name, args, body, call_type, ret_typ, tag) ->
      AFun (name, List.map (map_tags_abind f) args, map_tags_aexpr f body, call_type, ret_typ, f tag)
;;

let map_tags_aprogram (f : 'a -> 'b) (p : 'a aprogram) : 'b aprogram =
  match p with
  | AProgram (decls, tag) -> AProgram (List.map (map_tags_adecl f) decls, f tag)
;;

let tag_of_immexpr (e : 'a immexpr) : 'a =
  match e with
  | ImmLiteral (_, tag) | ImmId (_, tag) -> tag
;;

let tag_of_cexpr (c : 'a cexpr) : 'a =
  match c with
  | CIf (_, _, _, tag)
   |CPrim1 (_, _, tag)
   |CPrim2 (_, _, _, tag)
   |CApp (_, _, tag)
   |CGetReference (_, tag) -> tag
  | CImmExpr e -> tag_of_immexpr e
;;

let tag_of_aexpr (a : 'a aexpr) : 'a =
  match a with
  | ASeq (_, _, tag) | ALet (_, _, _, tag) -> tag
  | ACExpr c -> tag_of_cexpr c
;;

let tag_of_adecl (d : 'a adecl) : 'a =
  match d with
  | AFun (_, _, _, _, _, tag) -> tag
;;

let tag_of_aprogram (p : 'a aprogram) : 'a =
  match p with
  | AProgram (_, tag) -> tag
;;

let tag_of_abind ((_, tag) : 'a abind) : 'a = tag

let atag_prog p =
  let next = ref 0 in
  let tag typ =
    next := !next + 1;
    (!next, typ)
  in
  map_tags_aprogram tag p
;;

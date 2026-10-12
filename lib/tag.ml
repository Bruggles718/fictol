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

let tag_span_prog (p : sourcespan program) : (tag * sourcespan) program =
  let next = ref 0 in
  let tag (span) =
    next := !next + 1;
    (!next, span)
  in
  map_tags_program tag p
;;

let tag_span_typ_prog (p : (sourcespan * typ) program) : (tag * typ) program =
  let next = ref 0 in
  let tag (span, typ) =
    next := !next + 1;
    (!next, typ)
  in
  map_tags_program tag p
;;

let untag_tag_span_prog (p: (tag * sourcespan) program) : sourcespan program =
  let untag (tag, span) = span in
  map_tags_program untag p

let tag_other_gensym name ((tag, _) : tag * 'a) =
  sprintf "%s_%d" name tag
;;

let rename (rename_with_tag: string -> 'a -> string) (p : 'a program) : 'a program =
  let rec helpP env p =
    match p with
    | Program (decls, tag) -> Program (List.map (helpD env) decls, tag)
  and helpD env decl =
    match decl with
    | DFun (name, [], args, body, call_type, ret_typ, tag) ->
        let newArgs, env' = helpBS env args in
        DFun (name, [], newArgs, Option.map (helpE env') body, call_type, ret_typ, tag)
    (* | _ -> ice "Rename: Found non DFun after monomorphization?? Is that allowed?? Idk" *)
    | _ -> decl
  and helpB env b =
    match b with
    | BBlank _ -> (b, env)
    | BName (name, allow_shadow, b_typ, tag) ->
        let name' = rename_with_tag name tag in
        (BName (name', allow_shadow, b_typ, tag), (name, name') :: env)
  and helpBS env (bs : 'a bind list) =
    match bs with
    | [] -> ([], env)
    | b :: bs ->
        let b', env' = helpB env b in
        let bs', env'' = helpBS env' bs in
        (b' :: bs', env'')
  and helpBG env (bindings : 'a binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE env e in
        let bindings', env'' = helpBG env' bindings in
        ((b', e', a) :: bindings', env'')
  and helpE env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE env e1, helpE env e2, tag)
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE env arg, tag)
    | EPrim2 (op, left, right, tag) -> EPrim2 (op, helpE env left, helpE env right, tag)
    | EIf (c, t, f, tag) -> EIf (helpE env c, helpE env t, helpE env f, tag)
    | ELiteral _ -> e
    | EId (name, tag) -> ( try EId (find env name, tag) with InternalCompilerError _ -> e )
    | EApp (func, args, tag) ->
        (* Figure out a way to determine call type. 
      Maybe build a global env of externs, and a global env of top level functions,
      and if its not in either then it's extern?
      But that doesn't work because how do I know what func is?
      maybe i have to resolve it later...
      WAIT! I can check the type of the expr func and determine if it's a closure or a regular arrow type.
      That tells me if it's a function or a closure. If arrow type, check a global extern env. If not found,
      FictolFunc. If found, extern of that type.
      WAIT AGAIN! This doesn't work because I don't have a name to look up in the env. func could be anything.
      Can I rely on well-formedness to prove any invariants? 
      Should the call type be encoded in the arrow type?
      
      OK heres what to do:
      after rename and ANF, each func will have a unique id and be called from that unique id, and I can
      know the call type from that. I'm not sure how this will work across function boundaries though.
      maybe don't have raw function pointers at all, only allow passing around explicit closures?*)
        let func = helpE env func in
        EApp (func, List.map (helpE env) args, tag)
    | ELet (binds, body, tag) ->
        let binds', env' = helpBG env binds in
        let body' = helpE env' body in
        ELet (binds', body', tag)
    | EGetReference (body, tag) -> EGetReference (helpE env body, tag)
    | EBorrow (borrowed_expr, ref_name, region, body, tag) ->
      let new_ref_name = rename_with_tag ref_name tag in
      EBorrow (helpE env borrowed_expr, new_ref_name, region, helpE ((ref_name, new_ref_name) :: env) body, tag)
    | _ -> ice (sprintf "Rename: unsupported expr %s" (string_of_expr e)) 
  in
  helpP [] p
;;

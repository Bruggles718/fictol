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

let tag_of_expr (e : 'a expr) : 'a =
  match e with
  | ESeq (_, _, t)
   |ELet (_, _, t)
   |EPrim1 (_, _, t)
   |EPrim2 (_, _, _, t)
   |EIf (_, _, _, t)
   |ELiteral (_, t)
   |EId (_, t)
   |EApp (_, _, t)
  | EBorrow (_, _, _, _, t) -> t
;;

let type_of_expr (e : typed_tag expr) : typ = snd (tag_of_expr e)

let span_of_expr (e : typed_tag expr) : sourcespan = fst (tag_of_expr e)

(* Rebuild an AST piece with every tag mapped by f. The tag type parameter changes, so
   predicates (whose 'a is phantom) are rebuilt too. *)

let rec map_tags_expr (f : 'a -> 'b) (e : 'a expr) : 'b expr =
  let go = map_tags_expr f in
  match e with
  | ESeq (e1, e2, tag) -> ESeq (go e1, go e2, f tag)
  | ELet (bindings, body, tag) ->
      ELet
        ( List.map (fun (b, bound, btag) -> (map_tags_bind f b, go bound, f btag)) bindings,
          go body,
          f tag )
  | EPrim1 (op, body, tag) -> EPrim1 (op, go body, f tag)
  | EPrim2 (op, l, r, tag) -> EPrim2 (op, go l, go r, f tag)
  | EIf (c, t, el, tag) -> EIf (go c, go t, go el, f tag)
  | ELiteral (lit, tag) -> ELiteral (lit, f tag)
  | EId (x, tag) -> EId (x, f tag)
  | EApp (fn, args, tag) -> EApp (go fn, List.map go args, f tag)
  | EBorrow (borrowed_expr, ref_name, region, body, tag) ->
      EBorrow (go borrowed_expr, ref_name, region, go body, f tag)

and map_tags_bind (f : 'a -> 'b) (b : 'a bind) : 'b bind =
  match b with
  | BBlank tag -> BBlank (f tag)
  | BName (name, Some(typ), tag) -> BName (name, (Some(map_tags_expr f typ)), f tag)
  | BName (name, None, tag) -> BName (name, None, f tag)


and map_tags_fun_param (f : 'a -> 'b) (b : 'a fun_param) : 'b fun_param =
  match b with
  | FPName (name, typ, piinfo, tag) -> FPName (name, map_tags_expr f typ, piinfo, f tag)
;;

let map_tags_fun_sig (f : 'a -> 'b) (fs : 'a fun_sig) : 'b fun_sig =
  { fname= fs.fname;
    fparams= List.map (map_tags_fun_param f) fs.fparams;
    fret_type= map_tags_expr f fs.fret_type;
    fbody= Option.map (map_tags_expr f) fs.fbody;
    fcall_type= fs.fcall_type;
    ftag= f fs.ftag }
;;

let rec map_tags_decl (f : 'a -> 'b) (d : 'a decl) : 'b decl =
  match d with
  | DFun (fs) ->
      DFun
        ( map_tags_fun_sig f fs )
  | DClass (name, params, supers, sigs, tag) ->
      DClass
        (name, params, List.map (map_tags_expr f) supers, List.map (map_tags_fun_sig f) sigs, f tag)
  | DInstance (generics, head, impls, tag) ->
      DInstance
        ( List.map (map_tags_fun_param f) generics,
          map_tags_expr f head,
          List.map (map_tags_impl f) impls,
          f tag )

and map_tags_impl (f : 'a -> 'b) (impl : 'a method_impl) : 'b method_impl =
  match impl with
  | ImplDecl d -> ImplDecl (map_tags_decl f d)
  | ImplPrim1 op -> ImplPrim1 op
  | ImplPrim2 op -> ImplPrim2 op
;;

let map_tags_program (f : 'a -> 'b) (p : 'a program) : 'b program =
  match p with
  | Program (decls, tag) -> Program (List.map (map_tags_decl f) decls, f tag)
;;

let tag_span_prog (p : sourcespan program) : (tag * sourcespan) program =
  let next = ref 0 in
  let tag (span: sourcespan) : (tag * sourcespan) =
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

let rename (rename_with_tag : string -> 'a -> string) (p : 'a program) : 'a program =
  let rec helpP env p =
    match p with
    | Program (decls, tag) ->
        Program (List.map (helpD env) decls, tag)

  and helpD env decl =
    match decl with
    | DFun fs ->
        let new_params, env' = helpFPs env fs.fparams in
        DFun {
          fs with
          fparams = new_params;
          fret_type = helpE env' fs.fret_type;
          fbody = Option.map (helpE env') fs.fbody;
        }

    | DClass (name, params, constraints, methods, tag) ->
        DClass (
          name,
          params,
          List.map (helpE env) constraints,
          List.map (fun fs ->
            let new_params, env' = helpFPs env fs.fparams in
            {
              fs with
              fparams = new_params;
              fret_type = helpE env' fs.fret_type;
              fbody = Option.map (helpE env') fs.fbody;
            }
          ) methods,
          tag
        )

    | DInstance (params, constraint_expr, methods, tag) ->
        let params', env' = helpFPs env params in
        DInstance (
          params',
          helpE env' constraint_expr,
          List.map (helpMethodImpl env') methods,
          tag
        )
  and helpMethodImpl env meth =
    match meth with
    | ImplDecl(decl) -> ImplDecl(helpD env decl)
    | ImplPrim1 _ | ImplPrim2 _ -> meth
  and helpB env b =
    match b with
    | BBlank tag ->
        (b, env)

    | BName (name, annotation, tag) ->
        let annotation' = Option.map (helpE env) annotation in
        let name' = rename_with_tag name tag in
        (BName (name', annotation', tag), (name, name') :: env)

  (* and helpBS env (bs : 'a bind list) =
    match bs with
    | [] ->
        ([], env)

    | b :: bs ->
        let b', env' = helpB env b in
        let bs', env'' = helpBS env' bs in
        (b' :: bs', env'') *)

  and helpFP env (FPName (name, typ, info, tag)) =
    let typ' = helpE env typ in
    let name' = rename_with_tag name tag in
    (FPName (name', typ', info, tag), (name, name') :: env)

  and helpFPs env (params : 'a fun_param list) =
    match params with
    | [] ->
        ([], env)

    | param :: params ->
        let param', env' = helpFP env param in
        let params', env'' = helpFPs env' params in
        (param' :: params', env'')

  and helpBG env (bindings : 'a binding list) =
    match bindings with
    | [] ->
        ([], env)

    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE env e in
        let bindings', env'' = helpBG env' bindings in
        ((b', e', a) :: bindings', env'')

  and helpE env e =
    match e with
    | ESeq (e1, e2, tag) ->
        ESeq (helpE env e1, helpE env e2, tag)

    | EPrim1 (op, arg, tag) ->
        EPrim1 (op, helpE env arg, tag)

    | EPrim2 (op, left, right, tag) ->
        EPrim2 (op, helpE env left, helpE env right, tag)

    | EIf (c, t, f, tag) ->
        EIf (helpE env c, helpE env t, helpE env f, tag)

    | ELiteral _ ->
        e

    | EId (name, tag) ->
        (try EId (List.assoc name env, tag)
         with Not_found -> e)

    | EApp (func, args, tag) ->
        EApp (
          helpE env func,
          List.map (helpE env) args,
          tag
        )

    | ELet (bindings, body, tag) ->
        let bindings', env' = helpBG env bindings in
        ELet (bindings', helpE env' body, tag)

    | EBorrow (borrowed_expr, ref_name, region, body, tag) ->
        let borrowed_expr' = helpE env borrowed_expr in
        let new_ref_name = rename_with_tag ref_name tag in
        EBorrow (
          borrowed_expr',
          new_ref_name,
          region,
          helpE ((ref_name, new_ref_name) :: env) body,
          tag
        )
  in
  helpP [] p
;;
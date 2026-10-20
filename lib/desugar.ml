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

let desugar (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s_%d" name !next
  in
  let rec helpBE bind =
    let b, e, btag = bind in
    let e = helpE e in
    match b with
    (* | BTuple (binds, ttag) -> (
      match e with
      | EId _ -> expandTuple binds ttag e
      | _ ->
          let newname = gensym "tup" in
          (BName (newname, false, ttag), e, btag) :: expandTuple binds ttag (EId (newname, ttag)) ) *)
    | _ -> [(b, e, btag)]
  (* and expandTuple binds tag source : sourcespan binding list =
    let tupleBind i b =
      match b with
      | BBlank _ -> []
      | BName (_, _, btag) ->
          [(b, EGetItem (source, ENumber (Int64.of_int i), tag), btag)]
      | BTuple (binds, tag) ->
          let newname = gensym "tup" in
          let newexpr = EId (newname, tag) in
          ( BName (newname, false, tag),
            EGetItem (source, ENumber (Int64.of_int i), tag),
            tag )
          :: expandTuple binds tag newexpr
    in
    let size_check =
      EPrim2 (CheckSize, source, ENumber (Int64.of_int (List.length binds)))
    in
    let size_check_bind = (BBlank dummy_span, size_check) in
    size_check_bind :: List.flatten (List.mapi tupleBind binds) *)
  and helpG g = List.map helpD g
  and helpImplD impl_d =
    match impl_d with
    | ImplDecl decl -> ImplDecl (helpD decl)
    | ImplPrim1 _ | ImplPrim2 _ -> impl_d
  and helpD d =
    match d with
    | DFun (name, generics, args, body, call_type, typ, tag) ->
        DFun (name, generics, args, Option.map helpE body, call_type, typ, tag)
    | DClass (name, params, supers, sigs, tag) ->
        DClass
          ( name,
            params,
            supers,
            List.map (fun s -> {s with ms_default= Option.map helpE s.ms_default}) sigs,
            tag )
    | DInstance (generics, head, methods, tag) ->
        DInstance (generics, head, List.map helpImplD methods, tag)
  and helpE e =
    match e with
    | ESeq (e1, e2, tag) -> ELet ([(BBlank tag, helpE e1, tag)], helpE e2, tag)
    | EId (x, tag) -> EId (x, tag)
    | ELiteral (n, tag) -> ELiteral (n, tag)
    | EPrim1 (op, body, tag) -> (
      match op with
      | _ when !desugar_overloaded_ops && Option.is_some (overloaded_prim1 op) ->
          let _, m = Option.get (overloaded_prim1 op) in
          EApp (EId (m, tag), [helpE body], tag)
      | Not -> EIf (helpE body, ELiteral (LitBool false, tag), ELiteral (LitBool true, tag), tag)
      | Add1 | Sub1 | Print | PrintStack | Neg | Deref | Ref -> EPrim1 (op, helpE body, tag) )
    | EPrim2 (op, left, right, tag) -> (
      match op with
      | _ when !desugar_overloaded_ops && Option.is_some (overloaded_prim2 op) ->
          let _, m = Option.get (overloaded_prim2 op) in
          EApp (EId (m, tag), [helpE left; helpE right], tag)
      | And -> EIf (helpE left, helpE right, ELiteral (LitBool false, tag), tag)
      | Or -> EIf (helpE left, ELiteral (LitBool true, tag), helpE right, tag)
      | Plus | Minus | Times | Divide | Greater | GreaterEq | Less | LessEq | Eq | CheckSize ->
          EPrim2 (op, helpE left, helpE right, tag) )
    | ELet (binds, body, tag) ->
        let newbinds = List.map helpBE binds in
        List.fold_right (fun binds body -> ELet (binds, body, tag)) newbinds (helpE body)
    (* | ELetRec (bindexps, body, tag) ->
        (* ASSUMES well-formed letrec, so only BName bindings *)
        let newbinds = List.map (fun (bind, e, tag) -> (bind, helpE e, tag)) bindexps in
        ELetRec (newbinds, helpE body, tag) *)
    | EIf (cond, thn, els, tag) -> EIf (helpE cond, helpE thn, helpE els, tag)
    | EApp (name, args, tag) -> EApp (helpE name, List.map helpE args, tag)
    | ETyApp (e, tys, tag) -> ETyApp (helpE e, tys, tag)
    | EBorrow (borrowed_expr, ref_name, region, body, tag) ->
        ELet
          ( [ ( BName
                  ( ref_name,
                    false,
                    TyApp
                      ( TyCon Reference,
                        [TyVar (gensym "T"); TyApp (TyCon Region, [TyCon (RegionName region)])] ),
                    tag ),
                helpE (EPrim1 (Ref, borrowed_expr, tag)),
                tag ) ],
            helpE body,
            tag )
    | EGetReference (body, tag) -> EGetReference (helpE body, tag)
    (* | ELambda (binds, body, tag) ->
        let expandBind bind =
          match bind with
          | BTuple (_, btag) ->
              let newparam = gensym "tuparg" in
              (BName (newparam, false, btag), helpBE (bind, EId (newparam, btag), btag))
          | _ -> (bind, [])
        in
        let params, newbinds = List.split (List.map expandBind binds) in
        let newbody =
          List.fold_right (fun binds body -> ELet (binds, body, tag)) newbinds (helpE body)
        in
        ELambda (params, newbody, tag) *)
    (* | EString (s, tag) ->
        let num_list = List.map (fun c -> ENumber (Int64.of_int (Char.code c), tag)) (explode s) in
        let nums_linked = List.fold_right (fun n l -> ETuple ([n; l], tag)) num_list (ENil tag) in
        helpE (EApp (EId ("String", tag), [nums_linked], Snake, tag)) *)
  in
  match p with
  | Program (decls, tag) -> Program (helpG decls, tag)
;;

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
  (* let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s_%d" name !next
  in *)
  let rec helpB (b : sourcespan bind) =
    match b with
    | BBlank _ ->
        b
    | BName (name, annotation, tag) ->
        BName (name, Option.map helpE annotation, tag)

  and helpBE (bind : sourcespan binding) =
    let b, e, btag = bind in
    let b' = helpB b in
    let e' = helpE e in
    (b', e', btag)

  and helpG (g : sourcespan decl list) =
    List.map helpD g

  and helpFP (FPName (name, typ, info, tag)) =
    FPName (name, helpE typ, info, tag)

  and helpFS (fs : sourcespan fun_sig) =
    {
      fs with
      fparams = List.map helpFP fs.fparams;
      fret_type = helpE fs.fret_type;
      fbody = Option.map helpE fs.fbody;
    }

  and helpImplD impl_d =
    match impl_d with
    | ImplDecl decl -> ImplDecl (helpD decl)
    | ImplPrim1 _ | ImplPrim2 _ -> impl_d

  and helpD (d : sourcespan decl) =
    match d with
    | DFun fs ->
        DFun (helpFS fs)

    | DClass (name, params, supers, sigs, tag) ->
        DClass (
          name,
          params,
          List.map helpE supers,
          List.map helpFS sigs,
          tag
        )

    | DInstance (generics, head, methods, tag) ->
        DInstance (
          List.map helpFP generics,
          helpE head,
          List.map helpImplD methods,
          tag
        )

  and helpE (e : sourcespan expr) : sourcespan expr =
    match e with
    | ESeq (e1, e2, tag) ->
        ELet ([(BBlank tag, helpE e1, tag)], helpE e2, tag)

    | EId _ ->
        e

    | ELiteral _ ->
        e

    | EPrim1 (op, body, tag) ->
        (match overloaded_prim1 op with
         | Some (_, method_name) ->
             EApp (EId (method_name, tag), [helpE body], tag)
         | None ->
             (match op with
              | Not ->
                  EIf (
                    helpE body,
                    ELiteral (LitBool false, tag),
                    ELiteral (LitBool true, tag),
                    tag
                  )
              | Neg | Deref | Ref ->
                  EPrim1 (op, helpE body, tag)))

    | EPrim2 (op, left, right, tag) ->
        (match overloaded_prim2 op with
         | Some (_, method_name) ->
             EApp (
               EId (method_name, tag),
               [helpE left; helpE right],
               tag
             )
         | None ->
             (match op with
              | And ->
                  EIf (
                    helpE left,
                    helpE right,
                    ELiteral (LitBool false, tag),
                    tag
                  )
              | Or ->
                  EIf (
                    helpE left,
                    ELiteral (LitBool true, tag),
                    helpE right,
                    tag
                  )
              | Plus | Minus | Times | Divide
              | Greater | GreaterEq | Less | LessEq | Eq ->
                  EPrim2 (op, helpE left, helpE right, tag)))

    | ELet (binds, body, tag) ->
        let newbinds = List.map helpBE binds in
        List.fold_right
          (fun bind body -> ELet ([bind], body, tag))
          newbinds
          (helpE body)

    | EIf (cond, thn, els, tag) ->
        EIf (helpE cond, helpE thn, helpE els, tag)

    | EApp (func, args, tag) ->
        EApp (helpE func, List.map helpE args, tag)

    | EBorrow (e_to_borrow, ref_name, region_name, body, tag) ->
      (* let region_name: region = RegionConstructor(), ref_name: ref<metavar, region_name> = prim1(ref, e) in body*)
        EBorrow (helpE e_to_borrow, ref_name, region_name, helpE body, tag)
  in
  match p with
  | Program (decls, tag) ->
      Program (helpG decls, tag)
;;

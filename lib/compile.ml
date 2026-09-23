open Printf
open Pretty
open Phases
open Exprs
open Errors
open Lexing
open Llvm
open Stdint
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

type 'a name_envt = (string * 'a) list

type 'a tag_envt = (tag * 'a) list

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

type scope_info = sourcespan * int option * int option

let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  let rec string_list_from_bind bind =
    match bind with
    | BName (name, _, tag) -> [(name, tag)]
    (* | BTuple (binds, _) -> List.concat (List.map string_list_from_bind binds) *)
    | BBlank _ -> []
  and binding_errs (scope_env, shadow_env, err_lst) x body_err =
    let adding_to_env = string_list_from_bind x in
    (* try
      let dups =
        let names = adding_to_env in
        List.map
          (fun (s, loc) ->
            let existing = List.assoc s shadow_env in
            DuplicateId (s, loc, existing) )
          names
      in *)
      (* (adding_to_env @ scope_env, adding_to_env @ shadow_env, err_lst @ dups @ body_err) *)
      (adding_to_env @ scope_env, adding_to_env @ shadow_env, err_lst @ body_err)
    (* with Not_found -> (adding_to_env @ scope_env, adding_to_env @ shadow_env, err_lst @ body_err) *)
  and wf_E_list e_lst env =
    let results = List.map (fun e -> wf_E e env) e_lst in
    List.fold_left List.append [] results
  and wf_E e env =
    match e with
    | ELiteral(LitBool(_), _) -> []
    | ELiteral (LitInt(n), loc) ->
        if (Int128.of_uint128 n) > (Int128.of_int32 Int32.max_int) || (Int128.of_uint128 n) < (Int128.of_int32 Int32.min_int) then
          [Overflow ((Int128.of_uint128 n), loc)]
        else
          []
    | EId (x, loc) -> (
      try
        ignore (List.assoc x env);
        []
      with Not_found -> [UnboundId (x, loc)] )
    | EPrim1 (_, e, _) -> wf_E e env
    | EPrim2 (_, l, r, _) -> wf_E_list [l; r] env
    | EIf (c, t, f, _) -> wf_E_list [c; t; f] env
    | ELet (binds, body, _) ->
        let env2, _, err_lst =
          List.fold_left
            (fun (scope_env, shadow_env, err_lst) (x, e, _) ->
              binding_errs (scope_env, shadow_env, err_lst) x (wf_E e scope_env) )
            (env, [], []) binds
        in
        err_lst @ wf_E body env2
    (* | EApp (_, args, Native, _) -> wf_E_list args env *)
    | EApp (closure, args, _, _) ->
        let fun_err = wf_E closure env in
        fun_err @ wf_E_list args env
    | ESeq (e1, e2, _) -> wf_E e1 env @ wf_E e2 env
  and wf_D d env (* other parameters may be needed here *) =
    match d with
    | DFun (_, args, body, _) ->
        let env2, _, args_err_lst =
          List.fold_left
            (fun (scope_env, shadow_env, args_err_lst) (x, loc) ->
              try
                let existing = List.assoc x shadow_env in
                let err = DuplicateId (x, loc, existing) in
                ((x, loc) :: scope_env, (x, loc) :: shadow_env, args_err_lst @ [err])
              with Not_found -> ((x, loc) :: scope_env, (x, loc) :: shadow_env, args_err_lst) )
            (env, [], [])
            (List.concat (List.map string_list_from_bind args))
        in
        let err_lst = args_err_lst @ wf_E body env2 in
        err_lst
  and wf_D_list decls env =
    let full_env = get_new_env decls in
    List.concat
      (List.mapi
         (fun i d ->
           match d with
           | DFun (name, _, _, loc) -> (
               let seq_env = full_env |> List.to_seq in
               let new_env =
                 Seq.append (Seq.take i seq_env) (Seq.drop (i + 1) seq_env) |> List.of_seq
               in
               let err_lst = wf_D d (full_env @ env) in
               try
                 let existing = List.assoc name new_env in
                 let err = DuplicateFun (name, loc, existing) in
                 [err] @ err_lst
               with Not_found -> err_lst )
          )
         decls )
  and get_new_env decls =
    match decls with
    | DFun (name, _, _, loc) :: rest -> (name, loc) :: get_new_env rest
    | [] -> []
  in
  match p with
  | Program (decls, _) -> (
      let rec helpP decls err_lst =
        (* let env = get_new_env decls in *)
        (wf_D_list decls [] @ err_lst)
      in
      let err_lst = helpP (decls) [] in
      match err_lst with
      | [] -> Ok p
      | _ -> Error err_lst )
;;


let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let compile_prog (prog: sourcespan program) : string =
  "finished"
;;

let compile_to_string (prog : sourcespan program pipeline) : string pipeline
    =
  prog
  |> add_err_phase well_formed is_well_formed
  |> add_phase result compile_prog
  (* prog *)
  (* |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase result compile_prog *)
;;
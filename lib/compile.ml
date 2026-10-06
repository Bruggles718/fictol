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
open Well_formed
open Desugar
open Typecheck
open Monomorphize
open Tag
open Anf
open Llvm_compile

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let compile_to_string (module_name : string) (prog : sourcespan program pipeline) : string pipeline
    =
  let context = global_context () in
  let the_module = create_module context module_name in
  let builder = builder context in
  prog
  |> add_phase type_names_resolved resolve_prog_typ_paths
  |> add_err_phase well_formed (fun p -> is_well_formed (add_builtins p))
  |> add_phase desugared desugar
  (* |> add_err_phase type_checked type_synth *)
  (* when ready: type_synth_tc here, then
     |> add_phase monomorphized monomorphize   (* new phase name in Phases *) *)
  |> add_err_phase type_checked type_synth_tc
  |> add_phase monomorphized monomorphize
  |> add_phase tagged tag_prog
  |> add_phase renamed rename
  |> add_phase anfed (fun p -> atag_prog (anf p))
  |> add_phase result (compile_prog context the_module builder)
;;
(* prog *)
(* |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase result compile_prog *)

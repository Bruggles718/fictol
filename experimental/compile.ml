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
open Builtins
(* open Compiler_common
open Well_formed
open Desugar
open Typecheck
open Monomorphize
open Tag
open Anf *)
(* open Llvm_compile *)

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let compile_prog prog = ""

let compile_to_string (module_name : string) (prog : sourcespan program pipeline) : string pipeline
    =
  (* let context = global_context () in
  let the_module = create_module context module_name in
  let builder = builder context in *)
  prog
  |> add_phase add_builtins_phase add_builtins
  (* |> add_err_phase well_formed is_well_formed *)
  (* |> add_phase desugared desugar *)
  (* |> add_phase desugared (fun p ->  desugar (untag_tag_span_prog (rename tag_other_gensym (tag_span_prog p)))) *)
  (* could potentially lead to confusing traces, but ultimately prevents shadowing built in 
    prim method names from breaking the program when desugaring. May try to think of a better solution to this. *)
  (* |> add_err_phase type_checked type_synth_tc
  |> add_phase monomorphized monomorphize
  |> add_phase tagged tag_span_typ_prog
  |> add_phase renamed (rename tag_other_gensym)
  |> add_phase anfed (fun p -> atag_prog (anf p)) *)
  |> add_phase result (compile_prog)
;;
(* prog *)
(* |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase result compile_prog *)

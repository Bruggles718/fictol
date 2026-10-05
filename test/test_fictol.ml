open Fictol.Compile
open Fictol.Runner
open OUnit2
open Fictol.Pretty
open Fictol.Exprs
open Fictol.Errors

let t name program input expected =
  name >:: test_run ~args:[] ~std_input:input program name expected
;;

let () = run_test_tt_main ("all_tests" >::: [input_file_test_suite ()])
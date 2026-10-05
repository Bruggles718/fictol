open Fictol.Compile
open Fictol.Runner
open OUnit2
open Fictol.Pretty
open Fictol.Exprs
open Fictol.Errors

let t name program input expected =
  name >:: test_run ~args:[] ~std_input:input ("extern \"C\" def test_entry() -> " ^ program) name expected
;;

let suite1 =
  "suite1"
  >::: [
    t "test_true" "bool: if true: true else: false" "" "1";
    t "test_false" "bool: if true: false else: true" "" "0";
    t "test_i32" "i32: 6 + 7" "" "13";
    t "test_u32" "u32: 5u32 + 5u32" "" "10";
    t "test_u8" "u8: 5u8 + 5u8" "" "10";
    t "test_u8_overflow" "u8: 255u8 + 5u8 + 5u8" "" "9";
    t "test_let" "i32: let x = 5 in let y = 7 in x + y" "" "12";
  ]

let () = run_test_tt_main ("all_tests" >::: [suite1; input_file_test_suite ()])
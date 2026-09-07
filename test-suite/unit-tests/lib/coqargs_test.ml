open OUnit
open Utest

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

let parse ?(init=Coqargs.default) args =
  fst (Coqargs.parse_args ~init args)

let first_args =
  [ "-I"; "ml-a"
  ; "-I"; "ml-b"
  ; "-R"; "."; "TestA"
  ; "-R"; "_build/default"; "TestB"
  ; "-load-vernac-source"; "first"
  ; "-load-vernac-source"; "second"
  ; "-set"; "Printing Depth=10"
  ; "-set"; "Printing Width=20"
  ]

let second_args =
  [ "-I"; "ml-c"
  ; "-R"; "theories"; "TestC"
  ; "-load-vernac-source"; "third"
  ; "-unset"; "Printing Depth"
  ]

let test_compositional () =
  let one_pass = parse (first_args @ second_args) in
  let split = parse ~init:(parse first_args) second_args in
  assert_equal one_pass split

let () = add_test "one-pass and incremental parsing agree" test_compositional

let test_empty_parse_identity () =
  let opts = parse (first_args @ second_args) in
  assert_equal opts (parse ~init:opts [])

let () = add_test "empty incremental parse preserves init" test_empty_parse_identity

let test_normalized_order () =
  let opts = parse (first_args @ second_args) in
  let expected_vo_includes : Coqargs.vo_path list =
    [ { implicit = true; unix_path = "."; rocq_path = "TestA" }
    ; { implicit = true; unix_path = "_build/default"; rocq_path = "TestB" }
    ; { implicit = true; unix_path = "theories"; rocq_path = "TestC" }
    ]
  in
  let expected_injections =
    [ Coqargs.OptionInjection (["Printing"; "Depth"], Coqargs.OptionSet (Some "10"))
    ; Coqargs.OptionInjection (["Printing"; "Width"], Coqargs.OptionSet (Some "20"))
    ; Coqargs.OptionInjection (["Printing"; "Depth"], Coqargs.OptionUnset)
    ]
  in
  assert_equal ["ml-a"; "ml-b"; "ml-c"] opts.pre.ml_includes;
  assert_equal expected_vo_includes opts.pre.vo_includes;
  assert_equal ["first.v"; "second.v"; "third.v"] opts.pre.load_vernacular_list;
  assert_equal expected_injections opts.pre.injections

let () = add_test "ordered options are returned in declaration order" test_normalized_order

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (List.rev !tests)

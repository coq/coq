open OUnit

(* general case to build a test *)
let mk_test nm test = nm >: test

(* common cases for building tests *)
let mk_eq_test nm descr expected actual =
  mk_test nm (TestCase (fun _ -> assert_equal ~msg:descr expected actual))

let mk_bool_test nm descr actual =
  mk_test nm (TestCase (fun _ -> assert_bool descr actual))

let cfprintf oc = Printf.(kfprintf (fun oc -> fprintf oc "\n%!") oc)

(* given test result, print message, return success boolean *)
let logger out_ch result =
  let cprintf s = cfprintf out_ch s in
  match result with
  | RSuccess path ->
     cprintf "TEST SUCCEEDED: %s" (string_of_path path);
     true
  | RError (path,msg)
  | RFailure (path,msg) ->
     cprintf "TEST FAILED: %s (%s)" (string_of_path path) msg;
     false
  | RSkip (path,msg)
  | RTodo (path,msg) ->
     cprintf "TEST DID NOT SUCCEED: %s (%s)" (string_of_path path) msg;
     false

(* run one OUnit test case, return successes, no. of tests *)
(* notionally one test, which might be a TestList *)
let run_one logit test =
  let rec process_results rs =
    match rs with
      [] -> (0,0)
    | (r::rest) ->
       let succ = if logit r then 1 else 0 in
       let succ_results,tot_results = process_results rest in
       (succ + succ_results,tot_results + 1)
  in
  let results = perform_test (fun _ -> ()) test in
  process_results results

let open_log_out_ch ml_fn =
  let log_fn = ml_fn ^ ".log" in
  open_out log_fn

(* run list of OUnit test cases, log results *)
let run_tests ml_fn out_ch tests =
  let cprintf s = cfprintf out_ch s in
  let ceprintf s = cfprintf stderr s in
  let logit = logger out_ch in
  let rec run_some tests succ tot =
    match tests with
      [] -> (succ,tot)
    | (t::ts) ->
       let succ_one,tot_one = run_one logit t in
       run_some ts (succ + succ_one) (tot + tot_one)
  in
  (* format for test-suite summary to find status
     success if all tests succeeded, else failure
   *)
  let succ,tot = run_some tests 0 0 in
  cprintf
      "*** Ran %d tests, with %d successes and %d failures ***"
      tot succ (tot - succ);
  if succ = tot then
    cprintf
      "==========> SUCCESS <==========\n    %s...Ok" ml_fn
  else begin
    cprintf
      "==========> FAILURE <==========\n    %s...Error!" ml_fn;
    ceprintf "FAILED    %s.log" ml_fn
  end;
  close_out out_ch

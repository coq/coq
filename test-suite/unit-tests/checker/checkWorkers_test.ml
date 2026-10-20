(* Deferred checks run by CheckWorkers in forked workers, with a time
   budget: a worker that stops early gives back the rest of its batch,
   and every check still runs exactly once. *)

open OUnit
open Utest
open Coq_checklib

let tests = ref []
let add_test name test = tests := mk_test name (TestCase test) :: !tests

(* Constant number [i]. *)
let constant i =
  let open Names in
  Constant.make2
    (ModPath.MPfile (DirPath.make [Id.of_string "CheckWorkersTest"]))
    (Id.of_string (Printf.sprintf "c%d" i))

(* Each check appends one line "pid index\n" to a file shared by all the
   processes: an append of one line is atomic, so the file says which
   process ran which check, and in which order. *)
let with_log f =
  let name = Filename.temp_file "checkworkers" ".log" in
  let fd = Unix.openfile name [Unix.O_WRONLY; Unix.O_APPEND] 0o600 in
  let finally () = Unix.close fd; Sys.remove name in
  Fun.protect ~finally (fun () ->
      let read () =
        let ic = open_in name in
        let rec lines acc =
          match input_line ic with
          | l -> Scanf.sscanf l "%d %d" (fun p i -> lines ((p, i) :: acc))
          | exception End_of_file -> close_in ic; List.rev acc
        in
        lines []
      in
      f fd read)

let record fd i =
  let line = Printf.sprintf "%d %d\n" (Unix.getpid ()) i in
  assert (Unix.write_substring fd line 0 (String.length line) = String.length line)

(* [n] deferred checks, [-j jobs], then [finish]. A check [refuse] raises;
   check [i] records itself, then runs [work i]. Returns the log, or the
   exception that [defer] or [finish] raised (after [abort], as the
   checker does).

   The checks are deferred within a fraction of a second, less than the
   dispatch window, unless [windows] is given: the checks are then cut
   into [windows] equal parts, and before the last check of each part
   the main process sleeps past the window, so that deferring that check
   deals batches as while the libraries are checked. [before_finish] is
   given the log reader after the last [defer]. *)
let run ?(jobs = 2) ?refuse ?(work = fun _ -> ()) ?(windows = 0)
    ?(before_finish = fun _ -> ()) ~budget n =
  with_log (fun fd read ->
      CheckWorkers.set_jobs ~profiling:false jobs;
      CheckWorkers.set_budget budget;
      Fun.protect
        ~finally:(fun () ->
            CheckWorkers.set_jobs ~profiling:false 1;
            CheckWorkers.set_budget CheckWorkers.default_budget)
        (fun () ->
           let part = if windows = 0 then 0 else n / windows in
           let result =
             try
               for i = 0 to n - 1 do
                 if part > 0 && i mod part = part - 1 then Unix.sleepf 1.05;
                 CheckWorkers.defer (constant i) (fun () ->
                     if Some i = refuse then failwith "refused";
                     record fd i;
                     work i)
               done;
               before_finish read;
               CheckWorkers.finish (); None
             with e -> CheckWorkers.abort (); Some e
           in
           (* No worker is left behind. *)
           (match Unix.waitpid [Unix.WNOHANG] (-1) with
            | exception Unix.Unix_error (Unix.ECHILD, _, _) -> ()
            | _ -> assert_failure "a worker was left behind");
           result, read ()))

let me = Unix.getpid ()

let assert_exactly_once n log =
  let seen = Array.make n 0 in
  List.iter (fun (_, i) -> seen.(i) <- seen.(i) + 1) log;
  Array.iteri (fun i c ->
      if c <> 1 then
        assert_failure (Printf.sprintf "check %d ran %d times" i c))
    seen

let workers_of log = List.filter (fun (p, _) -> p <> me) log

let checks_of p log = List.filter_map (fun (q, i) -> if q = p then Some i else None) log

let pids_of log = List.sort_uniq compare (List.map fst (workers_of log))

(* The batches [finish] deals to [slots] workers from [queue] when no
   worker stops early, in order: each has [ceil (r / (2 * slots))] checks
   taken one in [r / size] from the front of the [r] that remain, and the
   checks not taken stay in front, in order. *)
let finish_batches ~slots queue =
  let rec go acc queue =
    match queue with
    | [] -> List.rev acc
    | _ ->
      let r = List.length queue in
      let size = (r + 2 * slots - 1) / (2 * slots) in
      let lanes = max 1 (r / size) in
      let taken = min r (lanes * size) in
      let batch = List.filteri (fun i _ -> i < taken && i mod lanes = 0) queue in
      let rest = List.filteri (fun i _ -> not (i < taken && i mod lanes = 0)) queue in
      go (batch :: acc) rest
  in
  go [] queue

let expected_batches ~slots n = finish_batches ~slots (List.init n Fun.id)

(* The [k] batches of [size] checks dealt from [queue] while the libraries
   are checked, and what stays queued: when the queue holds [s >= k]
   batches of [size], batch [j] takes the checks at positions [j], [j + s],
   [j + 2s]... of the first [s * size], and its worker checks them newest
   first. *)
let library_batches ~k ~size queue =
  let s = max k (List.length queue / size) in
  let taken i = i < s * size && i mod s < k in
  let batch j = List.rev (List.filteri (fun i _ -> taken i && i mod s = j) queue) in
  List.init k batch, List.filteri (fun i _ -> not (taken i)) queue

let n = 200

let assert_no_exception = function
  | None -> ()
  | Some e -> assert_failure ("unexpected " ^ Printexc.to_string e)

(* The main process only queues and deals checks, and waits for workers:
   it checks a proof itself only when it cannot fork. *)
let assert_main_checked_nothing log =
  if List.exists (fun (p, _) -> p = me) log then
    assert_failure "the main process checked a proof"

let pr_batches l = String.concat "; " (List.map (fun b -> String.concat "," (List.map string_of_int b)) l)

(* Each worker checked exactly one of [expected], in its order. *)
let assert_batches expected log =
  let got = List.sort compare (List.map (fun p -> checks_of p log) (pids_of log)) in
  assert_equal ~printer:pr_batches (List.sort compare expected) got

let assert_batches_as_documented ~slots n log = assert_batches (expected_batches ~slots n) log

let () = add_test "no early stop: every check runs once" (fun () ->
    let result, log = run ~budget:CheckWorkers.default_budget n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_main_checked_nothing log;
    assert_batches_as_documented ~slots:2 n log)

(* Fewer than 2N x 10 checks left: they are still dealt to workers, down
   to batches of one check. *)
let () = add_test "few checks left: all dealt, in batches as documented" (fun () ->
    let result, log = run ~jobs:4 ~budget:CheckWorkers.default_budget 30 in
    assert_no_exception result;
    assert_exactly_once 30 log;
    assert_main_checked_nothing log;
    assert_batches_as_documented ~slots:4 30 log;
    assert_bool "batches of one check" (List.exists (fun p -> List.length (checks_of p log) = 1) (pids_of log)))

(* [k] checks that each wait until all [k] have started, so [k] workers
   run at once and end at about the same time. *)
let meeting k f =
  let dir = Filename.temp_file "checkworkers" ".meet" in
  Sys.remove dir;
  Unix.mkdir dir 0o700;
  let meet i =
    close_out (open_out (Filename.concat dir (string_of_int i)));
    let deadline = Unix.gettimeofday () +. 10. in
    while Array.length (Sys.readdir dir) < k do
      if Unix.gettimeofday () > deadline then failwith "checked alone";
      Unix.sleepf 0.01
    done
  in
  let clear () = Array.iter (fun f -> Sys.remove (Filename.concat dir f)) (Sys.readdir dir) in
  Fun.protect ~finally:(fun () -> clear (); Sys.rmdir dir) (fun () -> f meet clear)

(* With -j 2, two workers run at once after the libraries. *)
let () = add_test "after the libraries, N workers run at once" (fun () ->
    meeting 2 (fun meet _ ->
        let result, log = run ~jobs:2 ~budget:CheckWorkers.default_budget ~work:meet 2 in
        assert_no_exception result;
        assert_exactly_once 2 log;
        assert_main_checked_nothing log;
        assert_equal ~printer:string_of_int 2 (List.length (pids_of log))))

(* Workers dealt by [finish] that end together are all reaped, whichever
   way the main process sees them end, and it then stops waiting. *)
let () = add_test "workers dealt by finish that end together are all reaped" (fun () ->
    meeting 4 (fun meet clear ->
        for _ = 1 to 30 do
          clear ();
          let result, log = run ~jobs:4 ~budget:CheckWorkers.default_budget ~work:meet 4 in
          assert_no_exception result;
          assert_exactly_once 4 log;
          assert_main_checked_nothing log
        done))

(* Budget 0: a worker completes one check and stops, so the checking
   progresses and ends, and what the workers did not do is checked again
   exactly once, by a later worker. *)
let () = add_test "budget 0: each worker completes one check, all run once" (fun () ->
    let result, log = run ~budget:0. n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_main_checked_nothing log;
    let pids = pids_of log in
    assert_bool "workers ran" (pids <> []);
    List.iter (fun p -> assert_equal ~printer:string_of_int 1 (List.length (checks_of p log))) pids)

(* A budget that expires while a worker is in its batch. *)
let () = add_test "short budget: every check runs once" (fun () ->
    let result, log = run ~budget:0.05 ~work:(fun _ -> Unix.sleepf 0.02) n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_main_checked_nothing log;
    List.iter (fun p ->
        let k = List.length (checks_of p log) in
        assert_bool "a worker that stops has completed at least one check" (k >= 1);
        assert_bool "a worker stops once its budget has passed" (k < 50))
      (pids_of log))

(* The first worker overruns its budget on its first check and gives the
   rest of its batch back while many checks are still queued behind it
   (each takes some time, so the other worker cannot drain them first).
   The next check [a] of that batch is long: it lasts until the check [b]
   after it has started. So [b] must not wait behind [a], in the same
   batch: it goes to another batch, checked by another worker while [a]
   is being checked. *)
let () = add_test "re-queued tail with a long head: the check after it does not wait" (fun () ->
    let n = 400 in
    let first = List.hd (expected_batches ~slots:2 n) in
    let a = List.nth first 1 and b = List.nth first 2 in
    let started = Filename.temp_file "checkworkers" ".started" in
    Sys.remove started;
    let work i =
      if i = 0 then Unix.sleepf 0.1
      else if i = b then close_out (open_out started)
      else if i = a then begin
        let deadline = Unix.gettimeofday () +. 10. in
        while not (Sys.file_exists started) do
          if Unix.gettimeofday () > deadline then failwith "waited behind the long check";
          Unix.sleepf 0.01
        done
      end
      else Unix.sleepf 0.005
    in
    let finally () = if Sys.file_exists started then Sys.remove started in
    Fun.protect ~finally (fun () ->
        let result, log = run ~budget:0.05 ~work n in
        assert_no_exception result;
        assert_exactly_once n log;
        assert_main_checked_nothing log;
        let by i = fst (List.find (fun (_, j) -> j = i) log) in
        assert_bool "the overrun worker stopped after its first check" (checks_of (by 0) log = [0]);
        assert_bool "the long check and the one after it went to different workers" (by a <> by b)))

let () = add_test "several workers, budget 0: every check runs once" (fun () ->
    let result, log = run ~jobs:4 ~budget:0. n in
    assert_no_exception result;
    assert_exactly_once n log;
    assert_main_checked_nothing log)

(* A refusal behaves as with a worker that is not stopped: the worker that
   checks the proof exits with its error code and the main process raises
   WorkerFailed. The main process checks no proof itself, so it never
   raises CheckError here. *)
let assert_refusal = function
  | Some (CheckWorkers.WorkerFailed (_, Unix.WEXITED c, b)) ->
    assert_bool "exit code of the error" (c <> 0);
    assert_bool "batch size" (b.CheckWorkers.size >= 1)
  | Some e -> assert_failure ("unexpected " ^ Printexc.to_string e)
  | None -> assert_failure "the refusal was lost"

let () = add_test "refusal in the re-queued tail surfaces" (fun () ->
    (* With budget 0 the proof, deep in a batch, is only reached once the
       batch has been given back. *)
    let result, log = run ~budget:0. ~refuse:150 n in
    assert_refusal result;
    assert_bool "the refused check did not record itself"
      (not (List.exists (fun (_, i) -> i = 150) log)))

let () = add_test "refusal surfaces without early stop" (fun () ->
    let result, _ = run ~budget:CheckWorkers.default_budget ~refuse:150 n in
    assert_refusal result)

let () = add_test "refusal surfaces, several workers" (fun () ->
    let result, _ = run ~jobs:4 ~budget:0. ~refuse:150 n in
    assert_refusal result)

(* Batches dealt by [defer] while the libraries are checked (see the
   [windows] argument of [run]): a batch is a stride of the queue that its
   worker checks newest first, and what the worker does not check goes
   back to the front in the order it would have checked it. *)

(* The log once it holds [k] records, while the main process waits
   before [finish], so that only the batches dealt by [defer] run. *)
let wait_records read k =
  let deadline = Unix.gettimeofday () +. 10. in
  let rec go () =
    let log = read () in
    if List.length log >= k then log
    else if Unix.gettimeofday () > deadline then
      assert_failure (Printf.sprintf "%d checks recorded, %d expected" (List.length log) k)
    else (Unix.sleepf 0.01; go ())
  in
  go ()

let heads read k = List.sort compare (List.map snd (wait_records read k))

(* -j 2: 201 checks, one batch of 101 dealt while the libraries are
   checked (positions 0 to 100), the 100 others by [finish]. *)
let () = add_test "libraries, no early stop: one batch, newest first, then finish" (fun () ->
    let result, log = run ~jobs:2 ~windows:1 ~budget:CheckWorkers.default_budget 201 in
    assert_no_exception result;
    assert_exactly_once 201 log;
    assert_main_checked_nothing log;
    let lib, rest = library_batches ~k:1 ~size:101 (List.init 201 Fun.id) in
    assert_equal ~printer:pr_batches [List.init 101 (fun i -> 100 - i)] lib;
    assert_batches (lib @ finish_batches ~slots:2 rest) log)

(* -j 4: three strided batches of 51 (checks 0, 3... 150; 1, 4... 151;
   2, 5... 152), then [finish] deals the 48 others. *)
let () = add_test "libraries, no early stop: strided batches, newest first, then finish" (fun () ->
    let result, log = run ~jobs:4 ~windows:1 ~budget:CheckWorkers.default_budget 201 in
    assert_no_exception result;
    assert_exactly_once 201 log;
    assert_main_checked_nothing log;
    let lib, rest = library_batches ~k:3 ~size:51 (List.init 201 Fun.id) in
    assert_equal ~printer:pr_batches
      (List.init 3 (fun j -> List.init 51 (fun i -> 150 + j - 3 * i))) lib;
    assert_batches (lib @ finish_batches ~slots:4 rest) log)

(* Budget 0: the worker of each batch dealt while the libraries are
   checked completes only the newest check of its batch, then gives the
   others back, and they are all still checked exactly once. *)
let () = add_test "libraries, budget 0: the newest check heads its batch, -j 2" (fun () ->
    let before_finish read =
      assert_equal ~printer:pr_batches [[100]] [heads read 1] in
    let result, log = run ~jobs:2 ~windows:1 ~before_finish ~budget:0. 201 in
    assert_no_exception result;
    assert_exactly_once 201 log;
    assert_main_checked_nothing log)

let () = add_test "libraries, budget 0: the newest checks head the strided batches, -j 4" (fun () ->
    let before_finish read =
      assert_equal ~printer:pr_batches [[150; 151; 152]] [heads read 3] in
    let result, log = run ~jobs:4 ~windows:1 ~before_finish ~budget:0. 201 in
    assert_no_exception result;
    assert_exactly_once 201 log;
    assert_main_checked_nothing log)

(* Batches dealt in three windows, while the workers of earlier ones may
   still run or have given checks back. *)
let () = add_test "libraries, budget 0, three windows: every check runs once" (fun () ->
    let result, log = run ~jobs:3 ~windows:3 ~budget:0. 450 in
    assert_no_exception result;
    assert_exactly_once 450 log;
    assert_main_checked_nothing log;
    List.iter (fun p -> assert_equal ~printer:string_of_int 1 (List.length (checks_of p log))) (pids_of log))

let () = add_test "libraries, short budget, three windows: every check runs once" (fun () ->
    let result, log = run ~jobs:4 ~windows:3 ~budget:0.05 ~work:(fun _ -> Unix.sleepf 0.01) 600 in
    assert_no_exception result;
    assert_exactly_once 600 log;
    assert_main_checked_nothing log;
    List.iter (fun p ->
        let k = List.length (checks_of p log) in
        assert_bool "a worker that stops has completed at least one check" (k >= 1);
        assert_bool "a worker stops once its budget has passed" (k < 50))
      (pids_of log))

(* Check 150 heads the first batch dealt at -j 4: its worker fails on it,
   and the batch it reports is that one. *)
let () = add_test "libraries: refusal in a batch surfaces" (fun () ->
    let result, log = run ~jobs:4 ~windows:1 ~budget:CheckWorkers.default_budget ~refuse:150 201 in
    assert_refusal result;
    (match result with
     | Some (CheckWorkers.WorkerFailed (_, _, b)) ->
       assert_bool "the batch is the one headed by the refused check"
         (Names.Constant.CanOrd.equal b.CheckWorkers.first (constant 150) && b.CheckWorkers.size = 51)
     | _ -> ());
    assert_bool "the refused check did not record itself"
      (not (List.exists (fun (_, i) -> i = 150) log)))

(* Check 120 is deep in a batch dealt while the libraries are checked:
   with budget 0 it is only reached from checks given back. *)
let () = add_test "libraries, budget 0, three windows: refusal surfaces" (fun () ->
    let result, log = run ~jobs:4 ~windows:3 ~budget:0. ~refuse:120 450 in
    assert_refusal result;
    assert_bool "the refused check did not record itself"
      (not (List.exists (fun (_, i) -> i = 120) log)))

(* A worker that has ended and not been reaped. Needs /proc. *)
let zombie pid =
  let ic = open_in (Printf.sprintf "/proc/%d/stat" pid) in
  let l = Fun.protect ~finally:(fun () -> close_in ic) (fun () -> input_line ic) in
  l.[String.rindex l ')' + 2] = 'Z'

(* Workers that end together are all reaped, and then [finish] stops
   waiting. At -j 3, 100 checks are dealt in two batches of 50 while the
   libraries are checked, and none is left for [finish] to deal. Both
   workers have ended when [finish] starts, so its first look at them
   reaps the last one. *)
let () = if Sys.file_exists "/proc/self/stat" then add_test "workers that end together are all reaped" (fun () ->
    let before_finish read =
      let log = wait_records read 100 in
      assert_equal ~printer:string_of_int 2 (List.length (pids_of log));
      let deadline = Unix.gettimeofday () +. 10. in
      while not (List.for_all zombie (pids_of log)) do
        if Unix.gettimeofday () > deadline then assert_failure "a worker did not end";
        Unix.sleepf 0.01
      done
    in
    let result, log = run ~jobs:3 ~windows:1 ~before_finish ~budget:CheckWorkers.default_budget 100 in
    assert_no_exception result;
    assert_exactly_once 100 log;
    assert_main_checked_nothing log)

(* The report is the one thing the main process believes about what a
   worker did not do: anything but a well-formed count in [1, size],
   together with a normal exit, fails the batch. *)
let with_writer w f =
  CheckWorkers.set_report_writer w;
  Fun.protect ~finally:(fun () ->
      CheckWorkers.set_report_writer CheckWorkers.default_report_writer) f

let assert_worker_failed ?status writer =
  with_writer writer (fun () ->
      let result, _ = run ~budget:CheckWorkers.default_budget n in
      match result, status with
      | Some (CheckWorkers.WorkerFailed (_, s, b)), expected ->
        assert_bool "batch is not empty" (b.CheckWorkers.size >= 1);
        Option.iter (fun e -> assert_bool "status" (e = s)) expected
      | Some e, _ -> assert_failure ("unexpected " ^ Printexc.to_string e)
      | None, _ -> assert_failure "no failure")

let write_raw fd s = ignore (Unix.write_substring fd s 0 (String.length s))

let count_bytes k =
  let b = Bytes.create 8 in
  Bytes.set_int64_be b 0 k;
  Bytes.to_string b

let () = add_test "no report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun _ _ -> ()))

let () = add_test "short report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun fd _ -> write_raw fd "abcd"))

let () = add_test "long report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun fd c -> write_raw fd (count_bytes (Int64.of_int c) ^ "x")))

let () = add_test "report of 0 fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun fd _ -> write_raw fd (count_bytes 0L)))

let () = add_test "negative report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun fd _ -> write_raw fd (count_bytes (-1L))))

let () = add_test "report above the batch size fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0)
      (fun fd _ -> write_raw fd (count_bytes (Int64.of_int 1_000_000))))

let () = add_test "huge report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 0) (fun fd _ -> write_raw fd (count_bytes Int64.max_int)))

let () = add_test "report off by one above the batch size fails the worker" (fun () ->
    (* The batch is [n / stride] = 50 checks. *)
    assert_worker_failed ~status:(Unix.WEXITED 0)
      (fun fd c -> write_raw fd (count_bytes (Int64.of_int (c + 1)))))

let () = add_test "exit code 7 after a good report fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 7)
      (fun fd c -> CheckWorkers.default_report_writer fd c; Unix._exit 7))

let () = add_test "kill after a good report fails the worker" (fun () ->
    assert_worker_failed
      (fun fd c -> CheckWorkers.default_report_writer fd c; Unix.kill (Unix.getpid ()) Sys.sigkill))

let () = add_test "raise while reporting fails the worker" (fun () ->
    assert_worker_failed ~status:(Unix.WEXITED 3) (fun _ _ -> failwith "no report"))

let () = add_test "a good report is accepted" (fun () ->
    with_writer CheckWorkers.default_report_writer (fun () ->
        let result, log = run ~budget:CheckWorkers.default_budget n in
        assert_no_exception result;
        assert_exactly_once n log))

(* Every test above forks. *)
let fork_tests = if Sys.unix then List.rev !tests else []

let budget_test = mk_test "negative budget is refused" (TestCase (fun () ->
    assert_raises (Invalid_argument "CheckWorkers.set_budget") (fun () -> CheckWorkers.set_budget (-1.));
    assert_raises (Invalid_argument "CheckWorkers.set_budget") (fun () -> CheckWorkers.set_budget nan)))

(* With -j 1, when profiling, and where [Unix.fork] is not available,
   [defer] runs each check at once, in the main process, in order, and a
   refusal is the check's own exception, as without -j. *)
let assert_sequential ~jobs ~profiling =
  CheckWorkers.set_jobs ~profiling jobs;
  Fun.protect ~finally:(fun () -> CheckWorkers.set_jobs ~profiling:false 1) (fun () ->
      let ran = ref [] in
      for i = 0 to 9 do
        CheckWorkers.defer (constant i) (fun () -> ran := i :: !ran);
        assert_equal ~printer:string_of_int (i + 1) (List.length !ran)
      done;
      CheckWorkers.finish ();
      assert_equal ~printer:pr_batches [List.init 10 Fun.id] [List.rev !ran];
      assert_raises (Failure "refused") (fun () ->
          CheckWorkers.defer (constant 10) (fun () -> failwith "refused")))

let sequential_tests = [
  mk_test "-j 1: every check runs at once, in the main process"
    (TestCase (fun () -> assert_sequential ~jobs:1 ~profiling:false));
  mk_test "-j 4 when profiling: every check runs at once, in the main process"
    (TestCase (fun () -> assert_sequential ~jobs:4 ~profiling:true));
  (* On Unix this is the -j 4 case of the tests above. *)
  mk_test "-j 4 without fork: every check runs at once, in the main process"
    (TestCase (fun () -> if not Sys.unix then assert_sequential ~jobs:4 ~profiling:false));
]

let () = run_tests __FILE__ (open_log_out_ch __FILE__) (budget_test :: sequential_tests @ fork_tests)

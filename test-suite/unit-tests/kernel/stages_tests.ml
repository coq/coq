open Utest
open Util
open Stages
open SVars
open Stage
open Annot
open Constraints

let log_out_ch = open_log_out_ch __FILE__

(** Helpers for debugging *)

let str_tuple (a, b, c) = "(" ^ string_of_int a ^ "," ^ string_of_int b ^ "," ^ string_of_int c ^ ")"
let str_list_tuple lst = "[;" ^ List.fold_right (fun tup str -> str_tuple tup ^ ";" ^ str) lst "]"
let str_int_set set = "{," ^ SVars.fold (fun i str -> string_of_int i ^ "," ^ str) set "}"

let debug = Printf.printf "%s\n"

(* Testing constants *)

let test_prefix = "kernel-stages_test"

let inf = -1

let s0_0 = Stage (StageVar (0, 0))
let s0_1 = Stage (StageVar (0, 1))
let s2_0 = Stage (StageVar (2, 0))
let s5_0 = Stage (StageVar (5, 0))
let s9_0 = Stage (StageVar (9, 0))
let s9_1 = Stage (StageVar (9, 1))

let s0_0_and_s9_1 = (add s0_0 s9_1 empty)
let s9_0_and_s0_1 = (add s9_0 s0_1 empty)
let s0_1_and_s9_0 = (add s0_1 s9_0 empty)
let s9_1_and_s0_0 = (add s9_1 s0_0 empty)

let pos_cycle = union s0_0_and_s9_1 s9_0_and_s0_1
let pos_cycle_bigger =
  let cstrnts1 = add s0_0 s2_0 empty in
  let cstrnts2 = add s2_0 s9_1 cstrnts1 in
  add s9_0 s0_1 cstrnts2
let neg_cycle = union s0_1_and_s9_0 s9_1_and_s0_0
let neg_cycle_bigger =
  let cstrnts1 = add s0_1 s9_0 empty in
  let cstrnts2 = add s9_1 s5_0 cstrnts1 in
  add s5_0 s0_0 cstrnts2
let neg_cycle_extra1 =
  add s2_0 s0_0 neg_cycle_bigger
let neg_cycle_extra2 =
  add s0_0 s2_0 neg_cycle_bigger

(* Constraints tests *)

let add_prefix = test_prefix ^ "-add"
let add_name i = add_prefix ^ string_of_int i

let add1 = mk_eq_test
  (add_name 1)
  "s0⊑s0+1 not added"
  empty
  (add s0_0 s0_1 empty)
let add2 = mk_eq_test
  (add_name 2)
  "s0⊑∞ not added"
  empty
  (add s0_0 infty empty)
let add3 = mk_bool_test
  (add_name 3)
  "s0+1⊑s0 is added"
  (contains (0, 0) (add s0_1 s0_0 empty))
let add4 = mk_bool_test
  (add_name 4)
  "∞⊑s0 is added"
  (contains (inf, 0) (add infty s0_0 empty))
let add5 = mk_bool_test
  (add_name 5)
  "s9⊑s0 is added"
  (contains (9, 0) (add s9_0 s0_0 empty))
let add6 = mk_bool_test
  (add_name 6)
  "s9+1⊑s0+1 is added"
  (contains (9, 0) (add s9_1 s0_1 empty))
let add7 = mk_bool_test
  (add_name 7)
  "adding s0⊑s9 does not add s9⊑s0"
  (not (contains (9, 0) (add s0_0 s9_0 empty)))
let add_tests = [add1; add2; add3; add4; add5; add6]

let fold1 =
  let f vfrom vto wt lst = (vfrom, vto, wt) :: lst in
  let cstrnts_list = fold f pos_cycle [] in
  mk_bool_test
    (test_prefix ^ "-fold1")
    "folding constraints works"
    (List.mem (0, 9, 1) cstrnts_list && List.mem (9, 0, 1) cstrnts_list)
let fold_tests = [fold1]

let filter1 =
  let f vfrom vto wt = Int.equal 9 vto in
  let cstrnts = filter f pos_cycle in
  mk_bool_test
    (test_prefix ^ "-filter1")
    "filtering constraints works"
    (contains (0, 9) cstrnts && not (contains (9, 0) cstrnts))
let filter_tests = [filter1]

let sup1 =
  let cstrnts = add s5_0 s9_0 (add s5_0 s0_0 empty) in
  let sups = sup 5 cstrnts in
  mk_bool_test
    (test_prefix ^ "-sup1")
    "sup returns all superstages"
    (mem 0 sups && mem 9 sups)
let sup_tests = [sup1]

let sub1 =
  let cstrnts = add s9_0 s5_0 (add s0_0 s5_0 empty) in
  let subs = sub 5 cstrnts in
  mk_bool_test
    (test_prefix ^ "-sub1")
    "sup returns all substages"
    (mem 0 subs && mem 9 subs)
let sub_tests = [sub1]

(* RecCheck helper tests *)

let bf_prefix = test_prefix ^ "-bf"
let bf_name i = add_prefix ^ string_of_int i

let bf1 = mk_eq_test
  (bf_name 1)
  "Bellman-Ford returns empty set for positive size 2 cycle"
  SVars.empty
  (bellman_ford_all pos_cycle)
let bf2 = mk_eq_test
  (bf_name 2)
  "Bellman-Ford returns empty set for positive size 3 cycle"
  SVars.empty
  (bellman_ford_all pos_cycle_bigger)
let bf3 = mk_bool_test
  (bf_name 3)
  "Bellman-Ford returns nonempty set for negative size 2 cycle"
  (not (is_empty (bellman_ford_all neg_cycle)))
let bf4 = mk_bool_test
  (bf_name 4)
  "Bellman-Ford returns nonempty set for negative size 3 cycle"
  (not (is_empty (bellman_ford_all neg_cycle_bigger)))
let bf5 = mk_bool_test
  (bf_name 5)
  "Bellman-Form returns nonempty set for size 3 cycle without vertices NOT in cycle"
  (let vs = bellman_ford_all neg_cycle_extra1 in
  (not (is_empty vs) && not (mem 2 vs)))
let bellman_ford_tests = [bf1; bf2; bf3; bf4; bf5]

let upward_closure =
  let up = upward neg_cycle_extra1 (SVars.add 0 SVars.empty) in
  mk_bool_test
    (test_prefix ^ "-upward_closure")
    "upward closure from s0"
    (List.for_all (fun var -> mem var up) [0; 5; 9])
let downward_closure =
  let down = downward neg_cycle_extra2 (SVars.add 0 SVars.empty) in
  mk_bool_test
    (test_prefix ^ "-downward_closure")
    "downward closure from s0"
    (List.for_all (fun var -> mem var down) [0; 5; 9])
let closure_tests = [upward_closure; downward_closure]

(* RecCheck tests
  The constraints come from the Haskell cicminus implementation *)

let mkStage nm sz = Stage (StageVar (nm, sz))

let svars_of_list lst =
  List.fold_right SVars.add lst SVars.empty

let constraints_of_list lst =
  List.fold_right (fun (vfrom, vto) -> add vfrom vto) lst empty

let rec_check_lists_pass alpha vstarl vneql cstrntsl =
  try
    let _ = rec_check alpha (svars_of_list vstarl) (svars_of_list vneql) (constraints_of_list cstrntsl)
    in true
  with RecCheckFailed _ -> false

let rec_check_lists_fail alpha vstarl vneql cstrnts =
  not (rec_check_lists_pass alpha vstarl vneql cstrnts)

let rc_prefix = test_prefix ^ "-rec_check-"
let rc_name str = rc_prefix ^ str

let rec_check_plus =
  let cstrnts =
    [ mkStage 1 0, mkStage 4 0
    ; mkStage 2 0, mkStage 5 0
    ; mkStage 3 0, mkStage 0 0
    ; mkStage 4 0, mkStage 2 0
    ; mkStage 5 1, mkStage 4 0
    ] in
  mk_bool_test
    (rc_name "plus")
    "constraints for plus are satisfiable"
    (rec_check_lists_pass 0 [0] [1; 2] cstrnts)

let rec_check_minus =
  let cstrnts =
    [ mkStage  6 1, mkStage 13 0
    ; mkStage  8 0, mkStage 13 0
    ; mkStage  9 0, mkStage 6  0
    ; mkStage 10 0, mkStage 8  1
    ; mkStage 11 1, mkStage 10 0
    ; mkStage 12 0, mkStage 7  0
    ; mkStage 12 1, mkStage 7  0
    ; mkStage 13 0, mkStage 10 0
    ] in
  mk_bool_test
    (rc_name "minus")
    "constraints for minus are satisfiable"
    (rec_check_lists_pass 6 [8; 6] [7] cstrnts)

let rec_check_mult =
  let cstrnts =
    [ infty, mkStage 18 0
    ; mkStage 15 0, mkStage 20 0
    ; mkStage 17 0, mkStage 14 0
    ; mkStage 18 0, mkStage 16 0
    ; mkStage 19 1, mkStage 18 0
    ] in
  mk_bool_test
    (rc_name "mult")
    "constraints for mult are satisfiable"
    (rec_check_lists_pass 14 [14] [15; 16] cstrnts)

let rec_check_div =
  let cstrnts =
    [ mkStage 23 0, mkStage 27 0
    ; mkStage 24 0, mkStage 21 0
    ; mkStage 24 0, mkStage 28 0
    ; mkStage 25 0, mkStage 23 1
    ; mkStage 26 1, mkStage 25 0
    ; mkStage 27 1, mkStage 25 0
    ; mkStage 28 0, mkStage 21 0
    ] in
  mk_bool_test
    (rc_name "div")
    "constraints for div are satisfiable"
    (rec_check_lists_pass 21 [23; 21] [22] cstrnts)

let rec_check_fact =
  let cstrnts =
    [ infty, mkStage 32 0
    ; mkStage 30 0, mkStage 35 0
    ; mkStage 31 0, mkStage 29 0
    ; mkStage 32 0, mkStage 30 0
    ; mkStage 33 1, mkStage 32 0
    ; mkStage 34 1, mkStage 33 0
    ] in
  mk_bool_test
    (rc_name "fact")
    "constraints for fact are satisfiable"
    (rec_check_lists_pass 29 [29] [30] cstrnts)

(*
Fixpoint loop (n : nat) : Type :=
  match n with
  | O => Set
  | S n' => loop (S n')
  end.
*)
let rec_check_loop =
  let cstrnts =
    [ mkStage 5 0, mkStage 3 0
    ; mkStage 3 0, mkStage 5 0
    ; mkStage 4 1, mkStage 0 0
    ; mkStage 3 0, mkStage 4 0
    ; mkStage 2 0, mkStage 5 1
    ; mkStage 1 0, mkStage 5 1
    ; mkStage 1 0, mkStage 0 1
    ; mkStage 0 1, mkStage 1 0
    ] in
  mk_bool_test
    (rc_name "loop")
    "constraints for loop are not satisfiable"
    (rec_check_lists_fail 0 [1; 0] [] cstrnts)

(*
Fixpoint tozero (n : nat) : Type :=
  match n with
  | O => Set
  | S n' => tozero O
  end.
*)
let rec_check_tozero =
  let cstrnts =
    [ mkStage 5 0, mkStage 3 0
    ; mkStage 3 0, mkStage 5 0
    ; mkStage 4 1, mkStage 0 0
    ; mkStage 2 0, mkStage 5 1
    ; mkStage 1 0, mkStage 5 1
    ; mkStage 1 0, mkStage 0 1
    ; mkStage 0 1, mkStage 1 0
    ] in
  mk_bool_test
    (rc_name "tozero")
    "constraints for tozero are satisfiable"
    (rec_check_lists_pass 0 [0] [] cstrnts)

let rec_check_tests =
  [ rec_check_plus
  ; rec_check_minus
  ; rec_check_mult
  ; rec_check_div
  ; rec_check_fact
  ; rec_check_loop
  ; rec_check_tozero
  ]

(* Run tests *)

let tests = add_tests
  @ fold_tests
  @ filter_tests
  @ sup_tests
  @ sub_tests
  @ bellman_ford_tests
  @ closure_tests
  @ rec_check_tests

let _ = run_tests __FILE__ log_out_ch tests

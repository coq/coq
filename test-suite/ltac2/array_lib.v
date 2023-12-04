Require Import Ltac2.Ltac2.
Import Ltac2.Message.
Import Ltac2.Array.
Require Ltac2.List.
Require Ltac2.Int.

(* Array/List comparison functions which throw an exception on unequal *)

Ltac2 Type exn ::= [ Regression_Test_Failure ].

Ltac2 check_eq_int a l :=
  List.iter2
    (fun a b => match Int.equal a b with true => () | false => Control.throw Regression_Test_Failure end)
    (to_list a) l.

Ltac2 check_eq_bool a l :=
  List.iter2
    (fun a b => match Bool.equal a b with true => () | false => Control.throw Regression_Test_Failure end)
    (to_list a) l.

Ltac2 check_eq_int_matrix m ll :=
  List.iter2 (fun a b => check_eq_int a b) (to_list m) ll.

Ltac2 check_eq_bool_matrix m ll :=
  List.iter2 (fun a b => check_eq_bool a b) (to_list m) ll.

(* The below printing functions are mostly for debugging below test cases *)

Ltac2 print2 m1 m2 := print (Message.concat m1 m2).
Ltac2 print3 m1 m2 m3 := print2 m1 (Message.concat m2 m3).

Ltac2 print_int_array a :=
  iteri (fun i x => print3 (of_int i) (of_string "=") (of_int x)) a.

Ltac2 of_bool b := match b with true=>of_string "true" | false=>of_string "false" end.

Ltac2 print_bool_array a :=
  iteri (fun i x => print3 (of_int i) (of_string "=") (of_bool x)) a.

Ltac2 print_int_list a :=
  List.iteri (fun i x => print3 (of_int i) (of_string "=") (of_int x)) a.

Goal True.
  (* Test failure *)
  Fail check_eq_int ((init 3 (fun i => (Int.add i 10)))) [10;11;13].

  (* test empty with int *)
  check_eq_int empty [].
  check_eq_int (append empty (init 3 (fun i => (Int.add i 10)))) [10;11;12].
  check_eq_int (append (init 3 (fun i => (Int.add i 10))) empty) [10;11;12].

  (* test empty with bool *)
  check_eq_bool empty [].
  check_eq_bool (append empty (init 3 (fun i => (Int.ge i 2)))) [false;false;true].
  check_eq_bool (append (init 3 (fun i => (Int.ge i 2))) empty) [false;false;true].

  (* test init with int *)
  check_eq_int (init 0 (fun i => (Int.add i 10))) [].
  check_eq_int (init 4 (fun i => (Int.add i 10))) [10;11;12;13].

  (* test init with bool *)
  check_eq_bool (init 0 (fun i => (Int.ge i 2))) [].
  check_eq_bool (init 4 (fun i => (Int.ge i 2))) [false;false;true;true].

  (* test make_matrix, set, get *)
  let a := make_matrix 4 3 1 in
  Array.set (Array.get a 1) 2 0;
  check_eq_int_matrix a [[1;1;1];[1;1;0];[1;1;1];[1;1;1]].

  let a := make_matrix 3 4 false in
  Array.set (Array.get a 2) 1 true;
  check_eq_bool_matrix a [[false;false;false;false];[false;false;false;false];[false;true;false;false]].

  (* test copy *)
  let a := init 4 (fun i => (Int.add i 10)) in
  let b := copy a in
  check_eq_int b [10;11;12;13].

  (* test append *)
  let a := init 3 (fun i => (Int.add i 10)) in
  let b := init 4 (fun i => (Int.add i 20)) in
  check_eq_int (append a b) [10;11;12;20;21;22;23].

  (* test concat *)
  let a := init 3 (fun i => (Int.add i 10)) in
  let b := init 4 (fun i => (Int.add i 20)) in
  let c := init 5 (fun i => (Int.add i 30)) in
  check_eq_int (concat (a::b::c::[])) [10;11;12;20;21;22;23;30;31;32;33;34].

  (* test sub *)
  let a := init 10 (fun i => (Int.add i 10)) in
  let b := (sub a 3 0) in
  let c := (append b (init 3 (fun i => (Int.add i 10)))) in
  check_eq_int b [];
  check_eq_int c [10;11;12].

  let a := init 10 (fun i => (Int.add i 10)) in
  let b := (sub a 3 4) in
  check_eq_int b [13;14;15;16].

  (* test fill *)
  let a := init 10 (fun i => (Int.add i 10)) in
  fill a 3 4 0;
  check_eq_int a [10;11;12;0;0;0;0;17;18;19].

  (* test blit *)
  let a := init 10 (fun i => (Int.add i 10)) in
  let b := init 10 (fun i => (Int.add i 20)) in
  blit a 5 b 3 4;
  check_eq_int b [20;21;22;15;16;17;18;27;28;29].

  (* test iter *)
  let a := init 4 (fun i => (Int.add i 3)) in
  let b := init 10 (fun i => 10) in
  iter (fun x => Array.set b x x) a;
  check_eq_int b [10;10;10;3;4;5;6;10;10;10].

  (* test iter2 *)
  let a := init 4 (fun i => (Int.add i 2)) in
  let b := init 4 (fun i => (Int.add i 4)) in
  let c := init 8 (fun i => 10) in
  iter2 (fun x y => Array.set c x y) a b;
  check_eq_int c [10;10;4;5;6;7;10;10].

  (* test map *)
  let a := init 4 (fun i => (Int.add i 10)) in
  check_eq_bool (map (fun i => (Int.ge i 12)) a) [false;false;true;true].

  (* test map2 *)
  let a := init 4 (fun i => (Int.add 10 i)) in
  let b := init 4 (fun i => (Int.sub 13 i)) in
  check_eq_bool (map2 (fun x y => (Int.ge x y)) a b) [false;false;true;true].

  (* test iteri *)
  let a := init 4 (fun i => (Int.add i 10)) in
  let m := make_matrix 4 2 100 in
  iteri (fun i x => Array.set (Array.get m i) 0 i; Array.set (Array.get m i) 1 x) a;
  check_eq_int_matrix m [[0;10];[1;11];[2;12];[3;13]].

  (* test mapi *)
  let a := init 4 (fun i => (Int.sub 3 i)) in
  check_eq_bool (mapi (fun i x => (Int.ge i x)) a) [false;false;true;true].

  (* to_list is already tested in check_eq_... *)

  (* test of_list *)
  check_eq_int (of_list ([0;1;2;3])) [0;1;2;3].

  (* test fold_left *)
  let a := init 4 (fun i => (Int.add 10 i)) in
  check_eq_int (of_list (fold_left (fun a b => b::a) [] a)) [13;12;11;10].

  (* test fold_right *)
  let a := init 4 (fun i => (Int.add 10 i)) in
  check_eq_int (of_list (fold_right (fun a b => a::b) a [])) [10;11;12;13].

  (* test exist *)
  let a := init 4 (fun i => (Int.add 10 i)) in
  let l := [
    exist (fun x => Int.equal x 10) a;
    exist (fun x => Int.equal x 13) a;
    exist (fun x => Int.equal x 14) a] in
  check_eq_bool (of_list l) [true;true;false].

  (* test for_all *)
  let a := init 4 (fun i => (Int.add 10 i)) in
  let l := [
    for_all (fun x => Int.lt x 14) a;
    for_all (fun x => Int.lt x 13) a] in
  check_eq_bool (of_list l) [true;false].

  (* test mem *)
  let a := init 4 (fun i => (Int.add 10 i)) in
  let l := [
    mem Int.equal 10 a;
    mem Int.equal 13 a;
    mem Int.equal 14 a] in
  check_eq_bool (of_list l) [true;true;false].

exact I.
Qed.

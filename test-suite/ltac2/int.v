Require Import Ltac2.Ltac2.
Require Ltac2.Int.
Require Ltac2.Bool.

(* Int comparison functions which throw an exception on unequal *)

Ltac2 Type exn ::= [ Regression_Test_Failure ].

Ltac2 check_eq_int a b :=
  if Int.equal a b then () else Control.throw Regression_Test_Failure .

Ltac2 check_eq_bool a b :=
  if Bool.equal a b then () else Control.throw Regression_Test_Failure .

Goal True.
  (* Test failure *)
  Fail check_eq_int 2 3.
  Fail check_eq_bool true false.

  check_eq_bool (Int.equal 2 2) true.
  check_eq_bool (Int.equal 2 3) false.

  check_eq_int (Int.add 5 7) 12.
  check_eq_int (Int.sub 5 7) -2.
  check_eq_int (Int.mul 5 7) 35.
  check_eq_int (Int.div 7 5) 1.
  check_eq_int (Int.div 7 -5) -1.
  check_eq_int (Int.div -7 5) -1.
  check_eq_int (Int.div -7 -5) 1.
  Fail Ltac2 Eval Int.div 1 0.
  check_eq_int (Int.mod 7 5) 2.
  check_eq_int (Int.mod 7 -5) 2.
  check_eq_int (Int.mod -7 5) -2.
  check_eq_int (Int.mod -7 -5) -2.
  Fail Ltac2 Eval Int.mod 1 0.
  check_eq_int (Int.neg 5) -5.
  check_eq_int (Int.abs -5) 5.

  check_eq_int (Int.asr 16 2) 4.
  check_eq_int (Int.asr -16 2) -4.
  check_eq_int (Int.lsl 16 2) 64.
  check_eq_int (Int.lsl -16 2) -64.
  check_eq_int (Int.lsr 16 2) 4.
  check_eq_int (Int.compare (Int.lsr -16 2) 0) 1.
  check_eq_int (Int.land 7 12) 4.
  check_eq_int (Int.lor 7 12) 15.
  check_eq_int (Int.lxor 7 12) 11.
  check_eq_int (Int.lnot -1) 0.

  exact I.
Qed.

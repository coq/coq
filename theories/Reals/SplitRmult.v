(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i Lemma mult_non_zero :(r1,r2:R)``r1<>0`` /\ ``r2<>0`` -> ``r1*r2<>0``. i*)


Require Import Rbase.

Ltac split_Rmult :=
  match goal with
    |  |- ((?X1 * ?X2)%R <> 0%R) =>
      apply Rmult_integral_contrapositive; split; try split_Rmult
  end.

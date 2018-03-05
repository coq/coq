(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i Lemma mult_non_zero :(r1,r2:R)``r1<>0`` /\ ``r2<>0`` -> ``r1*r2<>0``. i*)


Require Import Rbase.

Ltac split_Rmult :=
  match goal with
    |  |- ((?X1 * ?X2)%R <> 0%R) =>
      apply Rmult_integral_contrapositive; split; try split_Rmult
  end.

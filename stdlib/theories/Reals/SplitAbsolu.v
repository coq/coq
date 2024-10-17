(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbasic_fun.

Ltac split_case_Rabs :=
  match goal with
    |  |- context [(Rcase_abs ?X1)] =>
      destruct (Rcase_abs X1) as [?Hlt|?Hge]; try split_case_Rabs
  end.


Ltac split_Rabs :=
  match goal with
    | id:context [(Rabs _)] |- _ => generalize id; clear id; try split_Rabs
    |  |- context [(Rabs ?X1)] =>
      unfold Rabs; try split_case_Rabs; intros
  end.

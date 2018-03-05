(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

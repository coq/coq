(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i      $Id$       i*)

Require Import Rbasic_fun.

Ltac split_case_Rabs :=
  match goal with
    |  |- context [(Rcase_abs ?X1)] =>
      case (Rcase_abs X1); try split_case_Rabs
  end.


Ltac split_Rabs :=
  match goal with
    | id:context [(Rabs _)] |- _ => generalize id; clear id; try split_Rabs
    |  |- context [(Rabs ?X1)] =>
      unfold Rabs in |- *; try split_case_Rabs; intros
  end.

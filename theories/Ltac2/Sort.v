(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 Type t := sort.

(** [sort_of_product s s'] is [s''] such that if [A : s] and [B : s'] then [A -> B : s'']. *)
Ltac2 @external sort_of_product : t -> t -> t
  := "rocq-runtime.plugins.ltac2" "sort_of_product".

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** THIS FILE IS DEPRECATED. Use [MinMax] instead. *)

Require Export MinMax.

Local Open Scope nat_scope.
Implicit Types m n p : nat.

Notation max := MinMax.max (only parsing).

Definition max_0_l := max_0_l.
Definition max_0_r := max_0_r.
Definition succ_max_distr := succ_max_distr.
Definition plus_max_distr_l := plus_max_distr_l.
Definition plus_max_distr_r := plus_max_distr_r.
Definition max_case_strong := max_case_strong.
Definition max_spec := max_spec.
Definition max_dec := max_dec.
Definition max_case := max_case.
Definition max_idempotent := max_id.
Definition max_assoc := max_assoc.
Definition max_comm := max_comm.
Definition max_l := max_l.
Definition max_r := max_r.
Definition le_max_l := le_max_l.
Definition le_max_r := le_max_r.
Definition max_lub_l := max_lub_l.
Definition max_lub_r := max_lub_r.
Definition max_lub := max_lub.

(* begin hide *)
(* Compatibility *)
Notation max_case2 := max_case (only parsing).
Notation max_SS := succ_max_distr (only parsing).
(* end hide *)

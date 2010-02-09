(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** THIS FILE IS DEPRECATED. Use [NPeano] and [MinMax] instead. *)

Require Import NPeano.
Require Export MinMax.

Local Open Scope nat_scope.
Implicit Types m n p : nat.

Notation max := NPeano.max (only parsing).

Definition max_0_l := max_0_l.
Definition max_0_r := max_0_r.
Definition succ_max_distr := succ_max_distr.
Definition plus_max_distr_l := plus_max_distr_l.
Definition plus_max_distr_r := plus_max_distr_r.
Definition max_case_strong := Nat.max_case_strong.
Definition max_spec := Nat.max_spec.
Definition max_dec := Nat.max_dec.
Definition max_case := Nat.max_case.
Definition max_idempotent := Nat.max_id.
Definition max_assoc := Nat.max_assoc.
Definition max_comm := Nat.max_comm.
Definition max_l := Nat.max_l.
Definition max_r := Nat.max_r.
Definition le_max_l := Nat.le_max_l.
Definition le_max_r := Nat.le_max_r.
Definition max_lub_l := Nat.max_lub_l.
Definition max_lub_r := Nat.max_lub_r.
Definition max_lub := Nat.max_lub.

(* begin hide *)
(* Compatibility *)
Notation max_case2 := max_case (only parsing).
Notation max_SS := succ_max_distr (only parsing).
(* end hide *)

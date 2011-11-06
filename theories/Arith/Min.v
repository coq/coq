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

Open Local Scope nat_scope.
Implicit Types m n p : nat.

Notation min := MinMax.min (only parsing).

Definition min_0_l := min_0_l.
Definition min_0_r := min_0_r.
Definition succ_min_distr := succ_min_distr.
Definition plus_min_distr_l := plus_min_distr_l.
Definition plus_min_distr_r := plus_min_distr_r.
Definition min_case_strong := min_case_strong.
Definition min_spec := min_spec.
Definition min_dec := min_dec.
Definition min_case := min_case.
Definition min_idempotent := min_id.
Definition min_assoc := min_assoc.
Definition min_comm := min_comm.
Definition min_l := min_l.
Definition min_r := min_r.
Definition le_min_l := le_min_l.
Definition le_min_r := le_min_r.
Definition min_glb_l := min_glb_l.
Definition min_glb_r := min_glb_r.
Definition min_glb := min_glb.

(* begin hide *)
(* Compatibility *)
Notation min_case2 := min_case (only parsing).
Notation min_SS := succ_min_distr (only parsing).
(* end hide *)
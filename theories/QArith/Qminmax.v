(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import QArith_base OrderedType2 QOrderedType GenericMinMax.

(** * Maximum and Minimum of two rational numbers *)

Local Open Scope Q_scope.

(** [Qmin] and [Qmax] are obtained the usual way from [Qcompare]. *)

Definition Qmax := gmax Qcompare.
Definition Qmin := gmin Qcompare.

Module QHasMinMax <: HasMinMax Q_as_OT.
 Module QMM := GenericMinMax Q_as_OT.
 Definition max := Qmax.
 Definition min := Qmin.
 Definition max_spec := QMM.max_spec.
 Definition min_spec := QMM.min_spec.
End QHasMinMax.

(** We obtain hence all the generic properties of max and min. *)

Module Import QMinMaxProps := MinMaxProperties Q_as_OT QHasMinMax.

Definition Qmax_case_strong := max_case_strong.
Definition Qmax_case := max_case.
Definition Qmax_monotone := max_monotone.
Definition Qmax_spec := max_spec.
Definition Qmax_spec_le := max_spec_le.
Definition Qmax_dec := max_dec.
Definition Qmax_unicity := max_unicity.
Definition Qmax_unicity_ext := max_unicity_ext.
Definition Qmax_id := max_id.
Notation Qmax_idempotent := Qmax_id (only parsing).
Definition Qmax_assoc := max_assoc.
Definition Qmax_comm := max_comm.
Definition Qmax_l := max_l.
Definition Qmax_r := max_r.
Definition Nle_max_l := le_max_l.
Definition Nle_max_r := le_max_r.
Definition Qmax_le := max_le.
Definition Qmax_le_iff := max_le_iff.
Definition Qmax_lt_iff := max_lt_iff.
Definition Qmax_lub_l := max_lub_l.
Definition Qmax_lub_r := max_lub_r.
Definition Qmax_lub := max_lub.
Definition Qmax_lub_iff := max_lub_iff.
Definition Qmax_lub_lt := max_lub_lt.
Definition Qmax_lub_lt_iff := max_lub_lt_iff.
Definition Qmax_le_compat_l := max_le_compat_l.
Definition Qmax_le_compat_r := max_le_compat_r.
Definition Qmax_le_compat := max_le_compat.

Definition Qmin_case_strong := min_case_strong.
Definition Qmin_case := min_case.
Definition Qmin_monotone := min_monotone.
Definition Qmin_spec := min_spec.
Definition Qmin_spec_le := min_spec_le.
Definition Qmin_dec := min_dec.
Definition Qmin_unicity := min_unicity.
Definition Qmin_unicity_ext := min_unicity_ext.
Definition Qmin_id := min_id.
Notation Qmin_idempotent := Qmin_id (only parsing).
Definition Qmin_assoc := min_assoc.
Definition Qmin_comm := min_comm.
Definition Qmin_l := min_l.
Definition Qmin_r := min_r.
Definition Nle_min_l := le_min_l.
Definition Nle_min_r := le_min_r.
Definition Qmin_le := min_le.
Definition Qmin_le_iff := min_le_iff.
Definition Qmin_lt_iff := min_lt_iff.
Definition Qmin_glb_l := min_glb_l.
Definition Qmin_glb_r := min_glb_r.
Definition Qmin_glb := min_glb.
Definition Qmin_glb_iff := min_glb_iff.
Definition Qmin_glb_lt := min_glb_lt.
Definition Qmin_glb_lt_iff := min_glb_lt_iff.
Definition Qmin_le_compat_l := min_le_compat_l.
Definition Qmin_le_compat_r := min_le_compat_r.
Definition Qmin_le_compat := min_le_compat.

Definition Qmin_max_absorption := min_max_absorption.
Definition Qmax_min_absorption := max_min_absorption.
Definition Qmax_min_distr := max_min_distr.
Definition Qmin_max_distr := min_max_distr.
Definition Qmax_min_modular := max_min_modular.
Definition Qmin_max_modular := min_max_modular.
Definition Qmax_min_disassoc := max_min_disassoc.
Definition Qmax_min_antimonotone := max_min_antimonotone.
Definition Qmin_max_antimonotone := min_max_antimonotone.



(** * Properties specific to the [Q] domain *)

(** Compatibilities (consequences of monotonicity) *)

Lemma Qplus_max_distr_l : forall n m p, Qmax (p + n) (p + m) == p + Qmax n m.
Proof.
 intros. apply Qmax_monotone.
 intros x x' Hx; rewrite Hx; auto with qarith.
 intros x x' Hx. apply Qplus_le_compat; q_order.
Qed.

Lemma Qplus_max_distr_r : forall n m p, Qmax (n + p) (m + p) == Qmax n m + p.
Proof.
 intros. rewrite (Qplus_comm n p), (Qplus_comm m p), (Qplus_comm _ p).
 apply Qplus_max_distr_l.
Qed.

Lemma Qplus_min_distr_l : forall n m p, Qmin (p + n) (p + m) == p + Qmin n m.
Proof.
 intros. apply Qmin_monotone.
 intros x x' Hx; rewrite Hx; auto with qarith.
 intros x x' Hx. apply Qplus_le_compat; q_order.
Qed.

Lemma Qplus_min_distr_r : forall n m p, Qmin (n + p) (m + p) == Qmin n m + p.
Proof.
 intros. rewrite (Qplus_comm n p), (Qplus_comm m p), (Qplus_comm _ p).
 apply Qplus_min_distr_l.
Qed.

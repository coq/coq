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

Module Q.

(** We obtain hence all the generic properties of max and min. *)

Include MinMaxProperties Q_as_OT QHasMinMax.


(** * Properties specific to the [Q] domain *)

(** Compatibilities (consequences of monotonicity) *)

Lemma plus_max_distr_l : forall n m p, Qmax (p + n) (p + m) == p + Qmax n m.
Proof.
 intros. apply max_monotone.
 intros x x' Hx; rewrite Hx; auto with qarith.
 intros x x' Hx. apply Qplus_le_compat; q_order.
Qed.

Lemma plus_max_distr_r : forall n m p, Qmax (n + p) (m + p) == Qmax n m + p.
Proof.
 intros. rewrite (Qplus_comm n p), (Qplus_comm m p), (Qplus_comm _ p).
 apply plus_max_distr_l.
Qed.

Lemma plus_min_distr_l : forall n m p, Qmin (p + n) (p + m) == p + Qmin n m.
Proof.
 intros. apply min_monotone.
 intros x x' Hx; rewrite Hx; auto with qarith.
 intros x x' Hx. apply Qplus_le_compat; q_order.
Qed.

Lemma plus_min_distr_r : forall n m p, Qmin (n + p) (m + p) == Qmin n m + p.
Proof.
 intros. rewrite (Qplus_comm n p), (Qplus_comm m p), (Qplus_comm _ p).
 apply plus_min_distr_l.
Qed.

End Q.
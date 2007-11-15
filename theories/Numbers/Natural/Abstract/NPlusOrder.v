(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i i*)

Require Export NOrder.

Module NPlusOrderPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NOrderPropMod := NOrderPropFunct NAxiomsMod.
Open Local Scope NatScope.

Theorem plus_lt_mono_l : forall n m p : N, n < m <-> p + n < p + m.
Proof NZplus_lt_mono_l.

Theorem plus_lt_mono_r : forall n m p : N, n < m <-> n + p < m + p.
Proof NZplus_lt_mono_r.

Theorem plus_lt_mono : forall n m p q : N, n < m -> p < q -> n + p < m + q.
Proof NZplus_lt_mono.

Theorem plus_le_mono_l : forall n m p : N, n <= m <-> p + n <= p + m.
Proof NZplus_le_mono_l.

Theorem plus_le_mono_r : forall n m p : N, n <= m <-> n + p <= m + p.
Proof NZplus_le_mono_r.

Theorem plus_le_mono : forall n m p q : N, n <= m -> p <= q -> n + p <= m + q.
Proof NZplus_le_mono.

Theorem plus_lt_le_mono : forall n m p q : N, n < m -> p <= q -> n + p < m + q.
Proof NZplus_lt_le_mono.

Theorem plus_le_lt_mono : forall n m p q : N, n <= m -> p < q -> n + p < m + q.
Proof NZplus_le_lt_mono.

Theorem plus_pos_pos : forall n m : N, 0 < n -> 0 < m -> 0 < n + m.
Proof NZplus_pos_pos.

Theorem lt_plus_pos_l : forall n m : N, 0 < n -> m < n + m.
Proof NZlt_plus_pos_l.

Theorem lt_plus_pos_r : forall n m : N, 0 < n -> m < m + n.
Proof NZlt_plus_pos_r.

Theorem le_lt_plus_lt : forall n m p q : N, n <= m -> p + m < q + n -> p < q.
Proof NZle_lt_plus_lt.

Theorem lt_le_plus_lt : forall n m p q : N, n < m -> p + m <= q + n -> p < q.
Proof NZlt_le_plus_lt.

Theorem le_le_plus_le : forall n m p q : N, n <= m -> p + m <= q + n -> p <= q.
Proof NZle_le_plus_le.

Theorem plus_lt_cases : forall n m p q : N, n + m < p + q -> n < p \/ m < q.
Proof NZplus_lt_cases.

Theorem plus_le_cases : forall n m p q : N, n + m <= p + q -> n <= p \/ m <= q.
Proof NZplus_le_cases.

Theorem plus_pos_cases : forall n m : N, 0 < n + m -> 0 < n \/ 0 < m.
Proof NZplus_pos_cases.

(** Theorems true for natural numbers *)

Theorem le_plus_r : forall n m : N, n <= n + m.
Proof.
intro n; induct m.
rewrite plus_0_r; now apply eq_le_incl.
intros m IH. rewrite plus_succ_r; now apply le_le_succ_r.
Qed.

Theorem lt_lt_plus_r : forall n m p : N, n < m -> n < m + p.
Proof.
intros n m p H; rewrite <- (plus_0_r n).
apply plus_lt_le_mono; [assumption | apply le_0_l].
Qed.

Theorem lt_lt_plus_l : forall n m p : N, n < m -> n < p + m.
Proof.
intros n m p; rewrite plus_comm; apply lt_lt_plus_r.
Qed.

Theorem plus_pos_l : forall n m : N, 0 < n -> 0 < n + m.
Proof.
intros; apply NZplus_pos_nonneg. assumption. apply le_0_l.
Qed.

Theorem plus_pos_r : forall n m : N, 0 < m -> 0 < n + m.
Proof.
intros; apply NZplus_nonneg_pos. apply le_0_l. assumption.
Qed.

(* The following property is used to prove the correctness of the
definition of order on integers constructed from pairs of natural numbers *)

Theorem plus_lt_repl_pair : forall n m n' m' u v : N,
  n + u < m + v -> n + m' == n' + m -> n' + u < m' + v.
Proof.
intros n m n' m' u v H1 H2.
symmetry in H2. assert (H3 : n' + m <= n + m') by now apply eq_le_incl.
pose proof (plus_lt_le_mono _ _ _ _ H1 H3) as H4.
rewrite (plus_shuffle2 n u), (plus_shuffle1 m v), (plus_comm m n) in H4.
do 2 rewrite <- plus_assoc in H4. do 2 apply <- plus_lt_mono_l in H4.
now rewrite (plus_comm n' u), (plus_comm m' v).
Qed.

End NPlusOrderPropFunct.
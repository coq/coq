(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export NOrder.

Module NPlusOrderPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NOrderPropMod := NOrderPropFunct NAxiomsMod.
Open Local Scope NatScope.

Theorem add_lt_mono_l : forall n m p : N, n < m <-> p + n < p + m.
Proof NZadd_lt_mono_l.

Theorem add_lt_mono_r : forall n m p : N, n < m <-> n + p < m + p.
Proof NZadd_lt_mono_r.

Theorem add_lt_mono : forall n m p q : N, n < m -> p < q -> n + p < m + q.
Proof NZadd_lt_mono.

Theorem add_le_mono_l : forall n m p : N, n <= m <-> p + n <= p + m.
Proof NZadd_le_mono_l.

Theorem add_le_mono_r : forall n m p : N, n <= m <-> n + p <= m + p.
Proof NZadd_le_mono_r.

Theorem add_le_mono : forall n m p q : N, n <= m -> p <= q -> n + p <= m + q.
Proof NZadd_le_mono.

Theorem add_lt_le_mono : forall n m p q : N, n < m -> p <= q -> n + p < m + q.
Proof NZadd_lt_le_mono.

Theorem add_le_lt_mono : forall n m p q : N, n <= m -> p < q -> n + p < m + q.
Proof NZadd_le_lt_mono.

Theorem add_pos_pos : forall n m : N, 0 < n -> 0 < m -> 0 < n + m.
Proof NZadd_pos_pos.

Theorem lt_add_pos_l : forall n m : N, 0 < n -> m < n + m.
Proof NZlt_add_pos_l.

Theorem lt_add_pos_r : forall n m : N, 0 < n -> m < m + n.
Proof NZlt_add_pos_r.

Theorem le_lt_add_lt : forall n m p q : N, n <= m -> p + m < q + n -> p < q.
Proof NZle_lt_add_lt.

Theorem lt_le_add_lt : forall n m p q : N, n < m -> p + m <= q + n -> p < q.
Proof NZlt_le_add_lt.

Theorem le_le_add_le : forall n m p q : N, n <= m -> p + m <= q + n -> p <= q.
Proof NZle_le_add_le.

Theorem add_lt_cases : forall n m p q : N, n + m < p + q -> n < p \/ m < q.
Proof NZadd_lt_cases.

Theorem add_le_cases : forall n m p q : N, n + m <= p + q -> n <= p \/ m <= q.
Proof NZadd_le_cases.

Theorem add_pos_cases : forall n m : N, 0 < n + m -> 0 < n \/ 0 < m.
Proof NZadd_pos_cases.

(* Theorems true for natural numbers *)

Theorem le_add_r : forall n m : N, n <= n + m.
Proof.
intro n; induct m.
rewrite add_0_r; now apply eq_le_incl.
intros m IH. rewrite add_succ_r; now apply le_le_succ_r.
Qed.

Theorem lt_lt_add_r : forall n m p : N, n < m -> n < m + p.
Proof.
intros n m p H; rewrite <- (add_0_r n).
apply add_lt_le_mono; [assumption | apply le_0_l].
Qed.

Theorem lt_lt_add_l : forall n m p : N, n < m -> n < p + m.
Proof.
intros n m p; rewrite add_comm; apply lt_lt_add_r.
Qed.

Theorem add_pos_l : forall n m : N, 0 < n -> 0 < n + m.
Proof.
intros; apply NZadd_pos_nonneg. assumption. apply le_0_l.
Qed.

Theorem add_pos_r : forall n m : N, 0 < m -> 0 < n + m.
Proof.
intros; apply NZadd_nonneg_pos. apply le_0_l. assumption.
Qed.

(* The following property is used to prove the correctness of the
definition of order on integers constructed from pairs of natural numbers *)

Theorem add_lt_repl_pair : forall n m n' m' u v : N,
  n + u < m + v -> n + m' == n' + m -> n' + u < m' + v.
Proof.
intros n m n' m' u v H1 H2.
symmetry in H2. assert (H3 : n' + m <= n + m') by now apply eq_le_incl.
pose proof (add_lt_le_mono _ _ _ _ H1 H3) as H4.
rewrite (add_shuffle2 n u), (add_shuffle1 m v), (add_comm m n) in H4.
do 2 rewrite <- add_assoc in H4. do 2 apply <- add_lt_mono_l in H4.
now rewrite (add_comm n' u), (add_comm m' v).
Qed.

End NPlusOrderPropFunct.

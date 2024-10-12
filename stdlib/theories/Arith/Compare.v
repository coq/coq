(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Equality is decidable on [nat] *)

Local Open Scope nat_scope.

Notation not_eq_sym := not_eq_sym (only parsing).

Implicit Types m n p q : nat.

Require Import Arith_base.
Require Import Peano_dec.
Require Import Compare_dec.

Definition le_or_le_S := le_le_S_dec.

Definition Pcompare := gt_eq_gt_dec.

Lemma le_dec : forall n m, {n <= m} + {m <= n}.
Proof le_ge_dec.

Definition lt_or_eq n m := {m > n} + {n = m}.

Lemma le_decide : forall n m, n <= m -> lt_or_eq n m.
Proof le_lt_eq_dec.

Lemma le_le_S_eq : forall n m, n <= m -> S n <= m \/ n = m.
Proof (fun n m Hle => proj1 (Nat.lt_eq_cases n m) Hle).

(* By special request of G. Kahn - Used in Group Theory *)
Lemma discrete_nat :
  forall n m, n < m -> S n = m \/ (exists r : nat, m = S (S (n + r))).
Proof.
  intros m n H.
  lapply (proj1 (Nat.le_succ_l m n)); auto.
  intro H'; lapply (proj1 (Nat.lt_eq_cases (S m) n)); auto.
  induction 1; auto.
  right; exists (n - S (S m)); simpl.
  rewrite (Nat.add_comm m (n - S (S m))).
  rewrite (plus_n_Sm (n - S (S m)) m).
  rewrite (plus_n_Sm (n - S (S m)) (S m)).
  rewrite (Nat.add_comm (n - S (S m)) (S (S m))).
  rewrite Nat.add_sub_assoc; [ | assumption ].
  rewrite Nat.add_comm.
  rewrite <- Nat.add_sub_assoc; [ | reflexivity ].
  rewrite Nat.sub_diag.
  symmetry; apply Nat.add_0_r.
Qed.

Require Export Wf_nat.

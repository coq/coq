(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Equality is decidable on [nat] *)

Local Open Scope nat_scope.

Notation not_eq_sym := not_eq_sym (only parsing).

Implicit Types m n p q : nat.

Require Import PeanoNat.
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
Proof. apply Nat.lt_eq_cases. Qed.

(* By special request of G. Kahn - Used in Group Theory *)
Lemma discrete_nat :
  forall n m, n < m -> S n = m \/ (exists r : nat, m = S (S (n + r))).
Proof.
  intros m n H.
  inversion H as [ | k H1 H2 ]; auto; subst.
  right; exists (S k - S (S m)).
  rewrite (Nat.add_comm m (S k - S (S m))).
  rewrite (plus_n_Sm (S k - S (S m)) m).
  rewrite (plus_n_Sm (S k - S (S m)) (S m)).
  rewrite Nat.sub_add; auto.
  now apply Nat.succ_le_mono in H1.
Qed.

Require Export Wf_nat.

(*
Require Export Min Max.
*)

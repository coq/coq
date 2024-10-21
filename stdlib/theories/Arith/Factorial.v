(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PeanoNat.
Local Open Scope nat_scope.

(** Factorial *)

Fixpoint fact (n:nat) : nat :=
  match n with
    | O => 1
    | S n => S n * fact n
  end.

Arguments fact n%_nat.

Lemma lt_O_fact n : 0 < fact n.
Proof.
  induction n; simpl; auto.
  apply Nat.lt_lt_add_r; assumption.
Qed.

Lemma fact_neq_0 n : fact n <> 0.
Proof.
 apply Nat.neq_0_lt_0, lt_O_fact.
Qed.

Lemma fact_le n m : n <= m -> fact n <= fact m.
Proof.
  induction 1 as [|m ?].
  - apply le_n.
  - simpl. transitivity (fact m).
    + trivial.
    + apply Nat.le_add_r.
Qed.

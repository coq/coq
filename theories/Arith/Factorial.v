(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PeanoNat Plus Mult Lt.
Local Open Scope nat_scope.

(** Factorial *)

Fixpoint fact (n:nat) : nat :=
  match n with
    | O => 1
    | S n => S n * fact n
  end.

Arguments fact n%nat.

Lemma lt_O_fact n : 0 < fact n.
Proof.
  induction n; simpl; auto with arith.
Qed.

Lemma fact_neq_0 n : fact n <> 0.
Proof.
 apply Nat.neq_0_lt_0, lt_O_fact.
Qed.

Lemma fact_le n m : n <= m -> fact n <= fact m.
Proof.
  induction 1.
  - apply le_n.
  - simpl. transitivity (fact m). trivial. apply Nat.le_add_r.
Qed.

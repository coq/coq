(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

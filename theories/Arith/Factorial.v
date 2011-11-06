(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Plus.
Require Import Mult.
Require Import Lt.
Open Local Scope nat_scope.

(** Factorial *)

Boxed Fixpoint fact (n:nat) : nat :=
  match n with
    | O => 1
    | S n => S n * fact n
  end.

Arguments Scope fact [nat_scope].

Lemma lt_O_fact : forall n:nat, 0 < fact n.
Proof.
  simple induction n; unfold lt in |- *; simpl in |- *; auto with arith.
Qed.

Lemma fact_neq_0 : forall n:nat, fact n <> 0.
Proof.
  intro.
  apply sym_not_eq.
  apply lt_O_neq.
  apply lt_O_fact.
Qed.

Lemma fact_le : forall n m:nat, n <= m -> fact n <= fact m.
Proof.
  induction 1.
  apply le_n.
  assert (1 * fact n <= S m * fact m).
  apply mult_le_compat.
  apply lt_le_S; apply lt_O_Sn.
  assumption.
  simpl (1 * fact n) in H0.
  rewrite <- plus_n_O in H0.
  assumption.
Qed.

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Plus.
Require Mult.
Require Lt.
V7only [Import nat_scope.].
Open Local Scope nat_scope.

(** Factorial *)

Fixpoint fact [n:nat]:nat:=
  Cases n of
     O     => (S O)
    |(S n) => (mult (S n) (fact n))
  end.

Arguments Scope fact [ nat_scope ].

Lemma lt_O_fact : (n:nat)(lt O (fact n)).
Proof.
Induction n; Unfold lt; Simpl; Auto with arith.
Qed.

Lemma fact_neq_0:(n:nat)~(fact n)=O.
Proof.
Intro.
Apply sym_not_eq.
Apply lt_O_neq.
Apply lt_O_fact.
Qed.

Lemma fact_growing : (n,m:nat) (le n m) -> (le (fact n) (fact m)).
Proof.
NewInduction 1.
Apply le_n.
Assert (le (mult (S O) (fact n)) (mult (S m) (fact m))).
Apply le_mult_mult.
Apply lt_le_S; Apply lt_O_Sn.
Assumption.
Simpl (mult (S O) (fact n)) in H0.
Rewrite <- plus_n_O in H0.
Assumption.
Qed.

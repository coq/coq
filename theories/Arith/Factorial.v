(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

Lemma fact_growing : (m,n:nat) (le m n) -> (le (fact m) (fact n)).
Proof.
NewInduction 1.
Apply le_n.
Assert (le (mult (S O) (fact m)) (mult (S m0) (fact m0))).
Apply le_mult_mult.
Apply lt_le_S; Apply lt_O_Sn.
Assumption.
Simpl (mult (S O) (fact m)) in H0.
Rewrite <- plus_n_O in H0.
Assumption.
Qed.

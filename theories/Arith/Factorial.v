(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Plus.
Require Lt.

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


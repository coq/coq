(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Classical Propositional Logic *)

Require ProofIrrelevance.

Hints Unfold not : core.

Axiom classic: (P:Prop)(P \/ ~(P)).

Lemma NNPP : (p:Prop)~(~(p))->p.
Proof.
Unfold not; Intros; Elim (classic p); Auto.
Intro NP; Elim (H NP).
Qed.

Lemma not_imply_elim : (P,Q:Prop)~(P->Q)->P.
Proof.
Intros; Apply NNPP; Red.
Intro; Apply H; Intro; Absurd P; Trivial.
Qed.

Lemma not_imply_elim2 : (P,Q:Prop)~(P->Q) -> ~Q.
Proof.
Intros; Elim (classic Q); Auto.
Qed.

Lemma imply_to_or : (P,Q:Prop)(P->Q) -> ~P \/ Q.
Proof.
Intros; Elim (classic P); Auto.
Qed.

Lemma imply_to_and : (P,Q:Prop)~(P->Q) -> P /\ ~Q.
Proof.
Intros; Split.
Apply not_imply_elim with Q;  Trivial.
Apply not_imply_elim2 with P; Trivial.
Qed.

Lemma or_to_imply : (P,Q:Prop)(~P \/ Q) -> P->Q.
Proof.
Induction 1; Auto.
Intros H1 H2; Elim (H1 H2).
Qed.

Lemma not_and_or : (P,Q:Prop)~(P/\Q)-> ~P \/ ~Q.
Proof.
Intros; Elim (classic P); Auto.
Qed.

Lemma or_not_and : (P,Q:Prop)(~P \/ ~Q) -> ~(P/\Q).
Proof.
Induction 1; Red; Induction 2; Auto.
Qed.

Lemma not_or_and : (P,Q:Prop)~(P\/Q)-> ~P /\ ~Q.
Proof.
Intros; Elim (classic P); Auto.
Qed.

Lemma and_not_or : (P,Q:Prop)(~P /\ ~Q) -> ~(P\/Q).
Proof.
Induction 1; Red; Induction 3; Trivial.
Qed.

Lemma imply_and_or: (P,Q:Prop)(P->Q) -> P \/ Q -> Q.
Proof.
Induction 2; Trivial.
Qed.

Lemma imply_and_or2: (P,Q,R:Prop)(P->Q) -> P \/ R -> Q \/ R.
Proof.
Induction 2; Auto.
Qed.

Lemma proof_irrelevance: (P:Prop)(p1,p2:P)p1==p2.
Proof (proof_irrelevance_cci classic).

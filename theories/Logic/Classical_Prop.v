(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Classical Propositional Logic *)

Require Import ProofIrrelevance.

Hint Unfold not: core.

Axiom classic : forall P:Prop, P \/ ~ P.

Lemma NNPP : forall p:Prop, ~ ~ p -> p.
Proof.
unfold not in |- *; intros; elim (classic p); auto.
intro NP; elim (H NP).
Qed.

Lemma not_imply_elim : forall P Q:Prop, ~ (P -> Q) -> P.
Proof.
intros; apply NNPP; red in |- *.
intro; apply H; intro; absurd P; trivial.
Qed.

Lemma not_imply_elim2 : forall P Q:Prop, ~ (P -> Q) -> ~ Q.
Proof.
intros; elim (classic Q); auto.
Qed.

Lemma imply_to_or : forall P Q:Prop, (P -> Q) -> ~ P \/ Q.
Proof.
intros; elim (classic P); auto.
Qed.

Lemma imply_to_and : forall P Q:Prop, ~ (P -> Q) -> P /\ ~ Q.
Proof.
intros; split.
apply not_imply_elim with Q; trivial.
apply not_imply_elim2 with P; trivial.
Qed.

Lemma or_to_imply : forall P Q:Prop, ~ P \/ Q -> P -> Q.
Proof.
simple induction 1; auto.
intros H1 H2; elim (H1 H2).
Qed.

Lemma not_and_or : forall P Q:Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
intros; elim (classic P); auto.
Qed.

Lemma or_not_and : forall P Q:Prop, ~ P \/ ~ Q -> ~ (P /\ Q).
Proof.
simple induction 1; red in |- *; simple induction 2; auto.
Qed.

Lemma not_or_and : forall P Q:Prop, ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
intros; elim (classic P); auto.
Qed.

Lemma and_not_or : forall P Q:Prop, ~ P /\ ~ Q -> ~ (P \/ Q).
Proof.
simple induction 1; red in |- *; simple induction 3; trivial.
Qed.

Lemma imply_and_or : forall P Q:Prop, (P -> Q) -> P \/ Q -> Q.
Proof.
simple induction 2; trivial.
Qed.

Lemma imply_and_or2 : forall P Q R:Prop, (P -> Q) -> P \/ R -> Q \/ R.
Proof.
simple induction 2; auto.
Qed.

Lemma proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.
Proof proof_irrelevance_cci classic.
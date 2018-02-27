(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* File created for Coq V5.10.14b, Oct 1995 *)
(* Classical tactics for proving disjunctions by Julien Narboux, Jul 2005 *)
(* Inferred proof-irrelevance and eq_rect_eq added by Hugo Herbelin, Mar 2006 *)

(** Classical Propositional Logic *)

Require Import ClassicalFacts.

Hint Unfold not: core.

Axiom classic : forall P:Prop, P \/ ~ P.

Lemma NNPP : forall p:Prop, ~ ~ p -> p.
Proof.
unfold not; intros; elim (classic p); auto.
intro NP; elim (H NP).
Qed.

(** Peirce's law states [forall P Q:Prop, ((P -> Q) -> P) -> P].
    Thanks to [forall P, False -> P], it is equivalent to the
    following form *)

Lemma Peirce : forall P:Prop, ((P -> False) -> P) -> P.
Proof.
intros P H; destruct (classic P); auto.
Qed.

Lemma not_imply_elim : forall P Q:Prop, ~ (P -> Q) -> P.
Proof.
intros; apply NNPP; red.
intro; apply H; intro; absurd P; trivial.
Qed.

Lemma not_imply_elim2 : forall P Q:Prop, ~ (P -> Q) -> ~ Q.
Proof. (* Intuitionistic *)
tauto.
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
Proof. (* Intuitionistic *)
tauto.
Qed.

Lemma not_and_or : forall P Q:Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
intros; elim (classic P); auto.
Qed.

Lemma or_not_and : forall P Q:Prop, ~ P \/ ~ Q -> ~ (P /\ Q).
Proof.
simple induction 1; red; simple induction 2; auto.
Qed.

Lemma not_or_and : forall P Q:Prop, ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof. (* Intuitionistic *)
tauto.
Qed.

Lemma and_not_or : forall P Q:Prop, ~ P /\ ~ Q -> ~ (P \/ Q).
Proof. (* Intuitionistic *)
tauto.
Qed.

Lemma imply_and_or : forall P Q:Prop, (P -> Q) -> P \/ Q -> Q.
Proof. (* Intuitionistic *)
tauto.
Qed.

Lemma imply_and_or2 : forall P Q R:Prop, (P -> Q) -> P \/ R -> Q \/ R.
Proof. (* Intuitionistic *)
tauto.
Qed.

Lemma proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.
Proof proof_irrelevance_cci classic.

(* classical_left  transforms |- A \/ B into ~B |- A *)
(* classical_right transforms |- A \/ B into ~A |- B *)

Ltac classical_right := match goal with
|- ?X \/ _ => (elim (classic X);intro;[left;trivial|right])
end.

Ltac classical_left := match goal with
|- _ \/ ?X => (elim (classic X);intro;[right;trivial|left])
end.

Require Export EqdepFacts.

Module Eq_rect_eq.

Lemma eq_rect_eq :
  forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
Proof.
intros; rewrite proof_irrelevance with (p1:=h) (p2:=eq_refl p); reflexivity.
Qed.

End Eq_rect_eq.

Module EqdepTheory := EqdepTheory(Eq_rect_eq).
Export EqdepTheory.

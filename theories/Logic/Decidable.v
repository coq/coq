(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** Properties of decidable propositions *)

Definition decidable (P:Prop) := P \/ ~ P.

Theorem dec_not_not : forall P:Prop, decidable P -> (~ P -> False) -> P.
Proof.
unfold decidable; tauto.
Qed.

Theorem dec_True : decidable True.
Proof.
unfold decidable; auto.
Qed.

Theorem dec_False : decidable False.
Proof.
unfold decidable, not; auto.
Qed.

Theorem dec_or :
 forall A B:Prop, decidable A -> decidable B -> decidable (A \/ B).
Proof.
unfold decidable; tauto.
Qed.

Theorem dec_and :
 forall A B:Prop, decidable A -> decidable B -> decidable (A /\ B).
Proof.
unfold decidable; tauto.
Qed.

Theorem dec_not : forall A:Prop, decidable A -> decidable (~ A).
Proof.
unfold decidable; tauto.
Qed.

Theorem dec_imp :
 forall A B:Prop, decidable A -> decidable B -> decidable (A -> B).
Proof.
unfold decidable; tauto.
Qed.

Theorem dec_iff :
 forall A B:Prop, decidable A -> decidable B -> decidable (A<->B).
Proof.
unfold decidable. tauto.
Qed.

Theorem not_not : forall P:Prop, decidable P -> ~ ~ P -> P.
Proof.
unfold decidable; tauto.
Qed.

Theorem not_or : forall A B:Prop, ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
tauto.
Qed.

Theorem not_and : forall A B:Prop, decidable A -> ~ (A /\ B) -> ~ A \/ ~ B.
Proof.
unfold decidable; tauto.
Qed.

Theorem not_imp : forall A B:Prop, decidable A -> ~ (A -> B) -> A /\ ~ B.
Proof.
unfold decidable; tauto.
Qed.

Theorem imp_simp : forall A B:Prop, decidable A -> (A -> B) -> ~ A \/ B.
Proof.
unfold decidable; tauto.
Qed.

Theorem not_iff :
  forall A B:Prop, decidable A -> decidable B ->
    ~ (A <-> B) -> (A /\ ~ B) \/ (~ A /\ B).
Proof.
unfold decidable; tauto.
Qed.

(** Results formulated with iff, used in FSetDecide.
    Negation are expanded since it is unclear whether setoid rewrite
    will always perform conversion. *)

(** We begin with lemmas that, when read from left to right,
    can be understood as ways to eliminate uses of [not]. *)

Theorem not_true_iff : (True -> False) <-> False.
Proof.
tauto.
Qed.

Theorem not_false_iff : (False -> False) <-> True.
Proof.
tauto.
Qed.

Theorem not_not_iff : forall A:Prop, decidable A ->
  (((A -> False) -> False) <-> A).
Proof.
unfold decidable; tauto.
Qed.

Theorem contrapositive : forall A B:Prop, decidable A ->
  (((A -> False) -> (B -> False)) <-> (B -> A)).
Proof.
unfold decidable; tauto.
Qed.

Lemma or_not_l_iff_1 : forall A B: Prop, decidable A ->
  ((A -> False) \/ B <-> (A -> B)).
Proof.
unfold decidable. tauto.
Qed.

Lemma or_not_l_iff_2 : forall A B: Prop, decidable B ->
  ((A -> False) \/ B <-> (A -> B)).
Proof.
unfold decidable. tauto.
Qed.

Lemma or_not_r_iff_1 : forall A B: Prop, decidable A ->
  (A \/ (B -> False) <-> (B -> A)).
Proof.
unfold decidable. tauto.
Qed.

Lemma or_not_r_iff_2 : forall A B: Prop, decidable B ->
  (A \/ (B -> False) <-> (B -> A)).
Proof.
unfold decidable. tauto.
Qed.

Lemma imp_not_l : forall A B: Prop, decidable A ->
  (((A -> False) -> B) <-> (A \/ B)).
Proof.
unfold decidable. tauto.
Qed.


(** Moving Negations Around:
    We have four lemmas that, when read from left to right,
    describe how to push negations toward the leaves of a
    proposition and, when read from right to left, describe
    how to pull negations toward the top of a proposition. *)

Theorem not_or_iff : forall A B:Prop,
  (A \/ B -> False) <-> (A -> False) /\ (B -> False).
Proof.
tauto.
Qed.

Lemma not_and_iff : forall A B:Prop,
  (A /\ B -> False) <-> (A -> B -> False).
Proof.
tauto.
Qed.

Lemma not_imp_iff : forall A B:Prop, decidable A ->
  (((A -> B) -> False) <-> A /\ (B -> False)).
Proof.
unfold decidable. tauto.
Qed.

Lemma not_imp_rev_iff : forall A B : Prop, decidable A ->
  (((A -> B) -> False) <-> (B -> False) /\ A).
Proof.
unfold decidable. tauto.
Qed.

(* Functional relations on decidable co-domains are decidable *)

Theorem dec_functional_relation :
  forall (X Y : Type) (A:X->Y->Prop), (forall y y' : Y, decidable (y=y')) ->
  (forall x, exists! y, A x y) -> forall x y, decidable (A x y).
Proof.
intros X Y A Hdec H x y.
destruct (H x) as (y',(Hex,Huniq)).
destruct (Hdec y y') as [->|Hnot]; firstorder.
Qed.

(** With the following hint database, we can leverage [auto] to check
    decidability of propositions. *)

Hint Resolve dec_True dec_False dec_or dec_and dec_imp dec_not dec_iff
 : decidable_prop.

(** [solve_decidable using lib] will solve goals about the
    decidability of a proposition, assisted by an auxiliary
    database of lemmas.  The database is intended to contain
    lemmas stating the decidability of base propositions,
    (e.g., the decidability of equality on a particular
    inductive type). *)

Tactic Notation "solve_decidable" "using" ident(db) :=
  match goal with
   | |- decidable _ =>
     solve [ auto 100 with decidable_prop db ]
  end.

Tactic Notation "solve_decidable" :=
  solve_decidable using core.

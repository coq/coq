(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Coq.Logic.HLevelsDef.

(* It is rarely possible to prove that a type is a homotopy proposition
   without funext, so we assume it here. *)
Require Import Coq.Logic.FunctionalExtensionality.

Lemma forall_hprop : forall (A : Type) (P : A -> Prop),
    (forall x:A, IsHProp (P x))
    -> IsHProp (forall x:A, P x).
Proof.
  intros A P H p q. apply functional_extensionality_dep.
  intro x. apply H.
Qed.

Lemma impl_hprop : forall P Q : Prop,
    IsHProp Q -> IsHProp (P -> Q).
Proof.
  intros P Q H p q. apply functional_extensionality.
  intros. apply H.
Qed.

(* All negations are homotopy propositions. *)
Lemma not_hprop : forall P : Type, IsHProp (P -> False).
Proof.
  intros P p q. apply functional_extensionality.
  intros. contradiction.
Qed.

(* "IsHProp X" sounds like a proposition, because it asserts
   a property of the type X. And indeed: *)
Lemma hprop_hprop : forall X : Type,
    IsHProp (IsHProp X).
Proof.
  intros X p q.
  apply forall_hprop. intro x.
  apply forall_hprop. intro y. intros f g.
  apply (hset_hprop X p).
Qed.

Lemma hprop_hset : forall X : Type,
    IsHProp (IsHSet X).
Proof.
  intros X f g.
  apply functional_extensionality_dep. intro x.
  apply functional_extensionality_dep. intro y.
  apply functional_extensionality_dep. intro a.
  apply functional_extensionality_dep. intro b.
  apply (hset_hOneType). exact f.
Qed.

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Some facts and definitions about propositional and predicate extensionality

We investigate the relations between the following extensionality principles

- Proposition extensionality
- Predicate extensionality
- Propositional functional extensionality
- Provable-proposition extensionality
- Refutable-proposition extensionality
- Extensional proposition representatives
- Extensional predicate representatives
- Extensional propositional function representatives

Table of contents

1. Definitions

2.1 Predicate extensionality <-> Proposition extensionality + Propositional functional extensionality

2.2 Propositional extensionality -> Provable propositional extensionality

2.3 Propositional extensionality -> Refutable propositional extensionality

*)

Set Implicit Arguments.

(**********************************************************************)
(** * Definitions *)

(** Propositional extensionality *)

Local Notation PropositionalExtensionality :=
  (forall A B : Prop, (A <-> B) -> A = B).

(** Provable-proposition extensionality *)

Local Notation ProvablePropositionExtensionality :=
  (forall A:Prop, A -> A = True).

(** Refutable-proposition extensionality *)

Local Notation RefutablePropositionExtensionality :=
  (forall A:Prop, ~A -> A = False).

(** Predicate extensionality *)

Local Notation PredicateExtensionality :=
  (forall (A:Type) (P Q : A -> Prop), (forall x, P x <-> Q x) -> P = Q).

(** Propositional functional extensionality *)

Local Notation PropositionalFunctionalExtensionality :=
  (forall (A:Type) (P Q : A -> Prop), (forall x, P x = Q x) -> P = Q).

(**********************************************************************)
(** * Propositional and predicate extensionality                      *)

(**********************************************************************)
(** ** Predicate extensionality <-> Propositional extensionality + Propositional functional extensionality *)

Lemma PredExt_imp_PropExt : PredicateExtensionality -> PropositionalExtensionality.
Proof.
  intros Ext A B Equiv. 
  change A with ((fun _ => A) I).
  now rewrite Ext with (P := fun _ : True =>A) (Q := fun _ => B).
Qed.

Lemma PredExt_imp_PropFunExt : PredicateExtensionality -> PropositionalFunctionalExtensionality.
Proof.
  intros Ext A P Q Eq. apply Ext. intros x. now rewrite (Eq x).
Qed.

Lemma PropExt_and_PropFunExt_imp_PredExt :
  PropositionalExtensionality -> PropositionalFunctionalExtensionality -> PredicateExtensionality.
Proof.
  intros Ext FunExt A P Q Equiv.
  apply FunExt. intros x. now apply Ext.
Qed.

Theorem PropExt_and_PropFunExt_iff_PredExt :
  PropositionalExtensionality /\ PropositionalFunctionalExtensionality <-> PredicateExtensionality.
Proof.
  firstorder using PredExt_imp_PropExt, PredExt_imp_PropFunExt, PropExt_and_PropFunExt_imp_PredExt.
Qed.

(**********************************************************************)
(** ** Propositional extensionality and provable proposition extensionality *)

Lemma PropExt_imp_ProvPropExt : PropositionalExtensionality -> ProvablePropositionExtensionality.
Proof.
  intros Ext A Ha; apply Ext; split; trivial.
Qed.

(**********************************************************************)
(** ** Propositional extensionality and refutable proposition extensionality *)

Lemma PropExt_imp_RefutPropExt : PropositionalExtensionality -> RefutablePropositionExtensionality.
Proof.
  intros Ext A Ha; apply Ext; split; easy.
Qed.

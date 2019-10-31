(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** #<style> .doc { font-family: monospace; white-space: pre; } </style># **)

(** Compatibility layer for [under] and [setoid_rewrite].

 This file is intended to be required by [Require Import Setoid].

 In particular, we can use the [under] tactic with other relations
 than [eq] or [iff], e.g. a [RewriteRelation], by doing:
 [Require Import ssreflect. Require Setoid.]

 This file's instances have priority 12 > other stdlib instances
 and each [Under_rel] instance comes with a [Hint Cut] directive
 (otherwise Ring_polynom.v won't compile because of unbounded search).

 (Note: this file could be skipped when porting [under] to stdlib2.)
 *)

Require Import ssrclasses.
Require Import ssrunder.
Require Import RelationClasses.
Require Import Relation_Definitions.

(** Reconcile [Coq.Classes.RelationClasses.Reflexive] with
    [Coq.ssr.ssrclasses.Reflexive] *)

Instance compat_Reflexive :
  forall {A} {R : relation A},
    RelationClasses.Reflexive R ->
    ssrclasses.Reflexive R | 12.
Proof. now trivial. Qed.

(** Add instances so that ['Under[ F i ]] terms,
    that is, [Under_rel T R (F i) (?G i)] terms,
    can be manipulated with rewrite/setoid_rewrite with lemmas on [R].
    Note that this requires that [R] is a [Prop] relation, otherwise
    a [bool] relation may need to be "lifted": see the [TestPreOrder]
    section in test-suite/ssr/under.v *)

Instance Under_subrelation {A} (R : relation A) : subrelation R (Under_rel _ R) | 12.
Proof. now rewrite Under_relE. Qed.

(* see also Morphisms.trans_co_eq_inv_impl_morphism *)

Instance Under_Reflexive {A} (R : relation A) :
  RelationClasses.Reflexive R ->
  RelationClasses.Reflexive (Under_rel.Under_rel A R) | 12.
Proof. now rewrite Under_rel.Under_relE. Qed.

Hint Cut [_* Under_Reflexive Under_Reflexive] : typeclass_instances.

(* These instances are a bit off-topic given that (Under_rel A R) will
   typically be reflexive, to be able to trigger the [over] terminator

Instance under_Irreflexive {A} (R : relation A) :
  RelationClasses.Irreflexive R ->
  RelationClasses.Irreflexive (Under_rel.Under_rel A R) | 12.
Proof. now rewrite Under_rel.Under_relE. Qed.

Hint Cut [_* Under_Irreflexive Under_Irreflexive] : typeclass_instances.

Instance under_Asymmetric {A} (R : relation A) :
  RelationClasses.Asymmetric R ->
  RelationClasses.Asymmetric (Under_rel.Under_rel A R) | 12.
Proof. now rewrite Under_rel.Under_relE. Qed.

Hint Cut [_* Under_Asymmetric Under_Asymmetric] : typeclass_instances.

Instance under_StrictOrder {A} (R : relation A) :
  RelationClasses.StrictOrder R ->
  RelationClasses.StrictOrder (Under_rel.Under_rel A R) | 12.
Proof. now rewrite Under_rel.Under_relE. Qed.

Hint Cut [_* Under_Strictorder Under_Strictorder] : typeclass_instances.
 *)

Instance Under_Symmetric {A} (R : relation A) :
  RelationClasses.Symmetric R ->
  RelationClasses.Symmetric (Under_rel.Under_rel A R) | 12.
Proof. now rewrite Under_rel.Under_relE. Qed.

Hint Cut [_* Under_Symmetric Under_Symmetric] : typeclass_instances.

Instance Under_Transitive {A} (R : relation A) :
  RelationClasses.Transitive R ->
  RelationClasses.Transitive (Under_rel.Under_rel A R) | 12.
Proof. now rewrite Under_rel.Under_relE. Qed.

Hint Cut [_* Under_Transitive Under_Transitive] : typeclass_instances.

Instance Under_PreOrder {A} (R : relation A) :
  RelationClasses.PreOrder R ->
  RelationClasses.PreOrder (Under_rel.Under_rel A R) | 12.
Proof. now rewrite Under_rel.Under_relE. Qed.

Hint Cut [_* Under_PreOrder Under_PreOrder] : typeclass_instances.

Instance Under_PER {A} (R : relation A) :
  RelationClasses.PER R ->
  RelationClasses.PER (Under_rel.Under_rel A R) | 12.
Proof. now rewrite Under_rel.Under_relE. Qed.

Hint Cut [_* Under_PER Under_PER] : typeclass_instances.

Instance Under_Equivalence {A} (R : relation A) :
  RelationClasses.Equivalence R ->
  RelationClasses.Equivalence (Under_rel.Under_rel A R) | 12.
Proof. now rewrite Under_rel.Under_relE. Qed.

Hint Cut [_* Under_Equivalence Under_Equivalence] : typeclass_instances.

(* Don't handle Antisymmetric and PartialOrder classes for now,
   as these classes depend on two relation symbols... *)

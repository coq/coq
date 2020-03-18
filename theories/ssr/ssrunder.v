(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** #<style> .doc { font-family: monospace; white-space: pre; } </style># **)

(** Constants for under/over, to rewrite under binders using "context lemmas"

 Note: this file does not require [ssreflect]; it is both required by
 [ssrsetoid] and *exported* by [ssrunder].

 This preserves the following feature: we can use [Setoid] without
 requiring [ssreflect] and use [ssreflect] without requiring [Setoid].
*)

Require Import ssrclasses.

Module Type UNDER_REL.
Parameter Under_rel :
  forall (A : Type) (eqA : A -> A -> Prop), A -> A -> Prop.
Parameter Under_rel_from_rel :
  forall (A : Type) (eqA : A -> A -> Prop) (x y : A),
    @Under_rel A eqA x y -> eqA x y.
Parameter Under_relE :
  forall (A : Type) (eqA : A -> A -> Prop),
    @Under_rel A eqA = eqA.

(** [Over_rel, over_rel, over_rel_done]: for "by rewrite over_rel" *)
Parameter Over_rel :
  forall (A : Type) (eqA : A -> A -> Prop), A -> A -> Prop.
Parameter over_rel :
  forall (A : Type) (eqA : A -> A -> Prop) (x y : A),
    @Under_rel A eqA x y = @Over_rel A eqA x y.
Parameter over_rel_done :
  forall (A : Type) (eqA : A -> A -> Prop) (EeqA : Reflexive eqA) (x : A),
    @Over_rel A eqA x x.

(** [under_rel_done]: for Ltac-style over *)
Parameter under_rel_done :
  forall (A : Type) (eqA : A -> A -> Prop) (EeqA : Reflexive eqA) (x : A),
    @Under_rel A eqA x x.
Notation "''Under[' x ]" := (@Under_rel _ _ x _)
  (at level 8, format "''Under['  x  ]", only printing).
End UNDER_REL.

Module Export Under_rel : UNDER_REL.
Definition Under_rel (A : Type) (eqA : A -> A -> Prop) :=
  eqA.
Lemma Under_rel_from_rel :
  forall (A : Type) (eqA : A -> A -> Prop) (x y : A),
    @Under_rel A eqA x y -> eqA x y.
Proof. now trivial. Qed.
Lemma Under_relE (A : Type) (eqA : A -> A -> Prop) :
  @Under_rel A eqA = eqA.
Proof. now trivial. Qed.
Definition Over_rel := Under_rel.
Lemma over_rel :
  forall (A : Type) (eqA : A -> A -> Prop) (x y : A),
    @Under_rel A eqA x y = @Over_rel A eqA x y.
Proof. now trivial. Qed.
Lemma over_rel_done :
  forall (A : Type) (eqA : A -> A -> Prop) (EeqA : Reflexive eqA) (x : A),
    @Over_rel A eqA x x.
Proof. now unfold Over_rel. Qed.
Lemma under_rel_done :
  forall (A : Type) (eqA : A -> A -> Prop) (EeqA : Reflexive eqA) (x : A),
    @Under_rel A eqA x x.
Proof. now trivial. Qed.
End Under_rel.

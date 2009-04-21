(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Functional morphisms.
 
   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
   91405 Orsay, France *)

(* $Id$ *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.

Class Injective `(m : Proper (A -> B) (RA ++> RB) f) : Prop :=
  injective : forall x y : A, RB (f x) (f y) -> RA x y.

Class Surjective `(m : Proper (A -> B) (RA ++> RB) f) : Prop :=
  surjective : forall y, exists x : A, RB y (f x).

Definition Bijective `(m : Proper (A -> B) (RA ++> RB) (f : A -> B)) :=
  Injective m /\ Surjective m.

Class MonoMorphism `(m : Proper (A -> B) (eqA ++> eqB)) :=
  monic :> Injective m.

Class EpiMorphism `(m : Proper (A -> B) (eqA ++> eqB)) :=
  epic :> Surjective m.

Class IsoMorphism `(m : Proper (A -> B) (eqA ++> eqB)) :=
  { monomorphism :> MonoMorphism m ; epimorphism :> EpiMorphism m }.

Class AutoMorphism `(m : Proper (A -> A) (eqA ++> eqA)) {I : IsoMorphism m}.

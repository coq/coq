(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
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

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.

Class [ m : Morphism (A -> B) (RA ++> RB) f ] => Injective : Prop :=
  injective : forall x y : A, RB (f x) (f y) -> RA x y.

Class [ m : Morphism (A -> B) (RA ++> RB) f ] => Surjective : Prop :=
  surjective : forall y, exists x : A, RB y (f x).

Definition Bijective [ m : Morphism (A -> B) (RA ++> RB) (f : A -> B) ] :=
  Injective m /\ Surjective m.

Class [ m : Morphism (A -> B) (eqA ++> eqB) ] => MonoMorphism :=
  monic :> Injective m.

Class [ m : Morphism (A -> B) (eqA ++> eqB) ] => EpiMorphism :=
  epic :> Surjective m.

Class [ m : Morphism (A -> B) (eqA ++> eqB) ] => IsoMorphism :=
  monomorphism :> MonoMorphism m ; epimorphism :> EpiMorphism m.

Class [ m : Morphism (A -> A) (eqA ++> eqA), ! IsoMorphism m ] => AutoMorphism.

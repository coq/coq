(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certified Haskell Prelude.
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
 *              91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Require Import Coq.Program.Program.

Set Implicit Arguments.
Unset Strict Implicit.

(** We first define setoids on a carrier, it amounts to an equivalence relation. 
   Now [equiv] is overloaded for every [Setoid].
*)

Require Export Coq.Relations.Relations.

Class Setoid (carrier : Type) (equiv : relation carrier) where
  equiv_prf : equivalence carrier equiv.

(** Overloaded notation for setoid equivalence. Not to be confused with [eq] and [=]. *)

Definition equiv [ Setoid A R ] : _ := R.

Infix "==" := equiv (at level 70, no associativity).

Definition equiv_refl [ Setoid A R ] : forall x : A, R x x := equiv_refl _ _ equiv_prf.
Definition equiv_sym [ Setoid A R ] : forall x y : A, R x y -> R y x := equiv_sym _ _ equiv_prf.
Definition equiv_trans [ Setoid A R ] : forall x y z : A, R x y -> R y z -> R x z := equiv_trans _ _ equiv_prf.

Ltac refl :=
  match goal with
    [ |- ?R ?X _ ] => apply (equiv_refl (R:=R) X)
  end.

Ltac sym := 
  match goal with
    [ |- ?R ?X ?Y ] => apply (equiv_sym (R:=R) (x:=Y) (y:=X))
  end.

Ltac trans Y := 
  match goal with
    [ |- ?R ?X ?Z ] => apply (equiv_trans (R:=R) (x:=X) (y:=Y) (z:=Z))
  end.

Definition respectful [ sa : Setoid a eqa, sb : Setoid b eqb ] (m : a -> b) : Prop :=
  forall x y, eqa x y -> eqb (m x) (m y).

Class [ Setoid a eqa, Setoid b eqb ] => Morphism (m : a -> b) where
  respect : respectful m.

(** Here we build a setoid instance for functions which relates respectful ones only. *)

Definition respecting [ Setoid a R, Setoid b R' ] : Type := { morph : a -> b | respectful morph }.

Obligations Tactic := try red ; program_simpl ; unfold equiv in * ; try tauto.

Program Instance [ sa : Setoid a R, sb : Setoid b R' ] => arrow_setoid : 
  Setoid ({ morph : a -> b | respectful morph })
  (fun (f g : respecting) => forall (x y : a), R x y -> R' (`f x) (`g y)) where
  equiv_prf := Build_equivalence _ _ _ _ _.

Next Obligation.
Proof.
  trans (y x0) ; eauto.
  apply H.
  refl.
Qed.

Next Obligation.
Proof.
  sym ; apply H.
  sym ; auto.
Qed.

(** We redefine respect for binary morphims because we cannot get a satisfying instance of [Setoid (a -> b)] from 
   some arbitrary domain and codomain setoids. We can define it on respectful Coq functions though, see arrow_setoid.*)

Definition binary_respectful [ sa : Setoid a eqa, sb : Setoid b eqb, Setoid c eqc ] (m : a -> b -> c) : Prop :=
  forall x y, eqa x y -> 
    forall z w, eqb z w -> eqc (m x z) (m y w).

Class [ sa : Setoid a eqa, sb : Setoid b eqb, sc : Setoid c eqc ] => BinaryMorphism (m : a -> b -> c) where
  respect2 : binary_respectful m.

Program Instance iff_setoid : Setoid Prop iff where
  equiv_prf := @Build_equivalence _ _ iff_refl iff_trans iff_sym.

Program Instance not_morphism : Morphism Prop iff Prop iff not where.

Program Instance and_morphism : ? BinaryMorphism iff_setoid iff_setoid iff_setoid and where.

Set Printing All.

Print and_morphism.
Print BinaryMorphism.

(* We make the setoids implicit, they're always [iff] *)

Implicit Arguments Enriching BinaryMorphism [[!sa] [!sb] [!sc]].

Print BinaryMorphism.

Program Instance or_morphism : ? BinaryMorphism or where.

Definition impl (A B : Prop) := A -> B.

Program Instance impl_morphism : ? BinaryMorphism impl where.

Next Obligation.
Proof.
  unfold impl. tauto.
Qed.

Unset Printing All.

Print respect.

Program Instance [ Setoid a R ] => setoid_morphism : ? BinaryMorphism R where.

Next Obligation.
Proof with auto.
  split ; intros.
  trans x. sym... trans z...
  trans y... trans w... sym...
Qed.
  
Definition iff_morphism : BinaryMorphism iff := setoid_morphism.

Existing Instance iff_morphism.
Print BinaryMorphism.

Implicit Arguments eq [[A]].

Program Instance eq_setoid : Setoid A eq where
  equiv_prf := Build_equivalence _ _ _ _ _.

Program Instance eq_morphism : BinaryMorphism A eq A eq Prop iff eq where.

Program Instance arrow_morphism : BinaryMorphism A eq B eq C eq m where.

Implicit Arguments arrow_morphism [[A] [B] [C]].

Program Instance type_setoid : Setoid Type (fun x y => x = y) where
  equiv_prf := Build_equivalence _ _ _ _ _.

Lemma setoid_subst : forall (x y : Type), x == y -> x -> y.
Proof.
  intros.
  rewrite <- H.
  apply X.
Qed.

Lemma prop_setoid_subst : forall (x y : Prop), x == y -> x -> y.
Proof.
  intros.
  pose (equiv_sym H).
  clrewrite e.
  apply H0.
Qed.

Goal not True == not (not False) -> ((not True -> True)) \/ True.
  intros.
  clrewrite H.
  right ; auto.
Defined.

Print Unnamed_thm.

Definition reduced_thm := Eval compute in Unnamed_thm.

Print reduced_thm.

Lemma foo [ Setoid a R ] : True. (* forall x y, R x y -> x -> y. *)
Proof.
  intros.
  Print respect2.
  pose setoid_morphism.
  pose (respect2 (b0:=b)).
  simpl in b0.
  unfold binary_respectful in b0.
  pose (arrow_morphism R).
  pose (respect2 (b0:=b1)).
  unfold binary_respectful in b2.

  pose (eq_morphism (A:=a)).
  pose (respect2 (b0:=b3)).
  unfold binary_respectful in b4.
  exact I.
Qed.

Goal forall A B C (H : A <-> B) (H' : B <-> C), A /\ B <-> B /\ C.
  intros.
  clrewrite H.
  clrewrite H'.
  reflexivity.
Defined.

Print Unnamed_thm0.


Goal forall A B C (H : A <-> B) (H' : B <-> C), A /\ B <-> B /\ C.
  intros.
  rewrite H.
  rewrite H'.
  reflexivity.
Defined.

Require Import Setoid_tac.
Require Import Setoid_Prop.
Print Unnamed_thm1.


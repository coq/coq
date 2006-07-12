(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This module proves the validity of
    - well-founded recursion (also called course of values)
    - well-founded induction

    from a well-founded ordering on a given set *)

Set Implicit Arguments.

Require Import Notations.
Require Import Logic.
Require Import Datatypes.

(** Well-founded induction principle on [Prop] *)

Section Well_founded.

 Variable A : Type.
 Variable R : A -> A -> Prop.

 (** The accessibility predicate is defined to be non-informative *)

 Inductive Acc (x: A) : Prop :=
     Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.

 Lemma Acc_inv : forall x:A, Acc x -> forall y:A, R y x -> Acc y.
  destruct 1; trivial.
 Defined.

  (** Informative elimination :
     [let Acc_rec F = let rec wf x = F x wf in wf] *)

 Section AccRecType.
  Variable P : A -> Type.
  Variable F : forall x:A,
    (forall y:A, R y x -> Acc y) -> (forall y:A, R y x -> P y) -> P x.

  Fixpoint Acc_rect (x:A) (a:Acc x) {struct a} : P x :=
    F (Acc_inv a) (fun (y:A) (h:R y x) => Acc_rect (Acc_inv a h)).

 End AccRecType.

 Definition Acc_rec (P:A -> Set) := Acc_rect P.

 (** A simplified version of [Acc_rect] *)

 Section AccIter.
  Variable P : A -> Type.
  Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.

  Fixpoint Acc_iter (x:A) (a:Acc x) {struct a} : P x :=
    F (fun (y:A) (h:R y x) => Acc_iter (Acc_inv a h)).

 End AccIter.

 (** A relation is well-founded if every element is accessible *)

 Definition well_founded := forall a:A, Acc a.

 (** Well-founded induction on [Set] and [Prop] *)

 Hypothesis Rwf : well_founded.

 Theorem well_founded_induction_type :
  forall P:A -> Type,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
 Proof.
  intros; apply (Acc_iter P); auto.
 Defined.

 Theorem well_founded_induction :
  forall P:A -> Set,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
 Proof.
  exact (fun P:A -> Set => well_founded_induction_type P).
 Defined.

 Theorem well_founded_ind :
  forall P:A -> Prop,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
 Proof.
  exact (fun P:A -> Prop => well_founded_induction_type P).
 Defined.

(** Building fixpoints  *) 

 Section FixPoint.

  Variable P : A -> Type.
  Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.

  Notation Fix_F := (Acc_iter P F) (only parsing). (* alias *)

  Definition Fix (x:A) := Acc_iter P F (Rwf x).

  (** Proof that [well_founded_induction] satisfies the fixpoint equation. 
      It requires an extra property of the functional *)

  Hypothesis
    F_ext :
      forall (x:A) (f g:forall y:A, R y x -> P y),
        (forall (y:A) (p:R y x), f y p = g y p) -> F f = F g.

  Scheme Acc_inv_dep := Induction for Acc Sort Prop.

  Lemma Fix_F_eq :
   forall (x:A) (r:Acc x),
     F (fun (y:A) (p:R y x) => Fix_F y (Acc_inv r p)) = Fix_F x r.
  Proof. 
   destruct r using Acc_inv_dep; auto.
  Qed.

  Lemma Fix_F_inv : forall (x:A) (r s:Acc x), Fix_F x r = Fix_F x s.
  Proof.
   intro x; induction (Rwf x); intros.
   rewrite <- (Fix_F_eq r); rewrite <- (Fix_F_eq s); intros.
   apply F_ext; auto.
  Qed.

  Lemma Fix_eq : forall x:A, Fix x = F (fun (y:A) (p:R y x) => Fix y).
  Proof.
   intro x; unfold Fix in |- *.
   rewrite <- (Fix_F_eq (x:=x)).
   apply F_ext; intros.
   apply Fix_F_inv.
  Qed.

 End FixPoint.

End Well_founded. 

(** A recursor over pairs *)

Section Well_founded_2.

  Variables A B : Set.
  Variable R : A * B -> A * B -> Prop.

  Variable P : A -> B -> Type. 

  Section Acc_iter_2.
  Variable
    F :
      forall (x:A) (x':B),
        (forall (y:A) (y':B), R (y, y') (x, x') -> P y y') -> P x x'.

  Fixpoint Acc_iter_2 (x:A) (x':B) (a:Acc R (x, x')) {struct a} : 
   P x x' :=
    F
      (fun (y:A) (y':B) (h:R (y, y') (x, x')) =>
         Acc_iter_2 (x:=y) (x':=y') (Acc_inv a (y, y') h)).
  End Acc_iter_2.

  Hypothesis Rwf : well_founded R.

  Theorem well_founded_induction_type_2 :
   (forall (x:A) (x':B),
      (forall (y:A) (y':B), R (y, y') (x, x') -> P y y') -> P x x') ->
   forall (a:A) (b:B), P a b.
  Proof.
   intros; apply Acc_iter_2; auto.
  Defined.

End Well_founded_2.

Notation Fix_F := Acc_iter (only parsing). (* compatibility *)

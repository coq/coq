(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This module defines type constructors for types in [Type]
    ([Datatypes.v] and [Logic.v] defined them for types in [Set]) *)

Set Implicit Arguments.

Require Import Datatypes.
Require Export Logic.

(** Negation of a type in [Type] *)

Definition notT (A:Type) := A -> False.

(** Properties of [identity] *)

Section identity_is_a_congruence.

 Variables A B : Type.
 Variable f : A -> B.

 Variables x y z : A.
 
 Lemma sym_id : identity x y -> identity y x.
 Proof.
  destruct 1; trivial.
 Defined.

 Lemma trans_id : identity x y -> identity y z -> identity x z.
 Proof.
  destruct 2; trivial.
 Defined.

 Lemma congr_id : identity x y -> identity (f x) (f y).
 Proof.
  destruct 1; trivial.
 Defined.

 Lemma sym_not_id : notT (identity x y) -> notT (identity y x).
 Proof.
  red in |- *; intros H H'; apply H; destruct H'; trivial.
 Qed.

End identity_is_a_congruence.

Definition identity_ind_r :
  forall (A:Type) (a:A) (P:A -> Prop), P a -> forall y:A, identity y a -> P y.
 intros A x P H y H0; case sym_id with (1 := H0); trivial.
Defined.

Definition identity_rec_r :
  forall (A:Type) (a:A) (P:A -> Set), P a -> forall y:A, identity y a -> P y.
 intros A x P H y H0; case sym_id with (1 := H0); trivial.
Defined.

Definition identity_rect_r :
  forall (A:Type) (a:A) (P:A -> Type), P a -> forall y:A, identity y a -> P y.
 intros A x P H y H0; case sym_id with (1 := H0); trivial.
Defined.

Hint Immediate sym_id sym_not_id: core v62.

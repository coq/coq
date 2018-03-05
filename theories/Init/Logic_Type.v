(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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

 Lemma identity_sym : identity x y -> identity y x.
 Proof.
  destruct 1; trivial.
 Defined.

 Lemma identity_trans : identity x y -> identity y z -> identity x z.
 Proof.
  destruct 2; trivial.
 Defined.

 Lemma identity_congr : identity x y -> identity (f x) (f y).
 Proof.
  destruct 1; trivial.
 Defined.

 Lemma not_identity_sym : notT (identity x y) -> notT (identity y x).
 Proof.
  red; intros H H'; apply H; destruct H'; trivial.
 Qed.

End identity_is_a_congruence.

Definition identity_ind_r :
  forall (A:Type) (a:A) (P:A -> Prop), P a -> forall y:A, identity y a -> P y.
 intros A x P H y H0; case identity_sym with (1 := H0); trivial.
Defined.

Definition identity_rec_r :
  forall (A:Type) (a:A) (P:A -> Set), P a -> forall y:A, identity y a -> P y.
 intros A x P H y H0; case identity_sym with (1 := H0); trivial.
Defined.

Definition identity_rect_r :
  forall (A:Type) (a:A) (P:A -> Type), P a -> forall y:A, identity y a -> P y.
 intros A x P H y H0; case identity_sym with (1 := H0); trivial.
Defined.

Hint Immediate identity_sym not_identity_sym: core.

Notation refl_id := identity_refl (only parsing).
Notation sym_id := identity_sym (only parsing).
Notation trans_id := identity_trans (only parsing).
Notation sym_not_id := not_identity_sym (only parsing).

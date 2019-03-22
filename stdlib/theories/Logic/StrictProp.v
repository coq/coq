(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Utilities for SProp users. *)

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Record Box (A:SProp) : Prop := box { unbox : A }.
Arguments box {_} _.
Arguments unbox {_} _.

Inductive Squash (A:Type) : SProp := squash : A -> Squash A.
Arguments squash {_} _.

Inductive sEmpty : SProp :=.

Inductive sUnit : SProp := stt.
Definition sUnit_rect (P:sUnit -> Type) (v:P stt) (u:sUnit) : P u := v.
Definition sUnit_rec (P:sUnit -> Set) (v:P stt) (u:sUnit) : P u := v.
Definition sUnit_ind (P:sUnit -> Prop) (v:P stt) (u:sUnit) : P u := v.

Set Primitive Projections.
Record Ssig {A:Type} (P:A->SProp) := Sexists { Spr1 : A; Spr2 : P Spr1 }.
Arguments Sexists {_} _ _ _.
Arguments Spr1 {_ _} _.
Arguments Spr2 {_ _} _.

Lemma Spr1_inj {A P} {a b : @Ssig A P} (e : Spr1 a = Spr1 b) : a = b.
Proof.
  destruct a,b;simpl in e.
  destruct e. reflexivity.
Defined.

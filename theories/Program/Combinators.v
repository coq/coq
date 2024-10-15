(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** * Proofs about standard combinators, exports functional extensionality.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Stdlib.Program.Basics.
Require Export FunctionalExtensionality.

Open Scope program_scope.

(** Composition has [id] for neutral element and is associative. *)

Lemma compose_id_left : forall A B (f : A -> B), id ∘ f = f.
Proof.
  intros.
  reflexivity.
Qed.

Lemma compose_id_right : forall A B (f : A -> B), f ∘ id = f.
Proof.
  intros.
  reflexivity.
Qed.

Lemma compose_assoc : forall A B C D (f : A -> B) (g : B -> C) (h : C -> D),
  h ∘ g ∘ f = h ∘ (g ∘ f).
Proof.
  intros.
  reflexivity.
Qed.

Global Hint Rewrite @compose_id_left @compose_id_right : core.
Global Hint Rewrite <- @compose_assoc : core.

(** [flip] is involutive. *)

Lemma flip_flip : forall A B C, @flip A B C ∘ flip = id.
Proof.
  intros.
  reflexivity.
Qed.

(** [uncurry] and [curry] are each others inverses. *)

Lemma curry_uncurry : forall A B C, @curry A B C ∘ uncurry = id.
Proof.
  intros.
  reflexivity.
Qed.

Lemma uncurry_curry : forall A B C, @uncurry A B C ∘ curry = id.
Proof.
  simpl ; intros.
  unfold curry, uncurry, compose.
  extensionality x ; extensionality p.
  destruct p ; simpl ; reflexivity.
Qed.

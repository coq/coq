(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** * Proofs about standard combinators, exports functional extensionality.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Coq.Program.Basics.
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

Hint Rewrite @compose_id_left @compose_id_right : core.
Hint Rewrite <- @compose_assoc : core.

(** [flip] is involutive. *)

Lemma flip_flip : forall A B C, @flip A B C ∘ flip = id.
Proof.
  intros.
  reflexivity.
Qed.

(** [prod_curry] and [prod_uncurry] are each others inverses. *)

Lemma prod_uncurry_curry : forall A B C, @prod_uncurry A B C ∘ prod_curry = id.
Proof.
  intros.
  reflexivity.
Qed.

Lemma prod_curry_uncurry : forall A B C, @prod_curry A B C ∘ prod_uncurry = id.
Proof.
  simpl ; intros.
  unfold prod_uncurry, prod_curry, compose.
  extensionality x ; extensionality p.
  destruct p ; simpl ; reflexivity.
Qed.

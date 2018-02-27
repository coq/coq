(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file provides a constructive form of indefinite description that
    allows building choice functions; this is weaker than Hilbert's
    epsilon operator (which implies weakly classical properties) but
    stronger than the axiom of choice (which cannot be used outside
    the context of a theorem proof). *)

Require Import ChoiceFacts.

Set Implicit Arguments.

Axiom constructive_indefinite_description :
  forall (A : Type) (P : A->Prop),
    (exists x, P x) -> { x : A | P x }.

Lemma constructive_definite_description :
  forall (A : Type) (P : A->Prop),
    (exists! x, P x) -> { x : A | P x }.
Proof.
  intros; apply constructive_indefinite_description; firstorder.
Qed.

Lemma functional_choice :
  forall (A B : Type) (R:A->B->Prop),
    (forall x : A, exists y : B, R x y) ->
    (exists f : A->B, forall x : A, R x (f x)).
Proof.
  apply constructive_indefinite_descr_fun_choice.
  exact constructive_indefinite_description.
Qed.

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file provides classical logic and functional choice; this
    especially provides both indefinite descriptions and choice functions
    but this is weaker than providing epsilon operator and classical logic
    as the indefinite descriptions provided by the axiom of choice can
    be used only in a propositional context (especially, they cannot
    be used to build choice functions outside the scope of a theorem
    proof) *)

(** This file extends ClassicalUniqueChoice.v with full choice.
    As ClassicalUniqueChoice.v, it implies the double-negation of
    excluded-middle in [Set] and leads to a classical world populated
    with non computable functions. Especially it conflicts with the
    impredicativity of [Set], knowing that [true<>false] in [Set].  *)

Require Export ClassicalUniqueChoice.
Require Export RelationalChoice.
Require Import ChoiceFacts.

Set Implicit Arguments.

Definition subset (U:Type) (P Q:U->Prop) : Prop := forall x, P x -> Q x.

Theorem singleton_choice :
  forall (A : Type) (P : A->Prop),
  (exists x : A, P x) -> exists P' : A->Prop, subset P' P /\ exists! x, P' x.
Proof.
intros A P H.
destruct (relational_choice unit A (fun _ => P) (fun _ => H)) as (R',(Hsub,HR')).
exists (R' tt); firstorder.
Qed.

Theorem choice :
 forall (A B : Type) (R : A->B->Prop),
   (forall x : A, exists y : B, R x y) ->
    exists f : A->B, (forall x : A, R x (f x)).
Proof.
intros A B.
apply description_rel_choice_imp_funct_choice.
exact (unique_choice A B).
exact (relational_choice A B).
Qed.

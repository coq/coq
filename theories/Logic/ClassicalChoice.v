(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This file provides classical logic, and functional choice *)

(** This file extends ClassicalUniqueChoice.v with the axiom of choice.
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

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file provides classical logic and definite description, which is
    equivalent to providing classical logic and Church's iota operator *)

(** Classical logic and definite descriptions implies excluded-middle
    in [Set] and leads to a classical world populated with non
    computable functions. It conflicts with the impredicativity of
    [Set] *)

Set Implicit Arguments.

Require Export Classical.   (* Axiomatize classical reasoning *)
Require Export Description. (* Axiomatize constructive form of Church's iota *)
Require Import ChoiceFacts.

Local Notation inhabited A := A (only parsing).

(** The idea for the following proof comes from [ChicliPottierSimpson02] *)

Theorem excluded_middle_informative : forall P:Prop, {P} + {~ P}.
Proof.
apply
  (constructive_definite_descr_excluded_middle
   constructive_definite_description classic).
Qed.

Theorem classical_definite_description :
  forall (A : Type) (P : A->Prop), inhabited A ->
  { x : A | (exists! x : A, P x) -> P x }.
Proof.
intros A P i.
destruct (excluded_middle_informative (exists! x, P x)) as [Hex|HnonP].
  apply constructive_definite_description with (P:= fun x => (exists! x : A, P x) -> P x).
  destruct Hex as (x,(Hx,Huni)).
  exists x; split.
    intros _; exact Hx.
    firstorder.
exists i; tauto.
Qed.

(** Church's iota operator *)

Definition iota (A : Type) (i:inhabited A) (P : A->Prop) : A
  := proj1_sig (classical_definite_description P i).

Definition iota_spec (A : Type) (i:inhabited A) (P : A->Prop) :
  (exists! x:A, P x) -> P (iota i P)
  := proj2_sig (classical_definite_description P i).

(** Axiom of unique "choice" (functional reification of functional relations) *)
Theorem dependent_unique_choice :
  forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
    (forall x:A, exists! y : B x, R x y) ->
    (exists f : (forall x:A, B x), forall x:A, R x (f x)).
Proof.
intros A B R H.
assert (Hexuni:forall x, exists! y, R x y).
  intro x. apply H.
exists (fun x => proj1_sig (constructive_definite_description (R x) (Hexuni x))).
intro x.
apply (proj2_sig (constructive_definite_description (R x) (Hexuni x))).
Qed.

Theorem unique_choice :
  forall (A B:Type) (R:A -> B -> Prop),
    (forall x:A,  exists! y : B, R x y) ->
    (exists f : A -> B, forall x:A, R x (f x)).
Proof.
intros A B.
apply dependent_unique_choice with (B:=fun _:A => B).
Qed.

(** Compatibility lemmas *)

Unset Implicit Arguments.

Definition dependent_description := dependent_unique_choice.
Definition description := unique_choice.

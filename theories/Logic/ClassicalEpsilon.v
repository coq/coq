(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** *** This file provides classical logic and indefinite description
    (Hilbert's epsilon operator) *)

(** Classical epsilon's operator (i.e. indefinite description) implies
    excluded-middle in [Set] and leads to a classical world populated
    with non computable functions. It conflicts with the
    impredicativity of [Set] *)

Require Export Classical.
Require Import ChoiceFacts.

Set Implicit Arguments.

Notation Local "'inhabited' A" := A (at level 200, only parsing).

Axiom constructive_indefinite_description :
  forall (A : Type) (P : A->Prop), 
  (ex P) -> { x : A | P x }.

Lemma constructive_definite_description :
  forall (A : Type) (P : A->Prop), 
  (exists! x : A, P x) -> { x : A | P x }.
Proof.
intros; apply constructive_indefinite_description; firstorder.
Qed.

Theorem excluded_middle_informative : forall P:Prop, {P} + {~ P}.
Proof.
apply 
  (constructive_definite_descr_excluded_middle 
   constructive_definite_description classic).
Qed.

Theorem classical_indefinite_description : 
  forall (A : Type) (P : A->Prop), inhabited A ->
  { x : A | ex P -> P x }.
Proof.
intros A P i.
destruct (excluded_middle_informative (exists x, P x)) as [Hex|HnonP].
  apply constructive_indefinite_description with (P:= fun x => ex P -> P x).
  destruct Hex as (x,Hx).
    exists x; intros _; exact Hx.
    firstorder.
Qed.

(** Hilbert's epsilon operator *)

Definition epsilon (A : Type) (i:inhabited A) (P : A->Prop) : A
  := proj1_sig (classical_indefinite_description P i).

Definition epsilon_spec (A : Type) (i:inhabited A) (P : A->Prop) : 
  (ex P) -> P (epsilon i P)
  := proj2_sig (classical_indefinite_description P i).

Opaque epsilon.

(** Open question: is classical_indefinite_description constructively
    provable from [relational_choice] and
    [constructive_definite_description] (at least, using the fact that
    [functional_choice] is provable from [relational_choice] and
    [unique_choice], we know that the double negation of
    [classical_indefinite_description] is provable (see
    [relative_non_contradiction_of_indefinite_desc]). *)

(** Remark: we use [ex P] rather than [exists x, P x] (which is [ex
    (fun x => P x)] to ease unification *)

(** *** Weaker lemmas (compatibility lemmas) *)

Theorem choice :
 forall (A B : Type) (R : A->B->Prop),
   (forall x : A, exists y : B, R x y) ->
   (exists f : A->B, forall x : A, R x (f x)).
Proof.
intros A B R H.
exists (fun x => proj1_sig (constructive_indefinite_description (H x))).
intro x.
apply (proj2_sig (constructive_indefinite_description  (H x))).
Qed.


(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This module states the axiom of (dependent) functional extensionality and (dependent) eta-expansion.
   It introduces a tactic [extensionality] to apply the axiom of extensionality to an equality goal. *)

(** The converse of functional extensionality. *)

Lemma equal_f : forall {A B : Type} {f g : A -> B}, 
  f = g -> forall x, f x = g x.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

(** Statements of functional extensionality for simple and dependent functions. *)

Axiom functional_extensionality_dep : forall {A} {B : A -> Type}, 
  forall (f g : forall x : A, B x), 
  (forall x, f x = g x) -> f = g.

Lemma functional_extensionality {A B} (f g : A -> B) : 
  (forall x, f x = g x) -> f = g.
Proof.
  intros ; eauto using @functional_extensionality_dep.
Qed.

(** Apply [functional_extensionality], introducing variable x. *)

Tactic Notation "extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] => 
    (apply (@functional_extensionality _ _ X Y) || 
     apply (@functional_extensionality_dep _ _ X Y)) ; intro x
  end.

(** Eta expansion follows from extensionality. *)

Lemma eta_expansion_dep {A} {B : A -> Type} (f : forall x : A, B x) :
  f = fun x => f x.
Proof.
  intros.
  extensionality x.
  reflexivity.
Qed.
  
Lemma eta_expansion {A B} (f : A -> B) : f = fun x => f x.
Proof.
  intros A B f. apply (eta_expansion_dep f).
Qed.

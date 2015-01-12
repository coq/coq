(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

Lemma equal_f_dep : forall {A B} {f g : forall (x : A), B x},
  f = g -> forall x, f x = g x.
Proof.
intros A B f g <- H; reflexivity.
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

(** Extensionality of [forall]s follows from functional extensionality. *)
Lemma forall_extensionality {A} {B C : A -> Type} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof.
  apply functional_extensionality in H. destruct H. reflexivity.
Defined.

Lemma forall_extensionalityP {A} {B C : A -> Prop} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof.
  apply functional_extensionality in H. destruct H. reflexivity.
Defined.

Lemma forall_extensionalityS {A} {B C : A -> Set} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof.
  apply functional_extensionality in H. destruct H. reflexivity.
Defined.

(** Apply [functional_extensionality], introducing variable x. *)

Tactic Notation "extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
    (apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y) ||
     apply forall_extensionalityP ||
     apply forall_extensionalityS ||
     apply forall_extensionality) ; intro x
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
  apply (eta_expansion_dep f).
Qed.

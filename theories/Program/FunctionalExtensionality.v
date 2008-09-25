(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** This module states the axiom of (dependent) functional extensionality and (dependent) eta-expansion.
   It introduces a tactic [extensionality] to apply the axiom of extensionality to an equality goal. 

   It also defines two lemmas for expansion of fixpoint defs using extensionnality and proof-irrelevance
   to avoid a side condition on the functionals. *)
   
Require Import Coq.Program.Utils.
Require Import Coq.Program.Wf.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.

(** The converse of functional extensionality. *)

Lemma equal_f : forall A B : Type, forall (f g : A -> B), 
  f = g -> forall x, f x = g x.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

(** Statements of functional extensionality for simple and dependent functions. *)

Axiom fun_extensionality_dep : forall A, forall B : (A -> Type), 
  forall (f g : forall x : A, B x), 
  (forall x, f x = g x) -> f = g.

Lemma fun_extensionality : forall A B (f g : A -> B), 
  (forall x, f x = g x) -> f = g.
Proof.
  intros ; apply fun_extensionality_dep.
  assumption.
Qed.

Hint Resolve fun_extensionality fun_extensionality_dep : program.

(** Apply [fun_extensionality], introducing variable x. *)

Tactic Notation "extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] => apply (@fun_extensionality _ _ X Y) || apply (@fun_extensionality_dep _ _ X Y) ; intro x
  end.

(** Eta expansion follows from extensionality. *)

Lemma eta_expansion_dep : forall A (B : A -> Type) (f : forall x : A, B x), 
  f = fun x => f x.
Proof.
  intros.
  extensionality x.
  reflexivity.
Qed.
  
Lemma eta_expansion : forall A B (f : A -> B), 
  f = fun x => f x.
Proof.
  intros ; apply eta_expansion_dep.
Qed.

(** The two following lemmas allow to unfold a well-founded fixpoint definition without
   restriction using the functional extensionality axiom. *)

(** For a function defined with Program using a well-founded order. *)

Program Lemma fix_sub_eq_ext :
  forall (A : Set) (R : A -> A -> Prop) (Rwf : well_founded R)
    (P : A -> Set)
    (F_sub : forall x : A, (forall (y : A | R y x), P y) -> P x),
    forall x : A,
      Fix_sub A R Rwf P F_sub x =
        F_sub x (fun (y : A | R y x) => Fix A R Rwf P F_sub y).
Proof.
  intros ; apply Fix_eq ; auto.
  intros.
  assert(f = g).
  extensionality y ; apply H.
  rewrite H0 ; auto.
Qed.

(** For a function defined with Program using a measure. *)

Program Lemma fix_sub_measure_eq_ext :
  forall (A : Type) (f : A -> nat) (P : A -> Type)
    (F_sub : forall x : A, (forall (y : A | f y < f x), P y) -> P x),
    forall x : A,
      Fix_measure_sub A f P F_sub x =
        F_sub x (fun (y : A | f y < f x) => Fix_measure_sub A f P F_sub y).
Proof.
  intros ; apply Fix_measure_eq ; auto.
  intros.
  assert(f0 = g).
  extensionality y ; apply H.
  rewrite H0 ; auto.
Qed.

(** Tactics to fold/unfold definitions based on [Fix_measure_sub]. *)

Ltac fold_sub f :=
  match goal with
    | [ |- ?T ] => 
      match T with
        appcontext C [ @Fix_measure_sub _ _ _ _ ?arg ] => 
        let app := context C [ f arg ] in
         change app
      end
  end.

Ltac unfold_sub f fargs := 
  set (call:=fargs) ; unfold f in call ; unfold call ; clear call ; 
  rewrite fix_sub_measure_eq_ext ; repeat fold_sub fargs ; simpl proj1_sig.

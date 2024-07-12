(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** Reformulation of the Wf module using subsets where possible, providing
   the support for [Program]'s treatment of well-founded definitions. *)

Require Import Stdlib.Init.Wf.
Require Import Stdlib.Program.Utils.
Require Import Stdlib.Program.Wf.

Local Open Scope program_scope.

(** This module provides the fixpoint equation provided one assumes
   functional extensionality. *)
From Stdlib.Logic Require Import FunctionalExtensionality.

Module WfExtensionality.

  (** The two following lemmas allow to unfold a well-founded fixpoint definition without
     restriction using the functional extensionality axiom. *)

  (** For a function defined with Program using a well-founded order. *)

  Program Lemma fix_sub_eq_ext :
    forall (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R)
      (P : A -> Type)
      (F_sub : forall x : A, (forall y:{y : A | R y x}, P (` y)) -> P x),
      forall x : A,
        Fix_sub A R Rwf P F_sub x =
          F_sub x (fun y:{y : A | R y x} => Fix_sub A R Rwf P F_sub (` y)).
  Proof.
    intros A R Rwf P F_sub x; apply Fix_eq ; auto.
    intros ? f g H.
    assert(f = g) as H0.
    - extensionality y ; apply H.
    - rewrite H0 ; auto.
  Qed.

  (** Tactic to unfold once a definition based on [Fix_sub]. *)

  Ltac unfold_sub f fargs :=
    set (call:=fargs) ; unfold f in call ; unfold call ; clear call ;
      rewrite fix_sub_eq_ext ; repeat fold_sub f ; simpl proj1_sig.

End WfExtensionality.

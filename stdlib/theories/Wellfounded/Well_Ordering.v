(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Author: Cristina Cornes.
    From: Constructing Recursion Operators in Type Theory
    L. Paulson  JSC (1986) 2, 325-355 *)

Require Import EqdepFacts.

#[universes(template)]
Inductive WO (A : Type) (B : A -> Type) : Type :=
  sup : forall (a:A) (f:B a -> WO A B), WO A B.

Section WellOrdering.
  Variable A : Type.
  Variable B : A -> Type.

  Notation WO := (WO A B).

  Inductive le_WO : WO -> WO -> Prop :=
    le_sup : forall (a:A) (f:B a -> WO) (v:B a), le_WO (f v) (sup _ _ a f).

  Lemma le_WO_inv x y : le_WO x y -> exists a f v, f v = x /\ sup _ _ a f = y.
  Proof.
    destruct 1;eauto.
  Qed.

  Theorem wf_WO : well_founded le_WO.
  Proof.
    unfold well_founded; intro.
    apply Acc_intro.
    induction a as [a f IH].
    intros y Hle.
    apply le_WO_inv in Hle.
    destruct Hle as [a' [g [v [Hy Hsup]]]], Hy.
    assert (Heq : eq_dep _ (fun a => B a -> WO) a' g a f) by (inversion Hsup;reflexivity).
    clear Hsup;destruct Heq.
    apply Acc_intro.
    apply IH.
  Qed.

End WellOrdering.


Section Characterisation_wf_relations.

  (** Wellfounded relations are the inverse image of wellordering types *)
  (*  in course of development                                          *)


  Variable A : Type.
  Variable leA : A -> A -> Prop.

  Definition B (a:A) := {x : A | leA x a}.

  Theorem wof : well_founded leA -> A -> WO A B.
  Proof.
    intros.
    apply (well_founded_induction_type H (fun a:A => WO A B)); auto.
    intros x H1.
    apply (sup A B x).
    unfold B at 1.
    destruct 1 as [x0].
    apply (H1 x0); auto.
  Qed.

End Characterisation_wf_relations.

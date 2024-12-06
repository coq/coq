(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Author: Bruno Barras *)

Section Inverse_Image.

  Variables A B : Type.
  Variable R : B -> B -> Prop.
  Variable f : A -> B.

  Let Rof (x y:A) : Prop := R (f x) (f y).

  Remark Acc_lemma : forall y:B, Acc R y -> forall x:A, y = f x -> Acc Rof x.
  Proof.
    induction 1 as [y _ IHAcc]; intros x H.
    apply Acc_intro; intros y0 H1.
    apply (IHAcc (f y0)); try trivial.
    rewrite H; trivial.
  Qed.

  Lemma Acc_inverse_image : forall x:A, Acc R (f x) -> Acc Rof x.
  Proof.
    intros; apply (Acc_lemma (f x)); trivial.
  Qed.

  Theorem wf_inverse_image : well_founded R -> well_founded Rof.
  Proof.
    red; intros; apply Acc_inverse_image; auto.
  Qed.

  Variable F : A -> B -> Prop.
  Let RoF (x y:A) : Prop :=
    exists2 b : B, F x b & (forall c:B, F y c -> R b c).

  Lemma Acc_simulation (Q : A -> A -> Prop) :
    forall b, Acc R b ->
    (forall a1 a2 b1, Q a2 a1 -> F a1 b1 -> exists b2, F a2 b2 /\ R b2 b1) ->
    forall a, F a b -> Acc Q a.
  Proof.
    intros b Hb Hstep.
    induction Hb as [b IH1 IH2].
    intros a Hab.
    constructor. intros a' Ha'a.
    destruct (Hstep _ _ _ Ha'a Hab) as [? [??]].
    eapply IH2; eassumption.
  Defined.

  Lemma wf_simulation (Q : A -> A -> Prop) :
    well_founded R ->
    (forall a1 a2, Q a2 a1 -> exists b2, F a2 b2) ->
    (forall a1 a2 b1, Q a2 a1 -> F a1 b1 -> exists b2, F a2 b2 /\ R b2 b1) ->
    well_founded Q.
  Proof.
    intros HR Hintro Hstep a1.
    constructor. intros a2 Ha2a1.
    destruct (Hintro _ _ Ha2a1) as [b2 Ha2b2].
    apply (Acc_simulation _ _ (HR b2) Hstep _ Ha2b2).
  Defined.

  Lemma Acc_inverse_rel : forall b:B, Acc R b -> forall x:A, F x b -> Acc RoF x.
  Proof.
    intros b Hb a Hab.
    refine (Acc_simulation _ _ Hb _ _ Hab).
    intros ??? [b' ??] ?.
    exists b'; auto.
  Qed.

  Theorem wf_inverse_rel : well_founded R -> well_founded RoF.
  Proof.
    intros HR ?.
    constructor.
    intros ? [b ??].
    now apply (Acc_inverse_rel _ (HR b)).
  Qed.

End Inverse_Image.

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import NBase.

Module Homomorphism (N1 N2 : NAxiomsRecSig).

Local Notation "n == m" := (N2.eq n m) (at level 70, no associativity).

Definition homomorphism (f : N1.t -> N2.t) : Prop :=
  f N1.zero == N2.zero /\ forall n, f (N1.succ n) == N2.succ (f n).

Definition natural_isomorphism : N1.t -> N2.t :=
  N1.recursion N2.zero (fun (n : N1.t) (p : N2.t) => N2.succ p).

Instance natural_isomorphism_wd : Proper (N1.eq ==> N2.eq) natural_isomorphism.
Proof.
unfold natural_isomorphism.
repeat red; intros. f_equiv; trivial.
repeat red; intros. now f_equiv.
Qed.

Theorem natural_isomorphism_0 : natural_isomorphism N1.zero == N2.zero.
Proof.
unfold natural_isomorphism; now rewrite N1.recursion_0.
Qed.

Theorem natural_isomorphism_succ :
  forall n : N1.t, natural_isomorphism (N1.succ n) == N2.succ (natural_isomorphism n).
Proof.
unfold natural_isomorphism.
intro n. rewrite N1.recursion_succ; auto with *.
repeat red; intros. now f_equiv.
Qed.

Theorem hom_nat_iso : homomorphism natural_isomorphism.
Proof.
unfold homomorphism, natural_isomorphism; split;
[exact natural_isomorphism_0 | exact natural_isomorphism_succ].
Qed.

End Homomorphism.

Module Inverse (N1 N2 : NAxiomsRecSig).

Module Import NBasePropMod1 := NBaseProp N1.
(* This makes the tactic induct available. Since it is taken from
(NBasePropFunct NAxiomsMod1), it refers to induction on N1. *)

Module Hom12 := Homomorphism N1 N2.
Module Hom21 := Homomorphism N2 N1.

Local Notation h12 := Hom12.natural_isomorphism.
Local Notation h21 := Hom21.natural_isomorphism.
Local Notation "n == m" := (N1.eq n m) (at level 70, no associativity).

Lemma inverse_nat_iso : forall n : N1.t, h21 (h12 n) == n.
Proof.
induct n.
now rewrite Hom12.natural_isomorphism_0, Hom21.natural_isomorphism_0.
intros n IH.
now rewrite Hom12.natural_isomorphism_succ, Hom21.natural_isomorphism_succ, IH.
Qed.

End Inverse.

Module Isomorphism (N1 N2 : NAxiomsRecSig).

Module Hom12 := Homomorphism N1 N2.
Module Hom21 := Homomorphism N2 N1.
Module Inverse12 := Inverse N1 N2.
Module Inverse21 := Inverse N2 N1.

Local Notation h12 := Hom12.natural_isomorphism.
Local Notation h21 := Hom21.natural_isomorphism.

Definition isomorphism (f1 : N1.t -> N2.t) (f2 : N2.t -> N1.t) : Prop :=
  Hom12.homomorphism f1 /\ Hom21.homomorphism f2 /\
  forall n, N1.eq (f2 (f1 n)) n /\
  forall n, N2.eq (f1 (f2 n)) n.

Theorem iso_nat_iso : isomorphism h12 h21.
Proof.
unfold isomorphism.
split. apply Hom12.hom_nat_iso.
split. apply Hom21.hom_nat_iso.
split. apply Inverse12.inverse_nat_iso.
apply Inverse21.inverse_nat_iso.
Qed.

End Isomorphism.


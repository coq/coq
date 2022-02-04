(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * A typeclass to ease the handling of decidable properties. *)

(** A proposition is decidable whenever it is reflected by a boolean. *)

Class Decidable (P : Prop) := {
  Decidable_witness : bool;
  Decidable_spec : Decidable_witness = true <-> P
}.

(** Alternative ways of specifying the reflection property. *)

Lemma Decidable_sound : forall P (H : Decidable P),
  Decidable_witness = true -> P.
Proof.
intros P H Hp; apply -> Decidable_spec; assumption.
Qed.

Lemma Decidable_complete : forall P (H : Decidable P),
  P -> Decidable_witness = true.
Proof.
intros P H Hp; apply <- Decidable_spec; assumption.
Qed.

Lemma Decidable_sound_alt : forall P (H : Decidable P),
   ~ P -> Decidable_witness = false.
Proof.
intros P [wit spec] Hd; simpl; destruct wit; tauto.
Qed.

Lemma Decidable_complete_alt : forall P (H : Decidable P),
  Decidable_witness = false -> ~ P.
Proof.
intros P [wit spec] Hd Hc; simpl in *; intuition congruence.
Qed.

(** The generic function that should be used to program, together with some
  useful tactics. *)

Definition decide P {H : Decidable P} := @Decidable_witness _ H.

Ltac _decide_ P H :=
  let b := fresh "b" in
  set (b := decide P) in *;
  assert (H : decide P = b) by reflexivity;
  clearbody b;
  destruct b; [apply Decidable_sound in H|apply Decidable_complete_alt in H].

Tactic Notation "decide" constr(P) "as" ident(H) :=
  _decide_ P H.

Tactic Notation "decide" constr(P) :=
  let H := fresh "H" in _decide_ P H.

(** Some usual instances. *)

Require Import Bool Arith ZArith.

#[global]
Program Instance Decidable_not {P} `{Decidable P} : Decidable (~ P) := {
  Decidable_witness := negb Decidable_witness
}.
Next Obligation.
  split; intro Heq.
  - apply negb_true_iff in Heq.
    eapply Decidable_complete_alt; intuition.
  - erewrite Decidable_sound_alt; intuition.
Qed.

#[global]
Instance Decidable_eq_bool : forall (x y : bool), Decidable (eq x y) := {
  Decidable_spec := eqb_true_iff x y
}.

#[global]
Instance Decidable_eq_nat : forall (x y : nat), Decidable (eq x y) := {
  Decidable_spec := Nat.eqb_eq x y
}.

#[global]
Instance Decidable_le_nat : forall (x y : nat), Decidable (x <= y) := {
  Decidable_spec := Nat.leb_le x y
}.

(* Note: Decidable_lt_nat, Decidable_ge_nat, Decidable_gt_nat are not required,
   because lt, ge and gt are defined based on le in a way which type class
   resolution seems to understand. *)

#[global]
Instance Decidable_eq_Z : forall (x y : Z), Decidable (eq x y) := {
  Decidable_spec := Z.eqb_eq x y
}.

#[global]
Instance Decidable_le_Z : forall (x y : Z), DecidableClass.Decidable (x <= y)%Z := {
  Decidable_spec := Z.leb_le x y
}.

#[global]
Instance Decidable_lt_Z : forall (x y : Z), DecidableClass.Decidable (x < y)%Z := {
  Decidable_spec := Z.ltb_lt x y
}.

#[global]
Instance Decidable_ge_Z : forall (x y : Z), DecidableClass.Decidable (x >= y)%Z := {
  Decidable_spec := Z.geb_ge x y
}.

#[global]
Instance Decidable_gt_Z : forall (x y : Z), DecidableClass.Decidable (x > y)%Z := {
  Decidable_spec := Z.gtb_gt x y
}.

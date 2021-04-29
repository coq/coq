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
Program Instance Decidable_eq_bool : forall (x y : bool), Decidable (eq x y) := {
  Decidable_witness := Bool.eqb x y
}.
Next Obligation.
 apply eqb_true_iff.
Qed.

#[global]
Program Instance Decidable_eq_nat : forall (x y : nat), Decidable (eq x y) := {
  Decidable_witness := Nat.eqb x y
}.
Next Obligation.
 apply Nat.eqb_eq.
Qed.

#[global]
Program Instance Decidable_le_nat : forall (x y : nat), Decidable (x <= y) := {
  Decidable_witness := Nat.leb x y
}.
Next Obligation.
 apply Nat.leb_le.
Qed.

#[global]
Program Instance Decidable_eq_Z : forall (x y : Z), Decidable (eq x y) := {
  Decidable_witness := Z.eqb x y
}.
Next Obligation.
 apply Z.eqb_eq.
Qed.

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Here we define the predicates [even] and [odd] by mutual induction
    and we prove the decidability and the exclusion of those predicates.
    The main results about parity are proved in the module Div2. *)

Open Local Scope nat_scope.

Implicit Types m n : nat.


(** * Definition of [even] and [odd], and basic facts *)

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

Hint Constructors even: arith.
Hint Constructors odd: arith.

Lemma even_or_odd : forall n, even n \/ odd n.
Proof.
  induction n.
    auto with arith.
    elim IHn; auto with arith.
Qed.

Lemma even_odd_dec : forall n, {even n} + {odd n}.
Proof.
  induction n.
    auto with arith.
    elim IHn; auto with arith.
Defined.

Lemma not_even_and_odd : forall n, even n -> odd n -> False.
Proof.
  induction n.
    intros even_0 odd_0. inversion odd_0.
    intros even_Sn odd_Sn. inversion even_Sn. inversion odd_Sn. auto with arith.
Qed.


(** * Facts about [even] & [odd] wrt. [plus] *)

Lemma even_plus_split : forall n m,
  (even (n + m) -> even n /\ even m \/ odd n /\ odd m)
with odd_plus_split : forall n m,
  odd (n + m) -> odd n /\ even m \/ even n /\ odd m.
Proof.
intros. clear even_plus_split. destruct n; simpl in *.
 auto with arith.
 inversion_clear H;
   apply odd_plus_split in H0 as [(H0,?)|(H0,?)]; auto with arith.
intros. clear odd_plus_split. destruct n; simpl in *.
 auto with arith.
 inversion_clear H;
   apply even_plus_split in H0 as [(H0,?)|(H0,?)]; auto with arith.
Qed.

Lemma even_even_plus : forall n m, even n -> even m -> even (n + m)
with odd_plus_l : forall n m, odd n -> even m -> odd (n + m).
Proof.
intros n m [|] ?. trivial. apply even_S, odd_plus_l; trivial.
intros n m [] ?. apply odd_S, even_even_plus; trivial.
Qed.

Lemma odd_plus_r : forall n m, even n -> odd m -> odd (n + m)
with odd_even_plus : forall n m, odd n -> odd m -> even (n + m).
Proof.
intros n m [|] ?. trivial. apply odd_S, odd_even_plus; trivial.
intros n m [] ?. apply even_S, odd_plus_r; trivial.
Qed.

Lemma even_plus_aux : forall n m,
    (odd (n + m) <-> odd n /\ even m \/ even n /\ odd m) /\
    (even (n + m) <-> even n /\ even m \/ odd n /\ odd m).
Proof.
split; split; auto using odd_plus_split, even_plus_split.
intros [[]|[]]; auto using odd_plus_r, odd_plus_l.
intros [[]|[]]; auto using even_even_plus, odd_even_plus.
Qed.

Lemma even_plus_even_inv_r : forall n m, even (n + m) -> even n -> even m.
Proof.
  intros n m H; destruct (even_plus_split n m) as [[]|[]]; auto.
  intro; destruct (not_even_and_odd n); auto.
Qed.

Lemma even_plus_even_inv_l : forall n m, even (n + m) -> even m -> even n.
Proof.
  intros n m H; destruct (even_plus_split n m) as [[]|[]]; auto.
  intro; destruct (not_even_and_odd m); auto.
Qed.

Lemma even_plus_odd_inv_r : forall n m, even (n + m) -> odd n -> odd m.
Proof.
  intros n m H; destruct (even_plus_split n m) as [[]|[]]; auto.
  intro; destruct (not_even_and_odd n); auto.
Qed.

Lemma even_plus_odd_inv_l : forall n m, even (n + m) -> odd m -> odd n.
Proof.
  intros n m H; destruct (even_plus_split n m) as [[]|[]]; auto.
  intro; destruct (not_even_and_odd m); auto.
Qed.
Hint Resolve even_even_plus odd_even_plus: arith.

Lemma odd_plus_even_inv_l : forall n m, odd (n + m) -> odd m -> even n.
Proof.
  intros n m H; destruct (odd_plus_split n m) as [[]|[]]; auto.
  intro; destruct (not_even_and_odd m); auto.
Qed.

Lemma odd_plus_even_inv_r : forall n m, odd (n + m) -> odd n -> even m.
Proof.
  intros n m H; destruct (odd_plus_split n m) as [[]|[]]; auto.
  intro; destruct (not_even_and_odd n); auto.
Qed.

Lemma odd_plus_odd_inv_l : forall n m, odd (n + m) -> even m -> odd n.
Proof.
  intros n m H; destruct (odd_plus_split n m) as [[]|[]]; auto.
  intro; destruct (not_even_and_odd m); auto.
Qed.

Lemma odd_plus_odd_inv_r : forall n m, odd (n + m) -> even n -> odd m.
Proof.
  intros n m H; destruct (odd_plus_split n m) as [[]|[]]; auto.
  intro; destruct (not_even_and_odd n); auto.
Qed.
Hint Resolve odd_plus_l odd_plus_r: arith.


(** * Facts about [even] and [odd] wrt. [mult] *)

Lemma even_mult_aux :
  forall n m,
    (odd (n * m) <-> odd n /\ odd m) /\ (even (n * m) <-> even n \/ even m).
Proof.
  intros n; elim n; simpl in |- *; auto with arith.
  intros m; split; split; auto with arith.
  intros H'; inversion H'.
  intros H'; elim H'; auto.
  intros n0 H' m; split; split; auto with arith.
  intros H'0.
  elim (even_plus_aux m (n0 * m)); intros H'3 H'4; case H'3; intros H'1 H'2;
    case H'1; auto.
  intros H'5; elim H'5; intros H'6 H'7; auto with arith.
  split; auto with arith.
  case (H' m).
  intros H'8 H'9; case H'9.
  intros H'10; case H'10; auto with arith.
  intros H'11 H'12; case (not_even_and_odd m); auto with arith.
  intros H'5; elim H'5; intros H'6 H'7; case (not_even_and_odd (n0 * m)); auto.
  case (H' m).
  intros H'8 H'9; case H'9; auto.
  intros H'0; elim H'0; intros H'1 H'2; clear H'0.
  elim (even_plus_aux m (n0 * m)); auto.
  intros H'0 H'3.
  elim H'0.
  intros H'4 H'5; apply H'5; auto.
  left; split; auto with arith.
  case (H' m).
  intros H'6 H'7; elim H'7.
  intros H'8 H'9; apply H'9.
  left.
  inversion H'1; auto.
  intros H'0.
  elim (even_plus_aux m (n0 * m)); intros H'3 H'4; case H'4.
  intros H'1 H'2.
  elim H'1; auto.
  intros H; case H; auto.
  intros H'5; elim H'5; intros H'6 H'7; auto with arith.
  left.
  case (H' m).
  intros H'8; elim H'8.
  intros H'9; elim H'9; auto with arith.
  intros H'0; elim H'0; intros H'1.
  case (even_or_odd m); intros H'2.
  apply even_even_plus; auto.
  case (H' m).
  intros H H0; case H0; auto.
  apply odd_even_plus; auto.
  inversion H'1; case (H' m); auto.
  intros H1; case H1; auto.
  apply even_even_plus; auto.
  case (H' m).
  intros H H0; case H0; auto.
Qed.

Lemma even_mult_l : forall n m, even n -> even (n * m).
Proof.
  intros n m; case (even_mult_aux n m); auto.
  intros H H0; case H0; auto.
Qed.

Lemma even_mult_r : forall n m, even m -> even (n * m).
Proof.
  intros n m; case (even_mult_aux n m); auto.
  intros H H0; case H0; auto.
Qed.
Hint Resolve even_mult_l even_mult_r: arith.

Lemma even_mult_inv_r : forall n m, even (n * m) -> odd n -> even m.
Proof.
  intros n m H' H'0.
  case (even_mult_aux n m).
  intros H'1 H'2; elim H'2.
  intros H'3; elim H'3; auto.
  intros H; case (not_even_and_odd n); auto.
Qed.

Lemma even_mult_inv_l : forall n m, even (n * m) -> odd m -> even n.
Proof.
  intros n m H' H'0.
  case (even_mult_aux n m).
  intros H'1 H'2; elim H'2.
  intros H'3; elim H'3; auto.
  intros H; case (not_even_and_odd m); auto.
Qed.

Lemma odd_mult : forall n m, odd n -> odd m -> odd (n * m).
Proof.
  intros n m; case (even_mult_aux n m); intros H; case H; auto.
Qed.
Hint Resolve even_mult_l even_mult_r odd_mult: arith.

Lemma odd_mult_inv_l : forall n m, odd (n * m) -> odd n.
Proof.
  intros n m H'.
  case (even_mult_aux n m).
  intros H'1 H'2; elim H'1.
  intros H'3; elim H'3; auto.
Qed.

Lemma odd_mult_inv_r : forall n m, odd (n * m) -> odd m.
Proof.
  intros n m H'.
  case (even_mult_aux n m).
  intros H'1 H'2; elim H'1.
  intros H'3; elim H'3; auto.
Qed.

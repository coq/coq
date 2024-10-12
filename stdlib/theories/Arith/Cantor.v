(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Implementation of the Cantor pairing and its inverse function *)

Require Import PeanoNat Lia.

(** Bijections between [nat * nat] and [nat] *)

(** Cantor pairing [to_nat] *)

Definition to_nat '(x, y) : nat :=
  y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

(** Cantor pairing inverse [of_nat] *)

Definition of_nat (n : nat) : nat * nat :=
  nat_rec _ (0, 0) (fun _ '(x, y) =>
    match x with | S x => (x, S y) | _ => (S y, 0) end) n.

(** [of_nat] is the left inverse for [to_nat] *)

Lemma cancel_of_to p : of_nat (to_nat p) = p.
Proof.
  enough (H : forall n p, to_nat p = n -> of_nat n = p) by now apply H.
  intro n. induction n as [|n IHn].
  - now intros [[|?] [|?]].
  - intros [x [|y]].
    + destruct x as [|x]; [discriminate|].
      intros [=H]. cbn. fold (of_nat n).
      rewrite (IHn (0, x)); [reflexivity|].
      rewrite <- H. cbn. now rewrite PeanoNat.Nat.add_0_r.
    + intros [=H]. cbn. fold (of_nat n).
      rewrite (IHn (S x, y)); [reflexivity|].
      rewrite <- H. cbn. now rewrite Nat.add_succ_r.
Qed.

(** [to_nat] is injective *)

Corollary to_nat_inj p q : to_nat p = to_nat q -> p = q.
Proof.
  intros H %(f_equal of_nat). now rewrite ?cancel_of_to in H.
Qed.

(** [to_nat] is the left inverse for [of_nat] *)

Lemma cancel_to_of n : to_nat (of_nat n) = n.
Proof.
  induction n as [|n IHn]; [reflexivity|].
  cbn. fold (of_nat n). destruct (of_nat n) as [[|x] y].
  - rewrite <- IHn. cbn. now rewrite PeanoNat.Nat.add_0_r.
  - rewrite <- IHn. cbn. now rewrite (Nat.add_succ_r y x).
Qed.

(** [of_nat] is injective *)

Corollary of_nat_inj n m : of_nat n = of_nat m -> n = m.
Proof.
  intros H %(f_equal to_nat). now rewrite ?cancel_to_of in H.
Qed.

(** Polynomial specifications of [to_nat] *)

Lemma to_nat_spec x y :
  to_nat (x, y) * 2 = y * 2 + (y + x) * S (y + x).
Proof.
  cbn. induction (y + x) as [|n IHn]; cbn; lia.
Qed.

Lemma to_nat_spec2 x y :
  to_nat (x, y) = y + (y + x) * S (y + x) / 2.
Proof.
  now rewrite <- Nat.div_add_l, <- to_nat_spec, Nat.div_mul.
Qed.

(** [to_nat] is non-decreasing in (the sum of) pair components *)

Lemma to_nat_non_decreasing x y : y + x <= to_nat (x, y).
Proof.
  pose proof (to_nat_spec x y). nia.
Qed.

(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Binary Integers : properties of absolute value *)
(** Initial author : Pierre Crégut (CNET, Lannion, France) *)

(** THIS FILE IS DEPRECATED.
    It is now almost entirely made of compatibility formulations
    for results already present in BinInt.Z. *)

Require Import Arith_base.
Require Import BinPos.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Znat.
Require Import ZArith_dec.

Local Open Scope Z_scope.

(**********************************************************************)
(** * Properties of absolute value *)

Notation Zabs_eq := Z.abs_eq (compat "8.7").
Notation Zabs_non_eq := Z.abs_neq (only parsing).
Notation Zabs_Zopp := Z.abs_opp (only parsing).
Notation Zabs_pos := Z.abs_nonneg (only parsing).
Notation Zabs_involutive := Z.abs_involutive (compat "8.7").
Notation Zabs_eq_case := Z.abs_eq_cases (only parsing).
Notation Zabs_triangle := Z.abs_triangle (compat "8.7").
Notation Zsgn_Zabs := Z.sgn_abs (only parsing).
Notation Zabs_Zsgn := Z.abs_sgn (only parsing).
Notation Zabs_Zmult := Z.abs_mul (only parsing).
Notation Zabs_square := Z.abs_square (compat "8.7").

(** * Proving a property of the absolute value by cases *)

Lemma Zabs_ind :
  forall (P:Z -> Prop) (n:Z),
    (n >= 0 -> P n) -> (n <= 0 -> P (- n)) -> P (Z.abs n).
Proof.
 intros. apply Z.abs_case_strong; Z.swap_greater; trivial.
 intros x y Hx; now subst.
Qed.

Theorem Zabs_intro : forall P (n:Z), P (- n) -> P n -> P (Z.abs n).
Proof.
 now destruct n.
Qed.

Definition Zabs_dec : forall x:Z, {x = Z.abs x} + {x = - Z.abs x}.
Proof.
 destruct x; auto.
Defined.

Lemma Zabs_spec x :
  0 <= x /\ Z.abs x = x \/
  0 > x /\ Z.abs x = -x.
Proof.
 Z.swap_greater. apply Z.abs_spec.
Qed.

(** * Some results about the sign function. *)

Notation Zsgn_Zmult := Z.sgn_mul (only parsing).
Notation Zsgn_Zopp := Z.sgn_opp (only parsing).
Notation Zsgn_pos := Z.sgn_pos_iff (only parsing).
Notation Zsgn_neg := Z.sgn_neg_iff (only parsing).
Notation Zsgn_null := Z.sgn_null_iff (only parsing).

(** A characterization of the sign function: *)

Lemma Zsgn_spec x :
  0 < x /\ Z.sgn x = 1 \/
  0 = x /\ Z.sgn x = 0 \/
  0 > x /\ Z.sgn x = -1.
Proof.
 intros. Z.swap_greater. apply Z.sgn_spec.
Qed.

(** Compatibility *)

Notation inj_Zabs_nat := Zabs2Nat.id_abs (only parsing).
Notation Zabs_nat_Z_of_nat := Zabs2Nat.id (only parsing).
Notation Zabs_nat_mult := Zabs2Nat.inj_mul (only parsing).
Notation Zabs_nat_Zsucc := Zabs2Nat.inj_succ (only parsing).
Notation Zabs_nat_Zplus := Zabs2Nat.inj_add (only parsing).
Notation Zabs_nat_Zminus := (fun n m => Zabs2Nat.inj_sub m n) (only parsing).
Notation Zabs_nat_compare := Zabs2Nat.inj_compare (only parsing).

Lemma Zabs_nat_le n m : 0 <= n <= m -> (Z.abs_nat n <= Z.abs_nat m)%nat.
Proof.
 intros (H,H'). apply Zabs2Nat.inj_le; trivial. now transitivity n.
Qed.

Lemma Zabs_nat_lt n m : 0 <= n < m -> (Z.abs_nat n < Z.abs_nat m)%nat.
Proof.
 intros (H,H'). apply Zabs2Nat.inj_lt; trivial.
  transitivity n; trivial. now apply Z.lt_le_incl.
Qed.

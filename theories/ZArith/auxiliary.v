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

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Export Arith_base.
Require Import BinInt.
Require Import Zorder.
Require Import Decidable.
Require Import Peano_dec.
Require Export Compare_dec.

Local Open Scope Z_scope.

(***************************************************************)
(** * Moving terms from one side to the other of an inequality *)

Theorem Zne_left n m : Zne n m -> Zne (n + - m) 0.
Proof.
 unfold Zne. now rewrite <- Z.sub_move_0_r.
Qed.

Theorem Zegal_left n m : n = m -> n + - m = 0.
Proof.
 apply Z.sub_move_0_r.
Qed.

Theorem Zle_left n m : n <= m -> 0 <= m + - n.
Proof.
 apply Z.le_0_sub.
Qed.

Theorem Zle_left_rev n m : 0 <= m + - n -> n <= m.
Proof.
 apply Z.le_0_sub.
Qed.

Theorem Zlt_left_rev n m : 0 < m + - n -> n < m.
Proof.
 apply Z.lt_0_sub.
Qed.

Theorem Zlt_left_lt n m : n < m -> 0 < m + - n.
Proof.
 apply Z.lt_0_sub.
Qed.

Theorem Zlt_left n m : n < m -> 0 <= m + -1 + - n.
Proof.
 intros. rewrite Z.add_shuffle0. change (-1) with (- Z.succ 0).
 now apply Z.le_0_sub, Z.le_succ_l, Z.lt_0_sub.
Qed.

Theorem Zge_left n m : n >= m -> 0 <= n + - m.
Proof.
 Z.swap_greater. apply Z.le_0_sub.
Qed.

Theorem Zgt_left n m : n > m -> 0 <= n + -1 + - m.
Proof.
 Z.swap_greater. apply Zlt_left.
Qed.

Theorem Zgt_left_gt n m : n > m -> n + - m > 0.
Proof.
 Z.swap_greater. apply Z.lt_0_sub.
Qed.

Theorem Zgt_left_rev n m : n + - m > 0 -> n > m.
Proof.
 Z.swap_greater. apply Z.lt_0_sub.
Qed.

Theorem Zle_mult_approx n m p :
  n > 0 -> p > 0 -> 0 <= m -> 0 <= m * n + p.
Proof.
 Z.swap_greater. intros. Z.order_pos.
Qed.

Theorem Zmult_le_approx n m p :
  n > 0 -> n > p -> 0 <= m * n + p -> 0 <= m.
Proof.
 Z.swap_greater. intros. apply Z.lt_succ_r.
 apply Z.mul_pos_cancel_r with n; trivial. Z.nzsimpl.
 apply Z.le_lt_trans with (m*n+p); trivial.
 now apply Z.add_lt_mono_l.
Qed.


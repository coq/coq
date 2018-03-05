(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Wf_nat.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Bool.
Local Open Scope Z_scope.

(**********************************************************************)
(** Iterators *)

(** [n]th iteration of the function [f] *)

Notation iter := @Z.iter (only parsing).

Lemma iter_nat_of_Z : forall n A f x, 0 <= n ->
  Z.iter n f x = iter_nat (Z.abs_nat n) A f x.
Proof.
intros n A f x; case n; auto.
intros p _; unfold Z.iter, Z.abs_nat; apply Pos2Nat.inj_iter.
intros p abs; case abs; trivial.
Qed.

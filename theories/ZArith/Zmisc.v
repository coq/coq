(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Wf_nat.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Bool.
Open Local Scope Z_scope.

(**********************************************************************)
(** Iterators *)

(** [n]th iteration of the function [f] *)

Notation iter := @Z.iter (only parsing).

Lemma iter_nat_of_Z : forall n A f x, 0 <= n ->
  iter n A f x = iter_nat (Zabs_nat n) A f x.
intros n A f x; case n; auto.
intros p _; unfold Z.iter, Zabs_nat; apply iter_nat_of_P.
intros p abs; case abs; trivial.
Qed.

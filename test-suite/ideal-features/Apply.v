(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This needs step by step unfolding *)

Fixpoint T (n:nat) : Prop :=
  match n with
  | O => True
  | S p => n = n -> T p
  end.

Require Import Arith.

Goal T 3 -> T 1.
intro H.
apply H.

(* This needs unification on type *)

Goal forall n m : nat, S m = S n :>nat.
intros.
apply f_equal.

(* f_equal : forall (A B:Set) (f:A->B) (x y:A), x=y->(f x)=(f y) *)
(* and A cannot be deduced from the goal but only from the type of f, x or y *)

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* This needs unification on type *)

Goal (n,m:nat)(eq nat (S m) (S n)).
Intros.
Apply f_equal.

(* f_equal : (A,B:Set; f:(A->B); x,y:A)x=y->(f x)=(f y) *)
(* and A cannot be deduced from the goal but only from the type of f, x or y *)
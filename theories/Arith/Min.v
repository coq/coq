(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Arith.

(**************************************************************************)
(*                    minimum of two natural numbers                      *)
(**************************************************************************)

Fixpoint min [n:nat] : nat -> nat :=  
[m:nat]Cases n m of
          O      _     => O
       | (S n')  O     => O
       | (S n') (S m') => (S (min n' m'))
       end.

Lemma min_SS : (n,m:nat)((S (min n m))=(min (S n) (S m))).
Proof.
Auto with arith.
Qed.

Lemma le_min_l : (n,m:nat)(le (min n m) n).
Proof.
Induction n; Intros; Simpl; Auto with arith.
Elim m; Intros; Simpl; Auto with arith.
Qed.
Hints Resolve le_min_l : arith v62.

Lemma le_min_r : (n,m:nat)(le (min n m) m).
Proof.
Induction n; Simpl; Auto with arith.
Induction m; Simpl; Auto with arith.
Qed.
Hints Resolve le_min_r : arith v62.

(* min n m is equal to n or m *)

Lemma min_case : (n,m:nat)(P:nat->Set)(P n)->(P m)->(P (min n m)).
Proof.
Induction n; Simpl; Auto with arith.
Induction m; Intros; Simpl; Auto with arith.
Pattern (min n0 n1); Apply H ; Auto with arith.
Qed.

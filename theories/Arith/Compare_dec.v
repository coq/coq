(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Le.
Require Lt.
Require Gt.
Require Decidable.

Theorem zerop : (n:nat){n=O}+{lt O n}.
NewDestruct n; Auto with arith.
Save.

Theorem lt_eq_lt_dec : (n,m:nat){(lt n m)}+{n=m}+{(lt m n)}.
Proof.
NewInduction n; NewInduction m; Auto with arith.
Elim (IHn m).
NewInduction 1; Auto with arith.
Auto with arith.
Qed.

Lemma gt_eq_gt_dec : (n,m:nat)({(gt m n)}+{n=m})+{(gt n m)}.
Proof lt_eq_lt_dec.

Lemma le_lt_dec : (n,m:nat) {le n m} + {lt m n}.
Proof.
NewInduction n.
Auto with arith.
NewInduction m.
Auto with arith.
Elim (IHn m); Auto with arith.
Qed.

Lemma le_le_S_dec : (n,m:nat) {le n m} + {le (S m) n}.
Proof le_lt_dec.

Lemma le_ge_dec : (n,m:nat) {le n m} + {ge n m}.
Proof.
Intros; Elim (le_lt_dec n m); Auto with arith.
Qed.

Theorem le_gt_dec : (n,m:nat){(le n m)}+{(gt n m)}.
Proof le_lt_dec.


Theorem le_lt_eq_dec : (n,m:nat)(le n m)->({(lt n m)}+{n=m}).
Proof.
Intros; Elim (lt_eq_lt_dec n m); Auto with arith.
Intros; Absurd (lt m n); Auto with arith.
Qed.

(* Proofs of decidability *)

Theorem dec_le:(x,y:nat)(decidable (le x y)).
Intros x y; Unfold decidable ; Elim (le_gt_dec x y); [
  Auto with arith
| Intro; Right; Apply gt_not_le; Assumption].
Save.

Theorem dec_lt:(x,y:nat)(decidable (lt x y)).
Intros x y; Unfold lt; Apply dec_le.
Save.

Theorem dec_gt:(x,y:nat)(decidable (gt x y)).
Intros x y; Unfold gt; Apply dec_lt.
Save.

Theorem dec_ge:(x,y:nat)(decidable (ge x y)).
Intros x y; Unfold ge; Apply dec_le.
Save.

Theorem not_eq : (x,y:nat) ~ x=y -> (lt x y) \/ (lt y x).
Intros x y H; Elim (lt_eq_lt_dec x y); [
  Intros H1; Elim H1; [ Auto with arith | Intros H2; Absurd x=y; Assumption]
| Auto with arith].
Save.


Theorem not_le : (x,y:nat) ~(le x y) -> (gt x y).
Intros x y H; Elim (le_gt_dec x y);
  [ Intros H1; Absurd (le x y); Assumption | Trivial with arith ].
Save.

Theorem not_gt : (x,y:nat) ~(gt x y) -> (le x y).
Intros x y H; Elim (le_gt_dec x y);
  [ Trivial with arith | Intros H1; Absurd (gt x y); Assumption].
Save.

Theorem not_ge : (x,y:nat) ~(ge x y) -> (lt x y).
Intros x y H; Exact (not_le y x H).
Save.

Theorem not_lt : (x,y:nat) ~(lt x y) -> (ge x y).
Intros x y H; Exact (not_gt y x H). 
Save.


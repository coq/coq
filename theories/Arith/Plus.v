(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(**************************************************************************)
(*                         Properties of addition                         *)
(**************************************************************************)

Require Le.
Require Lt.

Lemma plus_sym : (n,m:nat)(plus n m)=(plus m n).
Proof.
Intros n m ; Elim n ; Simpl ; Auto with arith.
Intros y H ; Elim (plus_n_Sm m y) ; Auto with arith.
Qed.
Hints Immediate plus_sym : arith v62.

Lemma plus_Snm_nSm : 
  (n,m:nat)(plus (S n) m)=(plus n (S m)).
Intros.
Simpl.
Rewrite -> (plus_sym n m).
Rewrite -> (plus_sym n (S m)).
Trivial with arith.
Qed.

Lemma simpl_plus_l : (n,m,p:nat)((plus n m)=(plus n p))->(m=p).
Proof.
Induction n ; Simpl ; Auto with arith.
Qed.

Lemma plus_assoc_l : (n,m,p:nat)((plus n (plus m p))=(plus (plus n m) p)).
Proof.
Intros n m p; Elim n; Simpl; Auto with arith.
Qed.
Hints Resolve plus_assoc_l : arith v62.

Lemma plus_permute : (n,m,p:nat) ((plus n (plus m p))=(plus m (plus n p))).
Proof. 
Intros; Rewrite (plus_assoc_l m n p); Rewrite (plus_sym m n); Auto with arith.
Qed.

Lemma plus_assoc_r : (n,m,p:nat)((plus (plus n m) p)=(plus n (plus m p))).
Proof.
Auto with arith.
Qed.
Hints Resolve plus_assoc_r : arith v62.

Lemma simpl_le_plus_l : (p,n,m:nat)(le (plus p n) (plus p m))->(le n m).
Proof.
Induction p; Simpl; Auto with arith.
Qed.

Lemma le_reg_l : (n,m,p:nat)(le n m)->(le (plus p n) (plus p m)).
Proof.
Induction p; Simpl; Auto with arith.
Qed.
Hints Resolve le_reg_l : arith v62.

Lemma le_reg_r : (a,b,c:nat) (le a b)->(le (plus a c) (plus b c)).
Proof.
Induction 1 ; Simpl; Auto with arith.
Qed.
Hints Resolve le_reg_r : arith v62.

Lemma le_plus_plus : 
	(n,m,p,q:nat) (le n m)->(le p q)->(le (plus n p) (plus m q)).
Proof.
Intros n m p q H H0.
Elim H; Simpl; Auto with arith.
Qed.

Lemma le_plus_l : (n,m:nat)(le n (plus n m)).
Proof.
Induction n; Simpl; Auto with arith.
Qed.
Hints Resolve le_plus_l : arith v62.

Lemma le_plus_r : (n,m:nat)(le m (plus n m)).
Proof.
Intros n m; Elim n; Simpl; Auto with arith.
Qed.
Hints Resolve le_plus_r : arith v62.

Theorem le_plus_trans : (n,m,p:nat)(le n m)->(le n (plus m p)).
Proof.
Intros; Apply le_trans with m; Auto with arith.
Qed.
Hints Resolve le_plus_trans : arith v62.

Lemma simpl_lt_plus_l : (n,m,p:nat)(lt (plus p n) (plus p m))->(lt n m).
Proof.
Induction p; Simpl; Auto with arith.
Qed.

Lemma lt_reg_l : (n,m,p:nat)(lt n m)->(lt (plus p n) (plus p m)).
Proof.
Induction p; Simpl; Auto with arith.
Qed.
Hints Resolve lt_reg_l : arith v62.

Lemma lt_reg_r : (n,m,p:nat)(lt n m) -> (lt (plus n p) (plus m p)).
Proof.
Intros n m p H ; Rewrite (plus_sym n p) ; Rewrite (plus_sym m p).
Elim p; Auto with arith.
Qed.
Hints Resolve lt_reg_r : arith v62.

Theorem lt_plus_trans : (n,m,p:nat)(lt n m)->(lt n (plus m p)).
Proof.
Intros; Apply lt_le_trans with m; Auto with arith.
Qed.
Hints Immediate lt_plus_trans : arith v62.

Lemma le_lt_plus_plus : (n,m,p,q:nat) (le n m)->(lt p q)->(lt (plus n p) (plus m q)).
Proof.
  Unfold lt. Intros. Change (le (plus (S n) p) (plus m q)). Rewrite plus_Snm_nSm.
  Apply le_plus_plus; Assumption.
Qed.

Lemma lt_le_plus_plus : (n,m,p,q:nat) (lt n m)->(le p q)->(lt (plus n p) (plus m q)).
Proof.
  Unfold lt. Intros. Change (le (plus (S n) p) (plus m q)). Apply le_plus_plus; Assumption.
Qed.

Lemma lt_plus_plus : (n,m,p,q:nat) (lt n m)->(lt p q)->(lt (plus n p) (plus m q)).
Proof.
  Intros. Apply lt_le_plus_plus. Assumption.
  Apply lt_le_weak. Assumption.
Qed.


Lemma plus_is_O : (m,n:nat) (plus m n)=O -> m=O /\ n=O.
Proof.
  Destruct m; Auto.
  Intros. Discriminate H.
Qed.

Lemma plus_is_one : (m,n:nat) (plus m n)=(S O) -> {m=O /\ n=(S O)}+{m=(S O) /\ n=O}.
Proof.
  Destruct m; Auto.
  Destruct n; Auto.
  Intros. 
  Simpl in H. Discriminate H.
Qed.

Lemma plus_permute_2_in_4 : (a,b,c,d:nat)
      (plus (plus a b) (plus c d))=(plus (plus a c) (plus b d)).
Proof.
  Intros. 
  Rewrite <- (plus_assoc_l a b (plus c d)). Rewrite (plus_assoc_l b c d).
  Rewrite (plus_sym b c). Rewrite <- (plus_assoc_l c b d). Apply plus_assoc_l.
Qed.



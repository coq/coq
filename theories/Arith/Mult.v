(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Export Plus.
Require Export Minus.
Require Export Lt.

(**********************************************************)
(* Multiplication                                         *)
(**********************************************************)

Lemma mult_plus_distr : 
      (n,m,p:nat)((mult (plus n m) p)=(plus (mult n p) (mult m p))).
Proof.
Intros; Elim n; Simpl; Intros; Auto with arith.
Elim plus_assoc_l; Elim H; Auto with arith.
Qed.
Hints Resolve mult_plus_distr : arith v62.

Lemma mult_plus_distr_r : (n,m,p:nat) (mult n (plus m p))=(plus (mult n m) (mult n p)).
Proof.
  Induction n. Trivial.
  Intros. Simpl. Rewrite (H m p). Apply sym_eq. Apply plus_permute_2_in_4.
Qed.

Lemma mult_minus_distr : (n,m,p:nat)((mult (minus n m) p)=(minus (mult n p) (mult m p))).
Proof.
Intros; Pattern n m; Apply nat_double_ind; Simpl; Intros; Auto with arith.
Elim minus_plus_simpl; Auto with arith.
Qed.
Hints Resolve mult_minus_distr : arith v62.

Lemma mult_O_le : (n,m:nat)(m=O)\/(le n (mult m n)).
Proof.
Induction m; Simpl; Auto with arith.
Qed.
Hints Resolve mult_O_le : arith v62.

Lemma mult_assoc_r : (n,m,p:nat)((mult (mult n m) p) = (mult n (mult m p))).
Proof.
Intros; Elim n; Intros; Simpl; Auto with arith.
Rewrite mult_plus_distr.
Elim H; Auto with arith.
Qed.
Hints Resolve mult_assoc_r : arith v62.

Lemma mult_assoc_l : (n,m,p:nat)(mult n (mult m p)) = (mult (mult n m) p).
Auto with arith.
Save.
Hints Resolve mult_assoc_l : arith v62.

Lemma mult_1_n : (n:nat)(mult (S O) n)=n.
Simpl; Auto with arith.
Save.
Hints Resolve mult_1_n : arith v62.

Lemma mult_sym : (n,m:nat)(mult n m)=(mult m n).
Intros; Elim n; Intros; Simpl; Auto with arith.
Elim mult_n_Sm.
Elim H; Apply plus_sym.
Save.
Hints Resolve mult_sym : arith v62.

Lemma mult_n_1 : (n:nat)(mult n (S O))=n.
Intro; Elim mult_sym; Auto with arith.
Save.
Hints Resolve mult_n_1 : arith v62.


Lemma mult_le : (m,n,p:nat) (le n p) -> (le (mult m n) (mult m p)).
Proof.
  Induction m. Intros. Simpl. Apply le_n.
  Intros. Simpl. Apply le_plus_plus. Assumption.
  Apply H. Assumption.
Qed.
Hints Resolve mult_le : arith.

Lemma mult_lt : (m,n,p:nat) (lt n p) -> (lt (mult (S m) n) (mult (S m) p)).
Proof.
  Induction m. Intros. Simpl. Rewrite <- plus_n_O. Rewrite <- plus_n_O. Assumption.
  Intros. Exact (lt_plus_plus ? ? ? ? H0 (H ? ? H0)).
Qed.

Hints Resolve mult_lt : arith.

Lemma mult_le_conv_1 : (m,n,p:nat) (le (mult (S m) n) (mult (S m) p)) -> (le n p).
Proof.
  Intros. Elim (le_or_lt n p). Trivial.
  Intro H0. Cut (lt (mult (S m) n) (mult (S m) n)). Intro. Elim (lt_n_n ? H1).
  Apply le_lt_trans with m:=(mult (S m) p). Assumption.
  Apply mult_lt. Assumption.
Qed.

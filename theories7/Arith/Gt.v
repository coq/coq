(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Le.
Require Lt.
Require Plus.
V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type m,n,p:nat.

(** Order and successor *)

Theorem gt_Sn_O : (n:nat)(gt (S n) O).
Proof.
  Auto with arith.
Qed.
Hints Resolve gt_Sn_O : arith v62.

Theorem gt_Sn_n : (n:nat)(gt (S n) n).
Proof.
  Auto with arith.
Qed.
Hints Resolve gt_Sn_n : arith v62.

Theorem gt_n_S : (n,m:nat)(gt n m)->(gt (S n) (S m)).
Proof.
  Auto with arith.
Qed.
Hints Resolve gt_n_S : arith v62.

Lemma gt_S_n : (n,p:nat)(gt (S p) (S n))->(gt p n).
Proof.
  Auto with arith.
Qed.
Hints Immediate gt_S_n : arith v62.

Theorem gt_S : (n,m:nat)(gt (S n) m)->((gt n m)\/(m=n)).
Proof.
  Intros n m H; Unfold gt; Apply le_lt_or_eq; Auto with arith.
Qed.

Lemma gt_pred : (n,p:nat)(gt p (S n))->(gt (pred p) n).
Proof.
  Auto with arith.
Qed.
Hints Immediate gt_pred : arith v62.

(** Irreflexivity *)

Lemma gt_antirefl : (n:nat)~(gt n n).
Proof lt_n_n.
Hints Resolve gt_antirefl : arith v62.

(** Asymmetry *)

Lemma gt_not_sym : (n,m:nat)(gt n m) -> ~(gt m n).
Proof [n,m:nat](lt_not_sym m n).

Hints Resolve gt_not_sym : arith v62.

(** Relating strict and large orders *)

Lemma le_not_gt : (n,m:nat)(le n m) -> ~(gt n m).
Proof le_not_lt.
Hints Resolve le_not_gt : arith v62.

Lemma gt_not_le : (n,m:nat)(gt n m) -> ~(le n m).
Proof.
Auto with arith.
Qed.

Hints Resolve gt_not_le : arith v62.

Theorem le_S_gt : (n,m:nat)(le (S n) m)->(gt m n).
Proof.
  Auto with arith.
Qed.
Hints Immediate le_S_gt : arith v62.

Lemma gt_S_le : (n,p:nat)(gt (S p) n)->(le n p).
Proof.
  Intros n p; Exact (lt_n_Sm_le n p).
Qed.
Hints Immediate gt_S_le : arith v62.

Lemma gt_le_S : (n,p:nat)(gt p n)->(le (S n) p).
Proof.
  Auto with arith.
Qed.
Hints Resolve gt_le_S : arith v62.

Lemma le_gt_S : (n,p:nat)(le n p)->(gt (S p) n).
Proof.
  Auto with arith.
Qed.
Hints Resolve le_gt_S : arith v62.

(** Transitivity *)

Theorem le_gt_trans : (n,m,p:nat)(le m n)->(gt m p)->(gt n p).
Proof.
  Red; Intros; Apply lt_le_trans with m; Auto with arith.
Qed.

Theorem gt_le_trans : (n,m,p:nat)(gt n m)->(le p m)->(gt n p).
Proof.
  Red; Intros; Apply le_lt_trans with m; Auto with arith.
Qed.

Lemma gt_trans : (n,m,p:nat)(gt n m)->(gt m p)->(gt n p).
Proof.
  Red; Intros n m p H1 H2.
  Apply lt_trans with m; Auto with arith.
Qed.

Theorem gt_trans_S : (n,m,p:nat)(gt (S n) m)->(gt m p)->(gt n p).
Proof.
  Red; Intros; Apply lt_le_trans with m; Auto with arith.
Qed.

Hints Resolve gt_trans_S le_gt_trans gt_le_trans : arith v62.

(** Comparison to 0 *)

Theorem gt_O_eq : (n:nat)((gt n O)\/(O=n)).
Proof.
  Intro n ; Apply gt_S ; Auto with arith.
Qed.

(** Simplification and compatibility *)

Lemma simpl_gt_plus_l : (n,m,p:nat)(gt (plus p n) (plus p m))->(gt n m).
Proof.
  Red; Intros n m p H; Apply simpl_lt_plus_l with p; Auto with arith.
Qed.

Lemma gt_reg_l : (n,m,p:nat)(gt n m)->(gt (plus p n) (plus p m)).
Proof.
  Auto with arith.
Qed.
Hints Resolve gt_reg_l : arith v62.

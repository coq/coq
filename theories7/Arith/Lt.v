(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Le.
V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type m,n,p:nat.

(** Irreflexivity *)

Theorem lt_n_n : (n:nat)~(lt n n).
Proof le_Sn_n.
Hints Resolve lt_n_n : arith v62.

(** Relationship between [le] and [lt] *) 

Theorem lt_le_S : (n,p:nat)(lt n p)->(le (S n) p).
Proof.
Auto with arith.
Qed.
Hints Immediate lt_le_S : arith v62.

Theorem lt_n_Sm_le : (n,m:nat)(lt n (S m))->(le n m).
Proof.
Auto with arith.
Qed.
Hints Immediate lt_n_Sm_le : arith v62.

Theorem le_lt_n_Sm : (n,m:nat)(le n m)->(lt n (S m)).
Proof.
Auto with arith.
Qed.
Hints Immediate le_lt_n_Sm : arith v62.

Theorem le_not_lt : (n,m:nat)(le n m) -> ~(lt m n).
Proof.
NewInduction 1; Auto with arith.
Qed.

Theorem lt_not_le : (n,m:nat)(lt n m) -> ~(le m n).
Proof.
Red; Intros n m Lt Le; Exact (le_not_lt m n Le Lt).
Qed.
Hints Immediate le_not_lt lt_not_le : arith v62.

(** Asymmetry *)

Theorem lt_not_sym : (n,m:nat)(lt n m) -> ~(lt m n).
Proof.
NewInduction 1; Auto with arith.
Qed.

(** Order and successor *)

Theorem lt_n_Sn : (n:nat)(lt n (S n)).
Proof.
Auto with arith.
Qed.
Hints Resolve lt_n_Sn : arith v62.

Theorem lt_S : (n,m:nat)(lt n m)->(lt n (S m)).
Proof.
Auto with arith.
Qed.
Hints Resolve lt_S : arith v62.

Theorem lt_n_S : (n,m:nat)(lt n m)->(lt (S n) (S m)).
Proof.
Auto with arith.
Qed.
Hints Resolve lt_n_S : arith v62.

Theorem lt_S_n : (n,m:nat)(lt (S n) (S m))->(lt n m).
Proof.
Auto with arith.
Qed.
Hints Immediate lt_S_n : arith v62.

Theorem lt_O_Sn : (n:nat)(lt O (S n)).
Proof.
Auto with arith.
Qed.
Hints Resolve lt_O_Sn : arith v62.

Theorem lt_n_O : (n:nat)~(lt n O).
Proof le_Sn_O.
Hints Resolve lt_n_O : arith v62.

(** Predecessor *)

Lemma S_pred : (n,m:nat)(lt m n)->n=(S (pred n)).
Proof.
NewInduction 1; Auto with arith.
Qed.

Lemma lt_pred : (n,p:nat)(lt (S n) p)->(lt n (pred p)).
Proof.
NewInduction 1; Simpl; Auto with arith.
Qed.
Hints Immediate lt_pred : arith v62.

Lemma lt_pred_n_n : (n:nat)(lt O n)->(lt (pred n) n).
NewDestruct 1; Simpl; Auto with arith.
Qed.
Hints Resolve lt_pred_n_n : arith v62.

(** Transitivity properties *)

Theorem lt_trans : (n,m,p:nat)(lt n m)->(lt m p)->(lt n p).
Proof.
NewInduction 2; Auto with arith.
Qed.

Theorem lt_le_trans : (n,m,p:nat)(lt n m)->(le m p)->(lt n p).
Proof.
NewInduction 2; Auto with arith.
Qed.

Theorem le_lt_trans : (n,m,p:nat)(le n m)->(lt m p)->(lt n p).
Proof.
NewInduction 2; Auto with arith.
Qed.

Hints Resolve lt_trans lt_le_trans le_lt_trans : arith v62.

(** Large = strict or equal *)

Theorem le_lt_or_eq : (n,m:nat)(le n m)->((lt n m) \/ n=m).
Proof.
NewInduction 1; Auto with arith.
Qed.

Theorem lt_le_weak : (n,m:nat)(lt n m)->(le n m).
Proof.
Auto with arith.
Qed.
Hints Immediate lt_le_weak : arith v62.

(** Dichotomy *)

Theorem le_or_lt : (n,m:nat)((le n m)\/(lt m n)).
Proof.
Intros n m; Pattern n m; Apply nat_double_ind; Auto with arith.
NewInduction 1; Auto with arith.
Qed.

Theorem nat_total_order: (m,n: nat) ~ m = n -> (lt m n) \/ (lt n m).
Proof.
Intros m n diff.
Elim (le_or_lt n m); [Intro H'0 | Auto with arith].
Elim (le_lt_or_eq n m); Auto with arith.
Intro H'; Elim diff; Auto with arith.
Qed.

(** Comparison to 0 *)

Theorem neq_O_lt : (n:nat)(~O=n)->(lt O n).
Proof.
NewInduction n; Auto with arith.
Intros; Absurd O=O; Trivial with arith.
Qed.
Hints Immediate neq_O_lt : arith v62.

Theorem lt_O_neq : (n:nat)(lt O n)->(~O=n).
Proof.
NewInduction 1; Auto with arith.
Qed.
Hints Immediate lt_O_neq : arith v62.

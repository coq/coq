(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Order on natural numbers *)
V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type m,n,p:nat.

(** Reflexivity *)

Theorem le_refl : (n:nat)(le n n).
Proof.
Exact le_n.
Qed.

(** Transitivity *)

Theorem le_trans : (n,m,p:nat)(le n m)->(le m p)->(le n p).
Proof.
  NewInduction 2; Auto.
Qed.
Hints Resolve le_trans : arith v62.

(** Order, successor and predecessor *)

Theorem le_n_S : (n,m:nat)(le n m)->(le (S n) (S m)).
Proof.
  NewInduction 1; Auto.
Qed.

Theorem le_n_Sn : (n:nat)(le n (S n)).
Proof.
  Auto.
Qed.

Theorem le_O_n : (n:nat)(le O n).
Proof.
  NewInduction n ; Auto.
Qed.

Hints Resolve le_n_S le_n_Sn le_O_n le_n_S : arith v62.

Theorem le_pred_n : (n:nat)(le (pred n) n).
Proof.
NewInduction n ; Auto with arith.
Qed.
Hints Resolve le_pred_n : arith v62.

Theorem le_trans_S : (n,m:nat)(le (S n) m)->(le n m).
Proof.
Intros n m H ; Apply le_trans with (S n); Auto with arith.
Qed.
Hints Immediate le_trans_S : arith v62.

Theorem le_S_n : (n,m:nat)(le (S n) (S m))->(le n m).
Proof.
Intros n m H ; Change (le (pred (S n)) (pred (S m))).
Elim H ; Simpl ; Auto with arith.
Qed.
Hints Immediate le_S_n : arith v62.

Theorem le_pred : (n,m:nat)(le n m)->(le (pred n) (pred m)).
Proof.
NewInduction n as [|n IHn]. Simpl. Auto with arith.
NewDestruct m as [|m]. Simpl. Intro H. Inversion H.
Simpl. Auto with arith.
Qed.

(** Comparison to 0 *)

Theorem le_Sn_O : (n:nat)~(le (S n) O).
Proof.
Red ; Intros n H.
Change (IsSucc O) ; Elim H ; Simpl ; Auto with arith.
Qed.
Hints Resolve le_Sn_O : arith v62.

Theorem le_n_O_eq : (n:nat)(le n O)->(O=n).
Proof.
NewInduction n; Auto with arith.
Intro; Contradiction le_Sn_O with n.
Qed.
Hints Immediate le_n_O_eq : arith v62.

(** Negative properties *)

Theorem le_Sn_n : (n:nat)~(le (S n) n).
Proof.
NewInduction n; Auto with arith.
Qed.
Hints Resolve le_Sn_n : arith v62.

(** Antisymmetry *)

Theorem le_antisym : (n,m:nat)(le n m)->(le m n)->(n=m).
Proof.
Intros n m h ; NewDestruct h as [|m0]; Auto with arith.
Intros H1.
Absurd (le (S m0) m0) ; Auto with arith.
Apply le_trans with n ; Auto with arith.
Qed.
Hints Immediate le_antisym : arith v62.

(** A different elimination principle for the order on natural numbers *)

Lemma le_elim_rel : (P:nat->nat->Prop)
     ((p:nat)(P O p))->
     ((p,q:nat)(le p q)->(P p q)->(P (S p) (S q)))->
     (n,m:nat)(le n m)->(P n m).
Proof.
NewInduction n; Auto with arith.
Intros m Le.
Elim Le; Auto with arith.
Qed.

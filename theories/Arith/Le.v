(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(***************************************)
(* Order on natural numbers            *)
(***************************************)

Theorem le_n_S : (n,m:nat)(le n m)->(le (S n) (S m)).
Proof.
  NewInduction 1; Auto.
Qed.

Theorem le_trans : (n,m,p:nat)(le n m)->(le m p)->(le n p).
Proof.
  NewInduction 2; Auto.
Qed.

Theorem le_n_Sn : (n:nat)(le n (S n)).
Proof.
  Auto.
Qed.

Theorem le_O_n : (n:nat)(le O n).
Proof.
  NewInduction n ; Auto.
Qed.

Hints Resolve le_n_S le_n_Sn le_O_n le_n_S le_trans : arith v62.

Theorem le_pred_n : (n:nat)(le (pred n) n).
Proof.
NewInduction n ; Auto with arith.
Qed.
Hints Resolve le_pred_n : arith v62.

Theorem le_trans_S : (n,m:nat)(le (S n) m)->(le n m).
Proof.
Intros n m H ; Apply le_trans with (S n) ; Auto with arith.
Qed.
Hints Immediate le_trans_S : arith v62.

Theorem le_S_n : (n,m:nat)(le (S n) (S m))->(le n m).
Proof.
Intros n m H ; Change (le (pred (S n)) (pred (S m))).
(*  (le (pred (S n)) (pred (S m)))
    ============================
      H : (le (S n) (S m))
      m : nat
      n : nat *)
Elim H ; Simpl ; Auto with arith.
Qed.
Hints Immediate le_S_n : arith v62.

(* Negative properties *)

Theorem le_Sn_O : (n:nat)~(le (S n) O).
Proof.
Red ; Intros n H.
(*  False
    ============================
      H : (lt n O)
      n : nat *)
Change (IsSucc O) ; Elim H ; Simpl ; Auto with arith.
Qed.
Hints Resolve le_Sn_O : arith v62.

Theorem le_Sn_n : (n:nat)~(le (S n) n).
Proof.
NewInduction n; Auto with arith.
Qed.
Hints Resolve le_Sn_n : arith v62.

Theorem le_antisym : (n,m:nat)(le n m)->(le m n)->(n=m).
Proof.
Intros n m h ; Elim h ; Auto with arith.
(*  (m:nat)(le n m)->((le m n)->(n=m))->(le (S m) n)->(n=(S m))
    ============================
      h : (le n m)
      m : nat
      n : nat *)
Intros m0 H H0 H1.
Absurd (le (S m0) m0) ; Auto with arith.
(*  (le (S m0) m0)
    ============================
      H1 : (le (S m0) n)
      H0 : (le m0 n)->(<nat>n=m0)
      H : (le n m0)
      m0 : nat *)
Apply le_trans with n ; Auto with arith.
Qed.
Hints Immediate le_antisym : arith v62.

Theorem le_n_O_eq : (n:nat)(le n O)->(O=n).
Proof.
Auto with arith.
Qed.
Hints Immediate le_n_O_eq : arith v62.

(* A different elimination principle for the order on natural numbers *)

Lemma le_elim_rel : (P:nat->nat->Prop)
     ((p:nat)(P O p))->
     ((p,q:nat)(le p q)->(P p q)->(P (S p) (S q)))->
     (n,m:nat)(le n m)->(P n m).
Proof.
NewInduction n; Auto with arith.
Intros m Le.
Elim Le; Auto with arith.
Qed.

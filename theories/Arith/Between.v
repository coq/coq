(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Le.
Require Lt.

Section Between.
Variables P,Q : nat -> Prop.

Inductive between [k:nat] : nat -> Prop
 := bet_emp : (between k k)
 | bet_S : (l:nat)(between k l)->(P l)->(between k (S l)).

Hint constr_between : arith v62 := Constructors between.

Lemma bet_eq : (k,l:nat)(l=k)->(between k l).
Proof.
Induction 1; Auto with arith.
Qed.

Hints Resolve bet_eq : arith v62.

Lemma between_le : (k,l:nat)(between k l)->(le k l).
Proof.
Induction 1; Auto with arith.
Qed.
Hints Immediate between_le : arith v62.

Lemma between_Sk_l : (k,l:nat)(between k l)->(le (S k) l)->(between (S k) l).
Proof.
Induction 1.
Intros; Absurd (le (S k) k); Auto with arith.
Induction 1; Auto with arith.
Qed.
Hints Resolve between_Sk_l : arith v62.

Lemma between_restr : 
  (k,l,m:nat)(le k l)->(le l m)->(between k m)->(between l m).
Proof.
Induction 1; Auto with arith.
Qed.

Inductive exists [k:nat] : nat -> Prop
 := exists_S : (l:nat)(exists k l)->(exists k (S l))
 | exists_le: (l:nat)(le k l)->(Q l)->(exists k (S l)).

Hint constr_exists : arith v62 := Constructors exists.

Lemma exists_le_S : (k,l:nat)(exists k l)->(le (S k) l).
Proof.
Induction 1; Auto with arith.
Qed.

Lemma exists_lt : (k,l:nat)(exists k l)->(lt k l).
Proof exists_le_S.
Hints Immediate exists_le_S exists_lt : arith v62.

Lemma exists_S_le : (k,l:nat)(exists k (S l))->(le k l).
Proof.
Intros; Apply le_S_n; Auto with arith.
Qed.
Hints Immediate exists_S_le : arith v62.

Definition in_int := [p,q,r:nat](le p r)/\(lt r q).

Lemma in_int_intro : (p,q,r:nat)(le p r)->(lt r q)->(in_int p q r).
Proof.
Red; Auto with arith.
Qed.
Hints Resolve in_int_intro : arith v62.

Lemma in_int_lt : (p,q,r:nat)(in_int p q r)->(lt p q).
Proof.
Induction 1; Intros.
Apply le_lt_trans with r; Auto with arith.
Qed.

Lemma in_int_p_Sq : 
  (p,q,r:nat)(in_int p (S q) r)->((in_int p q r) \/ <nat>r=q).
Proof.
Induction 1; Intros.
Elim (le_lt_or_eq r q); Auto with arith.
Qed.

Lemma in_int_S : (p,q,r:nat)(in_int p q r)->(in_int p (S q) r).
Proof.
Induction 1;Auto with arith.
Qed.
Hints Resolve in_int_S : arith v62.

Lemma in_int_Sp_q : (p,q,r:nat)(in_int (S p) q r)->(in_int p q r).
Proof.
Induction 1; Auto with arith.
Qed.
Hints Immediate in_int_Sp_q : arith v62.

Lemma between_in_int : (k,l:nat)(between k l)->(r:nat)(in_int k l r)->(P r).
Proof.
Induction 1; Intros.
Absurd (lt k k); Auto with arith.
Apply in_int_lt with r; Auto with arith.
Elim (in_int_p_Sq k l0 r); Intros; Auto with arith.
Rewrite H4; Trivial with arith.
Qed.

Lemma in_int_between : 
  (k,l:nat)(le k l)->((r:nat)(in_int k l r)->(P r))->(between k l).
Proof.
Induction 1; Auto with arith.
Qed.

Lemma exists_in_int : 
  (k,l:nat)(exists k l)->(EX m:nat | (in_int k l m) & (Q m)).
Proof.
Induction 1.
Induction 2; Intros p inp Qp; Exists p; Auto with arith.
Intros; Exists l0; Auto with arith.
Qed.

Lemma in_int_exists : (k,l,r:nat)(in_int k l r)->(Q r)->(exists k l).
Proof.
Induction 1; Intros.
Elim H1; Auto with arith.
Qed.

Lemma between_or_exists : 
  (k,l:nat)(le k l)->((n:nat)(in_int k l n)->((P n)\/(Q n)))
     ->((between k l)\/(exists k l)).
Proof.
Induction 1; Intros; Auto with arith.
Elim H1; Intro; Auto with arith.
Elim (H2 m); Auto with arith.
Qed.

Lemma between_not_exists : (k,l:nat)(between k l)->
     ((n:nat)(in_int k l n) -> (P n) -> ~(Q n))
     -> ~(exists k l).
Proof.
Induction 1; Red; Intros.
Absurd (lt k k); Auto with arith.
Absurd (Q l0); Auto with arith.
Elim (exists_in_int k (S l0)); Auto with arith; Intros l' inl' Ql'.
Replace l0 with l'; Auto with arith.
Elim inl'; Intros.
Elim (le_lt_or_eq l' l0); Auto with arith; Intros.
Absurd (exists k l0); Auto with arith.
Apply in_int_exists with l'; Auto with arith.
Qed.

Inductive nth [init:nat] : nat->nat->Prop
  := nth_O : (nth init init O)
  | nth_S : (k,l:nat)(n:nat)(nth init k n)->(between (S k) l)
                        ->(Q l)->(nth init l (S n)).

Lemma nth_le : (init,l,n:nat)(nth init l n)->(le init l).
Proof.
Induction 1; Intros; Auto with arith.
Apply le_trans with (S k); Auto with arith.
Qed.

Definition eventually := [n:nat](EX k:nat | (le k n) & (Q k)).

Lemma event_O : (eventually O)->(Q O).
Proof.
Induction 1; Intros.
Replace O with x; Auto with arith.
Qed.

End Between.

Hints Resolve nth_O bet_S bet_emp bet_eq between_Sk_l exists_S exists_le 
 in_int_S in_int_intro : arith v62. 
Hints Immediate in_int_Sp_q exists_le_S exists_S_le : arith v62.

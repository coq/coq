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

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type k,l,p,q,r:nat.

Section Between.
Variables P,Q : nat -> Prop.

Inductive between [k:nat] : nat -> Prop
 := bet_emp : (between k k)
 | bet_S : (l:nat)(between k l)->(P l)->(between k (S l)).

Hint constr_between : arith v62 := Constructors between.

Lemma bet_eq : (k,l:nat)(l=k)->(between k l).
Proof.
NewInduction 1; Auto with arith.
Qed.

Hints Resolve bet_eq : arith v62.

Lemma between_le : (k,l:nat)(between k l)->(le k l).
Proof.
NewInduction 1; Auto with arith.
Qed.
Hints Immediate between_le : arith v62.

Lemma between_Sk_l : (k,l:nat)(between k l)->(le (S k) l)->(between (S k) l).
Proof.
NewInduction 1.
Intros; Absurd (le (S k) k); Auto with arith.
NewDestruct H; Auto with arith.
Qed.
Hints Resolve between_Sk_l : arith v62.

Lemma between_restr : 
  (k,l,m:nat)(le k l)->(le l m)->(between k m)->(between l m).
Proof.
NewInduction 1; Auto with arith.
Qed.

Inductive exists [k:nat] : nat -> Prop
 := exists_S : (l:nat)(exists k l)->(exists k (S l))
 | exists_le: (l:nat)(le k l)->(Q l)->(exists k (S l)).

Hint constr_exists : arith v62 := Constructors exists.

Lemma exists_le_S : (k,l:nat)(exists k l)->(le (S k) l).
Proof.
NewInduction 1; Auto with arith.
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
NewInduction 1; Intros.
Apply le_lt_trans with r; Auto with arith.
Qed.

Lemma in_int_p_Sq : 
  (p,q,r:nat)(in_int p (S q) r)->((in_int p q r) \/ <nat>r=q).
Proof.
NewInduction 1; Intros.
Elim (le_lt_or_eq r q); Auto with arith.
Qed.

Lemma in_int_S : (p,q,r:nat)(in_int p q r)->(in_int p (S q) r).
Proof.
NewInduction 1;Auto with arith.
Qed.
Hints Resolve in_int_S : arith v62.

Lemma in_int_Sp_q : (p,q,r:nat)(in_int (S p) q r)->(in_int p q r).
Proof.
NewInduction 1; Auto with arith.
Qed.
Hints Immediate in_int_Sp_q : arith v62.

Lemma between_in_int : (k,l:nat)(between k l)->(r:nat)(in_int k l r)->(P r).
Proof.
NewInduction 1; Intros.
Absurd (lt k k); Auto with arith.
Apply in_int_lt with r; Auto with arith.
Elim (in_int_p_Sq k l r); Intros; Auto with arith.
Rewrite H2; Trivial with arith.
Qed.

Lemma in_int_between : 
  (k,l:nat)(le k l)->((r:nat)(in_int k l r)->(P r))->(between k l).
Proof.
NewInduction 1; Auto with arith.
Qed.

Lemma exists_in_int : 
  (k,l:nat)(exists k l)->(EX m:nat | (in_int k l m) & (Q m)).
Proof.
NewInduction 1.
Case IHexists; Intros p inp Qp; Exists p; Auto with arith.
Exists l; Auto with arith.
Qed.

Lemma in_int_exists : (k,l,r:nat)(in_int k l r)->(Q r)->(exists k l).
Proof.
NewDestruct 1; Intros.
Elim H0; Auto with arith.
Qed.

Lemma between_or_exists : 
  (k,l:nat)(le k l)->((n:nat)(in_int k l n)->((P n)\/(Q n)))
     ->((between k l)\/(exists k l)).
Proof.
NewInduction 1; Intros; Auto with arith.
Elim IHle; Intro; Auto with arith.
Elim (H0 m); Auto with arith.
Qed.

Lemma between_not_exists : (k,l:nat)(between k l)->
     ((n:nat)(in_int k l n) -> (P n) -> ~(Q n))
     -> ~(exists k l).
Proof.
NewInduction 1; Red; Intros.
Absurd (lt k k); Auto with arith.
Absurd (Q l); Auto with arith.
Elim (exists_in_int k (S l)); Auto with arith; Intros l' inl' Ql'.
Replace l with l'; Auto with arith.
Elim inl'; Intros.
Elim (le_lt_or_eq l' l); Auto with arith; Intros.
Absurd (exists k l); Auto with arith.
Apply in_int_exists with l'; Auto with arith.
Qed.

Inductive P_nth [init:nat] : nat->nat->Prop
  := nth_O : (P_nth init init O)
  | nth_S : (k,l:nat)(n:nat)(P_nth init k n)->(between (S k) l)
                        ->(Q l)->(P_nth init l (S n)).

Lemma nth_le : (init,l,n:nat)(P_nth init l n)->(le init l).
Proof.
NewInduction 1; Intros; Auto with arith.
Apply le_trans with (S k); Auto with arith.
Qed.

Definition eventually := [n:nat](EX k:nat | (le k n) & (Q k)).

Lemma event_O : (eventually O)->(Q O).
Proof.
NewInduction 1; Intros.
Replace O with x; Auto with arith.
Qed.

End Between.

Hints Resolve nth_O bet_S bet_emp bet_eq between_Sk_l exists_S exists_le 
 in_int_S in_int_intro : arith v62. 
Hints Immediate in_int_Sp_q exists_le_S exists_S_le : arith v62.

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** Properties of addition *)

Require Le.
Require Lt.

Import nat_scope.

Lemma plus_sym : (n,m:nat)(n+m)=(m+n).
Proof.
Intros n m ; Elim n ; Simpl_rew ; Auto with arith.
Intros y H ; Elim (plus_n_Sm m y) ; Simpl_rew ; Auto with arith.
Qed.
Hints Immediate plus_sym : arith v62.

Lemma plus_Snm_nSm : (n,m:nat)((S n)+m)=(n+(S m)).
Intros.
Simpl_rew.
Rewrite -> (plus_sym n m).
Rewrite -> (plus_sym n (S m)).
Trivial with arith.
Qed.

Lemma simpl_plus_l : (n,m,p:nat)((n+m)=(n+p))->(m=p).
Proof.
NewInduction n ; Simpl ; Auto with arith.
Qed.

Lemma plus_assoc_l : (n,m,p:nat)((n+(m+p))=((n+m)+p)).
Proof.
Intros n m p; Elim n; Simpl_rew; Auto with arith.
Qed.
Hints Resolve plus_assoc_l : arith v62.

Lemma plus_permute : (n,m,p:nat) ((n+(m+p))=(m+(n+p))).
Proof. 
Intros; Rewrite (plus_assoc_l m n p); Rewrite (plus_sym m n); Auto with arith.
Qed.

Lemma plus_assoc_r : (n,m,p:nat)(((n+m)+p)=(n+(m+p))).
Proof.
Auto with arith.
Qed.
Hints Resolve plus_assoc_r : arith v62.

Lemma simpl_le_plus_l : (p,n,m:nat) (p+n)<=(p+m) -> n<=m.
Proof.
NewInduction p; Simpl; Auto with arith.
Qed.

Lemma le_reg_l : (n,m,p:nat) n<=m -> (p+n)<=(p+m).
Proof.
NewInduction p; Simpl_rew; Auto with arith.
Qed.
Hints Resolve le_reg_l : arith v62.

Lemma le_reg_r : (a,b,c:nat) a<=b -> (a+c)<=(b+c).
Proof.
NewInduction 1 ; Simpl_rew; Auto with arith.
Qed.
Hints Resolve le_reg_r : arith v62.

Lemma le_plus_plus : (n,m,p,q:nat)  n<=m -> p<=q -> (n+p)<=(m+q).
Proof.
Intros n m p q H H0.
Elim H; Simpl_rew; Auto with arith.
Qed.

Lemma le_plus_l : (n,m:nat) n<=(n+m).
Proof.
NewInduction n; Simpl_rew; Auto with arith.
Qed.
Hints Resolve le_plus_l : arith v62.

Lemma le_plus_r : (n,m:nat) m<=(n+m).
Proof.
Intros n m; Elim n; Simpl_rew; Auto with arith.
Qed.
Hints Resolve le_plus_r : arith v62.

Theorem le_plus_trans : (n,m,p:nat) n<=m -> n<=(m+p).
Proof.
Intros; Apply le_trans with m:=m; Auto with arith.
Qed.
Hints Resolve le_plus_trans : arith v62.

Lemma simpl_lt_plus_l : (n,m,p:nat) (p+n)<(p+m) -> n<m.
Proof.
NewInduction p; Simpl; Auto with arith.
Qed.

Lemma lt_reg_l : (n,m,p:nat) n<m -> (p+n)<(p+m).
Proof.
NewInduction p; Simpl_rew; Auto with arith.
Qed.
Hints Resolve lt_reg_l : arith v62.

Lemma lt_reg_r : (n,m,p:nat) n<m -> (n+p)<(m+p).
Proof.
Intros n m p H ; Rewrite (plus_sym n p) ; Rewrite (plus_sym m p).
Elim p; Auto with arith.
Qed.
Hints Resolve lt_reg_r : arith v62.

Theorem lt_plus_trans : (n,m,p:nat) n<m -> n<(m+p).
Proof.
Intros; Apply lt_le_trans with m:=m; Auto with arith.
Qed.
Hints Immediate lt_plus_trans : arith v62.

Lemma le_lt_plus_plus : (n,m,p,q:nat)  n<=m -> p<q -> (n+p)<(m+q).
Proof.
  Unfold lt. Intros. Change ((S n)+p)<=(m+q). Rewrite plus_Snm_nSm.
  Apply le_plus_plus; Assumption.
Qed.

Lemma lt_le_plus_plus : (n,m,p,q:nat) n<m -> p<=q -> (n+p)<(m+q).
Proof.
  Unfold lt. Intros. Change ((S n)+p)<=(m+q). Apply le_plus_plus; Assumption.
Qed.

Lemma lt_plus_plus : (n,m,p,q:nat) n<m -> p<q -> (n+p)<(m+q).
Proof.
  Intros. Apply lt_le_plus_plus. Assumption.
  Apply lt_le_weak. Assumption.
Qed.


Lemma plus_is_O : (m,n:nat) (m+n)=O -> m=O /\ n=O.
Proof.
  NewDestruct m; Auto.
  Simpl_rew. Intros. Discriminate H.
Qed.

Definition plus_is_one : 
      (m,n:nat) (m+n)=(S O) -> {m=O /\ n=(S O)}+{m=(S O) /\ n=O}.
Proof.
  NewDestruct m; Auto.
  NewDestruct n; Auto.
  Intros. 
  Simpl_rew in H. Discriminate H.
Defined.

Lemma plus_permute_2_in_4 : (a,b,c,d:nat) ((a+b)+(c+d))=((a+c)+(b+d)).
Proof.
  Intros. 
  Rewrite <- (plus_assoc_l a b (c+d)). Rewrite (plus_assoc_l b c d).
  Rewrite (plus_sym b c). Rewrite <- (plus_assoc_l c b d). Apply plus_assoc_l.
Qed.


(** Tail-recursive plus *)

(** [tail_plus] is an alternative definition for [plus] which is 
    tail-recursive, whereas [plus] is not. This can be useful
    when extracting programs. *)

Fixpoint plus_acc [s,n:nat] : nat := 
   Cases n of 
      O => s
      | (S p) => (plus_acc (S s) p)
    end.

Definition tail_plus := [n,m:nat](plus_acc m n).

Lemma plus_tail_plus : (n,m:nat)(n+m)=(tail_plus n m).
Induction n; Unfold tail_plus; Simpl; Auto.
Intros p H m; Rewrite <- H; Simpl; Auto.
Qed.

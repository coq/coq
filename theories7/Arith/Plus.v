(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Properties of addition *)

Require Le.
Require Lt.

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type m,n,p,q:nat.

(** Zero is neutral *)

Lemma plus_0_l : (n:nat) (O+n)=n.
Proof.
Reflexivity.
Qed.

Lemma plus_0_r : (n:nat) (n+O)=n.
Proof.
Intro; Symmetry; Apply plus_n_O.
Qed.

(** Commutativity *)

Lemma plus_sym : (n,m:nat)(n+m)=(m+n).
Proof.
Intros n m ; Elim n ; Simpl ; Auto with arith.
Intros y H ; Elim (plus_n_Sm m y) ; Auto with arith.
Qed.
Hints Immediate plus_sym : arith v62.

(** Associativity *)

Lemma plus_Snm_nSm : (n,m:nat)((S n)+m)=(n+(S m)).
Intros.
Simpl.
Rewrite -> (plus_sym n m).
Rewrite -> (plus_sym n (S m)).
Trivial with arith.
Qed.

Lemma plus_assoc_l : (n,m,p:nat)((n+(m+p))=((n+m)+p)).
Proof.
Intros n m p; Elim n; Simpl; Auto with arith.
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

(** Simplification *)

Lemma plus_reg_l : (m,p,n:nat)((n+m)=(n+p))->(m=p).
Proof.
Intros m p n; NewInduction n ; Simpl ; Auto with arith.
Qed.
V7only [
(* Compatibility order of arguments *)
Notation "'simpl_plus_l' c" := [a,b:nat](plus_reg_l a b c)
  (at level 10, c at next level).
Notation "'simpl_plus_l' c a" := [b:nat](plus_reg_l a b c)
  (at level 10, a, c at next level).
Notation "'simpl_plus_l' c a b" := (plus_reg_l a b c)
  (at level 10, a, b, c at next level).
Notation simpl_plus_l := plus_reg_l.
].

Lemma plus_le_reg_l : (n,m,p:nat)((p+n)<=(p+m))->(n<=m).
Proof.
NewInduction p; Simpl; Auto with arith.
Qed.
V7only [
(* Compatibility order of arguments *)
Notation "'simpl_le_plus_l' c" := [a,b:nat](plus_le_reg_l a b c)
  (at level 10, c at next level).
Notation "'simpl_le_plus_l' c a" := [b:nat](plus_le_reg_l a b c)
  (at level 10, a, c at next level).
Notation "'simpl_le_plus_l' c a b" := (plus_le_reg_l a b c)
  (at level 10, a, b, c at next level).
Notation simpl_le_plus_l := [p,n,m:nat](plus_le_reg_l n m p).
].

Lemma simpl_lt_plus_l : (n,m,p:nat) (p+n)<(p+m) -> n<m.
Proof.
NewInduction p; Simpl; Auto with arith.
Qed.

(** Compatibility with order *)

Lemma le_reg_l : (n,m,p:nat) n<=m -> (p+n)<=(p+m).
Proof.
NewInduction p; Simpl; Auto with arith.
Qed.
Hints Resolve le_reg_l : arith v62.

Lemma le_reg_r : (a,b,c:nat) a<=b -> (a+c)<=(b+c).
Proof.
NewInduction 1 ; Simpl; Auto with arith.
Qed.
Hints Resolve le_reg_r : arith v62.

Lemma le_plus_l : (n,m:nat) n<=(n+m).
Proof.
NewInduction n; Simpl; Auto with arith.
Qed.
Hints Resolve le_plus_l : arith v62.

Lemma le_plus_r : (n,m:nat) m<=(n+m).
Proof.
Intros n m; Elim n; Simpl; Auto with arith.
Qed.
Hints Resolve le_plus_r : arith v62.

Theorem le_plus_trans : (n,m,p:nat) n<=m -> n<=(m+p).
Proof.
Intros; Apply le_trans with m:=m; Auto with arith.
Qed.
Hints Resolve le_plus_trans : arith v62.

Theorem lt_plus_trans : (n,m,p:nat) n<m -> n<(m+p).
Proof.
Intros; Apply lt_le_trans with m:=m; Auto with arith.
Qed.
Hints Immediate lt_plus_trans : arith v62.

Lemma lt_reg_l : (n,m,p:nat) n<m -> (p+n)<(p+m).
Proof.
NewInduction p; Simpl; Auto with arith.
Qed.
Hints Resolve lt_reg_l : arith v62.

Lemma lt_reg_r : (n,m,p:nat) n<m -> (n+p)<(m+p).
Proof.
Intros n m p H ; Rewrite (plus_sym n p) ; Rewrite (plus_sym m p).
Elim p; Auto with arith.
Qed.
Hints Resolve lt_reg_r : arith v62.

Lemma le_plus_plus : (n,m,p,q:nat)  n<=m -> p<=q -> (n+p)<=(m+q).
Proof.
Intros n m p q H H0.
Elim H; Simpl; Auto with arith.
Qed.

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

(** Inversion lemmas *)

Lemma plus_is_O : (m,n:nat) (m+n)=O -> m=O /\ n=O.
Proof.
  Intro m; NewDestruct m; Auto.
  Intros. Discriminate H.
Qed.

Definition plus_is_one : 
      (m,n:nat) (m+n)=(S O) -> {m=O /\ n=(S O)}+{m=(S O) /\ n=O}.
Proof.
  Intro m; NewDestruct m; Auto.
  NewDestruct n; Auto.
  Intros. 
  Simpl in H. Discriminate H.
Defined.

(** Derived properties *)

Lemma plus_permute_2_in_4 : (m,n,p,q:nat) ((m+n)+(p+q))=((m+p)+(n+q)).
Proof.
  Intros m n p q. 
  Rewrite <- (plus_assoc_l m n (p+q)). Rewrite (plus_assoc_l n p q).
  Rewrite (plus_sym n p). Rewrite <- (plus_assoc_l p n q). Apply plus_assoc_l.
Qed.

(** Tail-recursive plus *)

(** [tail_plus] is an alternative definition for [plus] which is 
    tail-recursive, whereas [plus] is not. This can be useful
    when extracting programs. *)

Fixpoint plus_acc [q,n:nat] : nat := 
   Cases n of 
      O => q
      | (S p) => (plus_acc (S q) p)
    end.

Definition tail_plus := [n,m:nat](plus_acc m n).

Lemma plus_tail_plus : (n,m:nat)(n+m)=(tail_plus n m).
Unfold tail_plus; NewInduction n as [|n IHn]; Simpl; Auto.
Intro m; Rewrite <- IHn; Simpl; Auto.
Qed.

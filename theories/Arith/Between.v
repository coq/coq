(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Le.
Require Import Lt.

Local Open Scope nat_scope.

Implicit Types k l p q r : nat.

Section Between.
  Variables P Q : nat -> Prop.

  Inductive between k : nat -> Prop :=
    | bet_emp : between k k
    | bet_S : forall l, between k l -> P l -> between k (S l).

  Hint Constructors between: arith v62.

  Lemma bet_eq : forall k l, l = k -> between k l.
  Proof.
    induction 1; auto with arith.
  Qed.

  Hint Resolve bet_eq: arith v62.

  Lemma between_le : forall k l, between k l -> k <= l.
  Proof.
    induction 1; auto with arith.
  Qed.
  Hint Immediate between_le: arith v62.

  Lemma between_Sk_l : forall k l, between k l -> S k <= l -> between (S k) l.
  Proof.
    intros k l H; induction H as [|l H].
    intros; absurd (S k <= k); auto with arith.
    destruct H; auto with arith.
  Qed.
  Hint Resolve between_Sk_l: arith v62.

  Lemma between_restr :
    forall k l (m:nat), k <= l -> l <= m -> between k m -> between l m.
  Proof.
    induction 1; auto with arith.
  Qed.

  Inductive exists_between k : nat -> Prop :=
    | exists_S : forall l, exists_between k l -> exists_between k (S l)
    | exists_le : forall l, k <= l -> Q l -> exists_between k (S l).

  Hint Constructors exists_between: arith v62.

  Lemma exists_le_S : forall k l, exists_between k l -> S k <= l.
  Proof.
    induction 1; auto with arith.
  Qed.

  Lemma exists_lt : forall k l, exists_between k l -> k < l.
  Proof exists_le_S.
  Hint Immediate exists_le_S exists_lt: arith v62.

  Lemma exists_S_le : forall k l, exists_between k (S l) -> k <= l.
  Proof.
    intros; apply le_S_n; auto with arith.
  Qed.
  Hint Immediate exists_S_le: arith v62.

  Definition in_int p q r := p <= r /\ r < q.

  Lemma in_int_intro : forall p q r, p <= r -> r < q -> in_int p q r.
  Proof.
    red; auto with arith.
  Qed.
  Hint Resolve in_int_intro: arith v62.

  Lemma in_int_lt : forall p q r, in_int p q r -> p < q.
  Proof.
    induction 1; intros.
    apply le_lt_trans with r; auto with arith.
  Qed.

  Lemma in_int_p_Sq :
    forall p q r, in_int p (S q) r -> in_int p q r \/ r = q :>nat.
  Proof.
    induction 1; intros.
    elim (le_lt_or_eq r q); auto with arith.
  Qed.

  Lemma in_int_S : forall p q r, in_int p q r -> in_int p (S q) r.
  Proof.
    induction 1; auto with arith.
  Qed.
  Hint Resolve in_int_S: arith v62.

  Lemma in_int_Sp_q : forall p q r, in_int (S p) q r -> in_int p q r.
  Proof.
    induction 1; auto with arith.
  Qed.
  Hint Immediate in_int_Sp_q: arith v62.

  Lemma between_in_int :
    forall k l, between k l -> forall r, in_int k l r -> P r.
  Proof.
    induction 1; intros.
    absurd (k < k); auto with arith.
    apply in_int_lt with r; auto with arith.
    elim (in_int_p_Sq k l r); intros; auto with arith.
    rewrite H2; trivial with arith.
  Qed.

  Lemma in_int_between :
    forall k l, k <= l -> (forall r, in_int k l r -> P r) -> between k l.
  Proof.
    induction 1; auto with arith.
  Qed.

  Lemma exists_in_int :
    forall k l, exists_between k l ->  exists2 m : nat, in_int k l m & Q m.
  Proof.
    induction 1.
    case IHexists_between; intros p inp Qp; exists p; auto with arith.
    exists l; auto with arith.
  Qed.

  Lemma in_int_exists : forall k l r, in_int k l r -> Q r -> exists_between k l.
  Proof.
    destruct 1; intros.
    elim H0; auto with arith.
  Qed.

  Lemma between_or_exists :
    forall k l,
      k <= l ->
      (forall n:nat, in_int k l n -> P n \/ Q n) ->
      between k l \/ exists_between k l.
  Proof.
    induction 1; intros; auto with arith.
    elim IHle; intro; auto with arith.
    elim (H0 m); auto with arith.
  Qed.

  Lemma between_not_exists :
    forall k l,
      between k l ->
      (forall n:nat, in_int k l n -> P n -> ~ Q n) -> ~ exists_between k l.
  Proof.
    induction 1; red; intros.
    absurd (k < k); auto with arith.
    absurd (Q l); auto with arith.
    elim (exists_in_int k (S l)); auto with arith; intros l' inl' Ql'.
    replace l with l'; auto with arith.
    elim inl'; intros.
    elim (le_lt_or_eq l' l); auto with arith; intros.
    absurd (exists_between k l); auto with arith.
    apply in_int_exists with l'; auto with arith.
  Qed.

  Inductive P_nth (init:nat) : nat -> nat -> Prop :=
    | nth_O : P_nth init init 0
    | nth_S :
      forall k l (n:nat),
	P_nth init k n -> between (S k) l -> Q l -> P_nth init l (S n).

  Lemma nth_le : forall (init:nat) l (n:nat), P_nth init l n -> init <= l.
  Proof.
    induction 1; intros; auto with arith.
    apply le_trans with (S k); auto with arith.
  Qed.

  Definition eventually (n:nat) :=  exists2 k : nat, k <= n & Q k.

  Lemma event_O : eventually 0 -> Q 0.
  Proof.
    induction 1; intros.
    replace 0 with x; auto with arith.
  Qed.

End Between.

Hint Resolve nth_O bet_S bet_emp bet_eq between_Sk_l exists_S exists_le
  in_int_S in_int_intro: arith v62.
Hint Immediate in_int_Sp_q exists_le_S exists_S_le: arith v62.

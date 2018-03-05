(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Le.
Require Import Lt.

Local Open Scope nat_scope.

Implicit Types k l p q r : nat.

Section Between.
  Variables P Q : nat -> Prop.

  (** The [between] type expresses the concept
      [forall i: nat, k <= i < l -> P i.]. *)
  Inductive between k : nat -> Prop :=
    | bet_emp : between k k
    | bet_S : forall l, between k l -> P l -> between k (S l).

  Hint Constructors between: arith.

  Lemma bet_eq : forall k l, l = k -> between k l.
  Proof.
    intros * ->; auto with arith.
  Qed.

  Hint Resolve bet_eq: arith.

  Lemma between_le : forall k l, between k l -> k <= l.
  Proof.
    induction 1; auto with arith.
  Qed.
  Hint Immediate between_le: arith.

  Lemma between_Sk_l : forall k l, between k l -> S k <= l -> between (S k) l.
  Proof.
    induction 1 as [|* [|]]; auto with arith.
  Qed.
  Hint Resolve between_Sk_l: arith.

  Lemma between_restr :
    forall k l (m:nat), k <= l -> l <= m -> between k m -> between l m.
  Proof.
    induction 1; auto with arith.
  Qed.

  (** The [exists_between] type expresses the concept
      [exists i: nat, k <= i < l /\ Q i]. *)
  Inductive exists_between k : nat -> Prop :=
    | exists_S : forall l, exists_between k l -> exists_between k (S l)
    | exists_le : forall l, k <= l -> Q l -> exists_between k (S l).

  Hint Constructors exists_between: arith.

  Lemma exists_le_S : forall k l, exists_between k l -> S k <= l.
  Proof.
    induction 1; auto with arith.
  Qed.

  Lemma exists_lt : forall k l, exists_between k l -> k < l.
  Proof exists_le_S.
  Hint Immediate exists_le_S exists_lt: arith.

  Lemma exists_S_le : forall k l, exists_between k (S l) -> k <= l.
  Proof.
    intros; apply le_S_n; auto with arith.
  Qed.
  Hint Immediate exists_S_le: arith.

  Definition in_int p q r := p <= r /\ r < q.

  Lemma in_int_intro : forall p q r, p <= r -> r < q -> in_int p q r.
  Proof.
    split; assumption.
  Qed.
  Hint Resolve in_int_intro: arith.

  Lemma in_int_lt : forall p q r, in_int p q r -> p < q.
  Proof.
    intros * [].
    eapply le_lt_trans; eassumption.
  Qed.

  Lemma in_int_p_Sq :
    forall p q r, in_int p (S q) r -> in_int p q r \/ r = q.
  Proof.
    intros p q r [].
    destruct (le_lt_or_eq r q); auto with arith.
  Qed.

  Lemma in_int_S : forall p q r, in_int p q r -> in_int p (S q) r.
  Proof.
    intros * []; auto with arith.
  Qed.
  Hint Resolve in_int_S: arith.

  Lemma in_int_Sp_q : forall p q r, in_int (S p) q r -> in_int p q r.
  Proof.
    intros * []; auto with arith.
  Qed.
  Hint Immediate in_int_Sp_q: arith.

  Lemma between_in_int :
    forall k l, between k l -> forall r, in_int k l r -> P r.
  Proof.
    induction 1; intros.
    - absurd (k < k). { auto with arith. }
      eapply in_int_lt; eassumption.
    - destruct (in_int_p_Sq k l r) as [| ->]; auto with arith.
  Qed.

  Lemma in_int_between :
    forall k l, k <= l -> (forall r, in_int k l r -> P r) -> between k l.
  Proof.
    induction 1; auto with arith.
  Qed.

  Lemma exists_in_int :
    forall k l, exists_between k l -> exists2 m : nat, in_int k l m & Q m.
  Proof.
    induction 1 as [* ? (p, ?, ?)|].
    - exists p; auto with arith.
    - exists l; auto with arith.
  Qed.

  Lemma in_int_exists : forall k l r, in_int k l r -> Q r -> exists_between k l.
  Proof.
    intros * (?, lt_r_l) ?.
    induction lt_r_l; auto with arith.
  Qed.

  Lemma between_or_exists :
    forall k l,
      k <= l ->
      (forall n:nat, in_int k l n -> P n \/ Q n) ->
      between k l \/ exists_between k l.
  Proof.
    induction 1 as [|m ? IHle].
    - auto with arith.
    - intros P_or_Q.
      destruct IHle; auto with arith.
      destruct (P_or_Q m); auto with arith.
  Qed.

  Lemma between_not_exists :
    forall k l,
      between k l ->
      (forall n:nat, in_int k l n -> P n -> ~ Q n) -> ~ exists_between k l.
  Proof.
    induction 1; red; intros.
    - absurd (k < k); auto with arith.
    - absurd (Q l). { auto with arith. }
      destruct (exists_in_int k (S l)) as (l',[],?).
      + auto with arith.
      + replace l with l'. { trivial. }
        destruct (le_lt_or_eq l' l); auto with arith.
        absurd (exists_between k l). { auto with arith. }
        eapply in_int_exists; eauto with arith.
  Qed.

  Inductive P_nth (init:nat) : nat -> nat -> Prop :=
    | nth_O : P_nth init init 0
    | nth_S :
      forall k l (n:nat),
	P_nth init k n -> between (S k) l -> Q l -> P_nth init l (S n).

  Lemma nth_le : forall (init:nat) l (n:nat), P_nth init l n -> init <= l.
  Proof.
    induction 1.
    - auto with arith.
    - eapply le_trans; eauto with arith.
  Qed.

  Definition eventually (n:nat) :=  exists2 k : nat, k <= n & Q k.

  Lemma event_O : eventually 0 -> Q 0.
  Proof.
    intros (x, ?, ?).
    replace 0 with x; auto with arith.
  Qed.

End Between.

Hint Resolve nth_O bet_S bet_emp bet_eq between_Sk_l exists_S exists_le
  in_int_S in_int_intro: arith.
Hint Immediate in_int_Sp_q exists_le_S exists_S_le: arith.

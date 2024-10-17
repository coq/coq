(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PeanoNat.

Local Open Scope nat_scope.

Implicit Types k l p q r : nat.

Section Between.
  Variables P Q : nat -> Prop.

  (** The [between] type expresses the concept
      [forall i: nat, k <= i < l -> P i.]. *)
  Inductive between k : nat -> Prop :=
    | bet_emp : between k k
    | bet_S : forall l, between k l -> P l -> between k (S l).

  #[local]
  Hint Constructors between: core.

  Lemma bet_eq : forall k l, l = k -> between k l.
  Proof.
    intros * ->; constructor.
  Qed.

  #[local]
  Hint Resolve bet_eq: core.

  Lemma between_le : forall k l, between k l -> k <= l.
  Proof.
    induction 1; auto.
  Qed.
  #[local]
  Hint Immediate between_le: core.

  Lemma between_Sk_l : forall k l, between k l -> S k <= l -> between (S k) l.
  Proof.
    induction 1 as [|* [|]]; auto.
    - intros Hle; exfalso; apply (Nat.nle_succ_diag_l _ Hle).
    - intros Hle; inversion Hle; constructor; auto.
  Qed.
  #[local]
  Hint Resolve between_Sk_l: core.

  Lemma between_restr :
    forall k l (m:nat), k <= l -> l <= m -> between k m -> between l m.
  Proof.
    induction 1; auto.
    intros; auto.
    apply between_Sk_l; auto.
    apply IHle; auto.
    transitivity (S m0); auto.
  Qed.

  (** The [exists_between] type expresses the concept
      [exists i: nat, k <= i < l /\ Q i]. *)
  Inductive exists_between k : nat -> Prop :=
    | exists_S : forall l, exists_between k l -> exists_between k (S l)
    | exists_le : forall l, k <= l -> Q l -> exists_between k (S l).

  #[local]
  Hint Constructors exists_between: core.

  Lemma exists_le_S : forall k l, exists_between k l -> S k <= l.
  Proof.
    induction 1; auto.
    apply -> Nat.succ_le_mono; assumption.
  Qed.

  Lemma exists_lt : forall k l, exists_between k l -> k < l.
  Proof exists_le_S.
  #[local]
  Hint Immediate exists_le_S exists_lt: core.

  Lemma exists_S_le : forall k l, exists_between k (S l) -> k <= l.
  Proof.
    intros; apply le_S_n; auto.
  Qed.
  #[local]
  Hint Immediate exists_S_le: core.

  Definition in_int p q r := p <= r /\ r < q.

  Lemma in_int_intro : forall p q r, p <= r -> r < q -> in_int p q r.
  Proof.
    split; assumption.
  Qed.
  #[local]
  Hint Resolve in_int_intro: core.

  Lemma in_int_lt : forall p q r, in_int p q r -> p < q.
  Proof.
    intros * [].
    eapply Nat.le_lt_trans; eassumption.
  Qed.

  Lemma in_int_p_Sq :
    forall p q r, in_int p (S q) r -> in_int p q r \/ r = q.
  Proof.
    intros p q r [].
    destruct (proj1 (Nat.lt_eq_cases r q)); auto.
    apply Nat.lt_succ_r; assumption.
  Qed.

  Lemma in_int_S : forall p q r, in_int p q r -> in_int p (S q) r.
  Proof.
    intros * []; auto.
  Qed.
  #[local]
  Hint Resolve in_int_S: core.

  Lemma in_int_Sp_q : forall p q r, in_int (S p) q r -> in_int p q r.
  Proof.
    intros * []; auto.
    apply in_int_intro; auto.
    transitivity (S p); auto.
  Qed.
  #[local]
  Hint Immediate in_int_Sp_q: core.

  Lemma between_in_int :
    forall k l, between k l -> forall r, in_int k l r -> P r.
  Proof.
    intro k; induction 1 as [|l]; intros r ?.
    - absurd (k < k). { apply Nat.lt_irrefl. }
      eapply in_int_lt; eassumption.
    - destruct (in_int_p_Sq k l r) as [| ->]; auto.
  Qed.

  Lemma in_int_between :
    forall k l, k <= l -> (forall r, in_int k l r -> P r) -> between k l.
  Proof.
    induction 1; auto.
  Qed.

  Lemma exists_in_int :
    forall k l, exists_between k l -> exists2 m : nat, in_int k l m & Q m.
  Proof.
    induction 1 as [* ? (p, ?, ?)|l].
    - exists p; auto.
    - exists l; auto.
  Qed.

  Lemma in_int_exists : forall k l r, in_int k l r -> Q r -> exists_between k l.
  Proof.
    intros * (?, lt_r_l) ?.
    induction lt_r_l; auto.
  Qed.

  Lemma between_or_exists :
    forall k l,
      k <= l ->
      (forall n:nat, in_int k l n -> P n \/ Q n) ->
      between k l \/ exists_between k l.
  Proof.
    induction 1 as [|m ? IHle].
    - auto.
    - intros P_or_Q.
      destruct IHle; auto.
      destruct (P_or_Q m); auto.
  Qed.

  Lemma between_not_exists :
    forall k l,
      between k l ->
      (forall n:nat, in_int k l n -> P n -> ~ Q n) -> ~ exists_between k l.
  Proof.
    intro k; induction 1 as [|l]; red; intros.
    - absurd (k < k). { apply Nat.lt_irrefl. } auto.
    - absurd (Q l). { auto. }
      destruct (exists_in_int k (S l)) as (l',[],?).
      + auto.
      + replace l with l'. { trivial. }
        destruct (proj1 (Nat.lt_eq_cases l' l)); auto.
        * apply Nat.lt_succ_r; assumption.
        * absurd (exists_between k l). { auto. }
          apply in_int_exists with l'; auto.
  Qed.

  Inductive P_nth (init:nat) : nat -> nat -> Prop :=
    | nth_O : P_nth init init 0
    | nth_S :
      forall k l (n:nat),
        P_nth init k n -> between (S k) l -> Q l -> P_nth init l (S n).

  Lemma nth_le : forall (init:nat) l (n:nat), P_nth init l n -> init <= l.
  Proof.
    induction 1 as [|a b c H0 H1 H2 H3].
    - auto.
    - eapply Nat.le_trans; eauto.
      apply between_le in H2.
      transitivity (S a); auto.
  Qed.

  Definition eventually (n:nat) :=  exists2 k : nat, k <= n & Q k.

  Lemma event_O : eventually 0 -> Q 0.
  Proof.
    intros (x, ?, ?).
    replace 0 with x; auto.
    apply Nat.le_0_r; assumption.
  Qed.

End Between.

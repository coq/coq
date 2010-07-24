(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import BinPos.

(**********************************************************************)
(** Properties of the injection from binary positive numbers to Peano
    natural numbers *)

(** Original development by Pierre Crégut, CNET, Lannion, France *)

Require Import Le.
Require Import Lt.
Require Import Gt.
Require Import Plus.
Require Import Mult.
Require Import Minus.
Require Import Compare_dec.

Local Open Scope positive_scope.
Local Open Scope nat_scope.

(** [nat_of_P] is a morphism for addition *)

Lemma Pmult_nat_succ_morphism :
 forall (p:positive) (n:nat), Pmult_nat (Psucc p) n = n + Pmult_nat p n.
Proof.
intro x; induction x as [p IHp| p IHp| ]; simpl in |- *; auto; intro m;
 rewrite IHp; rewrite plus_assoc; trivial.
Qed.

Lemma nat_of_P_succ_morphism :
 forall p:positive, nat_of_P (Psucc p) = S (nat_of_P p).
Proof.
  intro; change (S (nat_of_P p)) with (1 + nat_of_P p) in |- *;
   unfold nat_of_P in |- *; apply Pmult_nat_succ_morphism.
Qed.

Theorem Pmult_nat_plus_carry_morphism :
 forall (p q:positive) (n:nat),
   Pmult_nat (Pplus_carry p q) n = n + Pmult_nat (p + q) n.
Proof.
intro x; induction x as [p IHp| p IHp| ]; intro y;
 [ destruct y as [p0| p0| ]
 | destruct y as [p0| p0| ]
 | destruct y as [p| p| ] ]; simpl in |- *; auto with arith;
 intro m;
 [ rewrite IHp; rewrite plus_assoc; trivial with arith
 | rewrite IHp; rewrite plus_assoc; trivial with arith
 | rewrite Pmult_nat_succ_morphism; rewrite plus_assoc; trivial with arith
 | rewrite Pmult_nat_succ_morphism; apply plus_assoc_reverse ].
Qed.

Theorem nat_of_P_plus_carry_morphism :
 forall p q:positive, nat_of_P (Pplus_carry p q) = S (nat_of_P (p + q)).
Proof.
intros; unfold nat_of_P in |- *; rewrite Pmult_nat_plus_carry_morphism;
 simpl in |- *; trivial with arith.
Qed.

Theorem Pmult_nat_l_plus_morphism :
 forall (p q:positive) (n:nat),
   Pmult_nat (p + q) n = Pmult_nat p n + Pmult_nat q n.
Proof.
intro x; induction x as [p IHp| p IHp| ]; intro y;
 [ destruct y as [p0| p0| ]
 | destruct y as [p0| p0| ]
 | destruct y as [p| p| ] ]; simpl in |- *; auto with arith;
 [ intros m; rewrite Pmult_nat_plus_carry_morphism; rewrite IHp;
    rewrite plus_assoc_reverse; rewrite plus_assoc_reverse;
    rewrite (plus_permute m (Pmult_nat p (m + m)));
    trivial with arith
 | intros m; rewrite IHp; apply plus_assoc
 | intros m; rewrite Pmult_nat_succ_morphism;
    rewrite (plus_comm (m + Pmult_nat p (m + m)));
    apply plus_assoc_reverse
 | intros m; rewrite IHp; apply plus_permute
 | intros m; rewrite Pmult_nat_succ_morphism; apply plus_assoc_reverse ].
Qed.

Theorem nat_of_P_plus_morphism :
 forall p q:positive, nat_of_P (p + q) = nat_of_P p + nat_of_P q.
Proof.
intros x y; exact (Pmult_nat_l_plus_morphism x y 1).
Qed.

(** [Pmult_nat] is a morphism for addition *)

Lemma Pmult_nat_r_plus_morphism :
 forall (p:positive) (n:nat),
   Pmult_nat p (n + n) = Pmult_nat p n + Pmult_nat p n.
Proof.
intro y; induction y as [p H| p H| ]; intro m;
 [ simpl in |- *; rewrite H; rewrite plus_assoc_reverse;
    rewrite (plus_permute m (Pmult_nat p (m + m)));
    rewrite plus_assoc_reverse; auto with arith
 | simpl in |- *; rewrite H; auto with arith
 | simpl in |- *; trivial with arith ].
Qed.

Lemma ZL6 : forall p:positive, Pmult_nat p 2 = nat_of_P p + nat_of_P p.
Proof.
intro p; change 2 with (1 + 1) in |- *; rewrite Pmult_nat_r_plus_morphism;
 trivial.
Qed.

(** [nat_of_P] is a morphism for multiplication *)

Theorem nat_of_P_mult_morphism :
 forall p q:positive, nat_of_P (p * q) = nat_of_P p * nat_of_P q.
Proof.
intros x y; induction x as [x' H| x' H| ];
 [ change (xI x' * y)%positive with (y + xO (x' * y))%positive in |- *;
    rewrite nat_of_P_plus_morphism; unfold nat_of_P at 2 3 in |- *;
    simpl in |- *; do 2 rewrite ZL6; rewrite H; rewrite mult_plus_distr_r;
    reflexivity
 | unfold nat_of_P at 1 2 in |- *; simpl in |- *; do 2 rewrite ZL6; rewrite H;
    rewrite mult_plus_distr_r; reflexivity
 | simpl in |- *; rewrite <- plus_n_O; reflexivity ].
Qed.

(** [nat_of_P] maps to the strictly positive subset of [nat] *)

Lemma ZL4 : forall p:positive,  exists h : nat, nat_of_P p = S h.
Proof.
intro y; induction y as [p H| p H| ];
 [ destruct H as [x H1]; exists (S x + S x); unfold nat_of_P in |- *;
    simpl in |- *; change 2 with (1 + 1) in |- *;
    rewrite Pmult_nat_r_plus_morphism; unfold nat_of_P in H1;
    rewrite H1; auto with arith
 | destruct H as [x H2]; exists (x + S x); unfold nat_of_P in |- *;
    simpl in |- *; change 2 with (1 + 1) in |- *;
    rewrite Pmult_nat_r_plus_morphism; unfold nat_of_P in H2;
    rewrite H2; auto with arith
 | exists 0; auto with arith ].
Qed.

(** Extra lemmas on [lt] on Peano natural numbers *)

Lemma ZL7 : forall n m:nat, n < m -> n + n < m + m.
Proof.
intros m n H; apply lt_trans with (m := m + n);
 [ apply plus_lt_compat_l with (1 := H)
 | rewrite (plus_comm m n); apply plus_lt_compat_l with (1 := H) ].
Qed.

Lemma ZL8 : forall n m:nat, n < m -> S (n + n) < m + m.
Proof.
intros m n H; apply le_lt_trans with (m := m + n);
 [ change (m + m < m + n) in |- *; apply plus_lt_compat_l with (1 := H)
 | rewrite (plus_comm m n); apply plus_lt_compat_l with (1 := H) ].
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [lt] (expressed
    from [compare] on [positive])

    Part 1: [lt] on [positive] is finer than [lt] on [nat]
*)

Lemma nat_of_P_lt_Lt_compare_morphism :
 forall p q:positive, (p ?= q) Eq = Lt -> nat_of_P p < nat_of_P q.
Proof.
intro x; induction x as [p H| p H| ]; intro y; destruct y as [q| q| ];
 intro H2;
 [ unfold nat_of_P in |- *; simpl in |- *; apply lt_n_S; do 2 rewrite ZL6;
    apply ZL7; apply H; simpl in H2; assumption
 | unfold nat_of_P in |- *; simpl in |- *; do 2 rewrite ZL6; apply ZL8;
    apply H; simpl in H2; apply Pcompare_Gt_Lt; assumption
 | simpl in |- *; discriminate H2
 | simpl in |- *; unfold nat_of_P in |- *; simpl in |- *; do 2 rewrite ZL6;
    elim (Pcompare_Lt_Lt p q H2);
    [ intros H3; apply lt_S; apply ZL7; apply H; apply H3
    | intros E; rewrite E; apply lt_n_Sn ]
 | simpl in |- *; unfold nat_of_P in |- *; simpl in |- *; do 2 rewrite ZL6;
    apply ZL7; apply H; assumption
 | simpl in |- *; discriminate H2
 | unfold nat_of_P in |- *; simpl in |- *; apply lt_n_S; rewrite ZL6;
    elim (ZL4 q); intros h H3; rewrite H3; simpl in |- *;
    apply lt_O_Sn
 | unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6; elim (ZL4 q);
    intros h H3; rewrite H3; simpl in |- *; rewrite <- plus_n_Sm;
    apply lt_n_S; apply lt_O_Sn
 | simpl in |- *; discriminate H2 ].
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [gt] (expressed
    from [compare] on [positive])

    Part 1: [gt] on [positive] is finer than [gt] on [nat]
*)

Lemma nat_of_P_gt_Gt_compare_morphism :
 forall p q:positive, (p ?= q) Eq = Gt -> nat_of_P p > nat_of_P q.
Proof.
intros p q GT. unfold gt.
apply nat_of_P_lt_Lt_compare_morphism.
change ((q ?= p) (CompOpp Eq) = CompOpp Gt).
rewrite <- Pcompare_antisym, GT; auto.
Qed.

(** [nat_of_P] is a morphism for [Pcompare] and [nat_compare] *)

Lemma nat_of_P_compare_morphism : forall p q,
 (p ?= q) Eq = nat_compare (nat_of_P p) (nat_of_P q).
Proof.
 intros p q; symmetry.
 destruct ((p ?= q) Eq) as [ | | ]_eqn.
 rewrite (Pcompare_Eq_eq p q); auto.
 apply <- nat_compare_eq_iff; auto.
 apply -> nat_compare_lt. apply nat_of_P_lt_Lt_compare_morphism; auto.
 apply -> nat_compare_gt. apply nat_of_P_gt_Gt_compare_morphism; auto.
Qed.

(** [nat_of_P] is hence injective. *)

Lemma nat_of_P_inj : forall p q:positive, nat_of_P p = nat_of_P q -> p = q.
Proof.
intros.
apply Pcompare_Eq_eq.
rewrite nat_of_P_compare_morphism.
apply <- nat_compare_eq_iff; auto.
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [lt] (expressed
    from [compare] on [positive])

    Part 2: [lt] on [nat] is finer than [lt] on [positive]
*)

Lemma nat_of_P_lt_Lt_compare_complement_morphism :
 forall p q:positive, nat_of_P p < nat_of_P q -> (p ?= q) Eq = Lt.
Proof.
 intros. rewrite nat_of_P_compare_morphism.
 apply -> nat_compare_lt; auto.
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [gt] (expressed
    from [compare] on [positive])

    Part 2: [gt] on [nat] is finer than [gt] on [positive]
*)

Lemma nat_of_P_gt_Gt_compare_complement_morphism :
 forall p q:positive, nat_of_P p > nat_of_P q -> (p ?= q) Eq = Gt.
Proof.
 intros. rewrite nat_of_P_compare_morphism.
 apply -> nat_compare_gt; auto.
Qed.


(** [nat_of_P] is strictly positive *)

Lemma le_Pmult_nat : forall (p:positive) (n:nat), n <= Pmult_nat p n.
induction p; simpl in |- *; auto with arith.
intro m; apply le_trans with (m + m); auto with arith.
Qed.

Lemma lt_O_nat_of_P : forall p:positive, 0 < nat_of_P p.
intro; unfold nat_of_P in |- *; apply lt_le_trans with 1; auto with arith.
apply le_Pmult_nat.
Qed.

(** Pmult_nat permutes with multiplication *)

Lemma Pmult_nat_mult_permute :
 forall (p:positive) (n m:nat), Pmult_nat p (m * n) = m * Pmult_nat p n.
Proof.
  simple induction p. intros. simpl in |- *. rewrite mult_plus_distr_l. rewrite <- (mult_plus_distr_l m n n).
  rewrite (H (n + n) m). reflexivity.
  intros. simpl in |- *. rewrite <- (mult_plus_distr_l m n n). apply H.
  trivial.
Qed.

Lemma Pmult_nat_2_mult_2_permute :
 forall p:positive, Pmult_nat p 2 = 2 * Pmult_nat p 1.
Proof.
  intros. rewrite <- Pmult_nat_mult_permute. reflexivity.
Qed.

Lemma Pmult_nat_4_mult_2_permute :
 forall p:positive, Pmult_nat p 4 = 2 * Pmult_nat p 2.
Proof.
  intros. rewrite <- Pmult_nat_mult_permute. reflexivity.
Qed.

(** Mapping of xH, xO and xI through [nat_of_P] *)

Lemma nat_of_P_xH : nat_of_P 1 = 1.
Proof.
  reflexivity.
Qed.

Lemma nat_of_P_xO : forall p:positive, nat_of_P (xO p) = 2 * nat_of_P p.
Proof.
  intros.
  change 2 with (nat_of_P 2).
  rewrite <- nat_of_P_mult_morphism.
  f_equal.
Qed.

Lemma nat_of_P_xI : forall p:positive, nat_of_P (xI p) = S (2 * nat_of_P p).
Proof.
  intros.
  change 2 with (nat_of_P 2).
  rewrite <- nat_of_P_mult_morphism, <- nat_of_P_succ_morphism.
  f_equal.
Qed.

(**********************************************************************)
(** Properties of the shifted injection from Peano natural numbers to
    binary positive numbers *)

(** Composition of [P_of_succ_nat] and [nat_of_P] is successor on [nat] *)

Theorem nat_of_P_o_P_of_succ_nat_eq_succ :
 forall n:nat, nat_of_P (P_of_succ_nat n) = S n.
Proof.
induction n as [|n H].
reflexivity.
simpl; rewrite nat_of_P_succ_morphism, H; auto.
Qed.

(** Miscellaneous lemmas on [P_of_succ_nat] *)

Lemma ZL3 :
 forall n:nat, Psucc (P_of_succ_nat (n + n)) = xO (P_of_succ_nat n).
Proof.
induction n as [| n H]; simpl;
 [ auto with arith
 | rewrite plus_comm; simpl; rewrite H;
    rewrite xO_succ_permute; auto with arith ].
Qed.

Lemma ZL5 : forall n:nat, P_of_succ_nat (S n + S n) = xI (P_of_succ_nat n).
Proof.
induction n as [| n H]; simpl;
 [ auto with arith
 | rewrite <- plus_n_Sm; simpl; simpl in H; rewrite H;
    auto with arith ].
Qed.

(** Composition of [nat_of_P] and [P_of_succ_nat] is successor on [positive] *)

Theorem P_of_succ_nat_o_nat_of_P_eq_succ :
 forall p:positive, P_of_succ_nat (nat_of_P p) = Psucc p.
Proof.
intros.
apply nat_of_P_inj.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ, nat_of_P_succ_morphism; auto.
Qed.

(** Composition of [nat_of_P], [P_of_succ_nat] and [Ppred] is identity
    on [positive] *)

Theorem pred_o_P_of_succ_nat_o_nat_of_P_eq_id :
 forall p:positive, Ppred (P_of_succ_nat (nat_of_P p)) = p.
Proof.
intros; rewrite P_of_succ_nat_o_nat_of_P_eq_succ, Ppred_succ; auto.
Qed.

(**********************************************************************)
(** Extra properties of the injection from binary positive numbers to Peano
    natural numbers *)

(** [nat_of_P] is a morphism for subtraction on positive numbers *)

Theorem nat_of_P_minus_morphism :
 forall p q:positive,
   (p ?= q) Eq = Gt -> nat_of_P (p - q) = nat_of_P p - nat_of_P q.
Proof.
intros x y H; apply plus_reg_l with (nat_of_P y); rewrite le_plus_minus_r;
 [ rewrite <- nat_of_P_plus_morphism; rewrite Pplus_minus; auto with arith
 | apply lt_le_weak; exact (nat_of_P_gt_Gt_compare_morphism x y H) ].
Qed.


Lemma ZL16 : forall p q:positive, nat_of_P p - nat_of_P q < nat_of_P p.
Proof.
intros p q; elim (ZL4 p); elim (ZL4 q); intros h H1 i H2; rewrite H1;
 rewrite H2; simpl in |- *; unfold lt in |- *; apply le_n_S;
 apply le_minus.
Qed.

Lemma ZL17 : forall p q:positive, nat_of_P p < nat_of_P (p + q).
Proof.
intros p q; rewrite nat_of_P_plus_morphism; unfold lt in |- *; elim (ZL4 q);
 intros k H; rewrite H; rewrite plus_comm; simpl in |- *;
 apply le_n_S; apply le_plus_r.
Qed.

(** Comparison and subtraction *)

Lemma Pcompare_minus_r :
 forall p q r:positive,
   (q ?= p) Eq = Lt ->
   (r ?= p) Eq = Gt ->
   (r ?= q) Eq = Gt -> (r - p ?= r - q) Eq = Lt.
Proof.
intros; apply nat_of_P_lt_Lt_compare_complement_morphism;
 rewrite nat_of_P_minus_morphism;
 [ rewrite nat_of_P_minus_morphism;
    [ apply plus_lt_reg_l with (p := nat_of_P q); rewrite le_plus_minus_r;
       [ rewrite plus_comm; apply plus_lt_reg_l with (p := nat_of_P p);
          rewrite plus_assoc; rewrite le_plus_minus_r;
          [ rewrite (plus_comm (nat_of_P p)); apply plus_lt_compat_l;
             apply nat_of_P_lt_Lt_compare_morphism;
             assumption
          | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism;
             apply ZC1; assumption ]
       | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism; apply ZC1;
          assumption ]
    | assumption ]
 | assumption ].
Qed.

Lemma Pcompare_minus_l :
 forall p q r:positive,
   (q ?= p) Eq = Lt ->
   (p ?= r) Eq = Gt ->
   (q ?= r) Eq = Gt -> (q - r ?= p - r) Eq = Lt.
Proof.
intros p q z; intros; apply nat_of_P_lt_Lt_compare_complement_morphism;
 rewrite nat_of_P_minus_morphism;
 [ rewrite nat_of_P_minus_morphism;
    [ unfold gt in |- *; apply plus_lt_reg_l with (p := nat_of_P z);
       rewrite le_plus_minus_r;
       [ rewrite le_plus_minus_r;
          [ apply nat_of_P_lt_Lt_compare_morphism; assumption
          | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism;
             apply ZC1; assumption ]
       | apply lt_le_weak; apply nat_of_P_lt_Lt_compare_morphism; apply ZC1;
          assumption ]
    | assumption ]
 | assumption ].
Qed.

(** Distributivity of multiplication over subtraction *)

Theorem Pmult_minus_distr_l :
 forall p q r:positive,
   (q ?= r) Eq = Gt ->
   (p * (q - r) = p * q - p * r)%positive.
Proof.
intros x y z H; apply nat_of_P_inj; rewrite nat_of_P_mult_morphism;
 rewrite nat_of_P_minus_morphism;
 [ rewrite nat_of_P_minus_morphism;
    [ do 2 rewrite nat_of_P_mult_morphism;
       do 3 rewrite (mult_comm (nat_of_P x)); apply mult_minus_distr_r
    | apply nat_of_P_gt_Gt_compare_complement_morphism;
       do 2 rewrite nat_of_P_mult_morphism; unfold gt in |- *;
       elim (ZL4 x); intros h H1; rewrite H1; apply mult_S_lt_compat_l;
       exact (nat_of_P_gt_Gt_compare_morphism y z H) ]
 | assumption ].
Qed.

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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
 forall p q:positive, (p ?= q)%positive Eq = Lt -> nat_of_P p < nat_of_P q.
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
 forall p q:positive, (p ?= q)%positive Eq = Gt -> nat_of_P p > nat_of_P q.
Proof.
unfold gt in |- *; intro x; induction x as [p H| p H| ]; intro y;
 destruct y as [q| q| ]; intro H2;
 [ simpl in |- *; unfold nat_of_P in |- *; simpl in |- *; do 2 rewrite ZL6;
    apply lt_n_S; apply ZL7; apply H; assumption
 | simpl in |- *; unfold nat_of_P in |- *; simpl in |- *; do 2 rewrite ZL6;
    elim (Pcompare_Gt_Gt p q H2);
    [ intros H3; apply lt_S; apply ZL7; apply H; assumption
    | intros E; rewrite E; apply lt_n_Sn ]
 | unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6; elim (ZL4 p);
    intros h H3; rewrite H3; simpl in |- *; apply lt_n_S; 
    apply lt_O_Sn
 | simpl in |- *; unfold nat_of_P in |- *; simpl in |- *; do 2 rewrite ZL6;
    apply ZL8; apply H; apply Pcompare_Lt_Gt; assumption
 | simpl in |- *; unfold nat_of_P in |- *; simpl in |- *; do 2 rewrite ZL6;
    apply ZL7; apply H; assumption
 | unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6; elim (ZL4 p);
    intros h H3; rewrite H3; simpl in |- *; rewrite <- plus_n_Sm;
    apply lt_n_S; apply lt_O_Sn
 | simpl in |- *; discriminate H2
 | simpl in |- *; discriminate H2
 | simpl in |- *; discriminate H2 ].
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [lt] (expressed
    from [compare] on [positive])

    Part 2: [lt] on [nat] is finer than [lt] on [positive]
*)

Lemma nat_of_P_lt_Lt_compare_complement_morphism :
 forall p q:positive, nat_of_P p < nat_of_P q -> (p ?= q)%positive Eq = Lt.
Proof.
intros x y; unfold gt in |- *; elim (Dcompare ((x ?= y)%positive Eq));
 [ intros E; rewrite (Pcompare_Eq_eq x y E); intros H;
    absurd (nat_of_P y < nat_of_P y); [ apply lt_irrefl | assumption ]
 | intros H; elim H;
    [ auto
    | intros H1 H2; absurd (nat_of_P x < nat_of_P y);
       [ apply lt_asym; change (nat_of_P x > nat_of_P y) in |- *;
          apply nat_of_P_gt_Gt_compare_morphism; assumption
       | assumption ] ] ].
Qed.

(** [nat_of_P] is a morphism from [positive] to [nat] for [gt] (expressed
    from [compare] on [positive])

    Part 2: [gt] on [nat] is finer than [gt] on [positive]
*)

Lemma nat_of_P_gt_Gt_compare_complement_morphism :
 forall p q:positive, nat_of_P p > nat_of_P q -> (p ?= q)%positive Eq = Gt.
Proof.
intros x y; unfold gt in |- *; elim (Dcompare ((x ?= y)%positive Eq));
 [ intros E; rewrite (Pcompare_Eq_eq x y E); intros H;
    absurd (nat_of_P y < nat_of_P y); [ apply lt_irrefl | assumption ]
 | intros H; elim H;
    [ intros H1 H2; absurd (nat_of_P y < nat_of_P x);
       [ apply lt_asym; apply nat_of_P_lt_Lt_compare_morphism; assumption
       | assumption ]
    | auto ] ].
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
  simple induction p. unfold nat_of_P in |- *. simpl in |- *. intros. rewrite Pmult_nat_2_mult_2_permute.
  rewrite Pmult_nat_4_mult_2_permute. rewrite H. simpl in |- *. rewrite <- plus_Snm_nSm. reflexivity.
  unfold nat_of_P in |- *. simpl in |- *. intros. rewrite Pmult_nat_2_mult_2_permute. rewrite Pmult_nat_4_mult_2_permute.
  rewrite H. reflexivity.
  reflexivity.
Qed.

Lemma nat_of_P_xI : forall p:positive, nat_of_P (xI p) = S (2 * nat_of_P p).
Proof.
  simple induction p. unfold nat_of_P in |- *. simpl in |- *. intro p0. intro. rewrite Pmult_nat_2_mult_2_permute.
  rewrite Pmult_nat_4_mult_2_permute; injection H; intro H1; rewrite H1;
   rewrite <- plus_Snm_nSm; reflexivity.
  unfold nat_of_P in |- *. simpl in |- *. intros. rewrite Pmult_nat_2_mult_2_permute. rewrite Pmult_nat_4_mult_2_permute.
  injection H; intro H1; rewrite H1; reflexivity.
  reflexivity.
Qed.

(**********************************************************************)
(** Properties of the shifted injection from Peano natural numbers to 
    binary positive numbers *)

(** Composition of [P_of_succ_nat] and [nat_of_P] is successor on [nat] *)

Theorem nat_of_P_o_P_of_succ_nat_eq_succ :
 forall n:nat, nat_of_P (P_of_succ_nat n) = S n.
Proof.
intro m; induction m as [| n H];
 [ reflexivity
 | simpl in |- *; rewrite nat_of_P_succ_morphism; rewrite H; auto ].
Qed.

(** Miscellaneous lemmas on [P_of_succ_nat] *)

Lemma ZL3 :
 forall n:nat, Psucc (P_of_succ_nat (n + n)) = xO (P_of_succ_nat n).
Proof.
intro x; induction x as [| n H];
 [ simpl in |- *; auto with arith
 | simpl in |- *; rewrite plus_comm; simpl in |- *; rewrite H;
    rewrite xO_succ_permute; auto with arith ].
Qed.

Lemma ZL5 : forall n:nat, P_of_succ_nat (S n + S n) = xI (P_of_succ_nat n).
Proof.
intro x; induction x as [| n H]; simpl in |- *;
 [ auto with arith
 | rewrite <- plus_n_Sm; simpl in |- *; simpl in H; rewrite H;
    auto with arith ].
Qed.

(** Composition of [nat_of_P] and [P_of_succ_nat] is successor on [positive] *)

Theorem P_of_succ_nat_o_nat_of_P_eq_succ :
 forall p:positive, P_of_succ_nat (nat_of_P p) = Psucc p.
Proof.
intro x; induction x as [p H| p H| ];
 [ simpl in |- *; rewrite <- H; change 2 with (1 + 1) in |- *;
    rewrite Pmult_nat_r_plus_morphism; elim (ZL4 p); 
    unfold nat_of_P in |- *; intros n H1; rewrite H1; 
    rewrite ZL3; auto with arith
 | unfold nat_of_P in |- *; simpl in |- *; change 2 with (1 + 1) in |- *;
    rewrite Pmult_nat_r_plus_morphism;
    rewrite <- (Ppred_succ (P_of_succ_nat (Pmult_nat p 1 + Pmult_nat p 1)));
    rewrite <- (Ppred_succ (xI p)); simpl in |- *; 
    rewrite <- H; elim (ZL4 p); unfold nat_of_P in |- *; 
    intros n H1; rewrite H1; rewrite ZL5; simpl in |- *; 
    trivial with arith
 | unfold nat_of_P in |- *; simpl in |- *; auto with arith ].
Qed.

(** Composition of [nat_of_P], [P_of_succ_nat] and [Ppred] is identity
    on [positive] *)

Theorem pred_o_P_of_succ_nat_o_nat_of_P_eq_id :
 forall p:positive, Ppred (P_of_succ_nat (nat_of_P p)) = p.
Proof.
intros x; rewrite P_of_succ_nat_o_nat_of_P_eq_succ; rewrite Ppred_succ;
 trivial with arith.
Qed.

(**********************************************************************)
(** Extra properties of the injection from binary positive numbers to Peano 
    natural numbers *)

(** [nat_of_P] is a morphism for subtraction on positive numbers *)

Theorem nat_of_P_minus_morphism :
 forall p q:positive,
   (p ?= q)%positive Eq = Gt -> nat_of_P (p - q) = nat_of_P p - nat_of_P q.
Proof.
intros x y H; apply plus_reg_l with (nat_of_P y); rewrite le_plus_minus_r;
 [ rewrite <- nat_of_P_plus_morphism; rewrite Pplus_minus; auto with arith
 | apply lt_le_weak; exact (nat_of_P_gt_Gt_compare_morphism x y H) ].
Qed.

(** [nat_of_P] is injective *)

Lemma nat_of_P_inj : forall p q:positive, nat_of_P p = nat_of_P q -> p = q.
Proof.
intros x y H; rewrite <- (pred_o_P_of_succ_nat_o_nat_of_P_eq_id x);
 rewrite <- (pred_o_P_of_succ_nat_o_nat_of_P_eq_id y); 
 rewrite H; trivial with arith.
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
   (q ?= p)%positive Eq = Lt ->
   (r ?= p)%positive Eq = Gt ->
   (r ?= q)%positive Eq = Gt -> (r - p ?= r - q)%positive Eq = Lt.
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
   (q ?= p)%positive Eq = Lt ->
   (p ?= r)%positive Eq = Gt ->
   (q ?= r)%positive Eq = Gt -> (q - r ?= p - r)%positive Eq = Lt.
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
   (q ?= r)%positive Eq = Gt ->
   (p * (q - r))%positive = (p * q - p * r)%positive.
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

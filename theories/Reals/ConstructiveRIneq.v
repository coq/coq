(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(*********************************************************)
(** * Basic lemmas for the contructive real numbers      *)
(*********************************************************)

(* Implement interface ConstructiveReals opaquely with
   Cauchy reals and prove basic results.
   Those are therefore true for any implementation of
   ConstructiveReals (for example with Dedekind reals). *)

Require Import ConstructiveCauchyReals.
Require Import ConstructiveRcomplete.
Require Export ConstructiveReals.
Require Import Zpower.
Require Export ZArithRing.
Require Import Omega.
Require Import QArith_base.
Require Import Qring.

Declare Scope R_scope_constr.

Local Open Scope Z_scope.
Local Open Scope R_scope_constr.

Definition CR : ConstructiveReals.
Proof.
  assert (isLinearOrder CReal CRealLt) as lin.
  { repeat split. exact CRealLt_asym.
    exact CRealLt_trans.
    intros. destruct (CRealLt_dec x z y H).
    left. exact c. right. exact c. }
  assert (forall r r1 r2 : CReal, CRealLt r1 r2 <-> CRealLt (r + r1) (r + r2))
    as plusLtCompat.
  { split. intros. apply CReal_plus_lt_compat_l. exact H.
    intros. apply CReal_plus_lt_reg_l in H. exact H. }
  apply (Build_ConstructiveReals
           CReal CRealLt lin
           (inject_Q 0) (inject_Q 1)
           CReal_plus CReal_opp CReal_mult
           CReal_isRing CReal_isRingExt CRealLt_0_1
           plusLtCompat CReal_mult_lt_0_compat
           CReal_inv CReal_inv_l CReal_inv_0_lt_compat
           CRealArchimedean).
  - intros. destruct (Rcauchy_complete xn) as [l cv].
    intro n. apply (H (IQR (1#n))). apply IQR_pos. reflexivity.
    exists l. intros eps epsPos.
    destruct (Rup_nat ((/eps) (or_intror epsPos))) as [n nmaj].
    specialize (cv (Pos.of_nat (S n))) as [p pmaj].
    exists p. intros. specialize (pmaj i H0). unfold absSmall in pmaj.
    apply (CReal_mult_lt_compat_l eps) in nmaj.
    rewrite CReal_inv_r, CReal_mult_comm in nmaj.
    2: apply epsPos. split.
    + apply (CRealLt_trans _ (-IQR (1 # Pos.of_nat (S n)))).
      2: apply pmaj. clear pmaj.
      apply CReal_opp_gt_lt_contravar. unfold CRealGt, IQR.
      rewrite CReal_mult_1_l. apply (CReal_mult_lt_reg_l (IPR (Pos.of_nat (S n)))).
      apply IPR_pos. rewrite CReal_inv_r, <- INR_IPR, Nat2Pos.id.
      2: discriminate. apply (CRealLt_trans _ (INR n * eps) _ nmaj).
      apply CReal_mult_lt_compat_r. exact epsPos. apply lt_INR, le_refl.
    + apply (CRealLt_trans _ (IQR (1 # Pos.of_nat (S n)))).
      apply pmaj. unfold IQR. rewrite CReal_mult_1_l.
      apply (CReal_mult_lt_reg_l (IPR (Pos.of_nat (S n)))).
      apply IPR_pos. rewrite CReal_inv_r, <- INR_IPR, Nat2Pos.id.
      2: discriminate. apply (CRealLt_trans _ (INR n * eps) _ nmaj).
      apply CReal_mult_lt_compat_r. exact epsPos. apply lt_INR, le_refl.
  - exact CRealLt_lpo_dec.
  - exact sig_lub.
Qed. (* Keep it opaque to possibly change the implementation later *)

Definition R := CRcarrier CR.

Definition Req := orderEq R (CRlt CR).
Definition Rle (x y : R) := ~CRlt CR y x.
Definition Rge (x y : R) := ~CRlt CR x y.
Definition Rlt := CRlt CR.
Definition Rgt (x y : R) := CRlt CR y x.
Definition Rappart := orderAppart R (CRlt CR).

Infix "==" := Req : R_scope_constr.
Infix "#" := Rappart : R_scope_constr.
Infix "<" := Rlt : R_scope_constr.
Infix ">" := Rgt : R_scope_constr.
Infix "<=" := Rle : R_scope_constr.
Infix ">=" := Rge : R_scope_constr.

Notation "x <= y <= z" := (x <= y /\ y <= z) : R_scope_constr.
Notation "x <= y < z"  := (x <= y /\ y <  z) : R_scope_constr.
Notation "x < y < z"   := (x <  y /\ y <  z) : R_scope_constr.
Notation "x < y <= z"  := (x <  y /\ y <= z) : R_scope_constr.

Lemma Rle_refl : forall x : R, x <= x.
Proof.
  intros. intro abs.
  destruct (CRltLinear CR), a.
  specialize (H x x abs). contradiction.
Qed.
Hint Immediate Rle_refl: rorders.

Lemma Req_refl : forall x : R, x == x.
Proof.
  intros. split; apply Rle_refl.
Qed.

Lemma Req_sym : forall x y : R, x == y -> y == x.
Proof.
  intros. destruct H. split; intro abs; contradiction.
Qed.

Lemma Req_trans : forall x y z : R, x == y -> y == z -> x == z.
Proof.
  intros. destruct H,H0. destruct (CRltLinear CR), a. split.
  - intro abs. destruct (s _ y _ abs); contradiction.
  - intro abs. destruct (s _ y _ abs); contradiction.
Qed.

Add Parametric Relation : R Req
    reflexivity proved by Req_refl
    symmetry proved by Req_sym
    transitivity proved by Req_trans
      as Req_rel.

Lemma linear_order_T : forall x y z : R,
    x < z -> {x < y} + {y < z}.
Proof.
  intros. destruct (CRltLinear CR). apply s. exact H.
Qed.

Add Parametric Morphism : Rlt
    with signature Req ==> Req ==> iff
      as Rlt_morph.
Proof.
  intros. destruct H, H0. split.
  - intro. destruct (linear_order_T x y x0). assumption.
    contradiction. destruct (linear_order_T y y0 x0).
    assumption. assumption. contradiction.
  - intro. destruct (linear_order_T y x y0). assumption.
    contradiction. destruct (linear_order_T x x0 y0).
    assumption. assumption. contradiction.
Qed.

Add Parametric Morphism : Rgt
    with signature Req ==> Req ==> iff
      as Rgt_morph.
Proof.
  intros. unfold Rgt. apply Rlt_morph; assumption.
Qed.

Add Parametric Morphism : Rappart
    with signature Req ==> Req ==> iff
      as Rappart_morph.
Proof.
  split.
  - intros. destruct H1. left. rewrite <- H0, <- H. exact H1.
    right. rewrite <- H0, <- H. exact H1.
  - intros. destruct H1. left. rewrite H0, H. exact H1.
    right. rewrite H0, H. exact H1.
Qed.

Add Parametric Morphism : Rle
    with signature Req ==> Req ==> iff
      as Rle_morph.
Proof.
  intros. split.
  - intros H1 H2. unfold CRealLe in H1.
    rewrite <- H0 in H2. rewrite <- H in H2. contradiction.
  - intros H1 H2. unfold CRealLe in H1.
    rewrite H0 in H2. rewrite H in H2. contradiction.
Qed.

Add Parametric Morphism : Rge
    with signature Req ==> Req ==> iff
      as Rge_morph.
Proof.
  intros. unfold Rge. apply Rle_morph; assumption.
Qed.


Definition Rplus := CRplus CR.
Definition Rmult := CRmult CR.
Definition Rinv := CRinv CR.
Definition Ropp := CRopp CR.
Definition Rminus := CRminus CR.

Add Parametric Morphism : Rplus
    with signature Req ==> Req ==> Req
      as Rplus_morph.
Proof.
  apply CRisRingExt.
Qed.

Add Parametric Morphism : Rmult
    with signature Req ==> Req ==> Req
      as Rmult_morph.
Proof.
  apply CRisRingExt.
Qed.

Add Parametric Morphism : Ropp
    with signature Req ==> Req
      as Ropp_morph.
Proof.
  apply (Ropp_ext (CRisRingExt CR)).
Qed.

Add Parametric Morphism : Rminus
    with signature Req ==> Req ==> Req
      as Rminus_morph.
Proof.
  intros. unfold Rminus, CRminus. rewrite H,H0. reflexivity.
Qed.

Infix "+" := Rplus : R_scope_constr.
Notation "- x" := (Ropp x) : R_scope_constr.
Infix "-" := Rminus : R_scope_constr.
Infix "*" := Rmult : R_scope_constr.
Notation "/ x" := (CRinv CR x) (at level 35, right associativity) : R_scope_constr.

Notation "0" := (CRzero CR) : R_scope_constr.
Notation "1" := (CRone CR) : R_scope_constr.

(* Help Add Ring to find the correct equality *)
Lemma RisRing : ring_theory 0 1
                            Rplus Rmult
                            Rminus Ropp
                            Req.
Proof.
  exact (CRisRing CR).
Qed.

Add Ring CRealRing : RisRing.

Lemma Rplus_comm : forall x y:R, x + y == y + x.
Proof. intros. ring. Qed.

Lemma Rplus_assoc : forall x y z:R, (x + y) + z == x + (y + z).
Proof. intros. ring. Qed.

Lemma Rplus_opp_r : forall x:R, x + -x == 0.
Proof. intros. ring. Qed.

Lemma Rplus_0_l : forall x:R, 0 + x == x.
Proof. intros. ring. Qed.

Lemma Rmult_0_l : forall x:R, 0 * x == 0.
Proof. intros. ring. Qed.

Lemma Rmult_1_l : forall x:R, 1 * x == x.
Proof. intros. ring. Qed.

Lemma Rmult_comm : forall x y:R, x * y == y * x.
Proof. intros. ring. Qed.

Lemma Rmult_assoc : forall x y z:R, (x * y) * z == x * (y * z).
Proof. intros. ring. Qed.

Definition Rinv_l := CRinv_l CR.

Lemma Rmult_plus_distr_l : forall r1 r2 r3 : R,
    r1 * (r2 + r3) == (r1 * r2) + (r1 * r3).
Proof. intros. ring. Qed.

Definition Rlt_0_1 := CRzero_lt_one CR.

Lemma Rlt_asym : forall x y :R, x < y -> ~(y < x).
Proof.
  intros. intro abs. destruct (CRltLinear CR), a.
  apply (H0 x y); assumption.
Qed.

Lemma Rlt_trans : forall x y z : R, x < y -> y < z -> x < z.
Proof.
  intros. destruct (CRltLinear CR), a.
  apply (H2 x y); assumption.
Qed.

Lemma Rplus_lt_compat_l : forall x y z : R,
    y < z -> x + y < x + z.
Proof.
  intros. apply CRplus_lt_compat_l. exact H.
Qed.

Lemma Ropp_mult_distr_l
  : forall r1 r2 : R, -(r1 * r2) == (- r1) * r2.
Proof.
  intros. ring.
Qed.

Lemma Rplus_lt_reg_l : forall r r1 r2, r + r1 < r + r2 -> r1 < r2.
Proof.
  intros. apply CRplus_lt_compat_l in H. exact H.
Qed.

Lemma Rmult_lt_compat_l : forall x y z : R,
    0 < x -> y < z -> x * y < x * z.
Proof.
  intros. rewrite (CRplus_lt_compat_l CR (- (x * y))).
  rewrite Rplus_comm. pose proof Rplus_opp_r.
  rewrite H1.
  rewrite Rmult_comm, Ropp_mult_distr_l, Rmult_comm.
  rewrite <- Rmult_plus_distr_l.
  apply CRmult_lt_0_compat. exact H.
  apply (Rplus_lt_reg_l y).
  rewrite Rplus_comm, Rplus_0_l.
  rewrite <- Rplus_assoc, H1, Rplus_0_l. exact H0.
Qed.

Hint Resolve Rplus_comm Rplus_assoc Rplus_opp_r Rplus_0_l
     Rmult_comm Rmult_assoc Rinv_l Rmult_1_l Rmult_plus_distr_l
     Rlt_0_1 Rlt_asym Rlt_trans Rplus_lt_compat_l Rmult_lt_compat_l
     Rmult_0_l : creal.

Fixpoint INR (n:nat) : R :=
  match n with
  | O => 0
  | S O => 1
  | S n => INR n + 1
  end.
Arguments INR n%nat.

(* compact representation for 2*p *)
Fixpoint IPR_2 (p:positive) : R :=
  match p with
  | xH => 1 + 1
  | xO p => (1 + 1) * IPR_2 p
  | xI p => (1 + 1) * (1 + IPR_2 p)
  end.

Definition IPR (p:positive) : R :=
  match p with
  | xH => 1
  | xO p => IPR_2 p
  | xI p => 1 + IPR_2 p
  end.
Arguments IPR p%positive : simpl never.

(**********)
Definition IZR (z:Z) : R :=
  match z with
  | Z0 => 0
  | Zpos n => IPR n
  | Zneg n => - IPR n
  end.
Arguments IZR z%Z : simpl never.

Notation "2" := (IZR 2) : R_scope_constr.


(*********************************************************)
(** ** Relation between orders and equality              *)
(*********************************************************)

Lemma Rge_refl : forall r, r <= r.
Proof. exact Rle_refl. Qed.
Hint Immediate Rge_refl: rorders.

(** Irreflexivity of the strict order *)

Lemma Rlt_irrefl : forall r, ~ r < r.
Proof.
  intros r H; eapply Rlt_asym; eauto.
Qed.
Hint Resolve Rlt_irrefl: creal.

Lemma Rgt_irrefl : forall r, ~ r > r.
Proof. exact Rlt_irrefl. Qed.

Lemma Rlt_not_eq : forall r1 r2, r1 < r2 -> r1 <> r2.
Proof.
  intros. intro abs. subst r2. exact (Rlt_irrefl r1 H).
Qed.

Lemma Rgt_not_eq : forall r1 r2, r1 > r2 -> r1 <> r2.
Proof.
  intros; apply not_eq_sym; apply Rlt_not_eq; auto with creal.
Qed.

(**********)
Lemma Rlt_dichotomy_converse : forall r1 r2, r1 < r2 \/ r1 > r2 -> r1 <> r2.
Proof.
  intros. destruct H.
  - intro abs. subst r2. exact (Rlt_irrefl r1 H).
  - intro abs. subst r2. exact (Rlt_irrefl r1 H).
Qed.
Hint Resolve Rlt_dichotomy_converse: creal.

(** Reasoning by case on equality and order *)


(*********************************************************)
(** ** Relating [<], [>], [<=] and [>=]  	         *)
(*********************************************************)

(*********************************************************)
(** ** Order                                             *)
(*********************************************************)

(** *** Relating strict and large orders *)

Lemma Rlt_le : forall r1 r2, r1 < r2 -> r1 <= r2.
Proof.
  intros. intro abs. apply (Rlt_asym r1 r2); assumption.
Qed.
Hint Resolve Rlt_le: creal.

Lemma Rgt_ge : forall r1 r2, r1 > r2 -> r1 >= r2.
Proof.
  intros. intro abs. apply (Rlt_asym r1 r2); assumption.
Qed.

(**********)
Lemma Rle_ge : forall r1 r2, r1 <= r2 -> r2 >= r1.
Proof.
  intros. intros abs. contradiction.
Qed.
Hint Immediate Rle_ge: creal.
Hint Resolve Rle_ge: rorders.

Lemma Rge_le : forall r1 r2, r1 >= r2 -> r2 <= r1.
Proof.
  intros. intro abs. contradiction.
Qed.
Hint Resolve Rge_le: creal.
Hint Immediate Rge_le: rorders.

(**********)
Lemma Rlt_gt : forall r1 r2, r1 < r2 -> r2 > r1.
Proof.
  trivial.
Qed.
Hint Resolve Rlt_gt: rorders.

Lemma Rgt_lt : forall r1 r2, r1 > r2 -> r2 < r1.
Proof.
  trivial.
Qed.
Hint Immediate Rgt_lt: rorders.

(**********)

Lemma Rnot_lt_le : forall r1 r2, ~ r1 < r2 -> r2 <= r1.
Proof.
  intros. intro abs. contradiction.
Qed.

Lemma Rnot_gt_le : forall r1 r2, ~ r1 > r2 -> r1 <= r2.
Proof.
  intros. intro abs. contradiction.
Qed.

Lemma Rnot_gt_ge : forall r1 r2, ~ r1 > r2 -> r2 >= r1.
Proof.
  intros. intro abs. contradiction.
Qed.

Lemma Rnot_lt_ge : forall r1 r2, ~ r1 < r2 -> r1 >= r2.
Proof.
  intros. intro abs. contradiction.
Qed.

(**********)
Lemma Rlt_not_le : forall r1 r2, r2 < r1 -> ~ r1 <= r2.
Proof.
  generalize Rlt_asym Rlt_dichotomy_converse; unfold CRealLe.
  unfold not; intuition eauto 3.
Qed.
Hint Immediate Rlt_not_le: creal.

Lemma Rgt_not_le : forall r1 r2, r1 > r2 -> ~ r1 <= r2.
Proof. exact Rlt_not_le. Qed.

Lemma Rlt_not_ge : forall r1 r2, r1 < r2 -> ~ r1 >= r2.
Proof. red; intros; eapply Rlt_not_le; eauto with creal. Qed.
Hint Immediate Rlt_not_ge: creal.

Lemma Rgt_not_ge : forall r1 r2, r2 > r1 -> ~ r1 >= r2.
Proof. exact Rlt_not_ge. Qed.

Lemma Rle_not_lt : forall r1 r2, r2 <= r1 -> ~ r1 < r2.
Proof.
  intros r1 r2. generalize (Rlt_asym r1 r2) (Rlt_dichotomy_converse r1 r2).
  unfold CRealLe; intuition.
Qed.

Lemma Rge_not_lt : forall r1 r2, r1 >= r2 -> ~ r1 < r2.
Proof. intros; apply Rle_not_lt; auto with creal. Qed.

Lemma Rle_not_gt : forall r1 r2, r1 <= r2 -> ~ r1 > r2.
Proof. do 2 intro; apply Rle_not_lt. Qed.

Lemma Rge_not_gt : forall r1 r2, r2 >= r1 -> ~ r1 > r2.
Proof. do 2 intro; apply Rge_not_lt. Qed.

(**********)
Lemma Req_le : forall r1 r2, r1 = r2 -> r1 <= r2.
Proof.
  intros. intro abs. subst r2. exact (Rlt_irrefl r1 abs).
Qed.
Hint Immediate Req_le: creal.

Lemma Req_ge : forall r1 r2, r1 = r2 -> r1 >= r2.
Proof.
  intros. intro abs. subst r2. exact (Rlt_irrefl r1 abs).
Qed.
Hint Immediate Req_ge: creal.

Lemma Req_le_sym : forall r1 r2, r2 = r1 -> r1 <= r2.
Proof.
  intros. intro abs. subst r2. exact (Rlt_irrefl r1 abs).
Qed.
Hint Immediate Req_le_sym: creal.

Lemma Req_ge_sym : forall r1 r2, r2 = r1 -> r1 >= r2.
Proof.
  intros. intro abs. subst r2. exact (Rlt_irrefl r1 abs).
Qed.
Hint Immediate Req_ge_sym: creal.

(** *** Asymmetry *)

(** Remark: [Rlt_asym] is an axiom *)

Lemma Rgt_asym : forall r1 r2, r1 > r2 -> ~ r2 > r1.
Proof. do 2 intro; apply Rlt_asym. Qed.


(** *** Compatibility with equality *)

Lemma Rlt_eq_compat :
  forall r1 r2 r3 r4, r1 = r2 -> r2 < r4 -> r4 = r3 -> r1 < r3.
Proof.
  intros x x' y y'; intros; replace x with x'; replace y with y'; assumption.
Qed.

Lemma Rgt_eq_compat :
  forall r1 r2 r3 r4, r1 = r2 -> r2 > r4 -> r4 = r3 -> r1 > r3.
Proof. intros; red; apply Rlt_eq_compat with (r2:=r4) (r4:=r2); auto. Qed.

(** *** Transitivity *)

Lemma Rle_trans : forall r1 r2 r3, r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Proof.
  intros. intro abs.
  destruct (linear_order_T r3 r2 r1 abs); contradiction.
Qed.

Lemma Rge_trans : forall r1 r2 r3, r1 >= r2 -> r2 >= r3 -> r1 >= r3.
Proof.
  intros. apply (Rle_trans _ r2); assumption.
Qed.

Lemma Rgt_trans : forall r1 r2 r3, r1 > r2 -> r2 > r3 -> r1 > r3.
Proof.
  intros. apply (Rlt_trans _ r2); assumption.
Qed.

(**********)
Lemma Rle_lt_trans : forall r1 r2 r3, r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros.
  destruct (linear_order_T r2 r1 r3 H0). contradiction. apply r.
Qed.

Lemma Rlt_le_trans : forall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 < r3.
Proof.
  intros.
  destruct (linear_order_T r1 r3 r2 H). apply r. contradiction.
Qed.

Lemma Rge_gt_trans : forall r1 r2 r3, r1 >= r2 -> r2 > r3 -> r1 > r3.
Proof.
  intros. apply (Rlt_le_trans _ r2); assumption.
Qed.

Lemma Rgt_ge_trans : forall r1 r2 r3, r1 > r2 -> r2 >= r3 -> r1 > r3.
Proof.
  intros. apply (Rle_lt_trans _ r2); assumption.
Qed.


(*********************************************************)
(** ** Addition                                          *)
(*********************************************************)

(** Remark: [Rplus_0_l] is an axiom *)

Lemma Rplus_0_r : forall r, r + 0 == r.
Proof.
  intros. rewrite Rplus_comm. rewrite Rplus_0_l. reflexivity.
Qed.
Hint Resolve Rplus_0_r: creal.

Lemma Rplus_ne : forall r, r + 0 == r /\ 0 + r == r.
Proof.
  split. apply Rplus_0_r. apply Rplus_0_l.
Qed.
Hint Resolve Rplus_ne: creal.

(**********)

(** Remark: [Rplus_opp_r] is an axiom *)

Lemma Rplus_opp_l : forall r, - r + r == 0.
Proof.
  intros. rewrite Rplus_comm. apply Rplus_opp_r.
Qed.
Hint Resolve Rplus_opp_l: creal.

(**********)
Lemma Rplus_opp_r_uniq : forall r1 r2, r1 + r2 == 0 -> r2 == - r1.
Proof.
  intros x y H. rewrite <- (Rplus_0_l y).
  rewrite <- (Rplus_opp_l x). rewrite Rplus_assoc.
  rewrite H. rewrite Rplus_0_r. reflexivity.
Qed.

Lemma Rplus_eq_compat_l : forall r r1 r2, r1 == r2 -> r + r1 == r + r2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma Rplus_eq_compat_r : forall r r1 r2, r1 == r2 -> r1 + r == r2 + r.
Proof.
  intros. rewrite H. reflexivity.
Qed.


(**********)
Lemma Rplus_eq_reg_l : forall r r1 r2, r + r1 == r + r2 -> r1 == r2.
Proof.
  intros; transitivity (- r + r + r1).
  rewrite Rplus_opp_l. rewrite Rplus_0_l. reflexivity.
  transitivity (- r + r + r2).
  repeat rewrite Rplus_assoc; rewrite <- H; reflexivity.
  rewrite Rplus_opp_l. rewrite Rplus_0_l. reflexivity.
Qed.
Hint Resolve Rplus_eq_reg_l: creal.

Lemma Rplus_eq_reg_r : forall r r1 r2, r1 + r == r2 + r -> r1 == r2.
Proof.
  intros r r1 r2 H.
  apply Rplus_eq_reg_l with r.
  now rewrite 2!(Rplus_comm r).
Qed.

(**********)
Lemma Rplus_0_r_uniq : forall r r1, r + r1 == r -> r1 == 0.
Proof.
  intros. apply (Rplus_eq_reg_l r). rewrite Rplus_0_r. exact H.
Qed.


(*********************************************************)
(** ** Multiplication                                    *)
(*********************************************************)

(**********)
Lemma Rinv_r : forall r (rnz : r # 0),
    r # 0 -> r * ((/ r) rnz) == 1.
Proof.
  intros. rewrite Rmult_comm. rewrite Rinv_l.
  reflexivity.
Qed.
Hint Resolve Rinv_r: creal.

Lemma Rinv_l_sym : forall r (rnz: r # 0), 1 == (/ r) rnz * r.
Proof.
  intros. symmetry. apply Rinv_l.
Qed.
Hint Resolve Rinv_l_sym: creal.

Lemma Rinv_r_sym : forall r (rnz : r # 0), 1 == r * (/ r) rnz.
Proof.
  intros. symmetry. apply Rinv_r. apply rnz.
Qed.
Hint Resolve Rinv_r_sym: creal.

(**********)
Lemma Rmult_0_r : forall r, r * 0 == 0.
Proof.
  intro; ring.
Qed.
Hint Resolve Rmult_0_r: creal.

(**********)
Lemma Rmult_ne : forall r, r * 1 == r /\ 1 * r == r.
Proof.
  intro; split; ring.
Qed.
Hint Resolve Rmult_ne: creal.

(**********)
Lemma Rmult_1_r : forall r, r * 1 == r.
Proof.
  intro; ring.
Qed.
Hint Resolve Rmult_1_r: creal.

(**********)
Lemma Rmult_eq_compat_l : forall r r1 r2, r1 == r2 -> r * r1 == r * r2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma Rmult_eq_compat_r : forall r r1 r2, r1 == r2 -> r1 * r == r2 * r.
Proof.
  intros. rewrite H. reflexivity.
Qed.

(**********)
Lemma Rmult_eq_reg_l : forall r r1 r2, r * r1 == r * r2 -> r # 0 -> r1 == r2.
Proof.
  intros. transitivity ((/ r) H0 * r * r1).
  rewrite Rinv_l. ring.
  transitivity ((/ r) H0 * r * r2).
  repeat rewrite Rmult_assoc; rewrite H; reflexivity.
  rewrite Rinv_l. ring.
Qed.

Lemma Rmult_eq_reg_r : forall r r1 r2, r1 * r == r2 * r -> r # 0 -> r1 == r2.
Proof.
  intros.
  apply Rmult_eq_reg_l with (2 := H0).
  now rewrite 2!(Rmult_comm r).
Qed.

(**********)
Lemma Rmult_eq_0_compat : forall r1 r2, r1 == 0 \/ r2 == 0 -> r1 * r2 == 0.
Proof.
  intros r1 r2 [H| H]; rewrite H; auto with creal.
Qed.

Hint Resolve Rmult_eq_0_compat: creal.

(**********)
Lemma Rmult_eq_0_compat_r : forall r1 r2, r1 == 0 -> r1 * r2 == 0.
Proof.
  auto with creal.
Qed.

(**********)
Lemma Rmult_eq_0_compat_l : forall r1 r2, r2 == 0 -> r1 * r2 == 0.
Proof.
  auto with creal.
Qed.

(**********)
Lemma Rmult_integral_contrapositive :
  forall r1 r2, r1 # 0 /\ r2 # 0 -> (r1 * r2) # 0.
Proof.
  assert (forall r, 0 > r -> 0 < - r).
  { intros. rewrite <- (Rplus_opp_l r), <- (Rplus_0_r (-r)), Rplus_assoc.
    apply Rplus_lt_compat_l. rewrite Rplus_0_l. apply H. }
  intros. destruct H0, H0, H1.
  - right. setoid_replace (r1*r2) with (-r1 * -r2). 2: ring.
    rewrite <- (Rmult_0_r (-r1)). apply Rmult_lt_compat_l; apply H; assumption.
  - left. rewrite <- (Rmult_0_r r2).
    rewrite Rmult_comm. apply (Rmult_lt_compat_l). apply H1. apply H0.
  - left. rewrite <- (Rmult_0_r r1). apply (Rmult_lt_compat_l). apply H0. apply H1.
  - right. rewrite <- (Rmult_0_r r1). apply Rmult_lt_compat_l; assumption.
Qed.
Hint Resolve Rmult_integral_contrapositive: creal.

Lemma Rmult_integral_contrapositive_currified :
  forall r1 r2, r1 # 0 -> r2 # 0 -> (r1 * r2) # 0.
Proof.
  intros. apply Rmult_integral_contrapositive.
  split; assumption.
Qed.

(**********)
Lemma Rmult_plus_distr_r :
  forall r1 r2 r3, (r1 + r2) * r3 == r1 * r3 + r2 * r3.
Proof.
  intros; ring.
Qed.

(*********************************************************)
(** ** Square function                                   *)
(*********************************************************)

(***********)
Definition Rsqr (r : R) := r * r.

Notation "r ²" := (Rsqr r) (at level 1, format "r ²") : R_scope_constr.

(***********)
Lemma Rsqr_0 : Rsqr 0 == 0.
  unfold Rsqr; auto with creal.
Qed.

(*********************************************************)
(** ** Opposite                                          *)
(*********************************************************)

(**********)
Lemma Ropp_eq_compat : forall r1 r2, r1 == r2 -> - r1 == - r2.
Proof.
  intros. rewrite H. reflexivity.
Qed.
Hint Resolve Ropp_eq_compat: creal.

(**********)
Lemma Ropp_0 : -0 == 0.
Proof.
  ring.
Qed.
Hint Resolve Ropp_0: creal.

(**********)
Lemma Ropp_eq_0_compat : forall r, r == 0 -> - r == 0.
Proof.
  intros; rewrite H; auto with creal.
Qed.
Hint Resolve Ropp_eq_0_compat: creal.

(**********)
Lemma Ropp_involutive : forall r, - - r == r.
Proof.
  intro; ring.
Qed.
Hint Resolve Ropp_involutive: creal.

(**********)
Lemma Ropp_plus_distr : forall r1 r2, - (r1 + r2) == - r1 + - r2.
Proof.
  intros; ring.
Qed.
Hint Resolve Ropp_plus_distr: creal.

(*********************************************************)
(** ** Opposite and multiplication                       *)
(*********************************************************)

Lemma Ropp_mult_distr_l_reverse : forall r1 r2, - r1 * r2 == - (r1 * r2).
Proof.
  intros; ring.
Qed.
Hint Resolve Ropp_mult_distr_l_reverse: creal.

(**********)
Lemma Rmult_opp_opp : forall r1 r2, - r1 * - r2 == r1 * r2.
Proof.
  intros; ring.
Qed.
Hint Resolve Rmult_opp_opp: creal.

Lemma Ropp_mult_distr_r : forall r1 r2, - (r1 * r2) == r1 * - r2.
Proof.
  intros; ring.
Qed.

Lemma Ropp_mult_distr_r_reverse : forall r1 r2, r1 * - r2 == - (r1 * r2).
Proof.
  intros; ring.
Qed.

(*********************************************************)
(** ** Subtraction                                      *)
(*********************************************************)

Lemma Rminus_0_r : forall r, r - 0 == r.
Proof.
  intro; ring.
Qed.
Hint Resolve Rminus_0_r: creal.

Lemma Rminus_0_l : forall r, 0 - r == - r.
Proof.
  intro; ring.
Qed.
Hint Resolve Rminus_0_l: creal.

(**********)
Lemma Ropp_minus_distr : forall r1 r2, - (r1 - r2) == r2 - r1.
Proof.
  intros; ring.
Qed.
Hint Resolve Ropp_minus_distr: creal.

Lemma Ropp_minus_distr' : forall r1 r2, - (r2 - r1) == r1 - r2.
Proof.
  intros; ring.
Qed.

(**********)
Lemma Rminus_diag_eq : forall r1 r2, r1 == r2 -> r1 - r2 == 0.
Proof.
  intros; rewrite H; ring.
Qed.
Hint Resolve Rminus_diag_eq: creal.

(**********)
Lemma Rminus_diag_uniq : forall r1 r2, r1 - r2 == 0 -> r1 == r2.
Proof.
  intros r1 r2. unfold Rminus,CRminus; rewrite Rplus_comm; intro.
  rewrite <- (Ropp_involutive r2); apply (Rplus_opp_r_uniq (- r2) r1 H).
Qed.
Hint Immediate Rminus_diag_uniq: creal.

Lemma Rminus_diag_uniq_sym : forall r1 r2, r2 - r1 == 0 -> r1 == r2.
Proof.
  intros; generalize (Rminus_diag_uniq r2 r1 H); clear H; intro H; rewrite H;
    ring.
Qed.
Hint Immediate Rminus_diag_uniq_sym: creal.

Lemma Rplus_minus : forall r1 r2, r1 + (r2 - r1) == r2.
Proof.
  intros; ring.
Qed.
Hint Resolve Rplus_minus: creal.

(**********)
Lemma Rmult_minus_distr_l :
  forall r1 r2 r3, r1 * (r2 - r3) == r1 * r2 - r1 * r3.
Proof.
  intros; ring.
Qed.


(*********************************************************)
(** ** Order and addition                                *)
(*********************************************************)

(** *** Compatibility *)

(** Remark: [Rplus_lt_compat_l] is an axiom *)

Lemma Rplus_gt_compat_l : forall r r1 r2, r1 > r2 -> r + r1 > r + r2.
Proof.
  intros. apply Rplus_lt_compat_l. apply H.
Qed.
Hint Resolve Rplus_gt_compat_l: creal.

(**********)
Lemma Rplus_lt_compat_r : forall r r1 r2, r1 < r2 -> r1 + r < r2 + r.
Proof.
  intros.
  rewrite (Rplus_comm r1 r); rewrite (Rplus_comm r2 r).
  apply Rplus_lt_compat_l. exact H.
Qed.
Hint Resolve Rplus_lt_compat_r: creal.

Lemma Rplus_gt_compat_r : forall r r1 r2, r1 > r2 -> r1 + r > r2 + r.
Proof. do 3 intro; apply Rplus_lt_compat_r. Qed.

(**********)

Lemma Rplus_lt_reg_r : forall r r1 r2, r1 + r < r2 + r -> r1 < r2.
Proof.
  intros.
  apply (Rplus_lt_reg_l r).
  now rewrite 2!(Rplus_comm r).
Qed.

Lemma Rplus_le_compat_l : forall r r1 r2, r1 <= r2 -> r + r1 <= r + r2.
Proof.
  intros. intro abs. apply Rplus_lt_reg_l in abs. contradiction.
Qed.

Lemma Rplus_ge_compat_l : forall r r1 r2, r1 >= r2 -> r + r1 >= r + r2.
Proof.
  intros. apply Rplus_le_compat_l. apply H.
Qed.
Hint Resolve Rplus_ge_compat_l: creal.

(**********)
Lemma Rplus_le_compat_r : forall r r1 r2, r1 <= r2 -> r1 + r <= r2 + r.
Proof.
  intros. intro abs. apply Rplus_lt_reg_r in abs. contradiction.
Qed.

Hint Resolve Rplus_le_compat_l Rplus_le_compat_r: creal.

Lemma Rplus_ge_compat_r : forall r r1 r2, r1 >= r2 -> r1 + r >= r2 + r.
Proof.
  intros. apply Rplus_le_compat_r. apply H.
Qed.

(*********)
Lemma Rplus_lt_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros; apply Rlt_trans with (r2 + r3); auto with creal.
Qed.
Hint Immediate Rplus_lt_compat: creal.

Lemma Rplus_le_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
  intros; apply Rle_trans with (r2 + r3); auto with creal.
Qed.
Hint Immediate Rplus_le_compat: creal.

Lemma Rplus_gt_compat :
  forall r1 r2 r3 r4, r1 > r2 -> r3 > r4 -> r1 + r3 > r2 + r4.
Proof.
  intros. apply Rplus_lt_compat; assumption.
Qed.

Lemma Rplus_ge_compat :
  forall r1 r2 r3 r4, r1 >= r2 -> r3 >= r4 -> r1 + r3 >= r2 + r4.
Proof.
  intros. apply Rplus_le_compat; assumption.
Qed.

(*********)
Lemma Rplus_lt_le_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 <= r4 -> r1 + r3 < r2 + r4.
Proof.
  intros; apply Rlt_le_trans with (r2 + r3); auto with creal.
Qed.

Lemma Rplus_le_lt_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros; apply Rle_lt_trans with (r2 + r3); auto with creal.
Qed.

Hint Immediate Rplus_lt_le_compat Rplus_le_lt_compat: creal.

Lemma Rplus_gt_ge_compat :
  forall r1 r2 r3 r4, r1 > r2 -> r3 >= r4 -> r1 + r3 > r2 + r4.
Proof.
  intros. apply Rplus_lt_le_compat; assumption.
Qed.

Lemma Rplus_ge_gt_compat :
  forall r1 r2 r3 r4, r1 >= r2 -> r3 > r4 -> r1 + r3 > r2 + r4.
Proof.
  intros. apply Rplus_le_lt_compat; assumption.
Qed.

(**********)
Lemma Rplus_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 + r2.
Proof.
  intros. apply (Rlt_trans _ (r1+0)). rewrite Rplus_0_r. exact H.
  apply Rplus_lt_compat_l. exact H0.
Qed.

Lemma Rplus_le_lt_0_compat : forall r1 r2, 0 <= r1 -> 0 < r2 -> 0 < r1 + r2.
Proof.
  intros. apply (Rle_lt_trans _ (r1+0)). rewrite Rplus_0_r. exact H.
  apply Rplus_lt_compat_l. exact H0.
Qed.

Lemma Rplus_lt_le_0_compat : forall r1 r2, 0 < r1 -> 0 <= r2 -> 0 < r1 + r2.
Proof.
  intros x y; intros; rewrite <- Rplus_comm; apply Rplus_le_lt_0_compat;
    assumption.
Qed.

Lemma Rplus_le_le_0_compat : forall r1 r2, 0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2.
Proof.
  intros. apply (Rle_trans _ (r1+0)). rewrite Rplus_0_r. exact H.
  apply Rplus_le_compat_l. exact H0.
Qed.

(**********)
Lemma sum_inequa_Rle_lt :
  forall a x b c y d,
    a <= x -> x < b -> c < y -> y <= d -> a + c < x + y < b + d.
Proof.
  intros; split.
  apply Rlt_le_trans with (a + y); auto with creal.
  apply Rlt_le_trans with (b + y); auto with creal.
Qed.

(** *** Cancellation *)

Lemma Rplus_le_reg_l : forall r r1 r2, r + r1 <= r + r2 -> r1 <= r2.
Proof.
  intros. intro abs. apply (Rplus_lt_compat_l r) in abs. contradiction.
Qed.

Lemma Rplus_le_reg_r : forall r r1 r2, r1 + r <= r2 + r -> r1 <= r2.
Proof.
  intros.
  apply (Rplus_le_reg_l r).
  now rewrite 2!(Rplus_comm r).
Qed.

Lemma Rplus_gt_reg_l : forall r r1 r2, r + r1 > r + r2 -> r1 > r2.
Proof.
  unfold CRealGt; intros; apply (Rplus_lt_reg_l r r2 r1 H).
Qed.

Lemma Rplus_ge_reg_l : forall r r1 r2, r + r1 >= r + r2 -> r1 >= r2.
Proof.
  intros; apply Rle_ge; apply Rplus_le_reg_l with r; auto with creal.
Qed.

(**********)
Lemma Rplus_le_reg_pos_r :
  forall r1 r2 r3, 0 <= r2 -> r1 + r2 <= r3 -> r1 <= r3.
Proof.
  intros. apply (Rle_trans _ (r1+r2)). 2: exact H0.
  rewrite <- (Rplus_0_r r1), Rplus_assoc.
  apply Rplus_le_compat_l. rewrite Rplus_0_l. exact H.
Qed.

Lemma Rplus_lt_reg_pos_r : forall r1 r2 r3, 0 <= r2 -> r1 + r2 < r3 -> r1 < r3.
Proof.
  intros. apply (Rle_lt_trans _ (r1+r2)). 2: exact H0.
  rewrite <- (Rplus_0_r r1), Rplus_assoc.
  apply Rplus_le_compat_l. rewrite Rplus_0_l. exact H.
Qed.

Lemma Rplus_ge_reg_neg_r :
  forall r1 r2 r3, 0 >= r2 -> r1 + r2 >= r3 -> r1 >= r3.
Proof.
  intros. apply (Rge_trans _ (r1+r2)). 2: exact H0.
  apply Rle_ge. rewrite <- (Rplus_0_r r1), Rplus_assoc.
  apply Rplus_le_compat_l. rewrite Rplus_0_l. exact H.
Qed.

Lemma Rplus_gt_reg_neg_r : forall r1 r2 r3, 0 >= r2 -> r1 + r2 > r3 -> r1 > r3.
Proof.
  intros. apply (Rlt_le_trans _ (r1+r2)). exact H0.
  rewrite <- (Rplus_0_r r1), Rplus_assoc.
  apply Rplus_le_compat_l. rewrite Rplus_0_l. exact H.
Qed.

(***********)
Lemma Rplus_eq_0_l :
  forall r1 r2, 0 <= r1 -> 0 <= r2 -> r1 + r2 == 0 -> r1 == 0.
Proof.
  intros. split.
  - intro abs. rewrite <- (Rplus_opp_r r1) in H1.
    apply Rplus_eq_reg_l in H1. rewrite H1 in H0. clear H1.
    apply (Rplus_le_compat_l r1) in H0.
    rewrite Rplus_opp_r in H0. rewrite Rplus_0_r in H0.
    contradiction.
  - intro abs. clear H. rewrite <- (Rplus_opp_r r1) in H1.
    apply Rplus_eq_reg_l in H1. rewrite H1 in H0. clear H1.
    apply (Rplus_le_compat_l r1) in H0.
    rewrite Rplus_opp_r in H0. rewrite Rplus_0_r in H0.
    contradiction.
Qed.

Lemma Rplus_eq_R0 :
  forall r1 r2, 0 <= r1 -> 0 <= r2 -> r1 + r2 == 0 -> r1 == 0 /\ r2 == 0.
Proof.
  intros a b; split.
  apply Rplus_eq_0_l with b; auto with creal.
  apply Rplus_eq_0_l with a; auto with creal.
  rewrite Rplus_comm; auto with creal.
Qed.


(*********************************************************)
(** ** Order and opposite                                *)
(*********************************************************)

(** *** Contravariant compatibility *)

Lemma Ropp_gt_lt_contravar : forall r1 r2, r1 > r2 -> - r1 < - r2.
Proof.
  unfold CRealGt; intros.
  apply (Rplus_lt_reg_l (r2 + r1)).
  setoid_replace (r2 + r1 + - r1) with r2 by ring.
  setoid_replace (r2 + r1 + - r2) with r1 by ring.
  exact H.
Qed.
Hint Resolve Ropp_gt_lt_contravar : creal.

Lemma Ropp_lt_gt_contravar : forall r1 r2, r1 < r2 -> - r1 > - r2.
Proof.
  intros. apply Ropp_gt_lt_contravar. exact H.
Qed.
Hint Resolve Ropp_lt_gt_contravar: creal.

(**********)
Lemma Ropp_lt_contravar : forall r1 r2, r2 < r1 -> - r1 < - r2.
Proof.
  auto with creal.
Qed.
Hint Resolve Ropp_lt_contravar: creal.

Lemma Ropp_gt_contravar : forall r1 r2, r2 > r1 -> - r1 > - r2.
Proof. auto with creal. Qed.

(**********)

Lemma Ropp_lt_cancel : forall r1 r2, - r2 < - r1 -> r1 < r2.
Proof.
  intros x y H'.
  rewrite <- (Ropp_involutive x); rewrite <- (Ropp_involutive y);
    auto with creal.
Qed.
Hint Immediate Ropp_lt_cancel: creal.

Lemma Ropp_gt_cancel : forall r1 r2, - r2 > - r1 -> r1 > r2.
Proof.
  intros. apply Ropp_lt_cancel. apply H.
Qed.

Lemma Ropp_le_ge_contravar : forall r1 r2, r1 <= r2 -> - r1 >= - r2.
Proof.
  intros. intro abs. apply Ropp_lt_cancel in abs. contradiction.
Qed.
Hint Resolve Ropp_le_ge_contravar: creal.

Lemma Ropp_ge_le_contravar : forall r1 r2, r1 >= r2 -> - r1 <= - r2.
Proof.
  intros. intro abs. apply Ropp_lt_cancel in abs. contradiction.
Qed.
Hint Resolve Ropp_ge_le_contravar: creal.

(**********)
Lemma Ropp_le_contravar : forall r1 r2, r2 <= r1 -> - r1 <= - r2.
Proof.
  intros. intro abs. apply Ropp_lt_cancel in abs. contradiction.
Qed.
Hint Resolve Ropp_le_contravar: creal.

Lemma Ropp_ge_contravar : forall r1 r2, r2 >= r1 -> - r1 >= - r2.
Proof.
  intros. apply Ropp_le_contravar. apply H.
Qed.

(**********)
Lemma Ropp_0_lt_gt_contravar : forall r, 0 < r -> 0 > - r.
Proof.
  intros; setoid_replace 0 with (-0); auto with creal. ring.
Qed.
Hint Resolve Ropp_0_lt_gt_contravar: creal.

Lemma Ropp_0_gt_lt_contravar : forall r, 0 > r -> 0 < - r.
Proof.
  intros; setoid_replace 0 with (-0); auto with creal. ring.
Qed.
Hint Resolve Ropp_0_gt_lt_contravar: creal.

(**********)
Lemma Ropp_lt_gt_0_contravar : forall r, r > 0 -> - r < 0.
Proof.
  intros; rewrite <- Ropp_0; auto with creal.
Qed.
Hint Resolve Ropp_lt_gt_0_contravar: creal.

Lemma Ropp_gt_lt_0_contravar : forall r, r < 0 -> - r > 0.
Proof.
  intros; rewrite <- Ropp_0; auto with creal.
Qed.
Hint Resolve Ropp_gt_lt_0_contravar: creal.

(**********)
Lemma Ropp_0_le_ge_contravar : forall r, 0 <= r -> 0 >= - r.
Proof.
  intros; setoid_replace 0 with (-0); auto with creal. ring.
Qed.
Hint Resolve Ropp_0_le_ge_contravar: creal.

Lemma Ropp_0_ge_le_contravar : forall r, 0 >= r -> 0 <= - r.
Proof.
  intros; setoid_replace 0 with (-0); auto with creal. ring.
Qed.
Hint Resolve Ropp_0_ge_le_contravar: creal.

(** *** Cancellation *)

Lemma Ropp_le_cancel : forall r1 r2, - r2 <= - r1 -> r1 <= r2.
Proof.
  intros. intro abs. apply Ropp_lt_gt_contravar in abs. contradiction.
Qed.
Hint Immediate Ropp_le_cancel: creal.

Lemma Ropp_ge_cancel : forall r1 r2, - r2 >= - r1 -> r1 >= r2.
Proof.
  intros. apply Ropp_le_cancel. apply H.
Qed.

(*********************************************************)
(** ** Order and multiplication                          *)
(*********************************************************)

(** Remark: [Rmult_lt_compat_l] is an axiom *)

(** *** Covariant compatibility *)

Lemma Rmult_lt_compat_r : forall r r1 r2, 0 < r -> r1 < r2 -> r1 * r < r2 * r.
Proof.
  intros; rewrite (Rmult_comm r1 r); rewrite (Rmult_comm r2 r); auto with creal.
Qed.
Hint Resolve Rmult_lt_compat_r : core.

Lemma Rmult_gt_compat_r : forall r r1 r2, r > 0 -> r1 > r2 -> r1 * r > r2 * r.
Proof.
  intros. apply Rmult_lt_compat_r; assumption.
Qed.

Lemma Rmult_gt_compat_l : forall r r1 r2, r > 0 -> r1 > r2 -> r * r1 > r * r2.
Proof.
  intros. apply Rmult_lt_compat_l; assumption.
Qed.

Lemma Rmult_gt_0_lt_compat :
  forall r1 r2 r3 r4,
    r3 > 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros; apply Rlt_trans with (r2 * r3); auto with creal.
Qed.

(*********)
Lemma Rmult_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 * r2.
Proof.
  intros; setoid_replace 0 with (0 * r2); auto with creal.
  rewrite Rmult_0_l. reflexivity.
Qed.

Lemma Rmult_gt_0_compat : forall r1 r2, r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof.
  apply Rmult_lt_0_compat.
Qed.

(** *** Contravariant compatibility *)

Lemma Rmult_lt_gt_compat_neg_l :
  forall r r1 r2, r < 0 -> r1 < r2 -> r * r1 > r * r2.
Proof.
  intros; setoid_replace r with (- - r); auto with creal.
  rewrite (Ropp_mult_distr_l_reverse (- r));
    rewrite (Ropp_mult_distr_l_reverse (- r)).
  apply Ropp_lt_gt_contravar; auto with creal.
  rewrite Ropp_involutive. reflexivity.
Qed.

(** *** Cancellation *)

Lemma Rinv_0_lt_compat : forall r (rpos : 0 < r), 0 < (/ r) (or_intror rpos).
Proof.
  intros. apply CRinv_0_lt_compat. exact rpos.
Qed.

Lemma Rmult_lt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof.
  intros z x y H H0.
  apply (Rmult_lt_compat_l ((/z) (or_intror H))) in H0.
  repeat rewrite <- Rmult_assoc in H0. rewrite Rinv_l in H0.
  repeat rewrite Rmult_1_l in H0. apply H0.
  apply Rinv_0_lt_compat.
Qed.

Lemma Rmult_lt_reg_r : forall r r1 r2, 0 < r -> r1 * r < r2 * r -> r1 < r2.
Proof.
  intros.
  apply Rmult_lt_reg_l with r.
  exact H.
  now rewrite 2!(Rmult_comm r).
Qed.

Lemma Rmult_gt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof.
  intros. apply Rmult_lt_reg_l in H0; assumption.
Qed.

Lemma Rmult_le_reg_l : forall r r1 r2, 0 < r -> r * r1 <= r * r2 -> r1 <= r2.
Proof.
  intros. intro abs. apply (Rmult_lt_compat_l r) in abs.
  contradiction. apply H.
Qed.

Lemma Rmult_le_reg_r : forall r r1 r2, 0 < r -> r1 * r <= r2 * r -> r1 <= r2.
Proof.
  intros.
  apply Rmult_le_reg_l with r.
  exact H.
  now rewrite 2!(Rmult_comm r).
Qed.

(*********************************************************)
(** ** Order and substraction                            *)
(*********************************************************)

Lemma Rlt_minus : forall r1 r2, r1 < r2 -> r1 - r2 < 0.
Proof.
  intros; apply (Rplus_lt_reg_l r2).
  setoid_replace (r2 + (r1 - r2)) with r1 by ring.
  now rewrite Rplus_0_r.
Qed.
Hint Resolve Rlt_minus: creal.

Lemma Rgt_minus : forall r1 r2, r1 > r2 -> r1 - r2 > 0.
Proof.
  intros; apply (Rplus_lt_reg_l r2).
  setoid_replace (r2 + (r1 - r2)) with r1 by ring.
  now rewrite Rplus_0_r.
Qed.

Lemma Rlt_Rminus : forall a b, a < b -> 0 < b - a.
Proof.
  intros a b; apply Rgt_minus.
Qed.

(**********)
Lemma Rle_minus : forall r1 r2, r1 <= r2 -> r1 - r2 <= 0.
Proof.
  intros. intro abs. apply (Rplus_lt_compat_l r2) in abs.
  ring_simplify in abs. contradiction.
Qed.

Lemma Rge_minus : forall r1 r2, r1 >= r2 -> r1 - r2 >= 0.
Proof.
  intros. intro abs. apply (Rplus_lt_compat_l r2) in abs.
  ring_simplify in abs. contradiction.
Qed.

(**********)
Lemma Rminus_lt : forall r1 r2, r1 - r2 < 0 -> r1 < r2.
Proof.
  intros. rewrite <- (Rplus_opp_r r2) in H.
  apply Rplus_lt_reg_r in H. exact H.
Qed.

Lemma Rminus_gt : forall r1 r2, r1 - r2 > 0 -> r1 > r2.
Proof.
  intros. rewrite <- (Rplus_opp_r r2) in H.
  apply Rplus_lt_reg_r in H. exact H.
Qed.

Lemma Rminus_gt_0_lt : forall a b, 0 < b - a -> a < b.
Proof. intro; intro; apply Rminus_gt. Qed.

(**********)
Lemma Rminus_le : forall r1 r2, r1 - r2 <= 0 -> r1 <= r2.
Proof.
  intros. rewrite <- (Rplus_opp_r r2) in H.
  apply Rplus_le_reg_r in H. exact H.
Qed.

Lemma Rminus_ge : forall r1 r2, r1 - r2 >= 0 -> r1 >= r2.
Proof.
  intros. rewrite <- (Rplus_opp_r r2) in H.
  apply Rplus_le_reg_r in H. exact H.
Qed.

(**********)
Lemma tech_Rplus : forall r s, 0 <= r -> 0 < s -> r + s <> 0.
Proof.
  intros; apply not_eq_sym; apply Rlt_not_eq.
  rewrite Rplus_comm; setoid_replace 0 with (0 + 0); auto with creal. ring.
Qed.
Hint Immediate tech_Rplus: creal.

(*********************************************************)
(** ** Zero is less than one                             *)
(*********************************************************)

Lemma Rle_0_1 : 0 <= 1.
Proof.
  intro abs. apply (Rlt_asym 0 1).
  apply Rlt_0_1. apply abs.
Qed.


(*********************************************************)
(** ** Inverse                                           *)
(*********************************************************)

Lemma Rinv_1 : forall nz : 1 # 0, (/ 1) nz == 1.
Proof.
  intros. rewrite <- (Rmult_1_l ((/1) nz)). rewrite Rinv_r.
  reflexivity. right. apply Rlt_0_1.
Qed.
Hint Resolve Rinv_1: creal.

(*********)
Lemma Ropp_inv_permute : forall r (rnz : r # 0) (ronz : (-r) # 0),
    - (/ r) rnz == (/ - r) ronz.
Proof.
  intros.
  apply (Rmult_eq_reg_l (-r)). rewrite Rinv_r.
  rewrite <- Ropp_mult_distr_l. rewrite <- Ropp_mult_distr_r.
  rewrite Ropp_involutive. rewrite Rinv_r. reflexivity.
  exact rnz. exact ronz. exact ronz.
Qed.

(*********)
Lemma Rinv_neq_0_compat : forall r (rnz : r # 0), ((/ r) rnz) # 0.
Proof.
  intros. destruct rnz. left.
  assert (0 < (/-r) (or_intror (Ropp_0_gt_lt_contravar _ c))).
  { apply Rinv_0_lt_compat. }
  rewrite <- (Ropp_inv_permute _ (or_introl c)) in H.
  apply Ropp_lt_cancel. rewrite Ropp_0. exact H.
  right. apply Rinv_0_lt_compat.
Qed.
Hint Resolve Rinv_neq_0_compat: creal.

(*********)
Lemma Rinv_involutive : forall r (rnz : r # 0) (rinz : ((/ r) rnz) # 0),
    (/ ((/ r) rnz)) rinz == r.
Proof.
  intros. apply (Rmult_eq_reg_l ((/r) rnz)). rewrite Rinv_r.
  rewrite Rinv_l. reflexivity. exact rinz. exact rinz.
Qed.
Hint Resolve Rinv_involutive: creal.

(*********)
Lemma Rinv_mult_distr :
  forall r1 r2 (r1nz : r1 # 0) (r2nz : r2 # 0) (rmnz : (r1*r2) # 0),
    (/ (r1 * r2)) rmnz == (/ r1) r1nz * (/ r2) r2nz.
Proof.
  intros. apply (Rmult_eq_reg_l r1). 2: exact r1nz.
  rewrite <- Rmult_assoc. rewrite Rinv_r. rewrite Rmult_1_l.
  apply (Rmult_eq_reg_l r2). 2: exact r2nz.
  rewrite Rinv_r. rewrite <- Rmult_assoc.
  rewrite (Rmult_comm r2 r1). rewrite Rinv_r.
  reflexivity. exact rmnz. exact r2nz. exact r1nz.
Qed.

Lemma Rinv_r_simpl_r : forall r1 r2 (rnz : r1 # 0), r1 * (/ r1) rnz * r2 == r2.
Proof.
  intros; transitivity (1 * r2); auto with creal.
  rewrite Rinv_r; auto with creal. rewrite Rmult_1_l. reflexivity.
Qed.

Lemma Rinv_r_simpl_l : forall r1 r2 (rnz : r1 # 0),
    r2 * r1 * (/ r1) rnz == r2.
Proof.
  intros. rewrite Rmult_assoc. rewrite Rinv_r, Rmult_1_r.
  reflexivity. exact rnz.
Qed.

Lemma Rinv_r_simpl_m : forall r1 r2 (rnz : r1 # 0),
    r1 * r2 * (/ r1) rnz == r2.
Proof.
  intros. rewrite Rmult_comm, <- Rmult_assoc, Rinv_l, Rmult_1_l.
  reflexivity.
Qed.
Hint Resolve Rinv_r_simpl_l Rinv_r_simpl_r Rinv_r_simpl_m: creal.

(*********)
Lemma Rinv_mult_simpl :
  forall r1 r2 r3 (r1nz : r1 # 0) (r2nz : r2 # 0),
    r1 * (/ r2) r2nz * (r3 * (/ r1) r1nz) == r3 * (/ r2) r2nz.
Proof.
  intros a b c; intros.
  transitivity (a * (/ a) r1nz * (c * (/ b) r2nz)); auto with creal.
  ring.
Qed.

Lemma Rinv_eq_compat : forall x y (rxnz : x # 0) (rynz : y # 0),
    x == y
    -> (/ x) rxnz == (/ y) rynz.
Proof.
  intros. apply (Rmult_eq_reg_l x). rewrite Rinv_r.
  rewrite H. rewrite Rinv_r. reflexivity.
  exact rynz. exact rxnz. exact rxnz.
Qed.


(*********************************************************)
(** ** Order and inverse                                 *)
(*********************************************************)

Lemma Rinv_lt_0_compat : forall r (rneg : r < 0), (/ r) (or_introl rneg) < 0.
Proof.
  intros. assert (0 < (/-r) (or_intror (Ropp_0_gt_lt_contravar r rneg))).
  { apply Rinv_0_lt_compat. }
  rewrite <- Ropp_inv_permute in H. rewrite <- Ropp_0 in H.
  apply Ropp_lt_cancel in H. apply H.
Qed.
Hint Resolve Rinv_lt_0_compat: creal.



(*********************************************************)
(** ** Miscellaneous                                     *)
(*********************************************************)

(**********)
Lemma Rle_lt_0_plus_1 : forall r, 0 <= r -> 0 < r + 1.
Proof.
  intros. apply (Rle_lt_trans _ (r+0)). rewrite Rplus_0_r.
  exact H. apply Rplus_lt_compat_l. apply Rlt_0_1.
Qed.
Hint Resolve Rle_lt_0_plus_1: creal.

(**********)
Lemma Rlt_plus_1 : forall r, r < r + 1.
Proof.
  intro r. rewrite <- Rplus_0_r. rewrite Rplus_assoc.
  apply Rplus_lt_compat_l. rewrite Rplus_0_l. exact Rlt_0_1.
Qed.
Hint Resolve Rlt_plus_1: creal.

(**********)
Lemma tech_Rgt_minus : forall r1 r2, 0 < r2 -> r1 > r1 - r2.
Proof.
  intros. apply (Rplus_lt_reg_r r2).
  unfold Rminus, CRminus; rewrite Rplus_assoc, Rplus_opp_l.
  apply Rplus_lt_compat_l. exact H.
Qed.

(*********************************************************)
(** ** Injection from [N] to [R]                         *)
(*********************************************************)

(**********)
Lemma S_INR : forall n:nat, INR (S n) == INR n + 1.
Proof.
  intro; destruct n. rewrite Rplus_0_l. reflexivity. reflexivity.
Qed.

Lemma lt_INR : forall n m:nat, (n < m)%nat -> INR n < INR m.
Proof.
  induction m.
  - intros. inversion H.
  - intros. unfold lt in H. apply le_S_n in H. destruct m.
    inversion H. apply Rlt_0_1. apply Nat.le_succ_r in H. destruct H.
    rewrite S_INR. apply (Rlt_trans _ (INR (S m) + 0)).
    rewrite Rplus_comm, Rplus_0_l. apply IHm.
    apply le_n_S. exact H.
    apply Rplus_lt_compat_l. exact Rlt_0_1.
    subst n. rewrite (S_INR (S m)). rewrite <- (Rplus_0_l).
    rewrite (Rplus_comm 0), Rplus_assoc.
    apply Rplus_lt_compat_l. rewrite Rplus_0_l.
    exact Rlt_0_1.
Qed.

(**********)
Lemma S_O_plus_INR : forall n:nat, INR (1 + n) == INR 1 + INR n.
Proof.
  intros; destruct n.
  - rewrite Rplus_comm, Rplus_0_l. reflexivity.
  - rewrite Rplus_comm. reflexivity.
Qed.

(**********)
Lemma plus_INR : forall n m:nat, INR (n + m) == INR n + INR m.
Proof.
  intros n m; induction  n as [| n Hrecn].
  - rewrite Rplus_0_l. reflexivity.
  - replace (S n + m)%nat with (S (n + m)); auto with arith.
    repeat rewrite S_INR.
    rewrite Hrecn; ring.
Qed.

(**********)
Lemma minus_INR : forall n m:nat, (m <= n)%nat -> INR (n - m) == INR n - INR m.
Proof.
  intros n m le; pattern m, n; apply le_elim_rel.
  intros. rewrite <- minus_n_O. simpl.
  unfold Rminus, CRminus. rewrite Ropp_0, Rplus_0_r. reflexivity.
  intros; repeat rewrite S_INR; simpl.
  unfold CReal_minus. rewrite H0. ring. exact le.
Qed.

(*********)
Lemma mult_INR : forall n m:nat, INR (n * m) == INR n * INR m.
Proof.
  intros n m; induction  n as [| n Hrecn].
  - rewrite Rmult_0_l. reflexivity.
  - intros; repeat rewrite S_INR; simpl.
    rewrite plus_INR. rewrite Hrecn; ring.
Qed.

Lemma INR_IPR : forall p, INR (Pos.to_nat p) == IPR p.
Proof.
  assert (H: forall p, 2 * INR (Pos.to_nat p) == IPR_2 p).
  { induction p as [p|p|].
    - unfold IPR_2; rewrite Pos2Nat.inj_xI, S_INR, mult_INR, <- IHp.
      rewrite Rplus_comm. reflexivity.
    - unfold IPR_2; now rewrite Pos2Nat.inj_xO, mult_INR, <- IHp.
    - apply Rmult_1_r. }
  intros [p|p|] ; unfold IPR.
  rewrite Pos2Nat.inj_xI, S_INR, mult_INR, <- H.
  apply Rplus_comm.
  now rewrite Pos2Nat.inj_xO, mult_INR, <- H.
  easy.
Qed.

Fixpoint pow (r:R) (n:nat) : R :=
  match n with
    | O => 1
    | S n => r * (pow r n)
  end.

Lemma Rpow_eq_compat : forall (x y : R) (n : nat),
    x == y -> pow x n == pow y n.
Proof.
  intro x. induction n.
  - reflexivity.
  - intros. simpl. rewrite IHn, H. reflexivity. exact H.
Qed.

Lemma pow_INR (m n: nat) :  INR (m ^ n) == pow (INR m) n.
Proof. now induction n as [|n IHn];[ | simpl; rewrite mult_INR, IHn]. Qed.

(*********)
Lemma lt_0_INR : forall n:nat, (0 < n)%nat -> 0 < INR n.
Proof.
  simple induction 1; intros. apply Rlt_0_1.
  rewrite S_INR. apply (Rlt_trans _ (INR m)). apply H1. apply Rlt_plus_1.
Qed.
Hint Resolve lt_0_INR: creal.

Lemma lt_1_INR : forall n:nat, (1 < n)%nat -> 1 < INR n.
Proof.
  apply lt_INR.
Qed.
Hint Resolve lt_1_INR: creal.

(**********)
Lemma pos_INR_nat_of_P : forall p:positive, 0 < INR (Pos.to_nat p).
Proof.
  intro; apply lt_0_INR.
  simpl; auto with creal.
  apply Pos2Nat.is_pos.
Qed.
Hint Resolve pos_INR_nat_of_P: creal.

(**********)
Lemma pos_INR : forall n:nat, 0 <= INR n.
Proof.
  intro n; case n.
  simpl; auto with creal.
  auto with arith creal.
Qed.
Hint Resolve pos_INR: creal.

Lemma INR_lt : forall n m:nat, INR n < INR m -> (n < m)%nat.
Proof.
  intros n m. revert n.
  induction m ; intros n H.
  - elim (Rlt_irrefl 0).
    apply Rle_lt_trans with (2 := H).
    apply pos_INR.
  - destruct n as [|n].
    apply Nat.lt_0_succ.
    apply lt_n_S, IHm.
    rewrite 2!S_INR in H.
    apply Rplus_lt_reg_r with (1 := H).
Qed.
Hint Resolve INR_lt: creal.

(*********)
Lemma le_INR : forall n m:nat, (n <= m)%nat -> INR n <= INR m.
Proof.
  simple induction 1; intros; auto with creal.
  rewrite S_INR.
  apply Rle_trans with (INR m0); auto with creal.
Qed.
Hint Resolve le_INR: creal.

(**********)
Lemma INR_not_0 : forall n:nat, INR n <> 0 -> n <> 0%nat.
Proof.
  red; intros n H H1.
  apply H.
  rewrite H1; trivial.
Qed.
Hint Immediate INR_not_0: creal.

(**********)
Lemma not_0_INR : forall n:nat, n <> 0%nat -> 0 < INR n.
Proof.
  intro n; case n.
  intro; absurd (0%nat = 0%nat); trivial.
  intros; rewrite S_INR.
  apply (Rlt_le_trans _ (0 + 1)). rewrite Rplus_0_l. apply Rlt_0_1.
  apply Rplus_le_compat_r. apply pos_INR.
Qed.
Hint Resolve not_0_INR: creal.

Lemma not_INR : forall n m:nat, n <> m -> INR n # INR m.
Proof.
  intros n m H; case (le_or_lt n m); intros H1.
  case (le_lt_or_eq _ _ H1); intros H2.
  left. apply lt_INR. exact H2. contradiction.
  right. apply lt_INR. exact H1.
Qed.
Hint Resolve not_INR: creal.

Lemma INR_eq : forall n m:nat, INR n == INR m -> n = m.
Proof.
  intros n m HR.
  destruct (dec_eq_nat n m) as [H|H].
  exact H. exfalso.
  apply not_INR in H. destruct HR,H; contradiction.
Qed.
Hint Resolve INR_eq: creal.

Lemma INR_le : forall n m:nat, INR n <= INR m -> (n <= m)%nat.
Proof.
  intros n m. revert n.
  induction m ; intros n H.
  - destruct n. apply le_refl. exfalso.
    rewrite S_INR in H.
    assert (0 + 1 <= 0). apply (Rle_trans _ (INR n + 1)).
    apply Rplus_le_compat_r. apply pos_INR. apply H.
    rewrite Rplus_0_l in H0. apply H0. apply Rlt_0_1.
  - destruct n as [|n]. apply le_0_n.
    apply le_n_S, IHm.
    rewrite 2!S_INR in H.
    apply Rplus_le_reg_r in H. apply H.
Qed.
Hint Resolve INR_le: creal.

Lemma not_1_INR : forall n:nat, n <> 1%nat -> INR n # 1.
Proof.
  intros n.
  apply not_INR.
Qed.
Hint Resolve not_1_INR: creal.

(*********************************************************)
(** ** Injection from [Z] to [R]                         *)
(*********************************************************)

Lemma IPR_pos : forall p:positive, 0 < IPR p.
Proof.
  intro p. rewrite <- INR_IPR. apply (lt_INR 0), Pos2Nat.is_pos.
Qed.

Lemma IPR_double : forall p:positive, IPR (2*p) == 2 * IPR p.
Proof.
  intro p. destruct p; try reflexivity.
  rewrite Rmult_1_r. reflexivity.
Qed.

Lemma INR_IZR_INZ : forall n:nat, INR n == IZR (Z.of_nat n).
Proof.
  intros [|n].
  easy.
  simpl Z.of_nat. unfold IZR.
  now rewrite <- INR_IPR, SuccNat2Pos.id_succ.
Qed.

Lemma plus_IZR_NEG_POS :
  forall p q:positive, IZR (Zpos p + Zneg q) == IZR (Zpos p) + IZR (Zneg q).
Proof.
  intros p q; simpl. rewrite Z.pos_sub_spec.
  case Pos.compare_spec; intros H; unfold IZR.
  subst. ring.
  rewrite <- 3!INR_IPR, Pos2Nat.inj_sub.
  rewrite minus_INR.
  2: (now apply lt_le_weak, Pos2Nat.inj_lt).
  ring.
  trivial.
  rewrite <- 3!INR_IPR, Pos2Nat.inj_sub.
  rewrite minus_INR.
  2: (now apply lt_le_weak, Pos2Nat.inj_lt).
  ring. trivial.
Qed.

Lemma plus_IPR : forall n m:positive, IPR (n + m) == IPR n + IPR m.
Proof.
  intros. repeat rewrite <- INR_IPR.
  rewrite Pos2Nat.inj_add. apply plus_INR.
Qed.

(**********)
Lemma plus_IZR : forall n m:Z, IZR (n + m) == IZR n + IZR m.
Proof.
  intro z; destruct z; intro t; destruct t; intros.
  - rewrite Rplus_0_l. reflexivity.
  - rewrite Rplus_0_l. rewrite Z.add_0_l. reflexivity.
  - rewrite Rplus_0_l. reflexivity.
  - rewrite Rplus_comm,Rplus_0_l. reflexivity.
  - rewrite <- Pos2Z.inj_add. unfold IZR. apply plus_IPR.
  - apply plus_IZR_NEG_POS.
  - rewrite Rplus_comm,Rplus_0_l, Z.add_0_r. reflexivity.
  - rewrite Z.add_comm; rewrite Rplus_comm; apply plus_IZR_NEG_POS.
  - simpl. unfold IZR. rewrite <- 3!INR_IPR, Pos2Nat.inj_add, plus_INR.
    ring.
Qed.

Lemma mult_IPR : forall n m:positive, IPR (n * m) == IPR n * IPR m.
Proof.
  intros. repeat rewrite <- INR_IPR.
  rewrite Pos2Nat.inj_mul. apply mult_INR.
Qed.

(**********)
Lemma mult_IZR : forall n m:Z, IZR (n * m) == IZR n * IZR m.
Proof.
  intros n m. destruct n.
  - rewrite Rmult_0_l. rewrite Z.mul_0_l. reflexivity.
  - destruct m. rewrite Z.mul_0_r, Rmult_0_r. reflexivity.
    simpl; unfold IZR. apply mult_IPR.
    simpl. unfold IZR. rewrite mult_IPR. ring.
  - destruct m. rewrite Z.mul_0_r, Rmult_0_r. reflexivity.
    simpl. unfold IZR. rewrite mult_IPR. ring.
    simpl. unfold IZR. rewrite mult_IPR. ring.
Qed.

Lemma pow_IZR : forall z n, pow (IZR z) n == IZR (Z.pow z (Z.of_nat n)).
Proof.
 intros z [|n];simpl; trivial. reflexivity.
 rewrite Zpower_pos_nat.
 rewrite SuccNat2Pos.id_succ. unfold Zpower_nat;simpl.
 rewrite mult_IZR.
 induction n;simpl;trivial. reflexivity.
 rewrite mult_IZR;ring[IHn].
Qed.

(**********)
Lemma succ_IZR : forall n:Z, IZR (Z.succ n) == IZR n + 1.
Proof.
  intro; unfold Z.succ; apply plus_IZR.
Qed.

(**********)
Lemma opp_IZR : forall n:Z, IZR (- n) == - IZR n.
Proof.
  intros [|z|z]; unfold IZR; simpl; auto with creal.
  ring.
  reflexivity. rewrite Ropp_involutive. reflexivity.
Qed.

Definition Ropp_Ropp_IZR := opp_IZR.

Lemma minus_IZR : forall n m:Z, IZR (n - m) == IZR n - IZR m.
Proof.
  intros; unfold Z.sub, Rminus,CRminus.
  rewrite <- opp_IZR.
  apply plus_IZR.
Qed.

(**********)
Lemma Z_R_minus : forall n m:Z, IZR n - IZR m == IZR (n - m).
Proof.
  intros z1 z2; unfold Rminus,CRminus; unfold Z.sub.
  rewrite <- (Ropp_Ropp_IZR z2); symmetry; apply plus_IZR.
Qed.

(**********)
Lemma lt_0_IZR : forall n:Z, 0 < IZR n -> (0 < n)%Z.
Proof.
  intro z; case z; simpl; intros.
  elim (Rlt_irrefl _ H).
  easy.
  elim (Rlt_not_le _ _ H).
  unfold IZR.
  rewrite <- INR_IPR.
  auto with creal.
Qed.

(**********)
Lemma lt_IZR : forall n m:Z, IZR n < IZR m -> (n < m)%Z.
Proof.
  intros z1 z2 H; apply Z.lt_0_sub.
  apply lt_0_IZR.
  rewrite <- Z_R_minus.
  exact (Rgt_minus (IZR z2) (IZR z1) H).
Qed.

(**********)
Lemma eq_IZR_R0 : forall n:Z, IZR n == 0 -> n = 0%Z.
Proof.
  intro z; destruct z; simpl; intros; auto with zarith.
  unfold IZR in H. rewrite <- INR_IPR in H.
  apply (INR_eq _ 0) in H.
  exfalso. pose proof (Pos2Nat.is_pos p).
  rewrite H in H0. inversion H0.
  unfold IZR in H. rewrite <- INR_IPR in H.
  apply (Rplus_eq_compat_r (INR (Pos.to_nat p))) in H.
  rewrite Rplus_opp_l, Rplus_0_l in H. symmetry in H.
  apply (INR_eq _ 0) in H.
  exfalso. pose proof (Pos2Nat.is_pos p).
  rewrite H in H0. inversion H0.
Qed.

(**********)
Lemma eq_IZR : forall n m:Z, IZR n == IZR m -> n = m.
Proof.
  intros z1 z2 H; generalize (Rminus_diag_eq (IZR z1) (IZR z2) H);
    rewrite (Z_R_minus z1 z2); intro; generalize (eq_IZR_R0 (z1 - z2) H0);
      intro; omega.
Qed.

Lemma IZR_lt : forall n m:Z, (n < m)%Z -> IZR n < IZR m.
Proof.
 assert (forall n:Z, Z.lt 0 n -> 0 < IZR n) as posCase.
 { intros. destruct (IZN n). apply Z.lt_le_incl. apply H.
   subst n. rewrite <- INR_IZR_INZ. apply (lt_INR 0).
   apply Nat2Z.inj_lt. apply H. }
  intros. apply (Rplus_lt_reg_r (-(IZR n))).
  pose proof minus_IZR. unfold Rminus,CRminus in H0.
  repeat rewrite <- H0. unfold Zminus.
  rewrite Z.add_opp_diag_r. apply posCase.
  rewrite (Z.add_lt_mono_l _ _ n). ring_simplify. apply H.
Qed.

(**********)
Lemma not_0_IZR : forall n:Z, n <> 0%Z -> IZR n # 0.
Proof.
  intros. destruct (Z.lt_trichotomy n 0).
  left. apply (IZR_lt n 0). exact H0.
  destruct H0. contradiction.
  right. apply (IZR_lt 0 n). exact H0.
Qed.

(*********)
Lemma le_0_IZR : forall n:Z, 0 <= IZR n -> (0 <= n)%Z.
Proof.
  intros. destruct n. discriminate. discriminate.
  exfalso. rewrite <- Ropp_0 in H. unfold IZR in H. apply H.
  apply Ropp_gt_lt_contravar. rewrite <- INR_IPR.
  apply (lt_INR 0). apply Pos2Nat.is_pos.
Qed.

(**********)
Lemma le_IZR : forall n m:Z, IZR n <= IZR m -> (n <= m)%Z.
Proof.
  intros. apply (Rplus_le_compat_r (-(IZR n))) in H.
  pose proof minus_IZR. unfold Rminus,CRminus in H0.
  repeat rewrite <- H0 in H. unfold Zminus in H.
  rewrite Z.add_opp_diag_r in H.
  apply (Z.add_le_mono_l _ _ (-n)). ring_simplify.
  rewrite Z.add_comm. apply le_0_IZR. apply H.
Qed.

(**********)
Lemma le_IZR_R1 : forall n:Z, IZR n <= 1 -> (n <= 1)%Z.
Proof.
  intros. apply (le_IZR n 1). apply H.
Qed.

(**********)
Lemma IZR_ge : forall n m:Z, (n >= m)%Z -> IZR n >= IZR m.
Proof.
  intros m n H; apply Rnot_lt_ge; red; intro.
  generalize (lt_IZR m n H0); intro; omega.
Qed.

Lemma IZR_le : forall n m:Z, (n <= m)%Z -> IZR n <= IZR m.
Proof.
  intros m n H; apply Rnot_gt_le; red; intro.
  unfold CRealGt in H0; generalize (lt_IZR n m H0); intro; omega.
Qed.

Lemma IZR_neq : forall z1 z2:Z, z1 <> z2 -> IZR z1 # IZR z2.
Proof.
  intros. destruct (Z.lt_trichotomy z1 z2).
  left. apply IZR_lt. exact H0.
  destruct H0. contradiction.
  right. apply IZR_lt. exact H0.
Qed.

Hint Extern 0 (IZR _ <= IZR _) => apply IZR_le, Zle_bool_imp_le, eq_refl : creal.
Hint Extern 0 (IZR _ >= IZR _) => apply Rle_ge, IZR_le, Zle_bool_imp_le, eq_refl : creal.
Hint Extern 0 (IZR _ <  IZR _) => apply IZR_lt, eq_refl : creal.
Hint Extern 0 (IZR _ >  IZR _) => apply IZR_lt, eq_refl : creal.
Hint Extern 0 (IZR _ <> IZR _) => apply IZR_neq, Zeq_bool_neq, eq_refl : creal.

Lemma one_IZR_lt1 : forall n:Z, -(1) < IZR n < 1 -> n = 0%Z.
Proof.
  intros z [H1 H2].
  apply Z.le_antisymm.
  apply Z.lt_succ_r; apply lt_IZR; trivial.
  change 0%Z with (Z.succ (-1)).
  apply Z.le_succ_l; apply lt_IZR; trivial.
Qed.

Lemma one_IZR_r_R1 :
  forall r (n m:Z), r < IZR n <= r + 1 -> r < IZR m <= r + 1 -> n = m.
Proof.
  intros r z x [H1 H2] [H3 H4].
  cut ((z - x)%Z = 0%Z); auto with zarith.
  apply one_IZR_lt1.
  rewrite <- Z_R_minus; split.
  setoid_replace (-(1)) with (r - (r + 1)).
  unfold CReal_minus; apply Rplus_lt_le_compat; auto with creal.
  ring.
  setoid_replace 1 with (r + 1 - r).
  unfold CReal_minus; apply Rplus_le_lt_compat; auto with creal.
  ring.
Qed.


(**********)
Lemma single_z_r_R1 :
  forall r (n m:Z),
    r < IZR n -> IZR n <= r + 1 -> r < IZR m -> IZR m <= r + 1 -> n = m.
Proof.
  intros; apply one_IZR_r_R1 with r; auto.
Qed.

(**********)
Lemma tech_single_z_r_R1 :
  forall r (n:Z),
    r < IZR n ->
    IZR n <= r + 1 ->
    (exists s : Z, s <> n /\ r < IZR s /\ IZR s <= r + 1) -> False.
Proof.
  intros r z H1 H2 [s [H3 [H4 H5]]].
  apply H3; apply single_z_r_R1 with r; trivial.
Qed.


Lemma Rmult_le_compat_l_half : forall r r1 r2,
    0 < r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros. intro abs. apply (Rmult_lt_reg_l) in abs.
  contradiction. apply H.
Qed.

Lemma INR_gen_phiZ : forall (n : nat),
    gen_phiZ 0 1 Rplus Rmult Ropp (Z.of_nat n) == INR n.
Proof.
  induction n.
  - apply Req_refl.
  - replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z.
    rewrite (gen_phiZ_add Req_rel (CRisRingExt CR) RisRing).
    rewrite IHn. clear IHn. simpl. rewrite (Rplus_comm 1).
    destruct n. rewrite Rplus_0_l. reflexivity. reflexivity.
    replace (S n) with (1 + n)%nat. 2: reflexivity.
    rewrite (Nat2Z.inj_add 1 n). reflexivity.
Qed.

Definition Rup_nat (x : R)
  : { n : nat | x < INR n }.
Proof.
  intros. destruct (CRarchimedean CR x) as [p maj].
  destruct p.
  - exists O. apply maj.
  - exists (Pos.to_nat p).
    rewrite <- positive_nat_Z, (INR_gen_phiZ (Pos.to_nat p)) in maj. exact maj.
  - exists O. apply (Rlt_trans _ _ _ maj). simpl.
    rewrite <- Ropp_0. apply Ropp_gt_lt_contravar.
    fold (gen_phiZ 0 1 Rplus Rmult Ropp (Z.pos p)).
    replace (gen_phiPOS 1 (CRplus CR) (CRmult CR) p)
      with (gen_phiZ 0 1 Rplus Rmult Ropp (Z.pos p)).
    2: reflexivity.
    rewrite <- positive_nat_Z, (INR_gen_phiZ (Pos.to_nat p)).
    apply (lt_INR 0). apply Pos2Nat.is_pos.
Qed.

Fixpoint Rarchimedean_ind (x:R) (n : Z) (p:nat) { struct p }
  : (x < IZR n < x + 2 + (INR p))
    -> { n:Z | x < IZR n /\ IZR n < x+2 }.
Proof.
  destruct p.
  - exists n. rewrite Rplus_0_r in H. exact H.
  - intros. destruct (linear_order_T (x+1+INR p) (IZR n) (x+2+INR p)).
    do 2 rewrite Rplus_assoc. apply Rplus_lt_compat_l, Rplus_lt_compat_r.
    rewrite <- (Rplus_0_r 1). apply Rplus_lt_compat_l. apply Rlt_0_1.
    + apply (Rarchimedean_ind x (n-1)%Z p). unfold Zminus.
      rewrite plus_IZR, opp_IZR.
      setoid_replace (IZR 1) with 1. 2: reflexivity.
      split.
      apply (Rplus_lt_reg_l 1). ring_simplify.
      apply (Rle_lt_trans _ (x + 1 + INR p)). 2: exact r.
      rewrite Rplus_assoc. apply Rplus_le_compat_l.
      rewrite <- (Rplus_0_r 1), Rplus_assoc. apply Rplus_le_compat_l.
      rewrite Rplus_0_l. apply (le_INR 0), le_0_n.
      apply (Rplus_lt_reg_l 1). ring_simplify.
      setoid_replace (x + 2 + INR p + 1) with (x + 2 + INR (S p)).
      apply H. rewrite S_INR. ring.
    + apply (Rarchimedean_ind x n p). split. apply H. exact r.
Qed.

Lemma Rarchimedean (x:R) : { n : Z | x < IZR n < x + 2 }.
Proof.
  destruct (Rup_nat x) as [n nmaj].
  destruct (Rup_nat (INR n + - (x + 2))) as [p pmaj].
  apply (Rplus_lt_compat_r (x+2)) in pmaj.
  rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r in pmaj.
  apply (Rarchimedean_ind x (Z.of_nat n) p).
  rewrite <- INR_IZR_INZ. split. exact nmaj.
  rewrite Rplus_comm in pmaj. exact pmaj.
Qed.

Lemma Rmult_le_0_compat : forall a b,
    0 <= a -> 0 <= b -> 0 <= a * b.
Proof.
  (* Limit of (a + 1/n)*b when n -> infty. *)
  intros. intro abs.
  assert (0 < -(a*b)) as epsPos.
  { rewrite <- Ropp_0. apply Ropp_gt_lt_contravar. apply abs. }
  pose proof (Rup_nat (b * (/ (-(a*b))) (or_intror (Ropp_0_gt_lt_contravar _ abs))))
    as [n maj].
  destruct n as [|n].
  - simpl in maj. apply (Rmult_lt_compat_r (-(a*b))) in maj.
    rewrite Rmult_0_l in maj.
    rewrite Rmult_assoc in maj. rewrite Rinv_l in maj.
    rewrite Rmult_1_r in maj. contradiction.
    apply epsPos.
  - (* n > 0 *)
    assert (0 < INR (S n)) as nPos.
    { apply (lt_INR 0). apply le_n_S, le_0_n. }
    assert (b * (/ (INR (S n))) (or_intror nPos) < -(a*b)).
    { apply (Rmult_lt_reg_r (INR (S n))). apply nPos.
      rewrite Rmult_assoc. rewrite Rinv_l.
      rewrite Rmult_1_r. apply (Rmult_lt_compat_r (-(a*b))) in maj.
      rewrite Rmult_assoc in maj. rewrite Rinv_l in maj.
      rewrite Rmult_1_r in maj. rewrite Rmult_comm.
      apply maj. exact epsPos. }
    pose proof (Rmult_le_compat_l_half (a + (/ (INR (S n))) (or_intror nPos))
                                       0 b).
    assert (a + (/ (INR (S n))) (or_intror nPos) > 0 + 0).
    apply Rplus_le_lt_compat. apply H. apply Rinv_0_lt_compat.
    rewrite Rplus_0_l in H3. specialize (H2 H3 H0).
    clear H3. rewrite Rmult_0_r in H2.
    apply H2. clear H2. rewrite Rmult_plus_distr_r.
    apply (Rplus_lt_compat_l (a*b)) in H1.
    rewrite Rplus_opp_r in H1.
    rewrite (Rmult_comm ((/ (INR (S n))) (or_intror nPos))).
    apply H1.
Qed.

Lemma Rmult_le_compat_l : forall r r1 r2,
    0 <= r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros. apply Rminus_ge. apply Rge_minus in H0.
  unfold Rminus,CRminus. rewrite Ropp_mult_distr_r.
  rewrite <- Rmult_plus_distr_l.
  apply Rmult_le_0_compat; assumption.
Qed.
Hint Resolve Rmult_le_compat_l: creal.

Lemma Rmult_le_compat_r : forall r r1 r2,
    0 <= r -> r1 <= r2 -> r1 * r <= r2 * r.
Proof.
  intros. rewrite <- (Rmult_comm r). rewrite <- (Rmult_comm r).
  apply Rmult_le_compat_l; assumption.
Qed.
Hint Resolve Rmult_le_compat_r: creal.

(*********)
Lemma Rmult_le_0_lt_compat :
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r3 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros. apply (Rle_lt_trans _ (r2 * r3)).
  apply Rmult_le_compat_r. apply H0. apply Rlt_asym.
  apply H1. apply Rmult_lt_compat_l. exact (Rle_lt_trans 0 r1 r2 H H1).
  exact H2.
Qed.

Lemma Rmult_le_compat_neg_l :
  forall r r1 r2, r <= 0 -> r1 <= r2 -> r * r2 <= r * r1.
Proof.
  intros. apply Ropp_le_cancel.
  do 2 rewrite Ropp_mult_distr_l. apply Rmult_le_compat_l.
  2: exact H0. apply Ropp_0_ge_le_contravar. exact H.
Qed.
Hint Resolve Rmult_le_compat_neg_l: creal.

Lemma Rmult_le_ge_compat_neg_l :
  forall r r1 r2, r <= 0 -> r1 <= r2 -> r * r1 >= r * r2.
Proof.
  intros; apply Rle_ge; auto with creal.
Qed.
Hint Resolve Rmult_le_ge_compat_neg_l: creal.


(**********)
Lemma Rmult_ge_compat_l :
  forall r r1 r2, r >= 0 -> r1 >= r2 -> r * r1 >= r * r2.
Proof.
  intros. apply Rmult_le_compat_l; assumption.
Qed.

Lemma Rmult_ge_compat_r :
  forall r r1 r2, r >= 0 -> r1 >= r2 -> r1 * r >= r2 * r.
Proof.
  intros. apply Rmult_le_compat_r; assumption.
Qed.


(**********)
Lemma Rmult_le_compat :
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r3 -> r1 <= r2 -> r3 <= r4 -> r1 * r3 <= r2 * r4.
Proof.
  intros x y z t H' H'0 H'1 H'2.
  apply Rle_trans with (r2 := x * t); auto with creal.
  repeat rewrite (fun x => Rmult_comm x t).
  apply Rmult_le_compat_l; auto.
  apply Rle_trans with z; auto.
Qed.
Hint Resolve Rmult_le_compat: creal.

Lemma Rmult_ge_compat :
  forall r1 r2 r3 r4,
    r2 >= 0 -> r4 >= 0 -> r1 >= r2 -> r3 >= r4 -> r1 * r3 >= r2 * r4.
Proof. auto with creal rorders. Qed.

Lemma mult_IPR_IZR : forall (n:positive) (m:Z), IZR (Z.pos n * m) == IPR n * IZR m.
Proof.
  intros. rewrite mult_IZR. apply Rmult_eq_compat_r. reflexivity.
Qed.

Definition IQR (q:Q) : R :=
  match q with
  | Qmake a b => IZR a * (/ (IPR b)) (or_intror (IPR_pos b))
  end.
Arguments IQR q%Q : simpl never.

Lemma plus_IQR : forall n m:Q, IQR (n + m) == IQR n + IQR m.
Proof.
  intros. destruct n,m; unfold Qplus,IQR; simpl.
  rewrite plus_IZR. repeat rewrite mult_IZR.
  setoid_replace ((/ IPR (Qden * Qden0)) (or_intror (IPR_pos (Qden * Qden0))))
    with ((/ IPR Qden) (or_intror (IPR_pos Qden))
          * (/ IPR Qden0) (or_intror (IPR_pos Qden0))).
  rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc. rewrite <- (Rmult_assoc (IZR (Z.pos Qden))).
  rewrite Rinv_r. rewrite Rmult_1_l.
  rewrite (Rmult_comm ((/IPR Qden) (or_intror (IPR_pos Qden)))).
  rewrite <- (Rmult_assoc (IZR (Z.pos Qden0))).
  rewrite Rinv_r. rewrite Rmult_1_l. reflexivity. unfold IZR.
  right. apply IPR_pos.
  right. apply IPR_pos.
  rewrite <- (Rinv_mult_distr
                _ _ _ _ (or_intror (Rmult_lt_0_compat _ _ (IPR_pos _) (IPR_pos _)))).
  apply Rinv_eq_compat. apply mult_IPR.
Qed.

Lemma IQR_pos : forall q:Q, Qlt 0 q -> 0 < IQR q.
Proof.
  intros. destruct q; unfold IQR.
  apply Rmult_lt_0_compat. apply (IZR_lt 0).
  unfold Qlt in H; simpl in H.
  rewrite Z.mul_1_r in H. apply H.
  apply Rinv_0_lt_compat.
Qed.

Lemma opp_IQR : forall q:Q, IQR (- q) == - IQR q.
Proof.
  intros [a b]; unfold IQR; simpl.
  rewrite Ropp_mult_distr_l.
  rewrite opp_IZR. reflexivity.
Qed.

Lemma lt_IQR : forall n m:Q, IQR n < IQR m -> (n < m)%Q.
Proof.
  intros. destruct n,m; unfold IQR in H.
  unfold Qlt; simpl. apply (Rmult_lt_compat_r (IPR Qden)) in H.
  rewrite Rmult_assoc in H. rewrite Rinv_l in H.
  rewrite Rmult_1_r in H. rewrite (Rmult_comm (IZR Qnum0)) in H.
  apply (Rmult_lt_compat_l (IPR Qden0)) in H.
  do 2 rewrite <- Rmult_assoc in H. rewrite Rinv_r in H.
  rewrite Rmult_1_l in H.
  rewrite (Rmult_comm (IZR Qnum0)) in H.
  do 2 rewrite <- mult_IPR_IZR in H. apply lt_IZR in H.
  rewrite Z.mul_comm. rewrite (Z.mul_comm Qnum0).
  apply H.
  right. rewrite <- INR_IPR. apply (lt_INR 0). apply Pos2Nat.is_pos.
  rewrite <- INR_IPR. apply (lt_INR 0). apply Pos2Nat.is_pos.
  apply IPR_pos.
Qed.

Lemma IQR_lt : forall n m:Q, Qlt n m -> IQR n < IQR m.
Proof.
  intros. apply (Rplus_lt_reg_r (-IQR n)).
  rewrite Rplus_opp_r. rewrite <- opp_IQR. rewrite <- plus_IQR.
  apply IQR_pos. apply (Qplus_lt_l _ _ n).
  ring_simplify. apply H.
Qed.

Lemma IQR_nonneg : forall q:Q, Qle 0 q -> 0 <= (IQR q).
Proof.
  intros [a b] H. unfold IQR;simpl.
  apply (Rle_trans _ (IZR a * 0)). rewrite Rmult_0_r. apply Rle_refl.
  apply Rmult_le_compat_l.
  apply (IZR_le 0 a). unfold Qle in H; simpl in H.
  rewrite Z.mul_1_r in H. apply H.
  apply Rlt_asym. apply Rinv_0_lt_compat.
Qed.

Lemma IQR_le : forall n m:Q, Qle n m -> IQR n <= IQR m.
Proof.
  intros. apply (Rplus_le_reg_r (-IQR n)).
  rewrite Rplus_opp_r. rewrite <- opp_IQR. rewrite <- plus_IQR.
  apply IQR_nonneg. apply (Qplus_le_l _ _ n).
  ring_simplify. apply H.
Qed.

Add Parametric Morphism : IQR
    with signature Qeq ==> Req
      as IQR_morph.
Proof.
  intros. destruct x,y; unfold IQR; simpl.
  unfold Qeq in H; simpl in H.
  apply (Rmult_eq_reg_r (IZR (Z.pos Qden))).
  rewrite Rmult_assoc. rewrite Rinv_l. rewrite Rmult_1_r.
  rewrite (Rmult_comm (IZR Qnum0)).
  apply (Rmult_eq_reg_l (IZR (Z.pos Qden0))).
  rewrite <- Rmult_assoc. rewrite <- Rmult_assoc. rewrite Rinv_r.
  rewrite Rmult_1_l.
  repeat rewrite <- mult_IZR.
  rewrite <- H. rewrite Zmult_comm. reflexivity.
  right. apply IPR_pos.
  right. apply (IZR_lt 0). apply Pos2Z.is_pos.
  right. apply IPR_pos.
Qed.

Fixpoint Rfloor_pos (a : R) (n : nat) { struct n }
  : 0 < a
    -> a < INR n
    -> { p : nat | INR p < a < INR p + 2 }.
Proof.
  (* Decreasing loop on n, until it is the first integer above a. *)
  intros H H0. destruct n.
  - exfalso. apply (Rlt_asym 0 a); assumption.
  - destruct n as [|p] eqn:des.
    + (* n = 1 *) exists O. split.
      apply H. rewrite Rplus_0_l. apply (Rlt_trans a (1+0)).
      rewrite Rplus_comm, Rplus_0_l. apply H0.
      apply Rplus_le_lt_compat.
      apply Rle_refl. apply Rlt_0_1.
    + (* n > 1 *)
      destruct (linear_order_T (INR p) a (INR (S p))).
      * rewrite <- Rplus_0_l, S_INR, Rplus_comm. apply Rplus_lt_compat_l.
        apply Rlt_0_1.
      * exists p. split. exact r.
        rewrite S_INR, S_INR, Rplus_assoc in H0. exact H0.
      * apply (Rfloor_pos a n H). rewrite des. apply r.
Qed.

Definition Rfloor (a : R)
  : { p : Z | IZR p < a < IZR p + 2 }.
Proof.
  destruct (linear_order_T 0 a 1 Rlt_0_1).
  - destruct (Rup_nat a). destruct (Rfloor_pos a x r r0).
    exists (Z.of_nat x0). rewrite <- INR_IZR_INZ. apply a0.
  - apply (Rplus_lt_compat_l (-a)) in r.
    rewrite Rplus_comm, Rplus_opp_r, Rplus_comm in r.
    destruct (Rup_nat (1-a)).
    destruct (Rfloor_pos (1-a) x r r0).
    exists (-(Z.of_nat x0 + 1))%Z. rewrite opp_IZR.
    rewrite plus_IZR. simpl. split.
    + rewrite <- (Ropp_involutive a). apply Ropp_gt_lt_contravar.
      destruct a0 as [_ a0]. apply (Rplus_lt_reg_r 1).
      rewrite Rplus_comm, Rplus_assoc. rewrite <- INR_IZR_INZ. apply a0.
    + destruct a0 as [a0 _]. apply (Rplus_lt_compat_l a) in a0.
      ring_simplify in a0. rewrite <- INR_IZR_INZ.
      apply (Rplus_lt_reg_r (INR x0)). unfold IZR, IPR, IPR_2.
      ring_simplify. exact a0.
Qed.

(* A point in an archimedean field is the limit of a
   sequence of rational numbers (n maps to the q between
   a and a+1/n). This is how real numbers compute,
   and they are measured by exact rational numbers. *)
Definition RQ_dense_pos (a b : R)
  : 0 < b
    -> a < b -> { q : Q | a < IQR q < b }.
Proof.
  intros H H0.
  assert (0 < b - a) as epsPos.
  { apply (Rplus_lt_compat_r (-a)) in H0.
    rewrite Rplus_opp_r in H0. apply H0. }
  pose proof (Rup_nat ((/(b-a)) (or_intror epsPos)))
    as [n maj].
  destruct n as [|k].
  - exfalso.
    apply (Rmult_lt_compat_l (b-a)) in maj. 2: apply epsPos.
    rewrite Rmult_0_r in maj. rewrite Rinv_r in maj.
    apply (Rlt_asym 0 1). apply Rlt_0_1. apply maj.
    right. apply epsPos.
  - (* 0 < n *)
    pose (Pos.of_nat (S k)) as n.
    destruct (Rfloor (IZR (2 * Z.pos n) * b)) as [p maj2].
    exists (p # (2*n))%Q. split.
    + apply (Rlt_trans a (b - IQR (1 # n))).
      apply (Rplus_lt_reg_r (IQR (1#n))).
      unfold Rminus,CRminus. rewrite Rplus_assoc. rewrite Rplus_opp_l.
      rewrite Rplus_0_r. apply (Rplus_lt_reg_l (-a)).
      rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
      rewrite Rplus_comm. unfold IQR.
      rewrite Rmult_1_l. apply (Rmult_lt_reg_l (IPR n)).
      apply IPR_pos. rewrite Rinv_r.
      apply (Rmult_lt_compat_l (b-a)) in maj.
      rewrite Rinv_r, Rmult_comm in maj.
      rewrite <- INR_IPR. unfold n. rewrite Nat2Pos.id.
      apply maj. discriminate. right. exact epsPos. exact epsPos.
      right. apply IPR_pos.
      apply (Rplus_lt_reg_r (IQR (1 # n))).
      unfold Rminus,CRminus. rewrite Rplus_assoc, Rplus_opp_l.
      rewrite Rplus_0_r. rewrite <- plus_IQR.
      destruct maj2 as [_ maj2].
      setoid_replace ((p # 2 * n) + (1 # n))%Q
        with ((p + 2 # 2 * n))%Q. unfold IQR.
      apply (Rmult_lt_reg_r (IZR (Z.pos (2 * n)))).
      apply (IZR_lt 0). reflexivity. rewrite Rmult_assoc.
      rewrite Rinv_l. rewrite Rmult_1_r. rewrite Rmult_comm.
      rewrite plus_IZR. apply maj2.
      setoid_replace (1#n)%Q with (2#2*n)%Q. 2: reflexivity.
      apply Qinv_plus_distr.
    + destruct maj2 as [maj2 _]. unfold IQR.
      apply (Rmult_lt_reg_r (IZR (Z.pos (2 * n)))).
      apply (IZR_lt 0). apply Pos2Z.is_pos. rewrite Rmult_assoc, Rinv_l.
      rewrite Rmult_1_r, Rmult_comm. apply maj2.
Qed.

Definition RQ_dense (a b : R)
  : a < b
    -> { q : Q | a < IQR q < b }.
Proof.
  intros H. destruct (linear_order_T a 0 b). apply H.
  - destruct (RQ_dense_pos (-b) (-a)) as [q maj].
    apply (Rplus_lt_compat_l (-a)) in r. rewrite Rplus_opp_l in r.
    rewrite Rplus_0_r in r. apply r.
    apply (Rplus_lt_compat_l (-a)) in H.
    rewrite Rplus_opp_l, Rplus_comm in H.
    apply (Rplus_lt_compat_l (-b)) in H. rewrite <- Rplus_assoc in H.
    rewrite Rplus_opp_l in H. rewrite Rplus_0_l in H.
    rewrite Rplus_0_r in H. apply H.
    exists (-q)%Q. split.
    + destruct maj as [_ maj].
      apply (Rplus_lt_compat_l (-IQR q)) in maj.
      rewrite Rplus_opp_l, <- opp_IQR, Rplus_comm in maj.
      apply (Rplus_lt_compat_l a) in maj. rewrite <- Rplus_assoc in maj.
      rewrite Rplus_opp_r, Rplus_0_l in maj.
      rewrite Rplus_0_r in maj. apply maj.
    + destruct maj as [maj _].
      apply (Rplus_lt_compat_l (-IQR q)) in maj.
      rewrite Rplus_opp_l, <- opp_IQR, Rplus_comm in maj.
      apply (Rplus_lt_compat_l b) in maj. rewrite <- Rplus_assoc in maj.
      rewrite Rplus_opp_r in maj. rewrite Rplus_0_l in maj.
      rewrite Rplus_0_r in maj. apply maj.
  - apply RQ_dense_pos. apply r. apply H.
Qed.

Definition RQ_limit : forall (x : R) (n:nat),
    { q:Q | x < IQR q < x + IQR (1 # Pos.of_nat n) }.
Proof.
  intros x n. apply (RQ_dense x (x + IQR (1 # Pos.of_nat n))).
  rewrite <- (Rplus_0_r x). rewrite Rplus_assoc.
  apply Rplus_lt_compat_l. rewrite Rplus_0_l. apply IQR_pos.
  reflexivity.
Qed.


(*********)
Lemma Rmult_le_pos : forall r1 r2, 0 <= r1 -> 0 <= r2 -> 0 <= r1 * r2.
Proof.
  intros x y H H0; rewrite <- (Rmult_0_l x); rewrite <- (Rmult_comm x);
    apply (Rmult_le_compat_l x 0 y H H0).
Qed.

Lemma Rinv_le_contravar :
  forall x y (xpos : 0 < x) (ynz : y # 0),
    x <= y -> (/ y) ynz <= (/ x) (or_intror xpos).
Proof.
  intros. intro abs. apply (Rmult_lt_compat_l x) in abs.
  2: apply xpos. rewrite Rinv_r in abs.
  apply (Rmult_lt_compat_r y) in abs.
  rewrite Rmult_assoc in abs. rewrite Rinv_l in abs.
  rewrite Rmult_1_r in abs. rewrite Rmult_1_l in abs. contradiction.
  exact (Rlt_le_trans _ x _ xpos H).
  right. exact xpos.
Qed.

Lemma Rle_Rinv : forall x y (xpos : 0 < x) (ypos : 0 < y),
    x <= y -> (/ y) (or_intror ypos) <= (/ x) (or_intror xpos).
Proof.
  intros.
  apply Rinv_le_contravar with (1 := H).
Qed.

Lemma Ropp_div : forall x y (ynz : y # 0),
    -x * (/y) ynz == - (x * (/ y) ynz).
Proof.
  intros; ring.
Qed.

Lemma double : forall r1, 2 * r1 == r1 + r1.
Proof.
  intros. rewrite (Rmult_plus_distr_r 1 1 r1), Rmult_1_l. reflexivity.
Qed.

Lemma Rlt_0_2 : 0 < 2.
Proof.
  apply (Rlt_trans 0 (0+1)). rewrite Rplus_0_l. exact Rlt_0_1.
  apply Rplus_lt_le_compat. exact Rlt_0_1. apply Rle_refl.
Qed.

Lemma double_var : forall r1, r1 == r1 * (/ 2) (or_intror Rlt_0_2)
                                    + r1 * (/ 2) (or_intror Rlt_0_2).
Proof.
  intro; rewrite <- double; rewrite <- Rmult_assoc;
    symmetry ; apply Rinv_r_simpl_m.
Qed.

(* IZR : Z -> R is a ring morphism *)
Lemma R_rm : ring_morph
  0 1 Rplus Rmult Rminus Ropp Req
  0%Z 1%Z Zplus Zmult Zminus Z.opp Zeq_bool IZR.
Proof.
constructor ; try easy.
exact plus_IZR.
exact minus_IZR.
exact mult_IZR.
exact opp_IZR.
intros x y H.
replace y with x. reflexivity.
now apply Zeq_bool_eq.
Qed.

Lemma Zeq_bool_IZR x y :
  IZR x == IZR y -> Zeq_bool x y = true.
Proof.
intros H.
apply Zeq_is_eq_bool.
now apply eq_IZR.
Qed.


(*********************************************************)
(** ** Other rules about < and <=                        *)
(*********************************************************)

Lemma Rmult_ge_0_gt_0_lt_compat :
  forall r1 r2 r3 r4,
    r3 >= 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros. apply (Rle_lt_trans _ (r2 * r3)).
  apply Rmult_le_compat_r. apply H. apply Rlt_asym. apply H1.
  apply Rmult_lt_compat_l. apply H0. apply H2.
Qed.

Lemma le_epsilon :
  forall r1 r2, (forall eps, 0 < eps -> r1 <= r2 + eps) -> r1 <= r2.
Proof.
  intros x y H. intro abs.
  assert (0 < (x - y) * (/ 2) (or_intror Rlt_0_2)).
  { apply (Rplus_lt_compat_r (-y)) in abs. rewrite Rplus_opp_r in abs.
    apply Rmult_lt_0_compat. exact abs.
    apply Rinv_0_lt_compat. }
  specialize (H ((x - y) * (/ 2) (or_intror Rlt_0_2)) H0).
  apply (Rmult_le_compat_l 2) in H.
  rewrite Rmult_plus_distr_l in H.
  apply (Rplus_le_compat_l (-x)) in H.
  rewrite (Rmult_comm (x-y)), <- Rmult_assoc, Rinv_r, Rmult_1_l,
  (Rmult_plus_distr_r 1 1), (Rmult_plus_distr_r 1 1)
    in H.
  ring_simplify in H; contradiction.
  right. apply Rlt_0_2. apply Rlt_asym. apply Rlt_0_2.
Qed.

(**********)
Lemma Rdiv_lt_0_compat : forall a b (bpos : 0 < b),
    0 < a -> 0 < a * (/b) (or_intror bpos).
Proof.
intros; apply Rmult_lt_0_compat;[|apply Rinv_0_lt_compat]; assumption.
Qed.

Lemma Rdiv_plus_distr : forall a b c (cnz : c # 0),
    (a + b)* (/c) cnz == a* (/c) cnz + b* (/c) cnz.
Proof.
  intros. apply Rmult_plus_distr_r.
Qed.

Lemma Rdiv_minus_distr : forall a b c (cnz : c # 0),
    (a - b)* (/c) cnz == a* (/c) cnz - b* (/c) cnz.
Proof.
  intros; unfold Rminus,CRminus; rewrite Rmult_plus_distr_r.
  apply Rplus_morph. reflexivity.
  rewrite Ropp_mult_distr_l. reflexivity.
Qed.


(*********************************************************)
(** * Definitions of new types                           *)
(*********************************************************)

Record nonnegreal : Type := mknonnegreal
  {nonneg :> R; cond_nonneg : 0 <= nonneg}.

Record posreal : Type := mkposreal {pos :> R; cond_pos : 0 < pos}.

Record nonposreal : Type := mknonposreal
  {nonpos :> R; cond_nonpos : nonpos <= 0}.

Record negreal : Type := mknegreal {neg :> R; cond_neg : neg < 0}.

Record nonzeroreal : Type := mknonzeroreal
  {nonzero :> R; cond_nonzero : nonzero <> 0}.

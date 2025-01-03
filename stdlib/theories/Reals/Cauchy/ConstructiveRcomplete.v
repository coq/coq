(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

Require Import PeanoNat.
Require Import QArith_base.
Require Import Qabs.
Require Import ConstructiveReals.
Require Import ConstructiveCauchyRealsMult.
Require Import Logic.ConstructiveEpsilon.
Require Import ConstructiveCauchyAbs.
Require Import Lia.
Require Import Lqa.
Require Import Qpower.
Require Import QExtra.
Require Import PosExtra.
Require Import ConstructiveExtra.

(** Proof that Cauchy reals are Cauchy-complete.

    WARNING: this file is experimental and likely to change in future releases.
 *)

Local Open Scope CReal_scope.

(* We use <= in sort Prop rather than < in sort Set,
   it is equivalent for the definition of limits and it
   extracts smaller programs. *)
Definition seq_cv (un : nat -> CReal) (l : CReal) : Set
  := forall p : positive,
    { n : nat  |  forall i:nat, le n i -> CReal_abs (un i - l) <= inject_Q (1#p) }.

Definition Un_cauchy_mod (un : nat -> CReal) : Set
  := forall p : positive,
    { n : nat  |  forall i j:nat, le n i -> le n j
                       -> CReal_abs (un i - un j) <= inject_Q (1#p) }.

Lemma seq_cv_proper : forall (un : nat -> CReal) (a b : CReal),
    seq_cv un a
    -> a == b
    -> seq_cv un b.
Proof.
  intros. intro p. specialize (H p) as [n H].
  exists n. intros. rewrite <- H0. apply H, H1.
Qed.

#[global]
Instance seq_cv_morph
  : forall (un : nat -> CReal), CMorphisms.Proper
      (CMorphisms.respectful CRealEq CRelationClasses.iffT) (seq_cv un).
Proof.
  split.
  - intros. apply (seq_cv_proper un x).
    + exact H0.
    + exact H.
  - intros. apply (seq_cv_proper un y).
    + exact H0.
    + symmetry. exact H.
Qed.


(* Sharpen the archimedean property : constructive versions of
   the usual floor and ceiling functions. *)
Definition Rfloor (a : CReal)
  : { p : Z  &  inject_Q (p#1) < a < inject_Q (p#1) + 2 }.
Proof.
  destruct (CRealArchimedean a) as [n [H H0]].
  exists (n-2)%Z. split.
  - setoid_replace (n - 2 # 1)%Q with ((n#1) + - 2)%Q.
    + rewrite inject_Q_plus, (opp_inject_Q 2).
      apply (CReal_plus_lt_reg_r 2). ring_simplify.
      rewrite CReal_plus_comm. exact H0.
    + rewrite Qinv_plus_distr. reflexivity.
  - setoid_replace (n - 2 # 1)%Q with ((n#1) + - 2)%Q.
    + rewrite inject_Q_plus, (opp_inject_Q 2).
      ring_simplify. exact H.
    + rewrite Qinv_plus_distr. reflexivity.
Qed.

(* ToDo: Move to ConstructiveCauchyAbs.v *)
Lemma Qabs_Rabs : forall q : Q,
    inject_Q (Qabs q) == CReal_abs (inject_Q q).
Proof.
  intro q. apply Qabs_case.
  - intros. rewrite CReal_abs_right.
    + reflexivity.
    + apply inject_Q_le, H.
  - intros. rewrite CReal_abs_left, opp_inject_Q.
    + reflexivity.
    + apply inject_Q_le, H.
Qed.

Lemma Qlt_trans_swap_hyp: forall x y z : Q,
  (y < z)%Q -> (x < y)%Q -> (x < z)%Q.
Proof.
  intros x y z H1 H2.
  apply (Qlt_trans x y z); assumption.
Qed.

Lemma Qle_trans_swap_hyp: forall x y z : Q,
  (y <= z)%Q -> (x <= y)%Q -> (x <= z)%Q.
Proof.
  intros x y z H1 H2.
  apply (Qle_trans x y z); assumption.
Qed.

(** This inequality is tight since it is equal for n=1 and n=2 *)

Lemma Qpower_2powneg_le_inv: forall (n : positive),
    (2 * 2 ^ Z.neg n <= 1 # n)%Q.
Proof.
  intros n.
  induction n using Pos.peano_ind.
  - cbn. lra.
  - rewrite <- Pos2Z.opp_pos, Pos2Z.inj_succ, Z.opp_succ, Pos2Z.opp_pos, <- Z.sub_1_r.
    rewrite Qpower_minus_pos.
    ring_simplify.
    apply (Qmult_le_l _ _ (1#2)) in IHn.
      2: lra.
    ring_simplify in IHn.
    apply (Qle_trans _ _ _ IHn).
    unfold Qle, Qmult, Qnum, Qden.
    ring_simplify; rewrite Pos2Z.inj_succ, <- Z.add_1_l.
    clear IHn; induction n using Pos.peano_ind.
    + reflexivity.
    + rewrite Pos2Z.inj_succ, <- Z.add_1_l.
      (* ToDo: does this lemma really need to be named like this and have this statement? *)
      rewrite <- POrderedType.Positive_as_OT.add_1_l.
      rewrite POrderedType.Positive_as_OT.mul_add_distr_l.
      rewrite Pos2Z.inj_add.
      apply Z.add_le_mono.
      * lia.
      * exact IHn.
Qed.

Lemma Pospow_lin_le_2pow: forall (n : positive),
    (2 * n <= 2 ^ n)%positive.
Proof.
  intros n.
  induction n using Pos.peano_ind.
  - cbn. lia.
  - rewrite Pos.mul_succ_r, Pos.pow_succ_r.
    lia.
Qed.

Lemma CReal_cv_self : forall (x : CReal) (n : positive),
    CReal_abs (x - inject_Q (seq x (Z.neg n))) <= inject_Q (1#n).
Proof.
  intros x n.
  (* ToDo: CRealLt_asym should be names CRealLt_Le_weak and asym should be x<y /\ y<x -> False *)
  apply CRealLt_asym.
  apply (CRealLt_RQ_from_single_dist _ _ (Z.neg n - 1)%Z).
  unfold CReal_abs, CReal_abs_seq, CReal_abs_scale.
  unfold CReal_minus, CReal_plus, CReal_plus_seq, CReal_abs_scale.
  unfold CReal_opp, CReal_opp_seq, CReal_opp_scale.
  unfold inject_Q.
  do 4 rewrite CReal_red_seq; rewrite Qred_correct.
  ring_simplify (Z.neg n - 1 - 1)%Z.
  pose proof cauchy x (Z.neg n) (Z.neg n - 2)%Z (Z.neg n) ltac:(lia) ltac:(lia) as Hxbnd.
  apply Qopp_lt_compat in Hxbnd.
  apply (Qplus_lt_r _ _ (1#n)) in Hxbnd.
  apply (Qlt_trans_swap_hyp _ _ _ Hxbnd); clear Hxbnd x.
  rewrite Qpower_minus_pos.
  apply (Qplus_lt_r _ _ (2 ^ Z.neg n)%Q); ring_simplify.
  pose proof Qpower_2powneg_le_inv n as Hpowinv.
  pose proof Qpower_0_lt 2 (Z.neg n) ltac:(lra) as Hpowpos.
  lra.
Qed.

Lemma CReal_cv_self' : forall (x : CReal) (n : Z),
    CReal_abs (x - inject_Q (seq x n)) <= inject_Q (2^n).
Proof.
  intros x n [k kmaj].
  unfold CReal_abs, CReal_abs_seq, CReal_abs_scale in kmaj.
  unfold CReal_minus, CReal_plus, CReal_plus_seq, CReal_abs_scale in kmaj.
  unfold CReal_opp, CReal_opp_seq, CReal_opp_scale in kmaj.
  unfold inject_Q in kmaj.
  do 4 rewrite CReal_red_seq in kmaj; rewrite Qred_correct in kmaj.
  apply (Qlt_not_le _ _ kmaj). clear kmaj.
  rewrite CReal_red_seq.
  apply (Qplus_le_l _ _ (2^n)%Q); ring_simplify.
  pose proof cauchy x (Z.max (k-1)%Z n) (k-1)%Z n ltac:(lia) ltac:(lia) as Hxbnd.
  apply Qlt_le_weak in Hxbnd.
  apply (Qle_trans _ _ _ Hxbnd); clear Hxbnd.
  apply Z.max_case.
  - rewrite <- Qplus_0_l; apply Qplus_le_compat.
    + apply Qpower_pos; lra.
    + rewrite Qpower_minus_pos.
      pose proof (Qpower_0_lt 2 k)%Q; lra.
  - rewrite <- Qplus_0_r; apply Qplus_le_compat.
    + lra.
    + pose proof (Qpower_0_lt 2 k)%Q; lra.
Qed.

Definition QCauchySeqLin (un : positive -> Q)
  : Prop
  := forall (k : positive) (p q : positive),
      Pos.le k p
      -> Pos.le k q
      -> Qlt (Qabs (un p - un q)) (1 # k).

(* We can probably reduce the factor 4. *)
Lemma Rcauchy_limit : forall (xn : nat -> CReal) (xcau : Un_cauchy_mod xn),
    QCauchySeqLin
      (fun n : positive =>
         let (p, _) := xcau (4 * n)%positive in seq (xn p) (4 * Z.neg n)%Z).
Proof.
  intros xn xcau n p q Hp Hq.
  destruct (xcau (4 * p)%positive) as [i imaj],
  (xcau (4 * q)%positive) as [j jmaj].
  assert (CReal_abs (xn i - xn j) <= inject_Q (1 # 4 * n)).
  { destruct (Nat.leb_spec i j) as [l|l].
    - apply (CReal_le_trans _ _ _ (imaj i j (Nat.le_refl _) l)).
      apply inject_Q_le. unfold Qle, Qnum, Qden.
      rewrite Z.mul_1_l, Z.mul_1_l. apply Pos2Z.pos_le_pos.
      apply Pos.mul_le_mono_l, Hp.
    - apply le_S, le_S_n in l.
      apply (CReal_le_trans _ _ _ (jmaj i j l (Nat.le_refl _))).
      apply inject_Q_le. unfold Qle, Qnum, Qden.
      rewrite Z.mul_1_l, Z.mul_1_l. apply Pos2Z.pos_le_pos.
      apply Pos.mul_le_mono_l, Hq. }
  clear jmaj imaj.
  setoid_replace (1#n)%Q with ((1#(3*n)) + ((1#(3*n)) + (1#(3*n))))%Q.
  2: rewrite Qinv_plus_distr, Qinv_plus_distr; reflexivity.
  apply lt_inject_Q. rewrite inject_Q_plus.
  rewrite Qabs_Rabs.
  apply (CReal_le_lt_trans _ (CReal_abs (inject_Q (seq (xn i) (4 * Z.neg p)%Z) - xn i) + CReal_abs (xn i - inject_Q(seq (xn j) (4 * Z.neg q)%Z)))).
  - unfold Qminus.
    rewrite inject_Q_plus, opp_inject_Q.
    setoid_replace (inject_Q (seq (xn i) (4 * Z.neg p)%Z) +
                    - inject_Q (seq (xn j) (4 * Z.neg q)%Z))
      with (inject_Q (seq (xn i) (4 * Z.neg p)%Z) - xn i
            + (xn i - inject_Q (seq (xn j) (4 * Z.neg q)%Z))).
    2: ring.
    apply CReal_abs_triang.
  - apply CReal_plus_le_lt_compat.
    + rewrite CReal_abs_minus_sym. apply (CReal_le_trans _ (inject_Q (1# 4*p))).
      * apply CReal_cv_self.
      * apply inject_Q_le. unfold Qle, Qnum, Qden.
        rewrite Z.mul_1_l, Z.mul_1_l.
        apply Pos2Z.pos_le_pos. apply (Pos.le_trans _ (4*n)).
        -- apply Pos.mul_le_mono_r. discriminate.
        -- apply Pos.mul_le_mono_l. exact Hp.
    + apply (CReal_le_lt_trans
               _ (CReal_abs (xn i - xn j + (xn j - inject_Q (seq (xn j) (4 * Z.neg q)%Z))))).
      * apply CReal_abs_morph. ring.
      * apply (CReal_le_lt_trans _ _ _ (CReal_abs_triang _ _)).
        rewrite inject_Q_plus. apply CReal_plus_le_lt_compat.
        -- apply (CReal_le_trans _ _ _ H). apply inject_Q_le.
           unfold Qle, Qnum, Qden. rewrite Z.mul_1_l, Z.mul_1_l.
           apply Pos2Z.pos_le_pos. apply Pos.mul_le_mono_r. discriminate.
        -- apply (CReal_le_lt_trans _ (inject_Q (1#4*q))).
           ++ apply CReal_cv_self.
           ++ apply inject_Q_lt. unfold Qlt, Qnum, Qden.
              rewrite Z.mul_1_l, Z.mul_1_l.
              apply Pos2Z.pos_lt_pos. apply (Pos.lt_le_trans _ (4*n)).
              ** apply Pos.mul_lt_mono_r. reflexivity.
              ** apply Pos.mul_le_mono_l. exact Hq.
Qed.

Definition CReal_from_cauchy_cm (n : Z) : positive :=
  match n with
    | Z0
    | Zpos _ => 1%positive
    | Zneg p => p
    end.

Lemma CReal_from_cauchy_cm_mono : forall (n p : Z),
    (p <= n)%Z
 -> (CReal_from_cauchy_cm n <= CReal_from_cauchy_cm p)%positive.
Proof.
  intros n p Hpn.
  unfold CReal_from_cauchy_cm; destruct n; destruct p; lia.
Qed.

Definition CReal_from_cauchy_seq (xn : nat -> CReal) (xcau : Un_cauchy_mod xn) (n : Z) : Q :=
  let p := CReal_from_cauchy_cm n in
  let (q, _) := xcau (4 * 2^p)%positive in
  seq (xn q) (Z.neg p - 2)%Z.

Lemma CReal_from_cauchy_cauchy : forall (xn : nat -> CReal) (xcau : Un_cauchy_mod xn),
    QCauchySeq (CReal_from_cauchy_seq xn xcau).
Proof.
  intros xn xcau n p q Hp Hq.
  remember (CReal_from_cauchy_cm n) as n'.
  remember (CReal_from_cauchy_cm p) as p'.
  remember (CReal_from_cauchy_cm q) as q'.
  unfold CReal_from_cauchy_seq.
  rewrite <- Heqp', <- Heqq'.
  destruct (xcau (4 * 2^p')%positive) as [i imaj].
  destruct (xcau (4 * 2^q')%positive) as [j jmaj].
  assert (CReal_abs (xn i - xn j) <= inject_Q (1 # 4 * 2^n')).
  { destruct (Nat.leb_spec i j) as [l|l].
    - apply (CReal_le_trans _ _ _ (imaj i j (Nat.le_refl _) l)).
      apply inject_Q_le. unfold Qle, Qnum, Qden.
      rewrite Z.mul_1_l, Z.mul_1_l. apply Pos2Z.pos_le_pos.
      subst; apply Pos.mul_le_mono_l, Pos_pow_le_mono_r, CReal_from_cauchy_cm_mono, Hp.
    - apply le_S, le_S_n in l.
      apply (CReal_le_trans _ _ _ (jmaj i j l (Nat.le_refl _))).
      apply inject_Q_le. unfold Qle, Qnum, Qden.
      rewrite Z.mul_1_l, Z.mul_1_l. apply Pos2Z.pos_le_pos.
      subst; apply Pos.mul_le_mono_l, Pos_pow_le_mono_r, CReal_from_cauchy_cm_mono, Hq.
  }
  clear jmaj imaj.
  setoid_replace (2^n)%Q with ((1#3)*2^n + ((1#3)*2^n + (1#3)*2^n))%Q by ring.
  apply lt_inject_Q. rewrite inject_Q_plus.
  rewrite Qabs_Rabs.
  apply (CReal_le_lt_trans _ (CReal_abs (inject_Q (seq (xn i) (Z.neg p' - 2)%Z) - xn i) + CReal_abs (xn i - inject_Q(seq (xn j) (Z.neg q' - 2)%Z)))).
  {
    unfold Qminus.
    rewrite inject_Q_plus, opp_inject_Q.
    setoid_replace (inject_Q (seq (xn i) (Z.neg p' - 2)%Z) +
                    - inject_Q (seq (xn j) (Z.neg q' -  2)%Z))
      with (inject_Q (seq (xn i) (Z.neg p' - 2)%Z) - xn i
            + (xn i - inject_Q (seq (xn j) (Z.neg q' - 2)%Z))).
    2: ring.
    apply CReal_abs_triang.
  }
  apply CReal_plus_le_lt_compat.
  {
    rewrite CReal_abs_minus_sym.
    apply (CReal_le_trans _ (inject_Q ((1#4)*2^(Z.neg p')))).
    - change (1#4)%Q with ((1#2)^2)%Q.
      rewrite Qmult_comm, <- Qpower_minus_pos.
      apply CReal_cv_self'.
    - apply inject_Q_le.
      apply Qmult_le_compat_nonneg.
      + lra.
      + { split.
          - apply Qpower_pos; lra.
          - apply Qpower_le_compat_l.
            + subst; unfold CReal_from_cauchy_cm; destruct p; lia.
            + lra. }
  }
  apply (CReal_le_lt_trans
           _ (CReal_abs (xn i - xn j + (xn j - inject_Q (seq (xn j) (Z.neg q' - 2)%Z))))).
  1: apply CReal_abs_morph; ring.
  apply (CReal_le_lt_trans _ _ _ (CReal_abs_triang _ _)).
  rewrite inject_Q_plus.
  apply CReal_plus_le_lt_compat.
  {
    apply (CReal_le_trans _ _ _ H). apply inject_Q_le.
    rewrite Qmult_frac_l.
    rewrite <- (Z.pow_1_l (Z.pos n')) at 2 by lia.
    rewrite <- (Qpower_decomp_pos).
    change (1#2)%Q with (/2)%Q; rewrite Qinv_power, <- Qpower_opp.
    apply Qmult_le_compat_nonneg.
    - lra.
    - { split.
        - apply Qpower_pos; lra.
        - apply Qpower_le_compat_l.
          + subst; unfold CReal_from_cauchy_cm; destruct n; lia.
          + lra. }
  }
  apply (CReal_le_lt_trans _ (inject_Q ((1#4)*2^(Z.neg q')))).
  {
    change (1#4)%Q with ((1#2)^2)%Q.
    rewrite Qmult_comm, <- Qpower_minus_pos.
    apply CReal_cv_self'.
  }
  apply inject_Q_lt.
  setoid_rewrite Qmult_comm at 1 2.
  apply Qmult_le_lt_compat_pos.
  + { split.
      - apply Qpower_0_lt; lra.
      - apply Qpower_le_compat_l.
        + subst; unfold CReal_from_cauchy_cm. destruct q; lia.
        + lra. }
  + lra.
Qed.

Lemma Rup_pos (x : CReal)
  : { n : positive  &  x < inject_Q (Z.pos n # 1) }.
Proof.
  intros. destruct (CRealArchimedean x) as [p [maj _]].
  destruct p.
  - exists 1%positive. apply (CReal_lt_trans _ 0 _ maj). apply CRealLt_0_1.
  - exists p. exact maj.
  - exists 1%positive. apply (CReal_lt_trans _ (inject_Q (Z.neg p # 1)) _ maj).
    apply (CReal_lt_trans _ 0).
    + apply inject_Q_lt. reflexivity.
    + apply CRealLt_0_1.
Qed.

Lemma CReal_abs_upper_bound (x : CReal)
  : { n : positive  &  CReal_abs x < inject_Q (Z.pos n # 1) }.
Proof.
  intros.
  destruct (Rup_pos x) as [np Hnp].
  destruct (Rup_pos (-x)) as [nn Hnn].
  exists (Pos.max np nn).
  apply Rabs_def1.
  - apply (CReal_lt_le_trans _ _ _ Hnp), inject_Q_le.
    unfold Qle, Qnum, Qden; ring_simplify. lia.
  - apply (CReal_lt_le_trans _ _ _ Hnn), inject_Q_le.
    unfold Qle, Qnum, Qden; ring_simplify. lia.
Qed.

Require Import Qminmax.

Lemma CRealLt_QR_from_single_dist : forall (q : Q) (r : CReal) (n :Z),
    (2^n < seq r n - q)%Q
 -> inject_Q q < r .
Proof.
  intros q r n Hapart.
  pose proof Qpower_0_lt 2 n ltac:(lra) as H2npos.
  destruct (QarchimedeanLowExp2_Z (seq r n - q - 2^n) ltac:(lra)) as [k Hk].
  unfold CRealLt; exists (Z.min n (k-1))%Z.
  unfold inject_Q; rewrite CReal_red_seq.
  pose proof cauchy r n n (Z.min n (k-1))%Z ltac:(lia) ltac:(lia) as Hrbnd.
  pose proof Qpower_le_compat_l 2 (Z.min n (k - 1))%Z (k-1)%Z ltac:(lia) ltac:(lra).
  apply (Qmult_le_l _ _ 2 ltac:(lra)) in H.
  apply (Qle_lt_trans _ _ _ H); clear H.
  rewrite Qpower_minus_pos.
  ring_simplify.
  apply Qabs_Qlt_condition in Hrbnd.
  lra.
Qed.

Lemma CReal_abs_Qabs: forall (x : CReal) (q : Q) (n : Z),
    CReal_abs x <= inject_Q q
 -> (Qabs (seq x n) <= q + 2^n)%Q.
Proof.
  intros x q n Hr.
  unfold CRealLe in Hr.
  apply Qnot_lt_le; intros Hq; apply Hr; clear Hr.
  apply (CRealLt_QR_from_single_dist _ _ n%Z).
  unfold CReal_abs, CReal_abs_seq; rewrite CReal_red_seq.
  lra.
Qed.

Lemma CReal_abs_Qabs_seq: forall (x : CReal) (n : Z),
    (seq (CReal_abs x) n == Qabs (seq x n))%Q.
Proof.
  intros x n.
  unfold CReal_abs, CReal_abs_seq; rewrite CReal_red_seq.
  reflexivity.
Qed.

Lemma CReal_abs_Qabs_diff: forall (x y : CReal) (q : Q) (n : Z),
    CReal_abs (x - y) <= inject_Q q
 -> (Qabs (seq x n - seq y n) <= q + 2*2^n)%Q.
Proof.
  intros x y q n Hr.
  unfold CRealLe in Hr.
  apply Qnot_lt_le; intros Hq; apply Hr; clear Hr.
  apply (CRealLt_QR_from_single_dist _ _ (n+1)%Z).
  unfold CReal_abs, CReal_abs_seq; rewrite CReal_red_seq.
  unfold CReal_minus, CReal_plus, CReal_plus_seq; rewrite CReal_red_seq, Qred_correct.
  unfold CReal_opp, CReal_opp_seq; rewrite CReal_red_seq.
  ring_simplify (n + 1 - 1)%Z.
  rewrite Qpower_plus by lra.
  ring_simplify; change (seq x n + - seq y n)%Q with (seq x n - seq y n)%Q.
  lra.
Qed.

(** Note: the <= in the conclusion is likely tight *)

Lemma CRealLt_QR_to_single_dist : forall (q : Q) (x : CReal) (n : Z),
    inject_Q q < x -> (-(2^n) <= seq x n - q)%Q.
Proof.
  intros q x n Hqltx.
  destruct (Qlt_le_dec (seq x n - q) (-(2^n))  ) as [Hdec|Hdec].
  - exfalso.
    pose proof CRealLt_RQ_from_single_dist x q n ltac:(lra) as contra.
    apply CRealLt_asym in contra. apply contra, Hqltx.
  - apply Hdec.
Qed.

Lemma CRealLt_RQ_to_single_dist : forall (x : CReal) (q : Q) (n : Z),
    x < inject_Q q -> (-(2^n) <= q - seq x n)%Q.
Proof.
  intros x q n Hxltq.
  destruct (Qlt_le_dec (q - seq x n) (-(2^n))  ) as [Hdec|Hdec].
  - exfalso.
    pose proof CRealLt_QR_from_single_dist q x n ltac:(lra) as contra.
    apply CRealLt_asym in contra. apply contra, Hxltq.
  - apply Hdec.
Qed.

Lemma Pos2Z_pos_is_pos : forall (p : positive),
    (1 <= Z.pos p)%Z.
Proof.
  intros p.
  lia.
Qed.

Lemma Qabs_Qgt_condition: forall x y : Q,
  (x < Qabs y)%Q <-> (x < y \/ x < -y)%Q.
Proof.
 intros x y.
 apply Qabs_case; lra.
Qed.

Lemma CReal_from_cauchy_seq_bound :
  forall (xn : nat -> CReal) (xcau : Un_cauchy_mod xn) (i j : Z),
    (Qabs (CReal_from_cauchy_seq xn xcau i - CReal_from_cauchy_seq xn xcau j) <= 1)%Q.
Proof.
  intros xn xcau i j.
  unfold CReal_from_cauchy_seq.
  destruct (xcau (4 * 2 ^ CReal_from_cauchy_cm i)%positive) as [i' imaj].
  destruct (xcau (4 * 2 ^ CReal_from_cauchy_cm j)%positive) as [j' jmaj].

  assert (CReal_abs (xn i' - xn j') <= inject_Q (1#4)) as Hxij.
    {
    destruct (Nat.leb_spec i' j') as [l|l].
    - apply (CReal_le_trans _ _ _ (imaj i' j' (Nat.le_refl _) l)).
      apply inject_Q_le; unfold Qle, Qnum, Qden; ring_simplify.
      apply Pos2Z_pos_is_pos.
    - apply le_S, le_S_n in l.
      apply (CReal_le_trans _ _ _ (jmaj i' j' l (Nat.le_refl _))).
      apply inject_Q_le; unfold Qle, Qnum, Qden; ring_simplify.
      apply Pos2Z_pos_is_pos.
    }
  clear imaj jmaj.
  unfold CReal_abs, CReal_abs_seq in Hxij.
  unfold CRealLe, CRealLt in Hxij.
  rewrite CReal_red_seq in Hxij.
  apply Qnot_lt_le; intros Hxij'; apply Hxij; clear Hxij.
  exists (-2)%Z.
  unfold inject_Q; rewrite CReal_red_seq.
  unfold CReal_minus, CReal_plus, CReal_plus_seq; rewrite CReal_red_seq, Qred_correct.
  unfold CReal_opp, CReal_opp_seq; rewrite CReal_red_seq.
  change (2 * 2 ^ (-2))%Q with (2#4)%Q.
  pose proof cauchy (xn i') (-3)%Z (-3)%Z (Z.neg (CReal_from_cauchy_cm i) - 2)%Z
    ltac:(lia) ltac:(unfold CReal_from_cauchy_cm; destruct i; lia) as Hxibnd.
  pose proof cauchy (xn j') (-3)%Z (-3)%Z (Z.neg (CReal_from_cauchy_cm j) - 2)%Z
    ltac:(lia) ltac:(unfold CReal_from_cauchy_cm; destruct j; lia) as Hxjbnd.
  apply (Qplus_lt_l _ _ (1 # 4)%Q); ring_simplify.
  (* ToDo: ring_simplify should return reduced fractions *)
  setoid_replace (12#16)%Q with (3#4)%Q by ring.
  change (2^(-3))%Q with (1#8)%Q in Hxibnd, Hxjbnd.
  change (-2-1)%Z with (-3)%Z.
  apply Qabs_Qlt_condition in Hxibnd.
  apply Qabs_Qlt_condition in Hxjbnd.
  apply Qabs_Qgt_condition.
  apply Qabs_Qgt_condition in Hxij'.
  lra.
Qed.

Definition CReal_from_cauchy_scale (xn : nat -> CReal) (xcau : Un_cauchy_mod xn) : Z :=
  Qbound_lt_ZExp2 (Qabs (CReal_from_cauchy_seq xn xcau (-1)) + 2)%Q.

Lemma CReal_from_cauchy_bound : forall (xn : nat -> CReal) (xcau : Un_cauchy_mod xn),
  QBound (CReal_from_cauchy_seq xn xcau) (CReal_from_cauchy_scale xn xcau).
Proof.
  intros xn xcau n.
  unfold CReal_from_cauchy_scale.

  (* Use the spec of Qbound_lt_ZExp2 to linearize the RHS *)
  apply (Qlt_trans_swap_hyp _ _ _ (Qbound_lt_ZExp2_spec _)).

  (* Massage the goal so that CReal_from_cauchy_seq_bound can be applied *)
  apply (Qplus_lt_l _ _ (-Qabs (CReal_from_cauchy_seq xn xcau (-1)))%Q); ring_simplify.
  assert(forall x y : Q, (x + -1*y == x-y)%Q) as Aux
    by (intros x y; lra); rewrite Aux; clear Aux.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle_reverse _ _)).
  apply (Qle_lt_trans _ 1%Q _).
    2: lra.
  apply CReal_from_cauchy_seq_bound.
Qed.

Definition CReal_from_cauchy (xn : nat -> CReal) (xcau : Un_cauchy_mod xn) : CReal :=
{|
  seq := CReal_from_cauchy_seq xn xcau;
  scale := CReal_from_cauchy_scale xn xcau;
  cauchy := CReal_from_cauchy_cauchy xn xcau;
  bound := CReal_from_cauchy_bound xn xcau
|}.

Lemma Rcauchy_complete : forall (xn : nat -> CReal),
    Un_cauchy_mod xn
    -> { l : CReal  &  seq_cv xn l }.
Proof.
  intros xn cau.
  exists (CReal_from_cauchy xn cau).

  intro p.
  pose proof (CReal_cv_self' (CReal_from_cauchy xn cau) (Z.neg p - 1)%Z) as H.

  pose proof (cau (2*p)%positive) as [k cv].

  rewrite CReal_abs_minus_sym in H.
  unfold CReal_from_cauchy at 1 in H.
  rewrite CReal_red_seq in H.
  unfold CReal_from_cauchy_seq in H.
  remember (CReal_from_cauchy_cm (Z.neg p - 1))%positive as i'.
  destruct (cau (4 * 2 ^ i')%positive) as [i imaj].
  exists (max k i).

  intros j H0.
  setoid_replace (xn j - CReal_from_cauchy xn cau)
  with (xn j -  inject_Q (seq (xn i) (Z.neg i' - 2)%Z)
     + (inject_Q (seq (xn i) (Z.neg i' - 2)%Z) - CReal_from_cauchy xn cau)).
  2: ring.
  apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
  apply (CReal_le_trans _ (inject_Q (1#2*p) + inject_Q (1#2*p))).
  - apply CReal_plus_le_compat.
    2: { apply (CReal_le_trans _ _ _ H). apply inject_Q_le.
         rewrite Qpower_minus_pos.
         assert(forall (n:Z) (p q : positive), n#(p*q) == (n#p) * (1#q))%Q as Aux
             by ( intros; unfold Qeq, Qmult, Qnum, Qden; ring ); rewrite Aux; clear Aux.
         rewrite Qmult_comm; apply Qmult_le_l; [lra|].
         pose proof Qpower_2powneg_le_inv p.
         pose proof Qpower_0_lt 2 (Z.neg p)%Z; lra. }

    (* Use imaj to relate xn i and xn j *)
    specialize (imaj j i (Nat.le_trans _ _ _ (Nat.le_max_r _ _) H0) (Nat.le_refl _)).
    apply (CReal_le_trans _ (inject_Q (1 # 4 * p) + inject_Q (1 # 4 * p))).
    + setoid_replace (xn j - inject_Q (seq (xn i) (Z.neg i' - 2)))
        with (xn j - xn i + (xn i - inject_Q (seq (xn i) (Z.neg i' - 2)))).
      2: ring.
      apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
      apply CReal_plus_le_compat.
      * apply (CReal_le_trans _ _ _ imaj).
        rewrite Heqi'. change (Z.neg p - 1)%Z with (Z.neg (p + 1))%Z.
        unfold CReal_from_cauchy_cm.
        apply inject_Q_le.
        unfold Qle, Qnum, Qden.
        rewrite Z.mul_1_l, Z.mul_1_l.
        apply Pos2Z.pos_le_pos, Pos.mul_le_mono_l.
        pose proof Pospow_lin_le_2pow p.
        rewrite Pos.add_1_r, Pos.pow_succ_r.
        lia.
      * clear imaj.

        (* Use CReal_cv_self' to relate xn i and seq (xn i) (...) *)
        pose proof CReal_cv_self' (xn i) (Z.neg i' - 2).
        apply (CReal_le_trans _ _ _ H1).
        apply inject_Q_le.
        rewrite Heqi'. change (Z.neg p - 1)%Z with (Z.neg (p + 1))%Z.
        unfold CReal_from_cauchy_cm.
        change (Z.neg (p + 1))%Z with (Z.neg p - 1)%Z.
        ring_simplify (Z.neg p - 1 - 2)%Z.
        rewrite Qpower_minus_pos.
        assert(forall (n:Z) (p q : positive), n#(p*q) == (n#p) * (1#q))%Q as Aux
            by ( intros; unfold Qeq, Qmult, Qnum, Qden; ring ); rewrite Aux; clear Aux.
        pose proof Qpower_2powneg_le_inv p.
        pose proof Qpower_0_lt 2 (Z.neg p)%Z; lra.

    + (* Solve remaining aux goals *)
      rewrite <- inject_Q_plus. rewrite (inject_Q_morph _ (1#2*p)).
      * apply CRealLe_refl.
      * rewrite Qinv_plus_distr; reflexivity.
  - rewrite <- inject_Q_plus. rewrite (inject_Q_morph _ (1#p)).
    + apply CRealLe_refl.
    + rewrite Qinv_plus_distr; reflexivity.
Qed.

Lemma CRealLtIsLinear : isLinearOrder CRealLt.
Proof.
  repeat split.
  - exact CRealLt_asym.
  - exact CReal_lt_trans.
  - intros. destruct (CRealLt_dec x z y H).
    + left. exact c.
    + right. exact c.
Qed.

Lemma CRealAbsLUB : forall x y : CReal,
  x <= y /\ (- x) <= y <-> (CReal_abs x) <= y.
Proof.
  split.
  - intros [H H0]. apply CReal_abs_le. split. 2: exact H.
    apply (CReal_plus_le_reg_r (y-x)). ring_simplify. exact H0.
  - intros. apply CReal_abs_def2 in H. destruct H. split.
    + exact H.
    + fold (-x <= y).
      apply (CReal_plus_le_reg_r (x-y)). ring_simplify. exact H0.
Qed.

Lemma CRealComplete :  forall xn : nat -> CReal,
  (forall p : positive,
   {n : nat |
   forall i j : nat,
   (n <= i)%nat -> (n <= j)%nat -> (CReal_abs (xn i + - xn j)) <= (inject_Q (1 # p))}) ->
  {l : CReal &
  forall p : positive,
  {n : nat |
  forall i : nat, (n <= i)%nat -> (CReal_abs (xn i + - l)) <= (inject_Q (1 # p))}}.
Proof.
  intros. destruct (Rcauchy_complete xn) as [l cv].
  - intro p. destruct (H p) as [n a]. exists n. intros.
    exact (a i j H0 H1).
  - exists l. intros p. destruct (cv p).
    exists x. exact c.
Qed.

Lemma Qnot_le_iff_lt: forall x y : Q,
  ~ (x <= y)%Q <-> (y < x)%Q.
Proof.
  intros x y; split.
  - apply Qnot_le_lt.
  - apply Qlt_not_le.
Qed.

Lemma Qnot_lt_iff_le: forall x y : Q,
  ~ (x < y)%Q <-> (y <= x)%Q.
Proof.
  intros x y; split.
  - apply Qnot_lt_le.
  - apply Qle_not_lt.
Qed.

Lemma CRealLtDisjunctEpsilon : forall a b c d : CReal,
    (CRealLtProp a b \/ CRealLtProp c d) -> CRealLt a b  +  CRealLt c d.
Proof.
  intros.
  (* Combine both existentials into one *)
  assert (exists n : Z, 2*2^n < seq b n - seq a n \/ 2*2^n < seq d n - seq c n)%Q.
  { destruct H.
    - destruct H as [n maj]. exists n. left. apply maj.
    - destruct H as [n maj]. exists n. right. apply maj. }
  apply constructive_indefinite_ground_description_Z in H0.
  - destruct H0 as [n maj].
    destruct (Qlt_le_dec (2 * 2^n) (seq b n - seq a n)).
    + left. exists n. apply q.
    + assert (2 * 2^n < seq d n - seq c n)%Q.
      { destruct maj.
        - exfalso.
          apply (Qlt_not_le (2 * 2^n) (seq b n - seq a n)); assumption.
        - assumption. }
      clear maj. right. exists n.
      apply H0.
  - clear H0 H. intro n.
    destruct (Qlt_le_dec (2 * 2 ^ n)%Q (seq b n - seq a n)%Q) as [H1|H1].
    + now left; left.
    + destruct (Qlt_le_dec (2 * 2 ^ n)%Q (seq d n - seq c n)%Q) as [H2|H2].
      * now left; right.
      * now right; intros [H3|H3]; apply Qle_not_lt with (2 := H3).
Qed.

Definition CRealConstructive : ConstructiveReals
  := Build_ConstructiveReals
       CReal CRealLt CRealLtIsLinear CRealLtProp
       CRealLtEpsilon CRealLtForget CRealLtDisjunctEpsilon
       inject_Q inject_Q_lt lt_inject_Q
       CReal_plus CReal_opp CReal_mult
       inject_Q_plus inject_Q_mult
       CReal_isRing CReal_isRingExt CRealLt_0_1
       CReal_plus_lt_compat_l CReal_plus_lt_reg_l
       CReal_mult_lt_0_compat
       CReal_inv CReal_inv_l CReal_inv_0_lt_compat
       CRealQ_dense Rup_pos CReal_abs CRealAbsLUB CRealComplete.

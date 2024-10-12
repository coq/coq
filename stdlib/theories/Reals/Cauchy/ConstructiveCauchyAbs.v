(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import QArith.
Require Import Qabs.
Require Import Qpower.
Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsMult.
Require Import Lia.
Require Import Lqa.
Require Import QExtra.

Local Open Scope CReal_scope.

Local Ltac simplify_Qabs :=
  match goal with |- context [(Qabs ?a)%Q] => ring_simplify a end.

Local Ltac simplify_Qlt :=
  match goal with |- (?l < ?r)%Q => ring_simplify l; ring_simplify r end.

Local Lemma Qopp_mult_mone : forall q : Q,
  (-1 * q == -q)%Q.
Proof.
  intros; ring.
Qed.

Local Lemma Qabs_involutive: forall q : Q,
  (Qabs (Qabs q) == Qabs q)%Q.
Proof.
  intros q; apply Qabs_case; intros Hcase.
  - reflexivity.
  - pose proof Qabs_nonneg q as Habspos.
    pose proof Qle_antisym _ _ Hcase Habspos as Heq0.
    setoid_rewrite Heq0.
    reflexivity.
Qed.

(**
   The constructive formulation of the absolute value on the real numbers.
   This is followed by the constructive definitions of minimum and maximum,
   as min x y := (x + y - |x-y|) / 2.

   WARNING: this file is experimental and likely to change in future releases.
*)


(* If a rational sequence is Cauchy, then so is its absolute value.
   This is how the constructive absolute value is defined.
   A more abstract way to put it is the real numbers are the metric completion
   of the rational numbers, so the uniformly continuous function
   Qabs : Q -> Q
   uniquely extends to a uniformly continuous function
   CReal_abs : CReal -> CReal
*)

Definition CReal_abs_seq (x : CReal) (n : Z) := Qabs (seq x n).

Definition CReal_abs_scale (x : CReal) := scale x.

Lemma CReal_abs_cauchy: forall (x : CReal),
    QCauchySeq (CReal_abs_seq x).
Proof.
  intros x n p q Hp Hq.
  pose proof (cauchy x n p q Hp Hq) as Hxbnd.
  apply (Qle_lt_trans _ (Qabs (seq x p - seq x q))).
  2: exact Hxbnd. apply Qabs_Qle_condition. split.
  2: apply Qabs_triangle_reverse.
  apply (Qplus_le_r _ _ (Qabs (seq x q))).
  rewrite <- Qabs_opp.
  apply (Qle_trans _ _ _ (Qabs_triangle_reverse _ _)).
  ring_simplify.
  unfold CReal_abs_seq.
  simplify_Qabs; setoid_rewrite Qopp_mult_mone.
  do 2 rewrite Qabs_opp.
  lra.
Qed.

Lemma CReal_abs_bound : forall (x : CReal),
  QBound (CReal_abs_seq x) (CReal_abs_scale x).
Proof.
  intros x n.
  unfold CReal_abs_seq, CReal_abs_scale.
  rewrite Qabs_involutive.
  apply (bound x).
Qed.

Definition CReal_abs (x : CReal) : CReal :=
{|
  seq := CReal_abs_seq x;
  scale := CReal_abs_scale x;
  cauchy := CReal_abs_cauchy x;
  bound := CReal_abs_bound x
|}.

Lemma CRealLt_RQ_from_single_dist : forall (r : CReal) (q : Q) (n :Z),
    (2^n < q - seq r n)%Q
 -> r < inject_Q q.
Proof.
  intros r q n Hapart.
  pose proof Qpower_0_lt 2 n ltac:(lra) as H2npos.
  destruct (QarchimedeanLowExp2_Z (q - seq r n - 2^n) ltac:(lra)) as [k Hk].
  unfold CRealLt; exists (Z.min n (k-1))%Z.
  unfold inject_Q; rewrite CReal_red_seq.
  pose proof cauchy r n n (Z.min n (k-1))%Z ltac:(lia) ltac:(lia) as Hrbnd.
  pose proof Qpower_le_compat_l 2 (Z.min n (k - 1))%Z (k-1)%Z ltac:(lia) ltac:(lra).
  apply (Qmult_le_l _ _ 2 ltac:(lra)) in H.
  apply (Qle_lt_trans _ _ _ H); clear H.
  rewrite Qpower_minus_pos.
  simplify_Qlt.
  apply Qabs_Qlt_condition in Hrbnd.
  lra.
Qed.

Lemma CRealLe_0R_to_single_dist : forall (x : CReal) (n : Z),
    0 <= x -> (-(2^n) <= seq x n)%Q.
Proof.
  intros x n Hxnonneg.
  destruct (Qlt_le_dec (seq x n) (-(2^n))) as [Hdec|Hdec].
  - exfalso; apply Hxnonneg.
    apply (CRealLt_RQ_from_single_dist x 0 n); lra.
  - exact Hdec.
Qed.

Lemma CReal_abs_right : forall x : CReal, 0 <= x -> CReal_abs x == x.
Proof.
  intros x Hxnonneg; apply CRealEq_diff; intro n.
  unfold CReal_abs, CReal_abs_seq, CReal_abs_scale;
    rewrite CReal_red_seq.
  pose proof CRealLe_0R_to_single_dist x n Hxnonneg.
  pose proof Qpower_0_lt 2 n ltac:(lra) as Hpowpos.
  do 2 apply Qabs_case; intros H1 H2; lra.
Qed.

Lemma CReal_le_abs : forall x : CReal, x <= CReal_abs x.
Proof.
  intros x [n nmaj].
  unfold CReal_abs, CReal_abs_seq, CReal_abs_scale in nmaj;
    rewrite CReal_red_seq in nmaj.
  apply (Qle_not_lt _ _ (Qle_Qabs (seq x n))).
  apply Qlt_minus_iff. apply (Qlt_trans _ (2*2^n)).
  - pose proof Qpower_0_lt 2 n ltac:(lra); lra.
  - exact nmaj.
Qed.

Lemma CReal_abs_pos : forall x : CReal, 0 <= CReal_abs x.
Proof.
  intros x [n nmaj].
  unfold CReal_abs, CReal_abs_seq, CReal_abs_scale in nmaj;
    rewrite CReal_red_seq in nmaj.
  apply (Qle_not_lt _ _ (Qabs_nonneg (seq x n))).
  apply Qlt_minus_iff. apply (Qlt_trans _ (2*2^n)).
  - pose proof Qpower_0_lt 2 n ltac:(lra); lra.
  - exact nmaj.
Qed.

Lemma CReal_abs_opp : forall x : CReal, CReal_abs (-x) == CReal_abs x.
Proof.
  intros x; apply CRealEq_diff; intro n.
  unfold CReal_abs, CReal_abs_seq, CReal_abs_scale;
  unfold CReal_opp, CReal_opp_seq, CReal_opp_scale;
    do 3 rewrite CReal_red_seq.
  rewrite Qabs_opp. simplify_Qabs.
  rewrite Qabs_pos by lra.
  pose proof Qpower_0_lt 2 n; lra.
Qed.

Lemma CReal_abs_left : forall x : CReal, x <= 0 -> CReal_abs x == -x.
Proof.
  intros x Hxnonpos.
  apply CReal_opp_ge_le_contravar in Hxnonpos. rewrite CReal_opp_0 in Hxnonpos.
  rewrite <- CReal_abs_opp. apply CReal_abs_right, Hxnonpos.
Qed.

Lemma CReal_abs_appart_0 : forall x : CReal,
    0 < CReal_abs x -> x # 0.
Proof.
  intros x [n nmaj].
  unfold CReal_abs, CReal_abs_seq, CReal_abs_scale in nmaj;
    rewrite CReal_red_seq in nmaj.
  destruct (Qlt_le_dec (seq x n) 0) as [Hdec|Hdec].
  - left. exists n. cbn in nmaj |- * .
    rewrite Qabs_neg in nmaj; lra.
  - right. exists n. cbn. rewrite Qabs_pos in nmaj.
    + exact nmaj.
    + exact Hdec.
Qed.

Add Parametric Morphism : CReal_abs
    with signature CRealEq ==> CRealEq
      as CReal_abs_morph.
Proof.
  intros. split.
  - intro abs. destruct (CReal_abs_appart_0 y).
    + apply (CReal_le_lt_trans _ (CReal_abs x)).
      * apply CReal_abs_pos.
      * apply abs.
    + rewrite CReal_abs_left, CReal_abs_left, H in abs.
      * exact (CRealLt_asym _ _ abs abs).
      * apply CRealLt_asym, c.
      * rewrite H. apply CRealLt_asym, c.
    + rewrite CReal_abs_right, CReal_abs_right, H in abs.
      * exact (CRealLt_asym _ _ abs abs).
      * apply CRealLt_asym, c.
      * rewrite H. apply CRealLt_asym, c.
  - intro abs. destruct (CReal_abs_appart_0 x).
    + apply (CReal_le_lt_trans _ (CReal_abs y)).
      * apply CReal_abs_pos.
      * apply abs.
    + rewrite CReal_abs_left, CReal_abs_left, H in abs.
      * exact (CRealLt_asym _ _ abs abs).
      * apply CRealLt_asym, c.
      * rewrite <- H. apply CRealLt_asym, c.
    + rewrite CReal_abs_right, CReal_abs_right, H in abs.
      * exact (CRealLt_asym _ _ abs abs).
      * apply CRealLt_asym, c.
      * rewrite <- H. apply CRealLt_asym, c.
Qed.

Lemma CReal_abs_le : forall a b:CReal, -b <= a <= b -> CReal_abs a <= b.
Proof.
  intros a b H [n nmaj].
  unfold CReal_abs, CReal_abs_seq, CReal_abs_scale in nmaj;
    rewrite CReal_red_seq in nmaj.
  destruct (Qlt_le_dec (seq a n) 0) as [Hdec|Hdec].
  - rewrite Qabs_neg in nmaj by lra. destruct H as [Hl Hr]. apply Hl. clear Hl Hr.
    exists n; cbn.
    unfold CReal_opp_seq; lra.
  - rewrite Qabs_pos in nmaj.
    + destruct H as [Hl Hr]. apply Hr. clear Hl Hr.
      exists n; cbn. exact nmaj.
    + exact Hdec.
Qed.

Lemma CReal_abs_minus_sym : forall x y : CReal,
    CReal_abs (x - y) == CReal_abs (y - x).
Proof.
  intros x y. setoid_replace (x - y) with (-(y-x)).
  - rewrite CReal_abs_opp. reflexivity.
  - ring.
Qed.

Lemma CReal_abs_lt : forall x y : CReal,
    CReal_abs x < y -> prod (x < y) (-x < y).
Proof.
  split.
  - apply (CReal_le_lt_trans _ _ _ (CReal_le_abs x)), H.
  - apply (CReal_le_lt_trans _ _ _ (CReal_le_abs (-x))).
    rewrite CReal_abs_opp. exact H.
Qed.

Lemma CReal_abs_triang : forall x y : CReal,
    CReal_abs (x + y) <= CReal_abs x + CReal_abs y.
Proof.
  intros. apply CReal_abs_le. split.
  - setoid_replace (x + y) with (-(-x - y)). 2: ring.
    apply CReal_opp_ge_le_contravar.
    apply CReal_plus_le_compat; rewrite <- CReal_abs_opp; apply CReal_le_abs.
  - apply CReal_plus_le_compat; apply CReal_le_abs.
Qed.

Lemma CReal_abs_triang_inv : forall x y : CReal,
    CReal_abs x - CReal_abs y <= CReal_abs (x - y).
Proof.
  intros. apply (CReal_plus_le_reg_l (CReal_abs y)).
  ring_simplify. rewrite CReal_plus_comm.
  apply (CReal_le_trans _ (CReal_abs (x - y + y))).
  - setoid_replace (x - y + y) with x.
    + apply CRealLe_refl.
    + ring.
  - apply CReal_abs_triang.
Qed.

Lemma CReal_abs_triang_inv2 : forall x y : CReal,
    CReal_abs (CReal_abs x - CReal_abs y) <= CReal_abs (x - y).
Proof.
  intros. apply CReal_abs_le. split.
  2: apply CReal_abs_triang_inv.
  apply (CReal_plus_le_reg_r (CReal_abs y)). ring_simplify.
  rewrite CReal_plus_comm, CReal_abs_minus_sym.
  apply (CReal_le_trans _ _ _ (CReal_abs_triang_inv y (y-x))).
  setoid_replace (y - (y - x)) with x. 2: ring. apply CRealLe_refl.
Qed.

Lemma CReal_abs_gt : forall x : CReal,
    x < CReal_abs x -> x < 0.
Proof.
  intros x [n nmaj].
  unfold CReal_abs, CReal_abs_seq, CReal_abs_scale in nmaj;
    rewrite CReal_red_seq in nmaj.
  assert (seq x n < 0)%Q.
  { destruct (Qlt_le_dec (seq x n) 0) as [Hdec|Hdec].
    - exact Hdec.
    - exfalso. rewrite Qabs_pos in nmaj by apply Hdec.
      pose proof Qpower_0_lt 2 n; lra. }
  rewrite Qabs_neg in nmaj by apply Qlt_le_weak, H.
  apply (CRealLt_RQ_from_single_dist _ _ n); lra.
Qed.

Lemma Rabs_def1 : forall x y : CReal,
    x < y -> -x < y -> CReal_abs x < y.
Proof.
  intros x y Hxlty Hmxlty.

  apply CRealLt_above in Hxlty. apply CRealLt_above in Hmxlty.
  destruct Hxlty as [i imaj]. destruct Hmxlty as [j jmaj].
  specialize (imaj (Z.min i j) ltac:(lia)).
  specialize (jmaj (Z.min i j) ltac:(lia)).
  cbn in jmaj; unfold CReal_opp_seq in jmaj.

  exists (Z.min i j).
  unfold CReal_abs, CReal_abs_seq, CReal_abs_scale;
    rewrite CReal_red_seq.

  pose proof Qpower_0_lt 2 (Z.min i j)%Z ltac:(lra) as Hpowij.
  pose proof Qpower_le_compat_l 2 (Z.min i j)%Z i ltac:(lia) ltac:(lra) as Hpowlei.
  pose proof Qpower_le_compat_l 2 (Z.min i j)%Z j ltac:(lia) ltac:(lra) as Hpowlej.
  apply Qabs_case; intros Hcase; lra.
Qed.

(* The proof by cases on the signs of x and y applies constructively,
   because of the positivity hypotheses. *)
Lemma CReal_abs_mult : forall x y : CReal,
    CReal_abs (x * y) == CReal_abs x * CReal_abs y.
Proof.
  assert (forall x y : CReal,
             x # 0
             -> y # 0
             -> CReal_abs (x * y) == CReal_abs x * CReal_abs y) as prep.
  { intros. destruct H, H0.
    - rewrite CReal_abs_right, CReal_abs_left, CReal_abs_left.
      + ring.
      + apply CRealLt_asym, c0.
      + apply CRealLt_asym, c.
      + setoid_replace (x*y) with (- x * - y).
        * apply CRealLt_asym, CReal_mult_lt_0_compat.
          -- rewrite <- CReal_opp_0. apply CReal_opp_gt_lt_contravar, c.
          -- rewrite <- CReal_opp_0. apply CReal_opp_gt_lt_contravar, c0.
        * ring.
    - rewrite CReal_abs_left, CReal_abs_left, CReal_abs_right.
      + ring.
      + apply CRealLt_asym, c0.
      + apply CRealLt_asym, c.
      + rewrite <- (CReal_mult_0_l y).
        apply CReal_mult_le_compat_r.
        * apply CRealLt_asym, c0.
        * apply CRealLt_asym, c.
    - rewrite CReal_abs_left, CReal_abs_right, CReal_abs_left.
      + ring.
      + apply CRealLt_asym, c0.
      + apply CRealLt_asym, c.
      + rewrite <- (CReal_mult_0_r x).
        apply CReal_mult_le_compat_l.
        * apply CRealLt_asym, c.
        * apply CRealLt_asym, c0.
    - rewrite CReal_abs_right, CReal_abs_right, CReal_abs_right.
      + ring.
      + apply CRealLt_asym, c0.
      + apply CRealLt_asym, c.
      + apply CRealLt_asym, CReal_mult_lt_0_compat; assumption. }
  split.
  - intro abs.
    assert (0 < CReal_abs x * CReal_abs y).
    { apply (CReal_le_lt_trans _ (CReal_abs (x*y))).
      - apply CReal_abs_pos.
      - exact abs. }
    pose proof (CReal_mult_pos_appart_zero _ _ H).
    rewrite CReal_mult_comm in H.
    apply CReal_mult_pos_appart_zero in H.
    destruct H. 2: apply (CReal_abs_pos y c).
    destruct H0. 2: apply (CReal_abs_pos x c0).
    apply CReal_abs_appart_0 in c.
    apply CReal_abs_appart_0 in c0.
    rewrite (prep x y) in abs.
    + exact (CRealLt_asym _ _ abs abs).
    + exact c0.
    + exact c.
  - intro abs.
    assert (0 < CReal_abs (x * y)).
    { apply (CReal_le_lt_trans _ (CReal_abs x * CReal_abs y)).
      - rewrite <- (CReal_mult_0_l (CReal_abs y)).
        apply CReal_mult_le_compat_r.
        + apply CReal_abs_pos.
        + apply CReal_abs_pos.
      - exact abs. }
    apply CReal_abs_appart_0 in H. destruct H.
    + apply CReal_opp_gt_lt_contravar in c.
      rewrite CReal_opp_0, CReal_opp_mult_distr_l in c.
      pose proof (CReal_mult_pos_appart_zero _ _ c).
      rewrite CReal_mult_comm in c.
      apply CReal_mult_pos_appart_zero in c.
      rewrite (prep x y) in abs.
      * exact (CRealLt_asym _ _ abs abs).
      * destruct H.
        -- left. apply CReal_opp_gt_lt_contravar in c0.
           rewrite CReal_opp_involutive, CReal_opp_0 in c0. exact c0.
        -- right. apply CReal_opp_gt_lt_contravar in c0.
           rewrite CReal_opp_involutive, CReal_opp_0 in c0. exact c0.
      * destruct c.
        -- right. exact c.
        -- left. exact c.
    + pose proof (CReal_mult_pos_appart_zero _ _ c).
      rewrite CReal_mult_comm in c.
      apply CReal_mult_pos_appart_zero in c.
      rewrite (prep x y) in abs.
      * exact (CRealLt_asym _ _ abs abs).
      * destruct H.
        -- right. exact c0.
        -- left. exact c0.
      * destruct c.
        -- right. exact c.
        -- left. exact c.
Qed.

Lemma CReal_abs_def2 : forall x a:CReal,
    CReal_abs x <= a -> (x <= a) /\ (- a <= x).
Proof.
  split.
  - exact (CReal_le_trans _ _ _ (CReal_le_abs _) H).
  - rewrite <- (CReal_opp_involutive x).
    apply CReal_opp_ge_le_contravar.
    rewrite <- CReal_abs_opp in H.
    exact (CReal_le_trans _ _ _ (CReal_le_abs _) H).
Qed.


(* Min and max *)

Definition CReal_min (x y : CReal) : CReal
  := (x + y - CReal_abs (y - x)) * inject_Q (1#2).

Definition CReal_max (x y : CReal) : CReal
  := (x + y + CReal_abs (y - x)) * inject_Q (1#2).

Add Parametric Morphism : CReal_min
    with signature CRealEq ==> CRealEq ==> CRealEq
      as CReal_min_morph.
Proof.
  intros. unfold CReal_min.
  rewrite H, H0. reflexivity.
Qed.

Add Parametric Morphism : CReal_max
    with signature CRealEq ==> CRealEq ==> CRealEq
      as CReal_max_morph.
Proof.
  intros. unfold CReal_max.
  rewrite H, H0. reflexivity.
Qed.

Lemma CReal_double : forall x:CReal, 2 * x == x + x.
Proof.
  intro x. rewrite (inject_Q_plus 1 1). ring.
Qed.

Lemma CReal_max_lub : forall x y z:CReal,
    x <= z -> y <= z -> CReal_max x y <= z.
Proof.
  intros. unfold CReal_max.
  apply (CReal_mult_le_reg_r 2).
  - apply inject_Q_lt; reflexivity.
  - rewrite CReal_mult_assoc, <- inject_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CReal_mult_1_r.
    apply (CReal_plus_le_reg_l (-x-y)). ring_simplify.
    apply CReal_abs_le. split.
    + unfold CReal_minus. repeat rewrite CReal_opp_plus_distr.
      do 2 rewrite CReal_opp_involutive.
      rewrite (CReal_plus_comm x), CReal_plus_assoc. apply CReal_plus_le_compat_l.
      apply (CReal_plus_le_reg_l (-x)).
      rewrite <- CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_l.
      rewrite CReal_mult_comm, CReal_double. rewrite CReal_opp_plus_distr.
      apply CReal_plus_le_compat; apply CReal_opp_ge_le_contravar; assumption.
    + unfold CReal_minus.
      rewrite (CReal_plus_comm y), CReal_plus_assoc. apply CReal_plus_le_compat_l.
      apply (CReal_plus_le_reg_l y).
      rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
      rewrite CReal_mult_comm, CReal_double.
      apply CReal_plus_le_compat; assumption.
Qed.

Lemma CReal_min_glb : forall x y z:CReal,
    z <= x -> z <= y -> z <= CReal_min x y.
Proof.
  intros. unfold CReal_min.
  apply (CReal_mult_le_reg_r 2).
  - apply inject_Q_lt; reflexivity.
  - rewrite CReal_mult_assoc, <- inject_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CReal_mult_1_r.
    apply (CReal_plus_le_reg_l (CReal_abs(y-x) - (z*2))). ring_simplify.
    apply CReal_abs_le. split.
    + unfold CReal_minus. repeat rewrite CReal_opp_plus_distr.
      rewrite CReal_opp_mult_distr_l, CReal_opp_involutive.
      rewrite (CReal_plus_comm (z*2)), (CReal_plus_comm y), CReal_plus_assoc.
      apply CReal_plus_le_compat_l, (CReal_plus_le_reg_r y).
      rewrite CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_r.
      rewrite CReal_mult_comm, CReal_double.
      apply CReal_plus_le_compat; assumption.
    + unfold CReal_minus.
      rewrite (CReal_plus_comm y). apply CReal_plus_le_compat.
      2: apply CRealLe_refl.
      apply (CReal_plus_le_reg_r (-x)).
      rewrite CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_r.
      rewrite CReal_mult_comm, CReal_double.
      apply CReal_plus_le_compat; apply CReal_opp_ge_le_contravar; assumption.
Qed.

Lemma CReal_max_l : forall x y : CReal, x <= CReal_max x y.
Proof.
  intros. unfold CReal_max.
  apply (CReal_mult_le_reg_r 2).
  - apply inject_Q_lt; reflexivity.
  - rewrite CReal_mult_assoc, <- inject_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CReal_mult_1_r.
    rewrite CReal_mult_comm, CReal_double.
    rewrite CReal_plus_assoc. apply CReal_plus_le_compat_l.
    apply (CReal_plus_le_reg_l (-y)).
    rewrite <- CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_l.
    rewrite CReal_abs_minus_sym, CReal_plus_comm.
    apply CReal_le_abs.
Qed.

Lemma CReal_max_r : forall x y : CReal, y <= CReal_max x y.
Proof.
  intros. unfold CReal_max.
  apply (CReal_mult_le_reg_r 2).
  - apply inject_Q_lt; reflexivity.
  - rewrite CReal_mult_assoc, <- inject_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CReal_mult_1_r.
    rewrite CReal_mult_comm, CReal_double.
    rewrite (CReal_plus_comm x).
    rewrite CReal_plus_assoc. apply CReal_plus_le_compat_l.
    apply (CReal_plus_le_reg_l (-x)).
    rewrite <- CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_l.
    rewrite CReal_plus_comm. apply CReal_le_abs.
Qed.

Lemma CReal_min_l : forall x y : CReal, CReal_min x y <= x.
Proof.
  intros. unfold CReal_min.
  apply (CReal_mult_le_reg_r 2).
  - apply inject_Q_lt; reflexivity.
  - rewrite CReal_mult_assoc, <- inject_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CReal_mult_1_r.
    rewrite CReal_mult_comm, CReal_double.
    unfold CReal_minus.
    rewrite CReal_plus_assoc. apply CReal_plus_le_compat_l.
    apply (CReal_plus_le_reg_l (CReal_abs (y + - x)+ -x)). ring_simplify.
    rewrite CReal_plus_comm. apply CReal_le_abs.
Qed.

Lemma CReal_min_r : forall x y : CReal, CReal_min x y <= y.
Proof.
  intros. unfold CReal_min.
  apply (CReal_mult_le_reg_r 2).
  - apply inject_Q_lt; reflexivity.
  - rewrite CReal_mult_assoc, <- inject_Q_mult.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
    rewrite CReal_mult_1_r.
    rewrite CReal_mult_comm, CReal_double.
    unfold CReal_minus. rewrite (CReal_plus_comm x).
    rewrite CReal_plus_assoc. apply CReal_plus_le_compat_l.
    apply (CReal_plus_le_reg_l (CReal_abs (y + - x)+ -y)). ring_simplify.
    fold (y-x). rewrite CReal_abs_minus_sym.
    rewrite CReal_plus_comm. apply CReal_le_abs.
Qed.

Lemma CReal_min_left : forall x y : CReal,
    x <= y -> CReal_min x y == x.
Proof.
  intros. unfold CReal_min.
  apply (CReal_mult_eq_reg_r 2). 2: right; apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  rewrite CReal_mult_comm, CReal_double.
  rewrite CReal_abs_right.
  - ring.
  - rewrite <- (CReal_plus_opp_r x). apply CReal_plus_le_compat.
    + exact H.
    + apply CRealLe_refl.
Qed.

Lemma CReal_min_right : forall x y : CReal,
    y <= x -> CReal_min x y == y.
Proof.
  intros. unfold CReal_min.
  apply (CReal_mult_eq_reg_r 2). 2: right; apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  rewrite CReal_mult_comm, CReal_double.
  rewrite CReal_abs_left.
  - ring.
  - rewrite <- (CReal_plus_opp_r x). apply CReal_plus_le_compat.
    + exact H.
    + apply CRealLe_refl.
Qed.

Lemma CReal_max_left : forall x y : CReal,
    y <= x -> CReal_max x y == x.
Proof.
  intros. unfold CReal_max.
  apply (CReal_mult_eq_reg_r 2). 2: right; apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  rewrite CReal_mult_comm, CReal_double.
  rewrite CReal_abs_left.
  - ring.
  - rewrite <- (CReal_plus_opp_r x). apply CReal_plus_le_compat.
    + exact H.
    + apply CRealLe_refl.
Qed.

Lemma CReal_max_right : forall x y : CReal,
    x <= y -> CReal_max x y == y.
Proof.
  intros. unfold CReal_max.
  apply (CReal_mult_eq_reg_r 2). 2: right; apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  rewrite CReal_mult_comm, CReal_double.
  rewrite CReal_abs_right.
  - ring.
  - rewrite <- (CReal_plus_opp_r x). apply CReal_plus_le_compat.
    + exact H.
    + apply CRealLe_refl.
Qed.

Lemma CReal_min_lt_r : forall x y : CReal,
    CReal_min x y < y -> CReal_min x y == x.
Proof.
  intros. unfold CReal_min. unfold CReal_min in H.
  apply (CReal_mult_eq_reg_r 2). 2: right; apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  rewrite CReal_mult_comm, CReal_double.
  rewrite CReal_abs_right.
  { ring. }
  apply (CReal_mult_lt_compat_r 2) in H. 2: apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult in H.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q in H. 2: reflexivity.
  rewrite CReal_mult_1_r in H.
  rewrite CReal_mult_comm, CReal_double in H.
  intro abs. rewrite CReal_abs_left in H.
  - unfold CReal_minus in H.
    rewrite CReal_opp_involutive, CReal_plus_comm in H.
    rewrite CReal_plus_assoc, <- (CReal_plus_assoc (-x)), CReal_plus_opp_l in H.
    rewrite CReal_plus_0_l in H. exact (CRealLt_asym _ _ H H).
  - apply CRealLt_asym, abs.
Qed.

Lemma posPartAbsMax : forall x : CReal,
    CReal_max 0 x == (x + CReal_abs x) * (inject_Q (1#2)).
Proof.
  split.
  - intro abs. apply (CReal_mult_lt_compat_r 2) in abs.
    2: apply (inject_Q_lt 0 2); reflexivity.
    rewrite CReal_mult_assoc, <- (inject_Q_mult) in abs.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q in abs. 2: reflexivity.
    rewrite CReal_mult_1_r in abs.
    apply (CReal_plus_lt_compat_l (-x)) in abs.
    rewrite <- CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_l in abs.
    apply CReal_abs_le in abs. { exact abs. } split.
    + rewrite CReal_opp_plus_distr, CReal_opp_involutive.
      apply (CReal_le_trans _ (x + 0)). 2: rewrite CReal_plus_0_r; apply CRealLe_refl.
      apply CReal_plus_le_compat_l. apply (CReal_le_trans _ (2 * 0)).
      * rewrite CReal_opp_mult_distr_l, <- (CReal_mult_comm 2). apply CReal_mult_le_compat_l_half.
        -- apply inject_Q_lt. reflexivity.
        -- apply (CReal_plus_le_reg_l (CReal_max 0 x)). rewrite CReal_plus_opp_r, CReal_plus_0_r.
           apply CReal_max_l.
      * rewrite CReal_mult_0_r. apply CRealLe_refl.
    + apply (CReal_plus_le_reg_l x).
      rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
      rewrite (inject_Q_plus 1 1), CReal_mult_plus_distr_l, CReal_mult_1_r.
      apply CReal_plus_le_compat; apply CReal_max_r.
  - apply CReal_max_lub.
    + rewrite <- (CReal_mult_0_l (inject_Q (1#2))).
      do 2 rewrite <- (CReal_mult_comm (inject_Q (1#2))).
      apply CReal_mult_le_compat_l_half.
      * apply inject_Q_lt; reflexivity.
      * rewrite <- (CReal_plus_opp_r x). apply CReal_plus_le_compat_l.
        rewrite <- CReal_abs_opp. apply CReal_le_abs.
    + intros abs.
      apply (CReal_mult_lt_compat_r 2) in abs. 2: apply inject_Q_lt; reflexivity.
      rewrite CReal_mult_assoc, <- inject_Q_mult in abs.
      setoid_replace ((1 # 2) * 2)%Q with 1%Q in abs. 2: reflexivity.
      rewrite CReal_mult_1_r, (inject_Q_plus 1 1), CReal_mult_plus_distr_l, CReal_mult_1_r in abs.
      apply CReal_plus_lt_reg_l in abs.
      exact (CReal_le_abs x abs).
Qed.

Lemma negPartAbsMin : forall x : CReal,
    CReal_min 0 x == (x - CReal_abs x) * (inject_Q (1#2)).
Proof.
  split.
  - intro abs. apply (CReal_mult_lt_compat_r 2) in abs.
    2: apply (inject_Q_lt 0 2); reflexivity.
    rewrite CReal_mult_assoc, <- (inject_Q_mult) in abs.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q in abs. 2: reflexivity.
    rewrite CReal_mult_1_r in abs.
    apply (CReal_plus_lt_compat_r (CReal_abs x)) in abs.
    unfold CReal_minus in abs.
    rewrite CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_r in abs.
    apply (CReal_plus_lt_compat_l (-(CReal_min 0 x * 2))) in abs.
    rewrite <- CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_l in abs.
    apply CReal_abs_lt in abs. destruct abs.
    apply (CReal_plus_lt_compat_l (CReal_min 0 x * 2)) in c0.
    rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l in c0.
    apply (CReal_plus_lt_compat_r x) in c0.
    rewrite CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_r in c0.
    rewrite <- CReal_double, CReal_mult_comm in c0. apply CReal_mult_lt_reg_l in c0.
    + apply CReal_min_lt_r in c0.
      rewrite c0, CReal_mult_0_l, CReal_opp_0, CReal_plus_0_l in c.
      exact (CRealLt_asym _ _ c c).
    + apply inject_Q_lt; reflexivity.
  - intro abs.
    assert ((x - CReal_abs x) * inject_Q (1 # 2) < 0 * inject_Q (1 # 2)).
    { rewrite CReal_mult_0_l.
      apply (CReal_lt_le_trans _ _ _ abs). apply CReal_min_l. }
    apply CReal_mult_lt_reg_r in H.
    2: apply inject_Q_lt; reflexivity.
    rewrite <- (CReal_plus_opp_r (CReal_abs x)) in H.
    apply CReal_plus_lt_reg_r, CReal_abs_gt in H.
    rewrite CReal_min_right, <- CReal_abs_opp, CReal_abs_right in abs.
    + unfold CReal_minus in abs.
      rewrite CReal_opp_involutive, <- CReal_double, CReal_mult_comm in abs.
      rewrite <- CReal_mult_assoc, <- inject_Q_mult in abs.
      setoid_replace ((1 # 2) * 2)%Q with 1%Q in abs.
      * rewrite CReal_mult_1_l in abs. exact (CRealLt_asym _ _ abs abs).
      * reflexivity.
    + rewrite <- CReal_opp_0.
      apply CReal_opp_ge_le_contravar, CRealLt_asym, H.
    + apply CRealLt_asym, H.
Qed.

Lemma CReal_min_sym : forall (x y : CReal),
    CReal_min x y == CReal_min y x.
Proof.
  intros. unfold CReal_min.
  rewrite CReal_abs_minus_sym. ring.
Qed.

Lemma CReal_max_sym : forall (x y : CReal),
    CReal_max x y == CReal_max y x.
Proof.
  intros. unfold CReal_max.
  rewrite CReal_abs_minus_sym. ring.
Qed.

Lemma CReal_min_mult :
  forall (p q r:CReal), 0 <= r -> CReal_min (r * p) (r * q) == r * CReal_min p q.
Proof.
  intros p q r H. unfold CReal_min.
  setoid_replace (r * q - r * p) with (r * (q - p)).
  2: ring. rewrite CReal_abs_mult.
  rewrite (CReal_abs_right r).
  - ring.
  - exact H.
Qed.

Lemma CReal_min_plus : forall (x y z : CReal),
    x + CReal_min y z == CReal_min (x + y) (x + z).
Proof.
  intros. unfold CReal_min.
  setoid_replace (x + z - (x + y)) with (z-y).
  2: ring.
  apply (CReal_mult_eq_reg_r 2). 2: right; apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_plus_distr_r.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  rewrite CReal_mult_comm, CReal_double. ring.
Qed.

Lemma CReal_max_plus : forall (x y z : CReal),
    x + CReal_max y z == CReal_max (x + y) (x + z).
Proof.
  intros. unfold CReal_max.
  setoid_replace (x + z - (x + y)) with (z-y).
  2: ring.
  apply (CReal_mult_eq_reg_r 2). 2: right; apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_plus_distr_r.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  rewrite CReal_mult_comm, CReal_double. ring.
Qed.

Lemma CReal_min_lt : forall x y z : CReal,
    z < x -> z < y -> z < CReal_min x y.
Proof.
  intros. unfold CReal_min.
  apply (CReal_mult_lt_reg_r 2). { apply inject_Q_lt; reflexivity. }
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  apply (CReal_plus_lt_reg_l (CReal_abs (y - x) - (z*2))).
  ring_simplify. apply Rabs_def1.
  - unfold CReal_minus. rewrite <- (CReal_plus_comm y).
    apply CReal_plus_lt_compat_l.
    apply (CReal_plus_lt_reg_r (-x)).
    rewrite CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_r.
    rewrite <- CReal_double, CReal_mult_comm. apply CReal_mult_lt_compat_r.
    + apply inject_Q_lt; reflexivity.
    + apply CReal_opp_gt_lt_contravar, H.
  - unfold CReal_minus. rewrite CReal_opp_plus_distr, CReal_opp_involutive.
    rewrite CReal_plus_comm, (CReal_plus_comm (-z*2)), CReal_plus_assoc.
    apply CReal_plus_lt_compat_l.
    apply (CReal_plus_lt_reg_r (-y)).
    rewrite CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_r.
    rewrite <- CReal_double, CReal_mult_comm. apply CReal_mult_lt_compat_r.
    + apply inject_Q_lt; reflexivity.
    + apply CReal_opp_gt_lt_contravar, H0.
Qed.

Lemma CReal_max_assoc : forall a b c : CReal,
    CReal_max a (CReal_max b c) == CReal_max (CReal_max a b) c.
Proof.
  split.
  - apply CReal_max_lub.
    + apply CReal_max_lub.
      * apply CReal_max_l.
      * apply (CReal_le_trans _ (CReal_max b c)).
        -- apply CReal_max_l.
        -- apply CReal_max_r.
    + apply (CReal_le_trans _ (CReal_max b c)).
      * apply CReal_max_r.
      * apply CReal_max_r.
  - apply CReal_max_lub.
    + apply (CReal_le_trans _ (CReal_max a b)).
      * apply CReal_max_l.
      * apply CReal_max_l.
    + apply CReal_max_lub.
      * apply (CReal_le_trans _ (CReal_max a b)).
        -- apply CReal_max_r.
        -- apply CReal_max_l.
      * apply CReal_max_r.
Qed.

Lemma CReal_min_max_mult_neg :
  forall (p q r:CReal), r <= 0 -> CReal_min (r * p) (r * q) == r * CReal_max p q.
Proof.
  intros p q r H. unfold CReal_min, CReal_max.
  setoid_replace (r * q - r * p) with (r * (q - p)).
  2: ring. rewrite CReal_abs_mult.
  rewrite (CReal_abs_left r).
  - ring.
  - exact H.
Qed.

Lemma CReal_min_assoc : forall a b c : CReal,
    CReal_min a (CReal_min b c) == CReal_min (CReal_min a b) c.
Proof.
  split.
  - apply CReal_min_glb.
    + apply (CReal_le_trans _ (CReal_min a b)).
      * apply CReal_min_l.
      * apply CReal_min_l.
    + apply CReal_min_glb.
      * apply (CReal_le_trans _ (CReal_min a b)).
        -- apply CReal_min_l.
        -- apply CReal_min_r.
      * apply CReal_min_r.
  - apply CReal_min_glb.
    + apply CReal_min_glb.
      * apply CReal_min_l.
      * apply (CReal_le_trans _ (CReal_min b c)).
        -- apply CReal_min_r.
        -- apply CReal_min_l.
    + apply (CReal_le_trans _ (CReal_min b c)).
      * apply CReal_min_r.
      * apply CReal_min_r.
Qed.

Lemma CReal_max_lub_lt : forall x y z : CReal,
    x < z -> y < z -> CReal_max x y < z.
Proof.
  intros. unfold CReal_max.
  apply (CReal_mult_lt_reg_r 2). { apply inject_Q_lt; reflexivity. }
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  apply (CReal_plus_lt_reg_l (-x -y)). ring_simplify.
  apply Rabs_def1.
  - unfold CReal_minus. rewrite (CReal_plus_comm y), CReal_plus_assoc.
    apply CReal_plus_lt_compat_l.
    apply (CReal_plus_lt_reg_l y).
    rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
    rewrite <- CReal_double, CReal_mult_comm. apply CReal_mult_lt_compat_r.
    + apply inject_Q_lt; reflexivity.
    + exact H0.
  - unfold CReal_minus. rewrite CReal_opp_plus_distr, CReal_opp_involutive.
    rewrite (CReal_plus_comm (-x)), CReal_plus_assoc.
    apply CReal_plus_lt_compat_l.
    apply (CReal_plus_lt_reg_l x).
    rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
    rewrite <- CReal_double, CReal_mult_comm. apply CReal_mult_lt_compat_r.
    + apply inject_Q_lt; reflexivity.
    + apply H.
Qed.

Lemma CReal_max_contract : forall x y a : CReal,
    CReal_abs (CReal_max x a - CReal_max y a)
    <= CReal_abs (x - y).
Proof.
  intros. unfold CReal_max.
  rewrite (CReal_abs_morph
             _ ((x - y + (CReal_abs (a - x) - CReal_abs (a - y))) * inject_Q (1 # 2))).
  2: ring.
  rewrite CReal_abs_mult, (CReal_abs_right (inject_Q (1 # 2))).
  2: apply inject_Q_le; discriminate.
  apply (CReal_le_trans
           _ ((CReal_abs (x - y) * 1 + CReal_abs (x-y) * 1)
              * inject_Q (1 # 2))).
  - apply CReal_mult_le_compat_r.
    + apply inject_Q_le. discriminate.
    + apply (CReal_le_trans _ (CReal_abs (x - y) + CReal_abs (CReal_abs (a - x) - CReal_abs (a - y)))).
      * apply CReal_abs_triang.
      * rewrite CReal_mult_1_r. apply CReal_plus_le_compat_l.
        rewrite (CReal_abs_minus_sym x y).
        rewrite (CReal_abs_morph (y-x) ((a-x)-(a-y))).
        -- apply CReal_abs_triang_inv2.
        -- unfold CReal_minus. rewrite (CReal_plus_comm (a + - x)).
           rewrite <- CReal_plus_assoc. apply CReal_plus_morph. 2: reflexivity.
           rewrite CReal_plus_comm, CReal_opp_plus_distr, <- CReal_plus_assoc.
           rewrite CReal_plus_opp_r, CReal_opp_involutive, CReal_plus_0_l.
           reflexivity.
  - rewrite <- CReal_mult_plus_distr_l, <- inject_Q_plus.
    rewrite CReal_mult_assoc, <- inject_Q_mult.
    setoid_replace ((1 + 1) * (1 # 2))%Q with 1%Q. 2: reflexivity.
    rewrite CReal_mult_1_r. apply CRealLe_refl.
Qed.

Lemma CReal_min_contract : forall x y a : CReal,
    CReal_abs (CReal_min x a - CReal_min y a)
    <= CReal_abs (x - y).
Proof.
  intros. unfold CReal_min.
  rewrite (CReal_abs_morph
             _ ((x - y + (CReal_abs (a - y) - CReal_abs (a - x))) * inject_Q (1 # 2))).
  2: ring.
  rewrite CReal_abs_mult, (CReal_abs_right (inject_Q (1 # 2))).
  2: apply inject_Q_le; discriminate.
  apply (CReal_le_trans
           _ ((CReal_abs (x - y) * 1 + CReal_abs (x-y) * 1)
              * inject_Q (1 # 2))).
  - apply CReal_mult_le_compat_r.
    + apply inject_Q_le. discriminate.
    + apply (CReal_le_trans _ (CReal_abs (x - y) + CReal_abs (CReal_abs (a - y) - CReal_abs (a - x)))).
      * apply CReal_abs_triang.
      * rewrite CReal_mult_1_r. apply CReal_plus_le_compat_l.
        rewrite (CReal_abs_morph (x-y) ((a-y)-(a-x))).
        -- apply CReal_abs_triang_inv2.
        -- unfold CReal_minus. rewrite (CReal_plus_comm (a + - y)).
           rewrite <- CReal_plus_assoc. apply CReal_plus_morph. 2: reflexivity.
           rewrite CReal_plus_comm, CReal_opp_plus_distr, <- CReal_plus_assoc.
           rewrite CReal_plus_opp_r, CReal_opp_involutive, CReal_plus_0_l.
           reflexivity.
  - rewrite <- CReal_mult_plus_distr_l, <- inject_Q_plus.
    rewrite CReal_mult_assoc, <- inject_Q_mult.
    setoid_replace ((1 + 1) * (1 # 2))%Q with 1%Q. 2: reflexivity.
    rewrite CReal_mult_1_r. apply CRealLe_refl.
Qed.

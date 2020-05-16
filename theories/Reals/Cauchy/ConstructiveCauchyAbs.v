(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import QArith.
Require Import Qabs.
Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsMult.

Local Open Scope CReal_scope.


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
Lemma CauchyAbsStable : forall xn : positive -> Q,
    QCauchySeq xn
    -> QCauchySeq (fun n => Qabs (xn n)).
Proof.
  intros xn cau n p q H H0.
  specialize (cau n p q H H0).
  apply (Qle_lt_trans _ (Qabs (xn p - xn q))).
  2: exact cau. apply Qabs_Qle_condition. split.
  2: apply Qabs_triangle_reverse.
  apply (Qplus_le_r _ _ (Qabs (xn q))).
  rewrite <- Qabs_opp.
  apply (Qle_trans _ _ _ (Qabs_triangle_reverse _ _)).
  ring_simplify.
  setoid_replace (-xn q - (xn p - xn q))%Q with (-(xn p))%Q.
  2: ring. rewrite Qabs_opp. apply Qle_refl.
Qed.

Definition CReal_abs (x : CReal) : CReal
  := let (xn, cau) := x in
     exist _ (fun n => Qabs (xn n)) (CauchyAbsStable xn cau).

Lemma CReal_neg_nth : forall (x : CReal) (n : positive),
    (proj1_sig x n < -1#n)%Q
    -> x < 0.
Proof.
  intros. destruct x as [xn cau]; unfold proj1_sig in H.
  apply Qlt_minus_iff in H.
  setoid_replace ((-1 # n) + - xn n)%Q
    with (- ((1 # n) + xn n))%Q in H.
  destruct (Qarchimedean (2 / (-((1#n) + xn n)))) as [k kmaj].
  exists (Pos.max k n). simpl. unfold Qminus; rewrite Qplus_0_l.
  specialize (cau n n (Pos.max k n)
                  (Pos.le_refl _) (Pos.le_max_r _ _)).
  apply (Qle_lt_trans _ (2#k)).
  unfold Qle, Qnum, Qden.
  apply Z.mul_le_mono_nonneg_l. discriminate.
  apply Pos2Z.pos_le_pos, Pos.le_max_l.
  apply (Qmult_lt_l _ _ (-((1 # n) + xn n))) in kmaj.
  rewrite Qmult_div_r in kmaj.
  apply (Qmult_lt_r _ _ (1 # k)) in kmaj.
  rewrite <- Qmult_assoc in kmaj.
  setoid_replace ((Z.pos k # 1) * (1 # k))%Q with 1%Q in kmaj.
  rewrite Qmult_1_r in kmaj.
  setoid_replace (2#k)%Q with (2 * (1 # k))%Q. 2: reflexivity.
  apply (Qlt_trans _ _ _ kmaj). clear kmaj.
  apply (Qplus_lt_l _ _ ((1#n) + xn (Pos.max k n))).
  ring_simplify. rewrite Qplus_comm.
  apply (Qle_lt_trans _ (Qabs (xn n - xn (Pos.max k n)))).
  2: exact cau.
  rewrite <- Qabs_opp.
  setoid_replace (- (xn n - xn (Pos.max k n)))%Q
    with (xn (Pos.max k n) + -1 * xn n)%Q.
  apply Qle_Qabs. ring. 2: reflexivity.
  unfold Qmult, Qeq, Qnum, Qden.
  rewrite Z.mul_1_r, Z.mul_1_r, Z.mul_1_l. reflexivity.
  2: exact H. intro abs. rewrite abs in H. exact (Qlt_irrefl 0 H).
  setoid_replace (-1 # n)%Q with (-(1#n))%Q. ring. reflexivity.
Qed.

Lemma CReal_nonneg : forall (x : CReal) (n : positive),
    0 <= x -> (-1#n <= proj1_sig x n)%Q.
Proof.
  intros. destruct x as [xn cau]; unfold proj1_sig.
  destruct (Qlt_le_dec (xn n) (-1#n)).
  2: exact q. exfalso. apply H. clear H.
  apply (CReal_neg_nth _ n). exact q.
Qed.

Lemma CReal_abs_right : forall x : CReal, 0 <= x -> CReal_abs x == x.
Proof.
  intros. apply CRealEq_diff. intro n.
  destruct x as [xn cau]; unfold CReal_abs, proj1_sig.
  apply (CReal_nonneg _ n) in H. simpl in H.
  rewrite Qabs_pos.
  2: unfold Qminus; rewrite <- Qle_minus_iff; apply Qle_Qabs.
  destruct (Qlt_le_dec (xn n) 0).
  - rewrite Qabs_neg. 2: apply Qlt_le_weak, q.
    apply Qopp_le_compat in H.
    apply (Qmult_le_l _ _ (1#2)). reflexivity. ring_simplify.
    setoid_replace ((1 # 2) * (2 # n))%Q with (-(-1#n))%Q.
    2: reflexivity.
    setoid_replace ((-2 # 2) * xn n)%Q with (- xn n)%Q.
    exact H. ring.
  - rewrite Qabs_pos. unfold Qminus. rewrite Qplus_opp_r. discriminate. exact q.
Qed.

Lemma CReal_le_abs : forall x : CReal, x <= CReal_abs x.
Proof.
  intros. intros [n nmaj]. destruct x as [xn cau]; simpl in nmaj.
  apply (Qle_not_lt _ _ (Qle_Qabs (xn n))).
  apply Qlt_minus_iff. apply (Qlt_trans _ (2#n)).
  reflexivity. exact nmaj.
Qed.

Lemma CReal_abs_pos : forall x : CReal, 0 <= CReal_abs x.
Proof.
  intros. intros [n nmaj]. destruct x as [xn cau]; simpl in nmaj.
  apply (Qle_not_lt _ _ (Qabs_nonneg (xn n))).
  apply Qlt_minus_iff. apply (Qlt_trans _ (2#n)).
  reflexivity. exact nmaj.
Qed.

Lemma CReal_abs_opp : forall x : CReal, CReal_abs (-x) == CReal_abs x.
Proof.
  intros. apply CRealEq_diff. intro n.
  destruct x as [xn cau]; unfold CReal_abs, CReal_opp, proj1_sig.
  rewrite Qabs_opp. unfold Qminus. rewrite Qplus_opp_r.
  discriminate.
Qed.

Lemma CReal_abs_left : forall x : CReal, x <= 0 -> CReal_abs x == -x.
Proof.
  intros.
  apply CReal_opp_ge_le_contravar in H. rewrite CReal_opp_0 in H.
  rewrite <- CReal_abs_opp. apply CReal_abs_right, H.
Qed.

Lemma CReal_abs_appart_0 : forall x : CReal,
    0 < CReal_abs x -> x # 0.
Proof.
  intros x [n nmaj]. destruct x as [xn cau]; simpl in nmaj.
  destruct (Qlt_le_dec (xn n) 0).
  - left. exists n. simpl. rewrite Qabs_neg in nmaj.
    apply (Qlt_le_trans _ _ _ nmaj). ring_simplify. apply Qle_refl.
    apply Qlt_le_weak, q.
  - right. exists n. simpl. rewrite Qabs_pos in nmaj.
    exact nmaj. exact q.
Qed.

Add Parametric Morphism : CReal_abs
    with signature CRealEq ==> CRealEq
      as CReal_abs_morph.
Proof.
  intros. split.
  - intro abs. destruct (CReal_abs_appart_0 y).
    apply (CReal_le_lt_trans _ (CReal_abs x)).
    apply CReal_abs_pos. apply abs.
    rewrite CReal_abs_left, CReal_abs_left, H in abs.
    exact (CRealLt_asym _ _ abs abs). apply CRealLt_asym, c.
    rewrite H. apply CRealLt_asym, c.
    rewrite CReal_abs_right, CReal_abs_right, H in abs.
    exact (CRealLt_asym _ _ abs abs). apply CRealLt_asym, c.
    rewrite H. apply CRealLt_asym, c.
  - intro abs. destruct (CReal_abs_appart_0 x).
    apply (CReal_le_lt_trans _ (CReal_abs y)).
    apply CReal_abs_pos. apply abs.
    rewrite CReal_abs_left, CReal_abs_left, H in abs.
    exact (CRealLt_asym _ _ abs abs). apply CRealLt_asym, c.
    rewrite <- H. apply CRealLt_asym, c.
    rewrite CReal_abs_right, CReal_abs_right, H in abs.
    exact (CRealLt_asym _ _ abs abs). apply CRealLt_asym, c.
    rewrite <- H. apply CRealLt_asym, c.
Qed.

Lemma CReal_abs_le : forall a b:CReal, -b <= a <= b -> CReal_abs a <= b.
Proof.
  intros a b H [n nmaj]. destruct a as [an cau]; simpl in nmaj.
  destruct (Qlt_le_dec (an n) 0).
  - rewrite Qabs_neg in nmaj. destruct H. apply H. clear H H0.
    exists n. simpl.
    destruct b as [bn caub]; simpl; simpl in nmaj.
    unfold Qminus. rewrite Qplus_comm. exact nmaj.
    apply Qlt_le_weak, q.
  - rewrite Qabs_pos in nmaj. destruct H. apply H0. clear H H0.
    exists n. simpl. exact nmaj. exact q.
Qed.

Lemma CReal_abs_minus_sym : forall x y : CReal,
    CReal_abs (x - y) == CReal_abs (y - x).
Proof.
  intros x y. setoid_replace (x - y) with (-(y-x)).
  rewrite CReal_abs_opp. reflexivity. ring.
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
  setoid_replace (x - y + y) with x. apply CRealLe_refl. ring.
  apply CReal_abs_triang.
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
  intros x [n nmaj]. destruct x as [xn cau]; simpl in nmaj.
  assert (xn n < 0)%Q.
  { destruct (Qlt_le_dec (xn n) 0). exact q.
    exfalso. rewrite Qabs_pos in nmaj. unfold Qminus in nmaj.
    rewrite Qplus_opp_r in nmaj. inversion nmaj. exact q. }
  rewrite Qabs_neg in nmaj. 2: apply Qlt_le_weak, H.
  apply (CReal_neg_nth _ n). simpl.
  ring_simplify in nmaj.
  apply (Qplus_lt_l _ _ ((1#n) - xn n)).
  apply (Qmult_lt_l _ _ 2). reflexivity. ring_simplify.
  setoid_replace (2 * (1 # n))%Q with (2 # n)%Q. 2: reflexivity.
  rewrite <- Qplus_assoc.
  setoid_replace ((2 # n) + 2 * (-1 # n))%Q with 0%Q.
  rewrite Qplus_0_r. exact nmaj.
  setoid_replace (2*(-1 # n))%Q with (-(2 # n))%Q.
  rewrite Qplus_opp_r. reflexivity. reflexivity.
Qed.

Lemma Rabs_def1 : forall x y : CReal,
    x < y -> -x < y -> CReal_abs x < y.
Proof.
  intros. apply CRealLt_above in H. apply CRealLt_above in H0.
  destruct H as [i imaj]. destruct H0 as [j jmaj].
  exists (Pos.max i j). destruct x as [xn caux], y as [yn cauy]; simpl.
  simpl in imaj, jmaj.
  destruct (Qlt_le_dec (xn (Pos.max i j)) 0).
  - rewrite Qabs_neg.
    specialize (jmaj (Pos.max i j) (Pos.le_max_r _ _)).
    apply (Qle_lt_trans _ (2#j)). 2: exact jmaj.
    unfold Qle, Qnum, Qden.
    apply Z.mul_le_mono_nonneg_l. discriminate.
    apply Pos2Z.pos_le_pos, Pos.le_max_r.
    apply Qlt_le_weak, q.
  - rewrite Qabs_pos.
    specialize (imaj (Pos.max i j) (Pos.le_max_l _ _)).
    apply (Qle_lt_trans _ (2#i)). 2: exact imaj.
    unfold Qle, Qnum, Qden.
    apply Z.mul_le_mono_nonneg_l. discriminate.
    apply Pos2Z.pos_le_pos, Pos.le_max_l.
    apply q.
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
    + rewrite CReal_abs_right, CReal_abs_left, CReal_abs_left. ring.
      apply CRealLt_asym, c0. apply CRealLt_asym, c.
      setoid_replace (x*y) with (- x * - y).
      apply CRealLt_asym, CReal_mult_lt_0_compat.
      rewrite <- CReal_opp_0. apply CReal_opp_gt_lt_contravar, c.
      rewrite <- CReal_opp_0. apply CReal_opp_gt_lt_contravar, c0. ring.
    + rewrite CReal_abs_left, CReal_abs_left, CReal_abs_right. ring.
      apply CRealLt_asym, c0. apply CRealLt_asym, c.
      rewrite <- (CReal_mult_0_l y).
      apply CReal_mult_le_compat_r.
      apply CRealLt_asym, c0. apply CRealLt_asym, c.
    + rewrite CReal_abs_left, CReal_abs_right, CReal_abs_left. ring.
      apply CRealLt_asym, c0. apply CRealLt_asym, c.
      rewrite <- (CReal_mult_0_r x).
      apply CReal_mult_le_compat_l.
      apply CRealLt_asym, c. apply CRealLt_asym, c0.
    + rewrite CReal_abs_right, CReal_abs_right, CReal_abs_right. ring.
      apply CRealLt_asym, c0. apply CRealLt_asym, c.
      apply CRealLt_asym, CReal_mult_lt_0_compat; assumption. }
  split.
  - intro abs.
    assert (0 < CReal_abs x * CReal_abs y).
    { apply (CReal_le_lt_trans _ (CReal_abs (x*y))).
      apply CReal_abs_pos. exact abs. }
    pose proof (CReal_mult_pos_appart_zero _ _ H).
    rewrite CReal_mult_comm in H.
    apply CReal_mult_pos_appart_zero in H.
    destruct H. 2: apply (CReal_abs_pos y c).
    destruct H0. 2: apply (CReal_abs_pos x c0).
    apply CReal_abs_appart_0 in c.
    apply CReal_abs_appart_0 in c0.
    rewrite (prep x y) in abs.
    exact (CRealLt_asym _ _ abs abs). exact c0. exact c.
  - intro abs.
    assert (0 < CReal_abs (x * y)).
    { apply (CReal_le_lt_trans _ (CReal_abs x * CReal_abs y)).
      rewrite <- (CReal_mult_0_l (CReal_abs y)).
      apply CReal_mult_le_compat_r.
      apply CReal_abs_pos. apply CReal_abs_pos. exact abs. }
    apply CReal_abs_appart_0 in H. destruct H.
    + apply CReal_opp_gt_lt_contravar in c.
      rewrite CReal_opp_0, CReal_opp_mult_distr_l in c.
      pose proof (CReal_mult_pos_appart_zero _ _ c).
      rewrite CReal_mult_comm in c.
      apply CReal_mult_pos_appart_zero in c.
      rewrite (prep x y) in abs.
      exact (CRealLt_asym _ _ abs abs).
      destruct H. left. apply CReal_opp_gt_lt_contravar in c0.
      rewrite CReal_opp_involutive, CReal_opp_0 in c0. exact c0.
      right. apply CReal_opp_gt_lt_contravar in c0.
      rewrite CReal_opp_involutive, CReal_opp_0 in c0. exact c0.
      destruct c. right. exact c. left. exact c.
    + pose proof (CReal_mult_pos_appart_zero _ _ c).
      rewrite CReal_mult_comm in c.
      apply CReal_mult_pos_appart_zero in c.
      rewrite (prep x y) in abs.
      exact (CRealLt_asym _ _ abs abs).
      destruct H. right. exact c0. left. exact c0.
      destruct c. right. exact c. left. exact c.
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
  apply (CReal_mult_le_reg_r 2). apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  apply (CReal_plus_le_reg_l (-x-y)). ring_simplify.
  apply CReal_abs_le. split.
  - unfold CReal_minus. repeat rewrite CReal_opp_plus_distr.
    do 2 rewrite CReal_opp_involutive.
    rewrite (CReal_plus_comm x), CReal_plus_assoc. apply CReal_plus_le_compat_l.
    apply (CReal_plus_le_reg_l (-x)).
    rewrite <- CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_l.
    rewrite CReal_mult_comm, CReal_double. rewrite CReal_opp_plus_distr.
    apply CReal_plus_le_compat; apply CReal_opp_ge_le_contravar; assumption.
  - unfold CReal_minus.
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
  apply (CReal_mult_le_reg_r 2). apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r.
  apply (CReal_plus_le_reg_l (CReal_abs(y-x) - (z*2))). ring_simplify.
  apply CReal_abs_le. split.
  - unfold CReal_minus. repeat rewrite CReal_opp_plus_distr.
    rewrite CReal_opp_mult_distr_l, CReal_opp_involutive.
    rewrite (CReal_plus_comm (z*2)), (CReal_plus_comm y), CReal_plus_assoc.
    apply CReal_plus_le_compat_l, (CReal_plus_le_reg_r y).
    rewrite CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_r.
    rewrite CReal_mult_comm, CReal_double.
    apply CReal_plus_le_compat; assumption.
  - unfold CReal_minus.
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
  apply (CReal_mult_le_reg_r 2). apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
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
  apply (CReal_mult_le_reg_r 2). apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
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
  apply (CReal_mult_le_reg_r 2). apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
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
  apply (CReal_mult_le_reg_r 2). apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
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
  rewrite CReal_abs_right. ring.
  rewrite <- (CReal_plus_opp_r x). apply CReal_plus_le_compat.
  exact H. apply CRealLe_refl.
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
  rewrite CReal_abs_left. ring.
  rewrite <- (CReal_plus_opp_r x). apply CReal_plus_le_compat.
  exact H. apply CRealLe_refl.
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
  rewrite CReal_abs_left. ring.
  rewrite <- (CReal_plus_opp_r x). apply CReal_plus_le_compat.
  exact H. apply CRealLe_refl.
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
  rewrite CReal_abs_right. ring.
  rewrite <- (CReal_plus_opp_r x). apply CReal_plus_le_compat.
  exact H. apply CRealLe_refl.
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
  rewrite CReal_abs_right. ring.
  apply (CReal_mult_lt_compat_r 2) in H. 2: apply inject_Q_lt; reflexivity.
  rewrite CReal_mult_assoc, <- inject_Q_mult in H.
  setoid_replace ((1 # 2) * 2)%Q with 1%Q in H. 2: reflexivity.
  rewrite CReal_mult_1_r in H.
  rewrite CReal_mult_comm, CReal_double in H.
  intro abs. rewrite CReal_abs_left in H.
  unfold CReal_minus in H.
  rewrite CReal_opp_involutive, CReal_plus_comm in H.
  rewrite CReal_plus_assoc, <- (CReal_plus_assoc (-x)), CReal_plus_opp_l in H.
  rewrite CReal_plus_0_l in H. exact (CRealLt_asym _ _ H H).
  apply CRealLt_asym, abs.
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
    apply CReal_abs_le in abs. exact abs. split.
    + rewrite CReal_opp_plus_distr, CReal_opp_involutive.
      apply (CReal_le_trans _ (x + 0)). 2: rewrite CReal_plus_0_r; apply CRealLe_refl.
      apply CReal_plus_le_compat_l. apply (CReal_le_trans _ (2 * 0)).
      rewrite CReal_opp_mult_distr_l, <- (CReal_mult_comm 2). apply CReal_mult_le_compat_l_half.
      apply inject_Q_lt. reflexivity.
      apply (CReal_plus_le_reg_l (CReal_max 0 x)). rewrite CReal_plus_opp_r, CReal_plus_0_r.
      apply CReal_max_l. rewrite CReal_mult_0_r. apply CRealLe_refl.
    + apply (CReal_plus_le_reg_l x).
      rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
      rewrite (inject_Q_plus 1 1), CReal_mult_plus_distr_l, CReal_mult_1_r.
      apply CReal_plus_le_compat; apply CReal_max_r.
  - apply CReal_max_lub. rewrite <- (CReal_mult_0_l (inject_Q (1#2))).
    do 2 rewrite <- (CReal_mult_comm (inject_Q (1#2))).
    apply CReal_mult_le_compat_l_half.
    apply inject_Q_lt; reflexivity.
    rewrite <- (CReal_plus_opp_r x). apply CReal_plus_le_compat_l.
    rewrite <- CReal_abs_opp. apply CReal_le_abs.
    intros abs.
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
    apply CReal_min_lt_r in c0.
    rewrite c0, CReal_mult_0_l, CReal_opp_0, CReal_plus_0_l in c.
    exact (CRealLt_asym _ _ c c). apply inject_Q_lt; reflexivity.
  - intro abs.
    assert ((x - CReal_abs x) * inject_Q (1 # 2) < 0 * inject_Q (1 # 2)).
    { rewrite CReal_mult_0_l.
      apply (CReal_lt_le_trans _ _ _ abs). apply CReal_min_l. }
    apply CReal_mult_lt_reg_r in H.
    2: apply inject_Q_lt; reflexivity.
    rewrite <- (CReal_plus_opp_r (CReal_abs x)) in H.
    apply CReal_plus_lt_reg_r, CReal_abs_gt in H.
    rewrite CReal_min_right, <- CReal_abs_opp, CReal_abs_right in abs.
    unfold CReal_minus in abs.
    rewrite CReal_opp_involutive, <- CReal_double, CReal_mult_comm in abs.
    rewrite <- CReal_mult_assoc, <- inject_Q_mult in abs.
    setoid_replace ((1 # 2) * 2)%Q with 1%Q in abs.
    rewrite CReal_mult_1_l in abs. exact (CRealLt_asym _ _ abs abs).
    reflexivity. rewrite <- CReal_opp_0.
    apply CReal_opp_ge_le_contravar, CRealLt_asym, H.
    apply CRealLt_asym, H.
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
  rewrite (CReal_abs_right r). ring. exact H.
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
  apply (CReal_mult_lt_reg_r 2). apply inject_Q_lt; reflexivity.
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
    apply inject_Q_lt; reflexivity.
    apply CReal_opp_gt_lt_contravar, H.
  - unfold CReal_minus. rewrite CReal_opp_plus_distr, CReal_opp_involutive.
    rewrite CReal_plus_comm, (CReal_plus_comm (-z*2)), CReal_plus_assoc.
    apply CReal_plus_lt_compat_l.
    apply (CReal_plus_lt_reg_r (-y)).
    rewrite CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_r.
    rewrite <- CReal_double, CReal_mult_comm. apply CReal_mult_lt_compat_r.
    apply inject_Q_lt; reflexivity.
    apply CReal_opp_gt_lt_contravar, H0.
Qed.

Lemma CReal_max_assoc : forall a b c : CReal,
    CReal_max a (CReal_max b c) == CReal_max (CReal_max a b) c.
Proof.
  split.
  - apply CReal_max_lub.
    + apply CReal_max_lub. apply CReal_max_l.
      apply (CReal_le_trans _ (CReal_max b c)).
      apply CReal_max_l. apply CReal_max_r.
    + apply (CReal_le_trans _ (CReal_max b c)).
      apply CReal_max_r. apply CReal_max_r.
  - apply CReal_max_lub.
    + apply (CReal_le_trans _ (CReal_max a b)).
      apply CReal_max_l. apply CReal_max_l.
    + apply CReal_max_lub.
      apply (CReal_le_trans _ (CReal_max a b)).
      apply CReal_max_r. apply CReal_max_l. apply CReal_max_r.
Qed.

Lemma CReal_min_max_mult_neg :
  forall (p q r:CReal), r <= 0 -> CReal_min (r * p) (r * q) == r * CReal_max p q.
Proof.
  intros p q r H. unfold CReal_min, CReal_max.
  setoid_replace (r * q - r * p) with (r * (q - p)).
  2: ring. rewrite CReal_abs_mult.
  rewrite (CReal_abs_left r). ring. exact H.
Qed.

Lemma CReal_min_assoc : forall a b c : CReal,
    CReal_min a (CReal_min b c) == CReal_min (CReal_min a b) c.
Proof.
  split.
  - apply CReal_min_glb.
    + apply (CReal_le_trans _ (CReal_min a b)).
      apply CReal_min_l. apply CReal_min_l.
    + apply CReal_min_glb.
      apply (CReal_le_trans _ (CReal_min a b)).
      apply CReal_min_l. apply CReal_min_r. apply CReal_min_r.
  - apply CReal_min_glb.
    + apply CReal_min_glb. apply CReal_min_l.
      apply (CReal_le_trans _ (CReal_min b c)).
      apply CReal_min_r. apply CReal_min_l.
    + apply (CReal_le_trans _ (CReal_min b c)).
      apply CReal_min_r. apply CReal_min_r.
Qed.

Lemma CReal_max_lub_lt : forall x y z : CReal,
    x < z -> y < z -> CReal_max x y < z.
Proof.
  intros. unfold CReal_max.
  apply (CReal_mult_lt_reg_r 2). apply inject_Q_lt; reflexivity.
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
    apply inject_Q_lt; reflexivity. exact H0.
  - unfold CReal_minus. rewrite CReal_opp_plus_distr, CReal_opp_involutive.
    rewrite (CReal_plus_comm (-x)), CReal_plus_assoc.
    apply CReal_plus_lt_compat_l.
    apply (CReal_plus_lt_reg_l x).
    rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
    rewrite <- CReal_double, CReal_mult_comm. apply CReal_mult_lt_compat_r.
    apply inject_Q_lt; reflexivity.
    apply H.
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
  apply CReal_mult_le_compat_r. apply inject_Q_le. discriminate.
  apply (CReal_le_trans _ (CReal_abs (x - y) + CReal_abs (CReal_abs (a - x) - CReal_abs (a - y)))).
  apply CReal_abs_triang. rewrite CReal_mult_1_r. apply CReal_plus_le_compat_l.
  rewrite (CReal_abs_minus_sym x y).
  rewrite (CReal_abs_morph (y-x) ((a-x)-(a-y))).
  apply CReal_abs_triang_inv2.
  unfold CReal_minus. rewrite (CReal_plus_comm (a + - x)).
  rewrite <- CReal_plus_assoc. apply CReal_plus_morph. 2: reflexivity.
  rewrite CReal_plus_comm, CReal_opp_plus_distr, <- CReal_plus_assoc.
  rewrite CReal_plus_opp_r, CReal_opp_involutive, CReal_plus_0_l.
  reflexivity.
  rewrite <- CReal_mult_plus_distr_l, <- inject_Q_plus.
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
  apply CReal_mult_le_compat_r. apply inject_Q_le. discriminate.
  apply (CReal_le_trans _ (CReal_abs (x - y) + CReal_abs (CReal_abs (a - y) - CReal_abs (a - x)))).
  apply CReal_abs_triang. rewrite CReal_mult_1_r. apply CReal_plus_le_compat_l.
  rewrite (CReal_abs_morph (x-y) ((a-y)-(a-x))).
  apply CReal_abs_triang_inv2.
  unfold CReal_minus. rewrite (CReal_plus_comm (a + - y)).
  rewrite <- CReal_plus_assoc. apply CReal_plus_morph. 2: reflexivity.
  rewrite CReal_plus_comm, CReal_opp_plus_distr, <- CReal_plus_assoc.
  rewrite CReal_plus_opp_r, CReal_opp_involutive, CReal_plus_0_l.
  reflexivity.
  rewrite <- CReal_mult_plus_distr_l, <- inject_Q_plus.
  rewrite CReal_mult_assoc, <- inject_Q_mult.
  setoid_replace ((1 + 1) * (1 # 2))%Q with 1%Q. 2: reflexivity.
  rewrite CReal_mult_1_r. apply CRealLe_refl.
Qed.

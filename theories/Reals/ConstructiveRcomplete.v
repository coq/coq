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

Require Import QArith_base.
Require Import Qabs.
Require Import ConstructiveCauchyReals.
Require Import ConstructiveRIneq.

Local Open Scope R_scope_constr.

Lemma CReal_absSmall : forall x y : CReal,
    (exists n : positive, Qlt (2 # n)
                             (proj1_sig x (Pos.to_nat n) - Qabs (proj1_sig y (Pos.to_nat n))))
    -> (CRealLt (CReal_opp x) y /\ CRealLt y x).
Proof.
  intros. destruct H as [n maj]. split.
  - exists n. destruct x as [xn caux], y as [yn cauy]; simpl.
    simpl in maj. unfold Qminus. rewrite Qopp_involutive.
    rewrite Qplus_comm.
    apply (Qlt_le_trans _ (xn (Pos.to_nat n) - Qabs (yn (Pos.to_nat n)))).
    apply maj. apply Qplus_le_r.
    rewrite <- (Qopp_involutive (yn (Pos.to_nat n))).
    apply Qopp_le_compat. rewrite Qabs_opp. apply Qle_Qabs.
  - exists n. destruct x as [xn caux], y as [yn cauy]; simpl.
    simpl in maj.
    apply (Qlt_le_trans _ (xn (Pos.to_nat n) - Qabs (yn (Pos.to_nat n)))).
    apply maj. apply Qplus_le_r. apply Qopp_le_compat. apply Qle_Qabs.
Qed.

Definition Un_cv_mod (un : nat -> CReal) (l : CReal) : Set
  := forall n : positive,
    { p : nat | forall i:nat, le p i
                     -> -IQR (1#n) < un i - l < IQR (1#n) }.

Lemma Un_cv_mod_eq : forall (v u : nat -> CReal) (s : CReal),
    (forall n:nat, u n == v n)
    -> Un_cv_mod u s -> Un_cv_mod v s.
Proof.
  intros v u s seq H1 p. specialize (H1 p) as [N H0].
  exists N. intros. rewrite <- seq. apply H0. apply H.
Qed.

Lemma IQR_double_inv : forall n : positive,
    IQR (1 # 2*n) + IQR (1 # 2*n) == IQR (1 # n).
Proof.
  intros. apply (Rmult_eq_reg_l (IPR (2*n))).
  unfold IQR. do 2 rewrite Rmult_1_l.
  rewrite Rmult_plus_distr_l, Rinv_r, IPR_double, Rmult_assoc, Rinv_r.
  rewrite (Rmult_plus_distr_r 1 1). ring.
  right. apply IPR_pos.
  right. apply IPR_pos.
  right. apply IPR_pos.
Qed.

Lemma CV_mod_plus :
  forall (An Bn:nat -> CReal) (l1 l2:CReal),
    Un_cv_mod An l1 -> Un_cv_mod Bn l2
    -> Un_cv_mod (fun i:nat => An i + Bn i) (l1 + l2).
Proof.
  assert (forall x:CReal, x + x == 2*x) as double.
  { intro. rewrite (Rmult_plus_distr_r 1 1), Rmult_1_l. reflexivity. }
  intros. intros n.
  destruct (H (2*n)%positive).
  destruct (H0 (2*n)%positive).
  exists (Nat.max x x0). intros.
  setoid_replace (An i + Bn i - (l1 + l2))
    with (An i - l1 + (Bn i - l2)). 2: ring.
  rewrite <- IQR_double_inv. split.
  - rewrite Ropp_plus_distr.
    apply Rplus_lt_compat. apply a. apply (le_trans _ (max x x0)).
    apply Nat.le_max_l. apply H1.
    apply a0. apply (le_trans _ (max x x0)).
    apply Nat.le_max_r. apply H1.
  - apply Rplus_lt_compat. apply a. apply (le_trans _ (max x x0)).
    apply Nat.le_max_l. apply H1.
    apply a0. apply (le_trans _ (max x x0)).
    apply Nat.le_max_r. apply H1.
Qed.

Lemma Un_cv_mod_const : forall x : CReal,
    Un_cv_mod (fun _ => x) x.
Proof.
  intros. intro p. exists O. intros.
  unfold CReal_minus. rewrite Rplus_opp_r.
  split. rewrite <- Ropp_0.
  apply Ropp_gt_lt_contravar. unfold IQR. rewrite Rmult_1_l.
  apply Rinv_0_lt_compat. unfold IQR. rewrite Rmult_1_l.
  apply Rinv_0_lt_compat.
Qed.

(** Unicity of limit for convergent sequences *)
Lemma UL_sequence_mod :
  forall (Un:nat -> CReal) (l1 l2:CReal),
    Un_cv_mod Un l1 -> Un_cv_mod Un l2 -> l1 == l2.
Proof.
  assert (forall (Un:nat -> CReal) (l1 l2:CReal),
             Un_cv_mod Un l1 -> Un_cv_mod Un l2
             -> l1 <= l2).
  - intros Un l1 l2; unfold Un_cv_mod; intros. intro abs.
    assert (0 < l1 - l2) as epsPos.
    { apply Rgt_minus. apply abs. }
    destruct (Rup_nat ((/(l1-l2)) (or_intror epsPos))) as [n nmaj].
    assert (lt 0 n) as nPos.
    { apply (INR_lt 0). apply (Rlt_trans _ ((/ (l1 - l2)) (or_intror epsPos))).
      2: apply nmaj. apply Rinv_0_lt_compat. }
    specialize (H (2*Pos.of_nat n)%positive) as [i imaj].
    specialize (H0 (2*Pos.of_nat n))%positive as [j jmaj].
    specialize (imaj (max i j) (Nat.le_max_l _ _)) as [imaj _].
    specialize (jmaj (max i j) (Nat.le_max_r _ _)) as [_ jmaj].
    apply Ropp_gt_lt_contravar in imaj. rewrite Ropp_involutive in imaj.
    unfold CReal_minus in imaj. rewrite Ropp_plus_distr in imaj.
    rewrite Ropp_involutive in imaj. rewrite Rplus_comm in imaj.
    apply (Rplus_lt_compat _ _ _ _ imaj) in jmaj.
    clear imaj.
    rewrite Rplus_assoc in jmaj. unfold CReal_minus in jmaj.
    rewrite <- (Rplus_assoc (- Un (Init.Nat.max i j))) in jmaj.
    rewrite Rplus_opp_l in jmaj.
    rewrite <- double in jmaj. rewrite Rplus_0_l in jmaj.
    rewrite (Rmult_plus_distr_r 1 1), Rmult_1_l, IQR_double_inv in jmaj.
    unfold IQR in jmaj. rewrite Rmult_1_l in jmaj.
    apply (Rmult_lt_compat_l (IPR (Pos.of_nat n))) in jmaj.
    rewrite Rinv_r, <- INR_IPR, Nat2Pos.id in jmaj.
    apply (Rmult_lt_compat_l (l1-l2)) in nmaj.
    rewrite Rinv_r in nmaj. rewrite Rmult_comm in jmaj.
    apply (CRealLt_asym 1 ((l1-l2)*INR n)); assumption.
    right. apply epsPos. apply epsPos.
    intro abss. subst n. inversion nPos.
    right. apply IPR_pos. apply IPR_pos.
  - intros. split; apply (H Un); assumption.
Qed.

Definition Un_cauchy_mod (un : nat -> CReal) : Set
  := forall n : positive,
    { p : nat | forall i j:nat, le p i
                       -> le p j
                       -> -IQR (1#n) < un i - un j < IQR (1#n) }.

Definition RQ_limit : forall (x : CReal) (n:nat),
    { q:Q | x < IQR q < x + IQR (1 # Pos.of_nat n) }.
Proof.
  intros x n. apply (FQ_dense x (x + IQR (1 # Pos.of_nat n))).
  rewrite <- (Rplus_0_r x). rewrite Rplus_assoc.
  apply Rplus_lt_compat_l. rewrite Rplus_0_l. apply IQR_pos.
  reflexivity.
Qed.

Definition Un_cauchy_Q (xn : nat -> Q) : Set
  := forall n : positive,
    { k : nat | forall p q : nat, le k p -> le k q
                                  -> Qlt (-(1#n)) (xn p - xn q)
                                     /\ Qlt (xn p - xn q) (1#n) }.

Lemma Rdiag_cauchy_sequence : forall (xn : nat -> CReal),
    Un_cauchy_mod xn
    -> Un_cauchy_Q (fun n => proj1_sig (RQ_limit (xn n) n)).
Proof.
  intros xn H p. specialize (H (2 * p)%positive) as [k cv].
  exists (max k (2 * Pos.to_nat p)). intros.
  specialize (cv p0 q). destruct cv.
  apply (le_trans _ (Init.Nat.max k (2 * Pos.to_nat p))).
  apply Nat.le_max_l. apply H.
  apply (le_trans _ (Init.Nat.max k (2 * Pos.to_nat p))).
  apply Nat.le_max_l. apply H0.
  split.
  - apply lt_IQR. unfold Qminus.
    apply (Rlt_trans _ (xn p0 - (xn q + IQR (1 # 2 * p)))).
    + unfold CReal_minus. rewrite Ropp_plus_distr. unfold CReal_minus.
      rewrite <- Rplus_assoc.
      apply (Rplus_lt_reg_r (IQR (1 # 2 * p))).
      rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r.
      rewrite <- plus_IQR.
      setoid_replace (- (1 # p) + (1 # 2 * p))%Q with (- (1 # 2 * p))%Q.
      rewrite opp_IQR. exact H1.
      rewrite Qplus_comm.
      setoid_replace (1#p)%Q with (2 # 2 *p)%Q. rewrite Qinv_minus_distr.
      reflexivity. reflexivity.
    + rewrite plus_IQR. apply Rplus_lt_compat.
      destruct (RQ_limit (xn p0) p0); simpl. apply a.
      destruct (RQ_limit (xn q) q); unfold proj1_sig.
      rewrite opp_IQR. apply Ropp_gt_lt_contravar.
      apply (Rlt_le_trans _ (xn q + IQR (1 # Pos.of_nat q))).
      apply a. apply Rplus_le_compat_l. apply IQR_le.
      apply Z2Nat.inj_le. discriminate. discriminate.
      simpl. assert ((Pos.to_nat p~0 <= q)%nat).
      { apply (le_trans _ (Init.Nat.max k (2 * Pos.to_nat p))).
        2: apply H0. replace (p~0)%positive with (2*p)%positive.
        2: reflexivity. rewrite Pos2Nat.inj_mul.
        apply Nat.le_max_r. }
      rewrite Nat2Pos.id. apply H3. intro abs. subst q.
      inversion H3. pose proof (Pos2Nat.is_pos (p~0)).
      rewrite H5 in H4. inversion H4.
  - apply lt_IQR. unfold Qminus.
    apply (Rlt_trans _ (xn p0 + IQR (1 # 2 * p) - xn q)).
    + rewrite plus_IQR. apply Rplus_lt_compat.
      destruct (RQ_limit (xn p0) p0); unfold proj1_sig.
      apply (Rlt_le_trans _ (xn p0 + IQR (1 # Pos.of_nat p0))).
      apply a. apply Rplus_le_compat_l. apply IQR_le.
      apply Z2Nat.inj_le. discriminate. discriminate.
      simpl. assert ((Pos.to_nat p~0 <= p0)%nat).
      { apply (le_trans _ (Init.Nat.max k (2 * Pos.to_nat p))).
        2: apply H. replace (p~0)%positive with (2*p)%positive.
        2: reflexivity. rewrite Pos2Nat.inj_mul.
        apply Nat.le_max_r. }
      rewrite Nat2Pos.id. apply H3. intro abs. subst p0.
      inversion H3. pose proof (Pos2Nat.is_pos (p~0)).
      rewrite H5 in H4. inversion H4.
      rewrite opp_IQR. apply Ropp_gt_lt_contravar.
      destruct (RQ_limit (xn q) q); simpl. apply a.
    + unfold CReal_minus. rewrite (Rplus_comm (xn p0)).
      rewrite Rplus_assoc.
      apply (Rplus_lt_reg_l (- IQR (1 # 2 * p))).
      rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
      rewrite <- opp_IQR. rewrite <- plus_IQR.
      setoid_replace (- (1 # 2 * p) + (1 # p))%Q with (1 # 2 * p)%Q.
      exact H2. rewrite Qplus_comm.
      setoid_replace (1#p)%Q with (2 # 2*p)%Q. rewrite Qinv_minus_distr.
      reflexivity. reflexivity.
Qed.

(* An element of CReal is a Cauchy sequence of rational numbers,
   show that it converges to itself in CReal. *)
Lemma CReal_cv_self : forall (qn : nat -> Q) (x : CReal) (cvmod : positive -> nat),
    QSeqEquiv qn (fun n => proj1_sig x n) cvmod
    -> Un_cv_mod (fun n => IQR (qn n)) x.
Proof.
  intros qn x cvmod H p.
  specialize (H (2*p)%positive). exists (cvmod (2*p)%positive).
  intros p0 H0. unfold CReal_minus. rewrite FinjectQ_CReal.
  setoid_replace (IQR (qn p0)) with (inject_Q (qn p0)).
  2: apply FinjectQ_CReal.
  apply CReal_absSmall.
  exists (Pos.max (4 * p)%positive (Pos.of_nat (cvmod (2 * p)%positive))).
  setoid_replace (proj1_sig (inject_Q (1 # p)) (Pos.to_nat (Pos.max (4 * p) (Pos.of_nat (cvmod (2 * p)%positive)))))
    with (1 # p)%Q.
  2: reflexivity.
  setoid_replace (proj1_sig (CReal_plus (inject_Q (qn p0)) (CReal_opp x)) (Pos.to_nat (Pos.max (4 * p) (Pos.of_nat (cvmod (2 * p)%positive)))))
    with (qn p0 - proj1_sig x (2 * (Pos.to_nat (Pos.max (4 * p) (Pos.of_nat (cvmod (2 * p)%positive)))))%nat)%Q.
  2: destruct x; reflexivity.
  apply (Qle_lt_trans _ (1 # 2 * p)).
  unfold Qle; simpl. rewrite Pos2Z.inj_max. apply Z.le_max_l.
  rewrite <- (Qplus_lt_r _ _ (-(1#p))). unfold Qminus. rewrite Qplus_assoc.
  rewrite (Qplus_comm _ (1#p)). rewrite Qplus_opp_r. rewrite Qplus_0_l.
  setoid_replace (- (1 # p) + (1 # 2 * p))%Q with (-(1 # 2 * p))%Q.
  apply Qopp_lt_compat. apply H. apply H0.

  rewrite Pos2Nat.inj_max.
  apply (le_trans _ (1 * Nat.max (Pos.to_nat (4 * p)) (Pos.to_nat (Pos.of_nat (cvmod (2 * p)%positive))))).
  destruct (cvmod (2*p)%positive). apply le_0_n. rewrite mult_1_l.
  rewrite Nat2Pos.id. 2: discriminate. apply Nat.le_max_r.
  apply Nat.mul_le_mono_nonneg_r. apply le_0_n. auto.
  setoid_replace (1 # p)%Q with (2 # 2 * p)%Q.
  rewrite Qplus_comm. rewrite Qinv_minus_distr.
  reflexivity. reflexivity.
Qed.

Lemma Un_cv_extens : forall (xn yn : nat -> CReal) (l : CReal),
    Un_cv_mod xn l
    -> (forall n : nat, xn n == yn n)
    -> Un_cv_mod yn l.
Proof.
  intros. intro p. destruct (H p) as [n cv]. exists n.
  intros. unfold CReal_minus. rewrite <- (H0 i). apply cv. apply H1.
Qed.

(* Q is dense in Archimedean fields, so all real numbers
   are limits of rational sequences.
   The biggest computable such field has all rational limits. *)
Lemma R_has_all_rational_limits : forall qn : nat -> Q,
    Un_cauchy_Q qn
    -> { r : CReal & Un_cv_mod (fun n => IQR (qn n)) r }.
Proof.
  (* qn is an element of CReal. Show that IQR qn
     converges to it in CReal. *)
  intros.
  destruct (standard_modulus qn (fun p => proj1_sig (H p))).
  - intros p n k H0 H1. destruct (H p); simpl in H0,H1.
    specialize (a n k H0 H1). apply Qabs_case.
    intros _. apply a. intros _.
    rewrite <- (Qopp_involutive (1#p)). apply Qopp_lt_compat.
    apply a.
  - exists (exist _ (fun n : nat =>
                       qn (increasing_modulus (fun p : positive => proj1_sig (H p)) n)) H0).
    apply (Un_cv_extens (fun n : nat => IQR (qn n))).
    apply (CReal_cv_self qn (exist _ (fun n : nat =>
                qn (increasing_modulus (fun p : positive => proj1_sig (H p)) n)) H0)
          (fun p : positive => Init.Nat.max (proj1_sig (H p)) (Pos.to_nat p))).
    apply H1. intro n. reflexivity.
Qed.

Lemma Rcauchy_complete : forall (xn : nat -> CReal),
    Un_cauchy_mod xn
    -> { l : CReal & Un_cv_mod xn l }.
Proof.
  intros xn cau.
  destruct (R_has_all_rational_limits (fun n => proj1_sig (RQ_limit (xn n) n))
                                      (Rdiag_cauchy_sequence xn cau))
    as [l cv].
  exists l. intro p. specialize (cv (2*p)%positive) as [k cv].
  exists (max k (2 * Pos.to_nat p)). intros p0 H. specialize (cv p0).
  destruct cv. apply (le_trans _ (max k (2 * Pos.to_nat p))).
  apply Nat.le_max_l. apply H.
  destruct (RQ_limit (xn p0) p0) as [q maj]; unfold proj1_sig in H0,H1.
  split.
  - apply (Rlt_trans _ (IQR q - IQR (1 # 2 * p) - l)).
    + unfold CReal_minus. rewrite (Rplus_comm (IQR q)).
      apply (Rplus_lt_reg_l (IQR (1 # 2 * p))).
      ring_simplify. unfold CReal_minus. rewrite <- opp_IQR. rewrite <- plus_IQR.
      setoid_replace ((1 # 2 * p) + - (1 # p))%Q with (-(1#2*p))%Q.
      rewrite opp_IQR. apply H0.
      setoid_replace (1#p)%Q with (2 # 2*p)%Q.
      rewrite Qinv_minus_distr. reflexivity. reflexivity.
    + unfold CReal_minus. apply Rplus_lt_compat_r.
      apply (Rplus_lt_reg_r (IQR (1 # 2 * p))).
      ring_simplify. rewrite Rplus_comm.
      apply (Rlt_le_trans _ (xn p0 + IQR (1 # Pos.of_nat p0))).
      apply maj. apply Rplus_le_compat_l.
      apply IQR_le.
      apply Z2Nat.inj_le. discriminate. discriminate.
      simpl. assert ((Pos.to_nat p~0 <= p0)%nat).
      { apply (le_trans _ (Init.Nat.max k (2 * Pos.to_nat p))).
        2: apply H. replace (p~0)%positive with (2*p)%positive.
        2: reflexivity. rewrite Pos2Nat.inj_mul.
        apply Nat.le_max_r. }
      rewrite Nat2Pos.id. apply H2. intro abs. subst p0.
      inversion H2. pose proof (Pos2Nat.is_pos (p~0)).
      rewrite H4 in H3. inversion H3.
  - apply (Rlt_trans _ (IQR q - l)).
    + apply Rplus_lt_compat_r. apply maj.
    + apply (Rlt_trans _ (IQR (1 # 2 * p))).
      apply H1. apply IQR_lt.
      rewrite <- Qplus_0_r.
      setoid_replace (1#p)%Q with ((1#2*p)+(1#2*p))%Q.
      apply Qplus_lt_r. reflexivity.
      rewrite Qplus_same_denom. reflexivity.
Qed.

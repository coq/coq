(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

Require Import QArith_base.
Require Import Qabs.
Require Import ConstructiveReals.
Require Import ConstructiveCauchyRealsMult.
Require Import Logic.ConstructiveEpsilon.
Require Import ConstructiveCauchyAbs.

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

Instance seq_cv_morph
  : forall (un : nat -> CReal), CMorphisms.Proper
      (CMorphisms.respectful CRealEq CRelationClasses.iffT) (seq_cv un).
Proof.
  split. intros. apply (seq_cv_proper un x). exact H0. exact H.
  intros. apply (seq_cv_proper un y). exact H0. symmetry. exact H.
Qed.

Lemma growing_transit : forall un : nat -> CReal,
    (forall n:nat, un n <= un (S n))
    -> forall n p : nat, le n p -> un n <= un p.
Proof.
  induction p.
  - intros. inversion H0. apply CRealLe_refl.
  - intros. apply Nat.le_succ_r in H0. destruct H0.
    apply (CReal_le_trans _ (un p)). apply IHp, H0. apply H.
    subst n. apply CRealLe_refl.
Qed.

Lemma growing_infinite : forall un : nat -> nat,
    (forall n:nat, lt (un n) (un (S n)))
    -> forall n : nat, le n (un n).
Proof.
  induction n.
  - apply le_0_n.
  - specialize (H n). unfold lt in H.
    apply (le_trans _ (S (un n))). apply le_n_S, IHn. exact H.
Qed.

Lemma Un_cv_growing : forall (un : nat -> CReal) (l : CReal),
    (forall n:nat, un n <= un (S n))
    -> (forall n:nat, un n <= l)
    -> (forall p : positive, { n : nat  |  l - un n <= inject_Q (1#p) })
    -> seq_cv un l.
Proof.
  intros. intro p.
  specialize (H1 p) as [n nmaj]. exists n.
  intros. rewrite CReal_abs_minus_sym, CReal_abs_right.
  apply (CReal_le_trans _ (l - un n)). apply CReal_plus_le_compat_l.
  apply CReal_opp_ge_le_contravar.
  exact (growing_transit _ H n i H1). exact nmaj.
  rewrite <- (CReal_plus_opp_r (un i)). apply CReal_plus_le_compat.
  apply H0. apply CRealLe_refl.
Qed.



(* Sharpen the archimedean property : constructive versions of
   the usual floor and ceiling functions. *)
Definition Rfloor (a : CReal)
  : { p : Z  &  inject_Q (p#1) < a < inject_Q (p#1) + 2 }.
Proof.
  destruct (CRealArchimedean a) as [n [H H0]].
  exists (n-2)%Z. split.
  - setoid_replace (n - 2 # 1)%Q with ((n#1) + - 2)%Q.
    rewrite inject_Q_plus, (opp_inject_Q 2).
    apply (CReal_plus_lt_reg_r 2). ring_simplify.
    rewrite CReal_plus_comm. exact H0.
    rewrite Qinv_plus_distr. reflexivity.
  - setoid_replace (n - 2 # 1)%Q with ((n#1) + - 2)%Q.
    rewrite inject_Q_plus, (opp_inject_Q 2).
    ring_simplify. exact H.
    rewrite Qinv_plus_distr. reflexivity.
Defined.


(* A point in an archimedean field is the limit of a
   sequence of rational numbers (n maps to the q between
   a and a+1/n). This will yield a maximum
   archimedean field, which is the field of real numbers. *)
Definition FQ_dense (a b : CReal)
  : a < b -> { q : Q & a < inject_Q q < b }.
Proof.
  intros H. assert (0 < b - a) as epsPos.
  { apply (CReal_plus_lt_compat_l (-a)) in H.
    rewrite CReal_plus_opp_l, CReal_plus_comm in H.
    apply H. }
  pose proof (Rup_pos ((/(b-a)) (inr epsPos)))
    as [n maj].
  destruct (Rfloor (inject_Q (2 * Z.pos n # 1) * b)) as [p maj2].
  exists (p # (2*n))%Q. split.
  - apply (CReal_lt_trans a (b - inject_Q (1 # n))).
    apply (CReal_plus_lt_reg_r (inject_Q (1#n))).
    unfold CReal_minus. rewrite CReal_plus_assoc. rewrite CReal_plus_opp_l.
    rewrite CReal_plus_0_r. apply (CReal_plus_lt_reg_l (-a)).
    rewrite <- CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_l.
    rewrite CReal_plus_comm.
    apply (CReal_mult_lt_reg_l (inject_Q (Z.pos n # 1))).
    apply inject_Q_lt. reflexivity. rewrite <- inject_Q_mult.
    setoid_replace ((Z.pos n # 1) * (1 # n))%Q with 1%Q.
    apply (CReal_mult_lt_compat_l (b-a)) in maj.
    rewrite CReal_inv_r, CReal_mult_comm in maj. exact maj.
    exact epsPos. unfold Qeq; simpl. do 2 rewrite Pos.mul_1_r. reflexivity.
    apply (CReal_plus_lt_reg_r (inject_Q (1 # n))).
    unfold CReal_minus. rewrite CReal_plus_assoc, CReal_plus_opp_l.
    rewrite CReal_plus_0_r. rewrite <- inject_Q_plus.
    destruct maj2 as [_ maj2].
    setoid_replace ((p # 2 * n) + (1 # n))%Q
      with ((p + 2 # 2 * n))%Q.
    apply (CReal_mult_lt_reg_r (inject_Q (Z.pos (2 * n) # 1))).
    apply inject_Q_lt. reflexivity. rewrite <- inject_Q_mult.
    setoid_replace ((p + 2 # 2 * n) * (Z.pos (2 * n) # 1))%Q
      with ((p#1) + 2)%Q.
    rewrite inject_Q_plus. rewrite Pos2Z.inj_mul.
    rewrite CReal_mult_comm. exact maj2.
    unfold Qeq; simpl. rewrite Pos.mul_1_r, Z.mul_1_r. ring.
    setoid_replace (1#n)%Q with (2#2*n)%Q. 2: reflexivity.
    apply Qinv_plus_distr.
  - destruct maj2 as [maj2 _].
    apply (CReal_mult_lt_reg_r (inject_Q (Z.pos (2 * n) # 1))).
    apply inject_Q_lt. reflexivity.
    rewrite <- inject_Q_mult.
    setoid_replace ((p # 2 * n) * (Z.pos (2 * n) # 1))%Q
      with ((p#1))%Q.
    rewrite CReal_mult_comm. exact maj2.
    unfold Qeq; simpl. rewrite Pos.mul_1_r, Z.mul_1_r. reflexivity.
Qed.

Definition RQ_limit : forall (x : CReal) (n:nat),
    { q:Q  &  x < inject_Q q < x + inject_Q (1 # Pos.of_nat n) }.
Proof.
  intros x n. apply (FQ_dense x (x + inject_Q (1 # Pos.of_nat n))).
  rewrite <- (CReal_plus_0_r x). rewrite CReal_plus_assoc.
  apply CReal_plus_lt_compat_l. rewrite CReal_plus_0_l. apply inject_Q_lt.
  reflexivity.
Qed.

Lemma Qabs_Rabs : forall q : Q,
    inject_Q (Qabs q) == CReal_abs (inject_Q q).
Proof.
  intro q. apply Qabs_case.
  - intros. rewrite CReal_abs_right. reflexivity.
    apply inject_Q_le, H.
  - intros. rewrite CReal_abs_left, opp_inject_Q. reflexivity.
    apply inject_Q_le, H.
Qed.

Definition Un_cauchy_Q (xn : nat -> Q) : Set
  := forall n : positive,
    { k : nat | forall p q : nat, le k p -> le k q
                                  -> (Qabs (xn p - xn q) <= 1#n)%Q }.

Lemma CReal_smaller_interval : forall a b c d : CReal,
    a <= c -> c <= b
    -> a <= d -> d <= b
    -> CReal_abs (d - c) <= b-a.
Proof.
  intros. apply CReal_abs_le. split.
  - apply (CReal_plus_le_reg_l (b+c)). ring_simplify.
    apply CReal_plus_le_compat; assumption.
  - apply (CReal_plus_le_reg_l (a+c)). ring_simplify.
    apply CReal_plus_le_compat; assumption.
Qed.

Lemma Rdiag_cauchy_sequence : forall (xn : nat -> CReal),
    Un_cauchy_mod xn
    -> Un_cauchy_Q (fun n:nat => let (l,_) := RQ_limit (xn n) n in l).
Proof.
  intros xn H p. specialize (H (2 * p)%positive) as [k cv].
  exists (max k (2 * Pos.to_nat p)). intros.
  specialize (cv p0 q
                 (le_trans _ _ _ (Nat.le_max_l _ _) H)
                 (le_trans _ _ _ (Nat.le_max_l _ _) H0)).
  destruct (RQ_limit (xn p0) p0) as [r rmaj].
  destruct (RQ_limit (xn q) q) as [s smaj].
  apply Qabs_Qle_condition. split.
  - apply le_inject_Q. unfold Qminus.
    apply (CReal_le_trans _ (xn p0 - (xn q + inject_Q (1 # 2 * p)))).
    + unfold CReal_minus. rewrite CReal_opp_plus_distr.
      rewrite <- CReal_plus_assoc.
      apply (CReal_plus_le_reg_r (xn q - xn p0 - inject_Q (-(1#p)))).
      ring_simplify. unfold CReal_minus. do 2 rewrite <- opp_inject_Q.
      rewrite <- inject_Q_plus.
      setoid_replace (- - (1 # p) + - (1 # 2 * p))%Q with (1 # 2 * p)%Q.
      rewrite CReal_abs_minus_sym in cv.
      exact (CReal_le_trans _ _ _ (CReal_le_abs _ ) cv).
      rewrite Qopp_involutive.
      setoid_replace (1#p)%Q with (2 # 2 *p)%Q. rewrite Qinv_minus_distr.
      reflexivity. reflexivity.
    + rewrite inject_Q_plus. apply CReal_plus_le_compat.
      apply CRealLt_asym.
      destruct (RQ_limit (xn p0) p0); simpl. apply rmaj.
      apply CRealLt_asym.
      rewrite opp_inject_Q. apply CReal_opp_gt_lt_contravar.
      destruct smaj. apply (CReal_lt_le_trans _ _ _ c0).
      apply CReal_plus_le_compat_l. apply inject_Q_le.
      apply Z2Nat.inj_le. discriminate. discriminate.
      simpl. assert ((Pos.to_nat p~0 <= q)%nat).
      { apply (le_trans _ (Init.Nat.max k (2 * Pos.to_nat p))).
        2: apply H0. replace (p~0)%positive with (2*p)%positive.
        2: reflexivity. rewrite Pos2Nat.inj_mul.
        apply Nat.le_max_r. }
      rewrite Nat2Pos.id. apply H1. intro abs. subst q.
      inversion H1. pose proof (Pos2Nat.is_pos (p~0)).
      rewrite H3 in H2. inversion H2.
  - apply le_inject_Q. unfold Qminus.
    apply (CReal_le_trans _ (xn p0 + inject_Q (1 # 2 * p) - xn q)).
    + rewrite inject_Q_plus. apply CReal_plus_le_compat.
      apply CRealLt_asym.
      destruct (RQ_limit (xn p0) p0); unfold proj1_sig.
      apply (CReal_lt_le_trans _ (xn p0 + inject_Q (1 # Pos.of_nat p0))).
      apply rmaj. apply CReal_plus_le_compat_l. apply inject_Q_le.
      apply Z2Nat.inj_le. discriminate. discriminate.
      simpl. assert ((Pos.to_nat p~0 <= p0)%nat).
      { apply (le_trans _ (Init.Nat.max k (2 * Pos.to_nat p))).
        2: apply H. replace (p~0)%positive with (2*p)%positive.
        2: reflexivity. rewrite Pos2Nat.inj_mul.
        apply Nat.le_max_r. }
      rewrite Nat2Pos.id. apply H1. intro abs. subst p0.
      inversion H1. pose proof (Pos2Nat.is_pos (p~0)).
      rewrite H3 in H2. inversion H2.
      apply CRealLt_asym.
      rewrite opp_inject_Q. apply CReal_opp_gt_lt_contravar.
      destruct (RQ_limit (xn q) q); simpl. apply smaj.
    + unfold CReal_minus. rewrite (CReal_plus_comm (xn p0)).
      rewrite CReal_plus_assoc.
      apply (CReal_plus_le_reg_l (- inject_Q (1 # 2 * p))).
      rewrite <- CReal_plus_assoc. rewrite CReal_plus_opp_l. rewrite CReal_plus_0_l.
      rewrite <- opp_inject_Q. rewrite <- inject_Q_plus.
      setoid_replace (- (1 # 2 * p) + (1 # p))%Q with (1 # 2 * p)%Q.
      exact (CReal_le_trans _ _ _ (CReal_le_abs _) cv).
      rewrite Qplus_comm.
      setoid_replace (1#p)%Q with (2 # 2*p)%Q. rewrite Qinv_minus_distr.
      reflexivity. reflexivity.
Qed.

Lemma CReal_absSmall : forall (x y : CReal) (n : positive),
    (Qlt (2 # n)
         (proj1_sig x (Pos.to_nat n) - Qabs (proj1_sig y (Pos.to_nat n))))
    -> CReal_abs y <= x.
Proof.
  intros x y n maj. apply CReal_abs_le. split.
  - apply CRealLt_asym. exists n. destruct x as [xn caux], y as [yn cauy]; simpl.
    simpl in maj. unfold Qminus. rewrite Qopp_involutive.
    rewrite Qplus_comm.
    apply (Qlt_le_trans _ (xn (Pos.to_nat n) - Qabs (yn (Pos.to_nat n)))).
    apply maj. apply Qplus_le_r.
    rewrite <- (Qopp_involutive (yn (Pos.to_nat n))).
    apply Qopp_le_compat. rewrite Qabs_opp. apply Qle_Qabs.
  - apply CRealLt_asym. exists n. destruct x as [xn caux], y as [yn cauy]; simpl.
    simpl in maj.
    apply (Qlt_le_trans _ (xn (Pos.to_nat n) - Qabs (yn (Pos.to_nat n)))).
    apply maj. apply Qplus_le_r. apply Qopp_le_compat. apply Qle_Qabs.
Qed.


(* An element of CReal is a Cauchy sequence of rational numbers,
   show that it converges to itself in CReal. *)
Lemma CReal_cv_self : forall (qn : nat -> Q) (x : CReal) (cvmod : positive -> nat),
    QSeqEquiv qn (fun n => proj1_sig x n) cvmod
    -> seq_cv (fun n => inject_Q (qn n)) x.
Proof.
  intros qn x cvmod H p.
  specialize (H (2*p)%positive). exists (cvmod (2*p)%positive).
  intros p0 H0.
  apply (CReal_absSmall
           _ _ (Pos.max (4 * p)%positive (Pos.of_nat (cvmod (2 * p)%positive)))).
  setoid_replace (proj1_sig (inject_Q (1 # p)) (Pos.to_nat (Pos.max (4 * p) (Pos.of_nat (cvmod (2 * p)%positive)))))
    with (1 # p)%Q.
  2: reflexivity.
  setoid_replace (proj1_sig (CReal_plus (inject_Q (qn p0)) (CReal_opp x)) (Pos.to_nat (Pos.max (4 * p) (Pos.of_nat (cvmod (2 * p)%positive)))))
    with (qn p0 - proj1_sig x (2 * (Pos.to_nat (Pos.max (4 * p) (Pos.of_nat (cvmod (2 * p)%positive)))))%nat)%Q.
  2: destruct x; reflexivity.
  apply (Qle_lt_trans _ (1 # 2 * p)).
  unfold Qle; simpl. rewrite Pos2Z.inj_max. apply Z.le_max_l.
  rewrite <- (Qplus_lt_r
               _ _ (Qabs
     (qn p0 -
      proj1_sig x
                (2 * Pos.to_nat (Pos.max (4 * p) (Pos.of_nat (cvmod (2 * p)%positive))))%nat)
                    -(1#2*p))).
  ring_simplify.
  setoid_replace (-1 * (1 # 2 * p) + (1 # p))%Q with (1 # 2 * p)%Q.
  apply H. apply H0. rewrite Pos2Nat.inj_max.
  apply (le_trans _ (1 * Nat.max (Pos.to_nat (4 * p)) (Pos.to_nat (Pos.of_nat (cvmod (2 * p)%positive))))).
  destruct (cvmod (2*p)%positive). apply le_0_n. rewrite mult_1_l.
  rewrite Nat2Pos.id. 2: discriminate. apply Nat.le_max_r.
  apply Nat.mul_le_mono_nonneg_r. apply le_0_n. auto.
  setoid_replace (1 # p)%Q with (2 # 2 * p)%Q.
  rewrite Qplus_comm. rewrite Qinv_minus_distr.
  reflexivity. reflexivity.
Qed.

(* Q is dense in Archimedean fields, so all real numbers
   are limits of rational sequences.
   The biggest computable such field has all rational limits. *)
Lemma R_has_all_rational_limits : forall qn : nat -> Q,
    Un_cauchy_Q qn
    -> { r : CReal  &  seq_cv (fun n:nat => inject_Q (qn n)) r }.
Proof.
  (* qn is an element of CReal. Show that inject_Q qn
     converges to it in CReal. *)
  intros.
  destruct (standard_modulus qn (fun p => proj1_sig (H (Pos.succ p)))).
  - intros p n k H0 H1. destruct (H (Pos.succ p)%positive) as [x a]; simpl in H0,H1.
    specialize (a n k H0 H1).
    apply (Qle_lt_trans _ (1#Pos.succ p) _ a).
    apply Pos2Z.pos_lt_pos. simpl. apply Pos.lt_succ_diag_r.
  - exists (exist _ (fun n : nat =>
                       qn (increasing_modulus (fun p : positive => proj1_sig (H (Pos.succ p))) n)) H0).
    apply (CReal_cv_self qn (exist _ (fun n : nat =>
                qn (increasing_modulus (fun p : positive => proj1_sig (H (Pos.succ p))) n)) H0)
          (fun p : positive => Init.Nat.max (proj1_sig (H (Pos.succ p))) (Pos.to_nat p))).
    apply H1.
Qed.

Lemma Rcauchy_complete : forall (xn : nat -> CReal),
    Un_cauchy_mod xn
    -> { l : CReal  &  seq_cv xn l }.
Proof.
  intros xn cau.
  destruct (R_has_all_rational_limits (fun n => let (l,_) := RQ_limit (xn n) n in l)
                                      (Rdiag_cauchy_sequence xn cau))
    as [l cv].
  exists l. intro p. specialize (cv (2*p)%positive) as [k cv].
  exists (max k (2 * Pos.to_nat p)). intros p0 H.
  specialize (cv p0 (le_trans _ _ _ (Nat.le_max_l _ _) H)).
  destruct (RQ_limit (xn p0) p0) as [q maj].
  apply CReal_abs_le. split.
  - apply (CReal_le_trans _ (inject_Q q - inject_Q (1 # 2 * p) - l)).
    + unfold CReal_minus. rewrite (CReal_plus_comm (inject_Q q)).
      apply (CReal_plus_le_reg_r (inject_Q (1 # p) + l - inject_Q q)).
      ring_simplify. unfold CReal_minus.
      rewrite <- (opp_inject_Q (1# 2*p)), <- inject_Q_plus.
      setoid_replace ((1 # p) + - (1 # 2* p))%Q with (1#2*p)%Q.
      rewrite CReal_abs_minus_sym in cv.
      exact (CReal_le_trans _ _ _ (CReal_le_abs _) cv).
      setoid_replace (1#p)%Q with (2 # 2*p)%Q.
      rewrite Qinv_minus_distr. reflexivity. reflexivity.
    + unfold CReal_minus.
      do 2 rewrite <- (CReal_plus_comm (-l)). apply CReal_plus_le_compat_l.
      apply (CReal_plus_le_reg_r (inject_Q (1 # 2 * p))).
      ring_simplify. rewrite CReal_plus_comm.
      apply (CReal_le_trans _ (xn p0 + inject_Q (1 # Pos.of_nat p0))).
      apply CRealLt_asym, maj. apply CReal_plus_le_compat_l.
      apply inject_Q_le.
      apply Z2Nat.inj_le. discriminate. discriminate.
      simpl. assert ((Pos.to_nat p~0 <= p0)%nat).
      { apply (le_trans _ (Init.Nat.max k (2 * Pos.to_nat p))).
        2: apply H. replace (p~0)%positive with (2*p)%positive.
        2: reflexivity. rewrite Pos2Nat.inj_mul.
        apply Nat.le_max_r. }
      rewrite Nat2Pos.id. apply H0. intro abs. subst p0.
      inversion H0. pose proof (Pos2Nat.is_pos (p~0)).
      rewrite H2 in H1. inversion H1.
  - apply (CReal_le_trans _ (inject_Q q - l)).
    + unfold CReal_minus. do 2 rewrite <- (CReal_plus_comm (-l)).
      apply CReal_plus_le_compat_l. apply CRealLt_asym, maj.
    + apply (CReal_le_trans _ (inject_Q (1 # 2 * p))).
      exact (CReal_le_trans _ _ _ (CReal_le_abs _) cv).
      apply inject_Q_le. rewrite <- Qplus_0_r.
      setoid_replace (1#p)%Q with ((1#2*p)+(1#2*p))%Q.
      apply Qplus_le_r. discriminate.
      rewrite Qinv_plus_distr. reflexivity.
Qed.

Lemma CRealLtIsLinear : isLinearOrder CRealLt.
Proof.
  repeat split. exact CRealLt_asym.
  exact CReal_lt_trans.
  intros. destruct (CRealLt_dec x z y H).
  left. exact c. right. exact c.
Qed.

Lemma CRealAbsLUB : forall x y : CReal,
  x <= y /\ (- x) <= y <-> (CReal_abs x) <= y.
Proof.
  split.
  - intros [H H0]. apply CReal_abs_le. split. 2: exact H.
    apply (CReal_plus_le_reg_r (y-x)). ring_simplify. exact H0.
  - intros. apply CReal_abs_def2 in H. destruct H. split.
   exact H. fold (-x <= y).
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
  intro p. destruct (H p) as [n a]. exists n. intros.
  exact (a i j H0 H1).
  exists l. intros p. destruct (cv p).
  exists x. exact c.
Defined.

Definition CRealConstructive : ConstructiveReals
  := Build_ConstructiveReals
       CReal CRealLt CRealLtIsLinear CRealLtProp
       CRealLtEpsilon CRealLtForget CRealLtDisjunctEpsilon
       (inject_Q 0) (inject_Q 1)
       CReal_plus CReal_opp CReal_mult
       CReal_isRing CReal_isRingExt CRealLt_0_1
       CReal_plus_lt_compat_l CReal_plus_lt_reg_l
       CReal_mult_lt_0_compat
       CReal_inv CReal_inv_l CReal_inv_0_lt_compat
       inject_Q inject_Q_plus inject_Q_mult
       inject_Q_one inject_Q_lt lt_inject_Q
       CRealQ_dense Rup_pos CReal_abs CRealAbsLUB CRealComplete.

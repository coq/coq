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
Require Import Logic.ConstructiveEpsilon.

Local Open Scope CReal_scope.

Lemma CReal_absSmall : forall (x y : CReal) (n : positive),
    (Qlt (2 # n)
         (proj1_sig x (Pos.to_nat n) - Qabs (proj1_sig y (Pos.to_nat n))))
    -> (CRealLt (CReal_opp x) y * CRealLt y x).
Proof.
  intros x y n maj. split.
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

Definition absSmall (a b : CReal) : Set
  := -b < a < b.

Definition Un_cv_mod (un : nat -> CReal) (l : CReal) : Set
  := forall n : positive,
    { p : nat & forall i:nat, le p i -> absSmall (un i - l) (IQR (1#n)) }.

Lemma Un_cv_mod_eq : forall (v u : nat -> CReal) (s : CReal),
    (forall n:nat, u n == v n)
    -> Un_cv_mod u s -> Un_cv_mod v s.
Proof.
  intros v u s seq H1 p. specialize (H1 p) as [N H0].
  exists N. intros. unfold absSmall. split.
  rewrite <- seq. apply H0. apply H.
  rewrite <- seq. apply H0. apply H.
Qed.

Definition Un_cauchy_mod (un : nat -> CReal) : Set
  := forall n : positive,
    { p : nat & forall i j:nat, le p i
                       -> le p j
                       -> -IQR (1#n) < un i - un j < IQR (1#n) }.


(* Sharpen the archimedean property : constructive versions of
   the usual floor and ceiling functions.

   n is a temporary parameter used for the recursion,
   look at Ffloor below. *)
Fixpoint Rfloor_pos (a : CReal) (n : nat) { struct n }
  : 0 < a
    -> a < INR n
    -> { p : nat & INR p < a < INR p + 2 }.
Proof.
  (* Decreasing loop on n, until it is the first integer above a. *)
  intros H H0. destruct n.
  - exfalso. apply (CRealLt_asym 0 a); assumption.
  - destruct n as [|p] eqn:des.
    + (* n = 1 *) exists O. split.
      apply H. rewrite CReal_plus_0_l. apply (CRealLt_trans a (1+0)).
      rewrite CReal_plus_comm, CReal_plus_0_l. apply H0.
      apply CReal_plus_le_lt_compat.
      apply CRealLe_refl. apply CRealLt_0_1.
    + (* n > 1 *)
      destruct (linear_order_T (INR p) a (INR (S p))).
      * rewrite <- CReal_plus_0_l, S_INR, CReal_plus_comm. apply CReal_plus_lt_compat_l.
        apply CRealLt_0_1.
      * exists p. split. exact c.
        rewrite S_INR, S_INR, CReal_plus_assoc in H0. exact H0.
      * apply (Rfloor_pos a n H). rewrite des. apply c.
Qed.

Definition Rfloor (a : CReal)
  : { p : Z & IZR p < a < IZR p + 2 }.
Proof.
  assert (forall x:CReal, 0 < x -> { n : nat & x < INR n }).
  { intros. pose proof (Rarchimedean x) as [n [maj _]].
    destruct n.
    + exfalso. apply (CRealLt_asym 0 x); assumption.
    + exists (Pos.to_nat p). rewrite INR_IPR. apply maj.
    + exfalso. apply (CRealLt_asym 0 x). apply H.
      apply (CRealLt_trans x (IZR (Z.neg p))). apply maj.
      apply (CReal_plus_lt_reg_l (-IZR (Z.neg p))).
      rewrite CReal_plus_comm, CReal_plus_opp_r. rewrite <- opp_IZR.
      rewrite CReal_plus_comm, CReal_plus_0_l.
      apply (IZR_lt 0). reflexivity. }
  destruct (linear_order_T 0 a 1 CRealLt_0_1).
  - destruct (H a c). destruct (Rfloor_pos a x c c0).
    exists (Z.of_nat x0). split; rewrite <- INR_IZR_INZ; apply p.
  - apply (CReal_plus_lt_compat_l (-a)) in c.
    rewrite CReal_plus_comm, CReal_plus_opp_r, CReal_plus_comm in c.
    destruct (H (1-a) c).
    destruct (Rfloor_pos (1-a) x c c0).
    exists (-(Z.of_nat x0 + 1))%Z. split; rewrite opp_IZR, plus_IZR.
    + rewrite <- (CReal_opp_involutive a). apply CReal_opp_gt_lt_contravar.
      destruct p as [_ a0]. apply (CReal_plus_lt_reg_r 1).
      rewrite CReal_plus_comm, CReal_plus_assoc. rewrite <- INR_IZR_INZ. apply a0.
    + destruct p as [a0 _]. apply (CReal_plus_lt_compat_l a) in a0.
      unfold CReal_minus in a0.
      rewrite <- (CReal_plus_comm (1+-a)), CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_r in a0.
      rewrite <- INR_IZR_INZ.
      apply (CReal_plus_lt_reg_r (INR x0)). unfold IZR, IPR, IPR_2.
      ring_simplify. exact a0.
Qed.

Definition Rup_nat (x : CReal)
  : { n : nat & x < INR n }.
Proof.
  intros. destruct (Rarchimedean x) as [p [maj _]].
  destruct p.
  - exists O. apply maj.
  - exists (Pos.to_nat p). rewrite INR_IPR. apply maj.
  - exists O. apply (CRealLt_trans _ (IZR (Z.neg p)) _ maj).
    apply (IZR_lt _ 0). reflexivity.
Qed.

(* A point in an archimedean field is the limit of a
   sequence of rational numbers (n maps to the q between
   a and a+1/n). This will yield a maximum
   archimedean field, which is the field of real numbers. *)
Definition FQ_dense_pos (a b : CReal)
  : 0 < b
    -> a < b -> { q : Q & a < IQR q < b }.
Proof.
  intros H H0.
  assert (0 < b - a) as epsPos.
  { apply (CReal_plus_lt_compat_l (-a)) in H0.
    rewrite CReal_plus_opp_l, CReal_plus_comm in H0.
    apply H0. }
  pose proof (Rup_nat ((/(b-a)) (inr epsPos)))
    as [n maj].
  destruct n as [|k].
  - exfalso.
    apply (CReal_mult_lt_compat_l (b-a)) in maj. 2: apply epsPos.
    rewrite CReal_mult_0_r in maj. rewrite CReal_inv_r in maj.
    apply (CRealLt_asym 0 1). apply CRealLt_0_1. apply maj.
  - (* 0 < n *)
    pose (Pos.of_nat (S k)) as n.
    destruct (Rfloor (IZR (2 * Z.pos n) * b)) as [p maj2].
    exists (p # (2*n))%Q. split.
    + apply (CRealLt_trans a (b - IQR (1 # n))).
      apply (CReal_plus_lt_reg_r (IQR (1#n))).
      unfold CReal_minus. rewrite CReal_plus_assoc. rewrite CReal_plus_opp_l.
      rewrite CReal_plus_0_r. apply (CReal_plus_lt_reg_l (-a)).
      rewrite <- CReal_plus_assoc, CReal_plus_opp_l, CReal_plus_0_l.
      rewrite CReal_plus_comm. unfold IQR.
      rewrite CReal_mult_1_l. apply (CReal_mult_lt_reg_l (IPR n)).
      apply IPR_pos. rewrite CReal_inv_r.
      apply (CReal_mult_lt_compat_l (b-a)) in maj.
      rewrite CReal_inv_r, CReal_mult_comm in maj.
      rewrite <- INR_IPR. unfold n. rewrite Nat2Pos.id.
      apply maj. discriminate. exact epsPos.
      apply (CReal_plus_lt_reg_r (IQR (1 # n))).
      unfold CReal_minus. rewrite CReal_plus_assoc, CReal_plus_opp_l.
      rewrite CReal_plus_0_r. rewrite <- plus_IQR.
      destruct maj2 as [_ maj2].
      setoid_replace ((p # 2 * n) + (1 # n))%Q
        with ((p + 2 # 2 * n))%Q. unfold IQR.
      apply (CReal_mult_lt_reg_r (IZR (Z.pos (2 * n)))).
      apply (IZR_lt 0). reflexivity. rewrite CReal_mult_assoc.
      rewrite CReal_inv_l. rewrite CReal_mult_1_r. rewrite CReal_mult_comm.
      rewrite plus_IZR. apply maj2.
      setoid_replace (1#n)%Q with (2#2*n)%Q. 2: reflexivity.
      apply Qinv_plus_distr.
    + destruct maj2 as [maj2 _]. unfold IQR.
      apply (CReal_mult_lt_reg_r (IZR (Z.pos (2 * n)))).
      apply (IZR_lt 0). apply Pos2Z.is_pos. rewrite CReal_mult_assoc, CReal_inv_l.
      rewrite CReal_mult_1_r, CReal_mult_comm. apply maj2.
Qed.

Definition FQ_dense (a b : CReal)
  : a < b
    -> { q : Q & a < IQR q < b }.
Proof.
  intros H. destruct (linear_order_T a 0 b). apply H.
  - destruct (FQ_dense_pos (-b) (-a)) as [q maj].
    apply (CReal_plus_lt_compat_l (-a)) in c. rewrite CReal_plus_opp_l in c.
    rewrite CReal_plus_0_r in c. apply c.
    apply (CReal_plus_lt_compat_l (-a)) in H.
    rewrite CReal_plus_opp_l, CReal_plus_comm in H.
    apply (CReal_plus_lt_compat_l (-b)) in H. rewrite <- CReal_plus_assoc in H.
    rewrite CReal_plus_opp_l in H. rewrite CReal_plus_0_l in H.
    rewrite CReal_plus_0_r in H. apply H.
    exists (-q)%Q. split.
    + destruct maj as [_ maj].
      apply (CReal_plus_lt_compat_l (-IQR q)) in maj.
      rewrite CReal_plus_opp_l, <- opp_IQR, CReal_plus_comm in maj.
      apply (CReal_plus_lt_compat_l a) in maj. rewrite <- CReal_plus_assoc in maj.
      rewrite CReal_plus_opp_r, CReal_plus_0_l in maj.
      rewrite CReal_plus_0_r in maj. apply maj.
    + destruct maj as [maj _].
      apply (CReal_plus_lt_compat_l (-IQR q)) in maj.
      rewrite CReal_plus_opp_l, <- opp_IQR, CReal_plus_comm in maj.
      apply (CReal_plus_lt_compat_l b) in maj. rewrite <- CReal_plus_assoc in maj.
      rewrite CReal_plus_opp_r in maj. rewrite CReal_plus_0_l in maj.
      rewrite CReal_plus_0_r in maj. apply maj.
  - apply FQ_dense_pos. apply c. apply H.
Qed.

Definition RQ_limit : forall (x : CReal) (n:nat),
    { q:Q & x < IQR q < x + IQR (1 # Pos.of_nat n) }.
Proof.
  intros x n. apply (FQ_dense x (x + IQR (1 # Pos.of_nat n))).
  rewrite <- (CReal_plus_0_r x). rewrite CReal_plus_assoc.
  apply CReal_plus_lt_compat_l. rewrite CReal_plus_0_l. apply IQR_pos.
  reflexivity.
Qed.

Definition Un_cauchy_Q (xn : nat -> Q) : Set
  := forall n : positive,
    { k : nat | forall p q : nat, le k p -> le k q
                                  -> Qlt (-(1#n)) (xn p - xn q)
                                     /\ Qlt (xn p - xn q) (1#n) }.

Lemma Rdiag_cauchy_sequence : forall (xn : nat -> CReal),
    Un_cauchy_mod xn
    -> Un_cauchy_Q (fun n => let (l,_) := RQ_limit (xn n) n in l).
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
    apply (CRealLt_trans _ (xn p0 - (xn q + IQR (1 # 2 * p)))).
    + unfold CReal_minus. rewrite CReal_opp_plus_distr. unfold CReal_minus.
      rewrite <- CReal_plus_assoc.
      apply (CReal_plus_lt_reg_r (IQR (1 # 2 * p))).
      rewrite CReal_plus_assoc. rewrite CReal_plus_opp_l. rewrite CReal_plus_0_r.
      rewrite <- plus_IQR.
      setoid_replace (- (1 # p) + (1 # 2 * p))%Q with (- (1 # 2 * p))%Q.
      rewrite opp_IQR. exact c.
      rewrite Qplus_comm.
      setoid_replace (1#p)%Q with (2 # 2 *p)%Q. rewrite Qinv_minus_distr.
      reflexivity. reflexivity.
    + rewrite plus_IQR. apply CReal_plus_le_lt_compat.
      apply CRealLt_asym.
      destruct (RQ_limit (xn p0) p0); simpl. apply p1.
      destruct (RQ_limit (xn q) q); unfold proj1_sig.
      rewrite opp_IQR. apply CReal_opp_gt_lt_contravar.
      apply (CRealLt_Le_trans _ (xn q + IQR (1 # Pos.of_nat q))).
      apply p1. apply CReal_plus_le_compat_l. apply IQR_le.
      apply Z2Nat.inj_le. discriminate. discriminate.
      simpl. assert ((Pos.to_nat p~0 <= q)%nat).
      { apply (le_trans _ (Init.Nat.max k (2 * Pos.to_nat p))).
        2: apply H0. replace (p~0)%positive with (2*p)%positive.
        2: reflexivity. rewrite Pos2Nat.inj_mul.
        apply Nat.le_max_r. }
      rewrite Nat2Pos.id. apply H1. intro abs. subst q.
      inversion H1. pose proof (Pos2Nat.is_pos (p~0)).
      rewrite H3 in H2. inversion H2.
  - apply lt_IQR. unfold Qminus.
    apply (CRealLt_trans _ (xn p0 + IQR (1 # 2 * p) - xn q)).
    + rewrite plus_IQR. apply CReal_plus_le_lt_compat.
      apply CRealLt_asym.
      destruct (RQ_limit (xn p0) p0); unfold proj1_sig.
      apply (CRealLt_Le_trans _ (xn p0 + IQR (1 # Pos.of_nat p0))).
      apply p1. apply CReal_plus_le_compat_l. apply IQR_le.
      apply Z2Nat.inj_le. discriminate. discriminate.
      simpl. assert ((Pos.to_nat p~0 <= p0)%nat).
      { apply (le_trans _ (Init.Nat.max k (2 * Pos.to_nat p))).
        2: apply H. replace (p~0)%positive with (2*p)%positive.
        2: reflexivity. rewrite Pos2Nat.inj_mul.
        apply Nat.le_max_r. }
      rewrite Nat2Pos.id. apply H1. intro abs. subst p0.
      inversion H1. pose proof (Pos2Nat.is_pos (p~0)).
      rewrite H3 in H2. inversion H2.
      rewrite opp_IQR. apply CReal_opp_gt_lt_contravar.
      destruct (RQ_limit (xn q) q); simpl. apply p1.
    + unfold CReal_minus. rewrite (CReal_plus_comm (xn p0)).
      rewrite CReal_plus_assoc.
      apply (CReal_plus_lt_reg_l (- IQR (1 # 2 * p))).
      rewrite <- CReal_plus_assoc. rewrite CReal_plus_opp_l. rewrite CReal_plus_0_l.
      rewrite <- opp_IQR. rewrite <- plus_IQR.
      setoid_replace (- (1 # 2 * p) + (1 # p))%Q with (1 # 2 * p)%Q.
      exact c0. rewrite Qplus_comm.
      setoid_replace (1#p)%Q with (2 # 2*p)%Q. rewrite Qinv_minus_distr.
      reflexivity. reflexivity.
Qed.

Lemma doubleLtCovariant : forall a b c d e f : CReal,
    a == b -> c == d -> e == f
    -> (a < c < e)
    -> (b < d < f).
Proof.
  split. rewrite <- H. rewrite <- H0. apply H2.
  rewrite <- H0. rewrite <- H1. apply H2.
Qed.

(* An element of CReal is a Cauchy sequence of rational numbers,
   show that it converges to itself in CReal. *)
Lemma CReal_cv_self : forall (qn : nat -> Q) (x : CReal) (cvmod : positive -> nat),
    QSeqEquiv qn (fun n => proj1_sig x n) cvmod
    -> Un_cv_mod (fun n => IQR (qn n)) x.
Proof.
  intros qn x cvmod H p.
  specialize (H (2*p)%positive). exists (cvmod (2*p)%positive).
  intros p0 H0. unfold absSmall, CReal_minus.
  apply (doubleLtCovariant (-inject_Q (1#p)) _ (inject_Q (qn p0) - x) _ (inject_Q (1#p))).
  rewrite FinjectQ_CReal. reflexivity.
  rewrite FinjectQ_CReal. reflexivity.
  rewrite FinjectQ_CReal. reflexivity.
  apply (CReal_absSmall _ _ (Pos.max (4 * p)%positive (Pos.of_nat (cvmod (2 * p)%positive)))).
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

Lemma Un_cv_extens : forall (xn yn : nat -> CReal) (l : CReal),
    Un_cv_mod xn l
    -> (forall n : nat, xn n == yn n)
    -> Un_cv_mod yn l.
Proof.
  intros. intro p. destruct (H p) as [n cv]. exists n.
  intros. unfold absSmall, CReal_minus.
  split; rewrite <- (H0 i); apply cv; apply H1.
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
    apply (Qplus_lt_r _ _ (qn n -qn k-(1#p))). ring_simplify.
    destruct a. ring_simplify in H2. exact H2.
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
  destruct (R_has_all_rational_limits (fun n => let (l,_) := RQ_limit (xn n) n in l)
                                      (Rdiag_cauchy_sequence xn cau))
    as [l cv].
  exists l. intro p. specialize (cv (2*p)%positive) as [k cv].
  exists (max k (2 * Pos.to_nat p)). intros p0 H. specialize (cv p0).
  destruct cv as [H0 H1]. apply (le_trans _ (max k (2 * Pos.to_nat p))).
  apply Nat.le_max_l. apply H.
  destruct (RQ_limit (xn p0) p0) as [q maj]; unfold proj1_sig in H0,H1.
  split.
  - apply (CRealLt_trans _ (IQR q - IQR (1 # 2 * p) - l)).
    + unfold CReal_minus. rewrite (CReal_plus_comm (IQR q)).
      apply (CReal_plus_lt_reg_l (IQR (1 # 2 * p))).
      ring_simplify. unfold CReal_minus. rewrite <- opp_IQR. rewrite <- plus_IQR.
      setoid_replace ((1 # 2 * p) + - (1 # p))%Q with (-(1#2*p))%Q.
      rewrite opp_IQR. apply H0.
      setoid_replace (1#p)%Q with (2 # 2*p)%Q.
      rewrite Qinv_minus_distr. reflexivity. reflexivity.
    + unfold CReal_minus.
      do 2 rewrite <- (CReal_plus_comm (-l)). apply CReal_plus_lt_compat_l.
      apply (CReal_plus_lt_reg_r (IQR (1 # 2 * p))).
      ring_simplify. rewrite CReal_plus_comm.
      apply (CRealLt_Le_trans _ (xn p0 + IQR (1 # Pos.of_nat p0))).
      apply maj. apply CReal_plus_le_compat_l.
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
  - apply (CRealLt_trans _ (IQR q - l)).
    + unfold CReal_minus. do 2 rewrite <- (CReal_plus_comm (-l)).
      apply CReal_plus_lt_compat_l. apply maj.
    + apply (CRealLt_trans _ (IQR (1 # 2 * p))).
      apply H1. apply IQR_lt.
      rewrite <- Qplus_0_r.
      setoid_replace (1#p)%Q with ((1#2*p)+(1#2*p))%Q.
      apply Qplus_lt_r. reflexivity.
      rewrite Qinv_plus_distr. reflexivity.
Qed.

Definition sig_forall_dec_T : Type
  := forall (P : nat -> Prop), (forall n, {P n} + {~P n})
                   -> {n | ~P n} + {forall n, P n}.

Definition sig_not_dec_T : Type := forall P : Prop, { ~~P } + { ~P }.

Definition is_upper_bound (E:CReal -> Prop) (m:CReal)
  := forall x:CReal, E x -> x <= m.

Definition is_lub (E:CReal -> Prop) (m:CReal) :=
  is_upper_bound E m /\ (forall b:CReal, is_upper_bound E b -> m <= b).

Lemma is_upper_bound_dec :
  forall (E:CReal -> Prop) (x:CReal),
    sig_forall_dec_T
    -> sig_not_dec_T
    -> { is_upper_bound E x } + { ~is_upper_bound E x }.
Proof.
  intros E x lpo sig_not_dec.
  destruct (sig_not_dec (~exists y:CReal, E y /\ CRealLtProp x y)).
  - left. intros y H.
    destruct (CRealLt_lpo_dec x y lpo). 2: exact f.
    exfalso. apply n. intro abs. apply abs.
    exists y. split. exact H. destruct c. exists x0. exact q.
  - right. intro abs. apply n. intros [y [H H0]].
    specialize (abs y H). apply CRealLtEpsilon in H0. contradiction.
Qed.

Lemma is_upper_bound_epsilon :
  forall (E:CReal -> Prop),
    sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x:CReal, is_upper_bound E x)
    -> { n:nat | is_upper_bound E (INR n) }.
Proof.
  intros E lpo sig_not_dec Ebound.
  apply constructive_indefinite_ground_description_nat.
  - intro n. apply is_upper_bound_dec. exact lpo. exact sig_not_dec.
  - destruct Ebound as [x H]. destruct (Rup_nat x). exists x0.
    intros y ey. specialize (H y ey).
    apply CRealLt_asym. apply (CRealLe_Lt_trans _ x); assumption.
Qed.

Lemma is_upper_bound_not_epsilon :
  forall E:CReal -> Prop,
    sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x : CReal, E x)
    -> { m:nat | ~is_upper_bound E (-INR m) }.
Proof.
  intros E lpo sig_not_dec H.
  apply constructive_indefinite_ground_description_nat.
  - intro n. destruct (is_upper_bound_dec E (-INR n) lpo sig_not_dec).
    right. intro abs. contradiction. left. exact n0.
  - destruct H as [x H]. destruct (Rup_nat (-x)) as [n H0].
    exists n. intro abs. specialize (abs x H).
    apply abs. apply (CReal_plus_lt_reg_l (INR n-x)).
    ring_simplify. exact H0.
Qed.

(* Decidable Dedekind cuts are Cauchy reals. *)
Record DedekindDecCut : Type :=
  {
    DDupcut : Q -> Prop;
    DDproper : forall q r : Q, (q == r -> DDupcut q -> DDupcut r)%Q;
    DDlow : Q;
    DDhigh : Q;
    DDdec : forall q:Q, { DDupcut q } + { ~DDupcut q };
    DDinterval : forall q r : Q, Qle q r -> DDupcut q -> DDupcut r;
    DDhighProp : DDupcut DDhigh;
    DDlowProp : ~DDupcut DDlow;
  }.

Lemma DDlow_below_up : forall (upcut : DedekindDecCut) (a b : Q),
    DDupcut upcut a -> ~DDupcut upcut b -> Qlt b a.
Proof.
  intros. destruct (Qlt_le_dec b a). exact q.
  exfalso. apply H0. apply (DDinterval upcut a).
  exact q. exact H.
Qed.

Fixpoint DDcut_limit_fix (upcut : DedekindDecCut) (r : Q) (n : nat) :
  Qlt 0 r
  -> (DDupcut upcut (DDlow upcut + (Z.of_nat n#1) * r))
  -> { q : Q | DDupcut upcut q /\ ~DDupcut upcut (q - r) }.
Proof.
  destruct n.
  - intros. exfalso. simpl in H0.
    apply (DDproper upcut _ (DDlow upcut)) in H0. 2: ring.
    exact (DDlowProp upcut H0).
  - intros. destruct (DDdec upcut (DDlow upcut + (Z.of_nat n # 1) * r)).
    + exact (DDcut_limit_fix upcut r n H d).
    + exists (DDlow upcut + (Z.of_nat (S n) # 1) * r)%Q. split.
      exact H0. intro abs.
      apply (DDproper upcut _ (DDlow upcut + (Z.of_nat n # 1) * r)) in abs.
      contradiction.
      rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite <- Qinv_plus_distr.
      ring.
Qed.

Lemma DDcut_limit : forall (upcut : DedekindDecCut) (r : Q),
  Qlt 0 r
  -> { q : Q | DDupcut upcut q /\ ~DDupcut upcut (q - r) }.
Proof.
  intros.
  destruct (Qarchimedean ((DDhigh upcut - DDlow upcut)/r)) as [n nmaj].
  apply (DDcut_limit_fix upcut r (Pos.to_nat n) H).
  apply (Qmult_lt_r _ _ r) in nmaj. 2: exact H.
  unfold Qdiv in nmaj.
  rewrite <- Qmult_assoc, (Qmult_comm (/r)), Qmult_inv_r, Qmult_1_r in nmaj.
  apply (DDinterval upcut (DDhigh upcut)). 2: exact (DDhighProp upcut).
  apply Qlt_le_weak. apply (Qplus_lt_r _ _ (-DDlow upcut)).
  rewrite Qplus_assoc, <- (Qplus_comm (DDlow upcut)), Qplus_opp_r,
  Qplus_0_l, Qplus_comm.
  rewrite positive_nat_Z. exact nmaj.
  intros abs. rewrite abs in H. exact (Qlt_irrefl 0 H).
Qed.

Lemma glb_dec_Q : forall upcut : DedekindDecCut,
    { x : CReal | forall r:Q, (x < IQR r -> DDupcut upcut r)
                         /\ (IQR r < x -> ~DDupcut upcut r) }.
Proof.
  intros.
  assert (forall a b : Q, Qle a b -> Qle (-b) (-a)).
  { intros. apply (Qplus_le_l _ _ (a+b)). ring_simplify. exact H. }
  assert (QCauchySeq (fun n:nat => proj1_sig (DDcut_limit
                                           upcut (1#Pos.of_nat n) (eq_refl _)))
                     Pos.to_nat).
  { intros p i j pi pj.
    destruct (DDcut_limit upcut (1 # Pos.of_nat i) eq_refl),
    (DDcut_limit upcut (1 # Pos.of_nat j) eq_refl); unfold proj1_sig.
    apply Qabs_case. intros.
    apply (Qplus_lt_l _ _ (x0- (1#p))). ring_simplify.
    setoid_replace (x + -1 * (1 # p))%Q with (x - (1 # p))%Q.
    2: ring. apply (Qle_lt_trans _ (x- (1#Pos.of_nat i))).
    apply Qplus_le_r. apply H.
    apply Z2Nat.inj_le. discriminate. discriminate. simpl.
    rewrite Nat2Pos.id. exact pi. intro abs.
    subst i. inversion pi. pose proof (Pos2Nat.is_pos p).
    rewrite H2 in H1. inversion H1.
    apply (DDlow_below_up upcut). apply a0. apply a.
    intros.
    apply (Qplus_lt_l _ _ (x- (1#p))). ring_simplify.
    setoid_replace (x0 + -1 * (1 # p))%Q with (x0 - (1 # p))%Q.
    2: ring. apply (Qle_lt_trans _ (x0- (1#Pos.of_nat j))).
    apply Qplus_le_r. apply H.
    apply Z2Nat.inj_le. discriminate. discriminate. simpl.
    rewrite Nat2Pos.id. exact pj. intro abs.
    subst j. inversion pj. pose proof (Pos2Nat.is_pos p).
    rewrite H2 in H1. inversion H1.
    apply (DDlow_below_up upcut). apply a. apply a0. }
  pose (exist (fun qn => QSeqEquiv qn qn Pos.to_nat) _ H0) as l.
  exists l. split.
  - intros. (* find an upper point between the limit and r *)
    rewrite FinjectQ_CReal in H1. destruct H1 as [p pmaj].
    unfold l,proj1_sig in pmaj.
    destruct (DDcut_limit upcut (1 # Pos.of_nat (Pos.to_nat p)) eq_refl) as [q qmaj]
    ; simpl in pmaj.
    apply (DDinterval upcut q). 2: apply qmaj.
    apply (Qplus_lt_l _ _ q) in pmaj. ring_simplify in pmaj.
    apply (Qle_trans _ ((2#p) + q)).
    apply (Qplus_le_l _ _ (-q)). ring_simplify. discriminate.
    apply Qlt_le_weak. exact pmaj.
  - intros H1 abs.
    rewrite FinjectQ_CReal in H1. destruct H1 as [p pmaj].
    unfold l,proj1_sig in pmaj.
    destruct (DDcut_limit upcut (1 # Pos.of_nat (Pos.to_nat p)) eq_refl) as [q qmaj]
    ; simpl in pmaj.
    rewrite Pos2Nat.id in qmaj.
    apply (Qplus_lt_r _ _ (r - (2#p))) in pmaj. ring_simplify in pmaj.
    destruct qmaj. apply H2.
    apply (DDinterval upcut r). 2: exact abs.
    apply Qlt_le_weak, (Qlt_trans _ (-1*(2#p) + q) _ pmaj).
    apply (Qplus_lt_l _ _ ((2#p) -q)). ring_simplify.
    setoid_replace (-1 * (1 # p))%Q with (-(1#p))%Q.
    2: ring. rewrite Qinv_minus_distr. reflexivity.
Qed.

Lemma is_upper_bound_glb :
  forall (E:CReal -> Prop),
    sig_not_dec_T
    -> sig_forall_dec_T
    -> (exists x : CReal, E x)
    -> (exists x : CReal, is_upper_bound E x)
    -> { x : CReal | forall r:Q, (x < IQR r -> is_upper_bound E (IQR r))
                           /\ (IQR r < x -> ~is_upper_bound E (IQR r)) }.
Proof.
  intros E sig_not_dec lpo Einhab Ebound.
  destruct (is_upper_bound_epsilon E lpo sig_not_dec Ebound) as [a luba].
  destruct (is_upper_bound_not_epsilon E lpo sig_not_dec Einhab) as [b glbb].
  pose (fun q => is_upper_bound E (IQR q)) as upcut.
  assert (forall q:Q, { upcut q } + { ~upcut q } ).
  { intro q. apply is_upper_bound_dec. exact lpo. exact sig_not_dec. }
  assert (forall q r : Q, (q <= r)%Q -> upcut q -> upcut r).
  { intros. intros x Ex. specialize (H1 x Ex). intro abs.
    apply H1. apply (CRealLe_Lt_trans _ (IQR r)). 2: exact abs.
    apply IQR_le. exact H0. }
  assert (upcut (Z.of_nat a # 1)%Q).
  { intros x Ex. unfold IQR. rewrite CReal_inv_1, CReal_mult_1_r.
    specialize (luba x Ex). rewrite <- INR_IZR_INZ. exact luba. }
  assert (~upcut (- Z.of_nat b # 1)%Q).
  { intros abs. apply glbb. intros x Ex.
    specialize (abs x Ex). unfold IQR in abs.
    rewrite CReal_inv_1, CReal_mult_1_r, opp_IZR, <- INR_IZR_INZ in abs.
    exact abs. }
  assert (forall q r : Q, (q == r)%Q -> upcut q -> upcut r).
  { intros. intros x Ex. specialize (H4 x Ex). rewrite <- H3. exact H4. }
  destruct (glb_dec_Q (Build_DedekindDecCut
                         upcut H3 (-Z.of_nat b # 1)%Q (Z.of_nat a # 1)
                         H H0 H1 H2)).
  simpl in a0. exists x. intro r. split.
  - intros. apply a0. exact H4.
  - intros H6 abs. specialize (a0 r) as [_ a0]. apply a0.
    exact H6. exact abs.
Qed.

Lemma is_upper_bound_closed :
  forall (E:CReal -> Prop) (sig_forall_dec : sig_forall_dec_T)
    (sig_not_dec : sig_not_dec_T)
    (Einhab : exists x : CReal, E x)
    (Ebound : exists x : CReal, is_upper_bound E x),
    is_lub
      E (proj1_sig (is_upper_bound_glb
                      E sig_not_dec sig_forall_dec Einhab Ebound)).
Proof.
  intros. split.
  - intros x Ex.
    destruct (is_upper_bound_glb E sig_not_dec sig_forall_dec Einhab Ebound); simpl.
    intro abs. destruct (FQ_dense x0 x abs) as [q [qmaj H]].
    specialize (a q) as [a _]. specialize (a qmaj x Ex).
    contradiction.
  - intros.
    destruct (is_upper_bound_glb E sig_not_dec sig_forall_dec Einhab Ebound); simpl.
    intro abs. destruct (FQ_dense b x abs) as [q [qmaj H0]].
    specialize (a q) as [_ a]. apply a. exact H0.
    intros y Ey. specialize (H y Ey). intro abs2.
    apply H. exact (CRealLt_trans _ (IQR q) _ qmaj abs2).
Qed.

Lemma sig_lub :
  forall (E:CReal -> Prop),
    sig_forall_dec_T
    -> sig_not_dec_T
    -> (exists x : CReal, E x)
    -> (exists x : CReal, is_upper_bound E x)
    -> { u : CReal | is_lub E u }.
Proof.
  intros E sig_forall_dec sig_not_dec Einhab Ebound.
  pose proof (is_upper_bound_closed E sig_forall_dec sig_not_dec Einhab Ebound).
  destruct (is_upper_bound_glb
              E sig_not_dec sig_forall_dec Einhab Ebound); simpl in H.
  exists x. exact H.
Qed.

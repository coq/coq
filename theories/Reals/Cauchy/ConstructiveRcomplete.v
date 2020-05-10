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

Instance seq_cv_morph
  : forall (un : nat -> CReal), CMorphisms.Proper
      (CMorphisms.respectful CRealEq CRelationClasses.iffT) (seq_cv un).
Proof.
  split. intros. apply (seq_cv_proper un x). exact H0. exact H.
  intros. apply (seq_cv_proper un y). exact H0. symmetry. exact H.
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

Lemma Qabs_Rabs : forall q : Q,
    inject_Q (Qabs q) == CReal_abs (inject_Q q).
Proof.
  intro q. apply Qabs_case.
  - intros. rewrite CReal_abs_right. reflexivity.
    apply inject_Q_le, H.
  - intros. rewrite CReal_abs_left, opp_inject_Q. reflexivity.
    apply inject_Q_le, H.
Qed.


(* For instance the rational sequence 1/n converges to 0. *)
Lemma CReal_cv_self : forall (x : CReal) (n : positive),
    CReal_abs (x - inject_Q (proj1_sig x n)) <= inject_Q (1#n).
Proof.
  intros x n [k kmaj].
  destruct x as [xn cau].
  unfold CReal_abs, CReal_minus, CReal_plus, CReal_opp, inject_Q, proj1_sig in kmaj.
  apply (Qlt_not_le _ _ kmaj). clear kmaj.
  unfold QCauchySeq in cau.
  rewrite <- (Qplus_le_l _ _ (1#n)). ring_simplify. unfold id in cau.
  destruct (Pos.lt_total (2*k) n). 2: destruct H.
  - specialize (cau k (2*k)%positive n).
    assert (k <= 2 * k)%positive.
    { apply (Pos.le_trans _ (1*k)). apply Pos.le_refl.
      apply Pos.mul_le_mono_r. discriminate. }
    apply (Qle_trans _ (1#k)). rewrite Qred_correct. apply Qlt_le_weak, cau.
    exact H0. apply (Pos.le_trans _ _ _ H0). apply Pos.lt_le_incl, H.
    rewrite <- (Qinv_plus_distr 1 1).
    apply (Qplus_le_l _ _ (-(1#k))). ring_simplify. discriminate.
  - subst n. rewrite Qplus_opp_r. discriminate.
  - specialize (cau n (2*k)%positive n).
    apply (Qle_trans _ (1#n)). rewrite Qred_correct. apply Qlt_le_weak, cau.
    apply Pos.lt_le_incl, H. apply Pos.le_refl.
    apply (Qplus_le_l _ _ (-(1#n))). ring_simplify. discriminate.
Qed.

(* We can probably reduce the factor 4. *)
Lemma Rcauchy_limit : forall (xn : nat -> CReal) (xcau : Un_cauchy_mod xn),
    QCauchySeq
      (fun n : positive =>
         let (p, _) := xcau (4 * n)%positive in proj1_sig (xn p) (4 * n)%positive).
Proof.
  intros xn xcau n p q H0 H1.
  destruct (xcau (4 * p)%positive) as [i imaj],
  (xcau (4 * q)%positive) as [j jmaj].
  assert (CReal_abs (xn i - xn j) <= inject_Q (1 # 4 * n)).
  { destruct (le_lt_dec i j).
    apply (CReal_le_trans _ _ _ (imaj i j (le_refl _) l)).
    apply inject_Q_le. unfold Qle, Qnum, Qden.
    rewrite Z.mul_1_l, Z.mul_1_l. apply Pos2Z.pos_le_pos.
    apply Pos.mul_le_mono_l, H0. apply le_S, le_S_n in l.
    apply (CReal_le_trans _ _ _ (jmaj i j l (le_refl _))).
    apply inject_Q_le. unfold Qle, Qnum, Qden.
    rewrite Z.mul_1_l, Z.mul_1_l. apply Pos2Z.pos_le_pos.
    apply Pos.mul_le_mono_l, H1. }
  clear jmaj imaj.
  setoid_replace (1#n)%Q with ((1#(3*n)) + ((1#(3*n)) + (1#(3*n))))%Q.
  2: rewrite Qinv_plus_distr, Qinv_plus_distr; reflexivity.
  apply lt_inject_Q. rewrite inject_Q_plus.
  rewrite Qabs_Rabs.
  apply (CReal_le_lt_trans _ (CReal_abs (inject_Q (proj1_sig (xn i) (4 * p)%positive) - xn i) + CReal_abs (xn i - inject_Q(proj1_sig (xn j) (4 * q)%positive)))).
  unfold Qminus.
  rewrite inject_Q_plus, opp_inject_Q.
  setoid_replace (inject_Q (proj1_sig (xn i) (4 * p)%positive) +
                  - inject_Q (proj1_sig (xn j) (4 * q)%positive))
    with (inject_Q (proj1_sig (xn i) (4 * p)%positive) - xn i
          + (xn i - inject_Q (proj1_sig (xn j) (4 * q)%positive))).
  2: ring.
  apply CReal_abs_triang. apply CReal_plus_le_lt_compat.
  rewrite CReal_abs_minus_sym. apply (CReal_le_trans _ (inject_Q (1# 4*p))).
  apply CReal_cv_self. apply inject_Q_le. unfold Qle, Qnum, Qden.
  rewrite Z.mul_1_l, Z.mul_1_l.
  apply Pos2Z.pos_le_pos. apply (Pos.le_trans _ (4*n)).
  apply Pos.mul_le_mono_r. discriminate.
  apply Pos.mul_le_mono_l. exact H0.
  apply (CReal_le_lt_trans
           _ (CReal_abs (xn i - xn j + (xn j - inject_Q (proj1_sig (xn j) (4 * q)%positive))))).
  apply CReal_abs_morph. ring.
  apply (CReal_le_lt_trans _ _ _ (CReal_abs_triang _ _)).
  rewrite inject_Q_plus. apply CReal_plus_le_lt_compat.
  apply (CReal_le_trans _ _ _ H). apply inject_Q_le.
  unfold Qle, Qnum, Qden. rewrite Z.mul_1_l, Z.mul_1_l.
  apply Pos2Z.pos_le_pos. apply Pos.mul_le_mono_r. discriminate.
  apply (CReal_le_lt_trans _ (inject_Q (1#4*q))).
  apply CReal_cv_self. apply inject_Q_lt. unfold Qlt, Qnum, Qden.
  rewrite Z.mul_1_l, Z.mul_1_l.
  apply Pos2Z.pos_lt_pos. apply (Pos.lt_le_trans _ (4*n)).
  apply Pos.mul_lt_mono_r. reflexivity.
  apply Pos.mul_le_mono_l. exact H1.
Qed.

Lemma Rcauchy_complete : forall (xn : nat -> CReal),
    Un_cauchy_mod xn
    -> { l : CReal  &  seq_cv xn l }.
Proof.
  intros xn cau.
  exists (exist _ (fun n : positive =>
                let (p, _) := cau (4 * n)%positive in
                proj1_sig (xn p) (4 * n)%positive)
           (Rcauchy_limit xn cau)).
  intro p.
  pose proof (CReal_cv_self (exist _ (fun n : positive =>
                let (p, _) := cau (4 * n)%positive in
                proj1_sig (xn p) (4 * n)%positive)
           (Rcauchy_limit xn cau)) (2*p)) as H.
  unfold proj1_sig in H.
  pose proof (cau (2*p)%positive) as [k cv].
  destruct (cau (4 * (2 * p))%positive) as [i imaj].
  (* The convergence modulus does not matter here, because a converging Cauchy
     sequence always converges to its limit with twice the Cauchy modulus. *)
  exists (max k i).
  intros j H0.
  setoid_replace (xn j -
     exist (fun x : positive -> Q => QCauchySeq x)
       (fun n : positive =>
        let (p0, _) := cau (4 * n)%positive in proj1_sig (xn p0) (4 * n)%positive)
       (Rcauchy_limit xn cau))
    with (xn j - inject_Q (proj1_sig (xn i) (p~0~0~0)%positive)
          + (inject_Q (proj1_sig (xn i) (p~0~0~0)%positive) -
     exist (fun x : positive -> Q => QCauchySeq x)
       (fun n : positive =>
        let (p0, _) := cau (4 * n)%positive in proj1_sig (xn p0) (4 * n)%positive)
       (Rcauchy_limit xn cau))).
  2: ring. apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
  apply (CReal_le_trans _ (inject_Q (1#2*p) + inject_Q (1#2*p))).
  apply CReal_plus_le_compat. unfold proj1_sig in H.
  2: rewrite CReal_abs_minus_sym; exact H.
  specialize (imaj j i (le_trans _ _ _ (Nat.le_max_r _ _) H0) (le_refl _)).
  apply (CReal_le_trans _ (inject_Q (1 # 4 * p) + inject_Q (1 # 4 * p))).
  setoid_replace (xn j - inject_Q (proj1_sig (xn i) (p~0~0~0)%positive))
    with (xn j - xn i
          + (xn i - inject_Q (proj1_sig (xn i) (p~0~0~0)%positive))).
  2: ring. apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
  apply CReal_plus_le_compat. apply (CReal_le_trans _ _ _ imaj).
  apply inject_Q_le. unfold Qle, Qnum, Qden.
  rewrite Z.mul_1_l, Z.mul_1_l.
  apply Pos2Z.pos_le_pos.
  apply (Pos.mul_le_mono_r p 4 8). discriminate.
  apply (CReal_le_trans _ _ _ (CReal_cv_self (xn i) (8*p))).
  apply inject_Q_le. unfold Qle, Qnum, Qden.
  rewrite Z.mul_1_l, Z.mul_1_l.
  apply Pos2Z.pos_le_pos.
  apply (Pos.mul_le_mono_r p 4 8). discriminate.
  rewrite <- inject_Q_plus. rewrite (inject_Q_morph _ (1#2*p)).
  apply CRealLe_refl. rewrite Qinv_plus_distr; reflexivity.
  rewrite <- inject_Q_plus. rewrite (inject_Q_morph _ (1#p)).
  apply CRealLe_refl. rewrite Qinv_plus_distr; reflexivity.
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
       inject_Q inject_Q_lt lt_inject_Q
       CReal_plus CReal_opp CReal_mult
       inject_Q_plus inject_Q_mult
       CReal_isRing CReal_isRingExt CRealLt_0_1
       CReal_plus_lt_compat_l CReal_plus_lt_reg_l
       CReal_mult_lt_0_compat
       CReal_inv CReal_inv_l CReal_inv_0_lt_compat
       CRealQ_dense Rup_pos CReal_abs CRealAbsLUB CRealComplete.

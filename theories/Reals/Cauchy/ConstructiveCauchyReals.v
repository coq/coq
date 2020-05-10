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

Require Import QArith.
Require Import Qabs.
Require Import Qround.
Require Import Logic.ConstructiveEpsilon.
Require CMorphisms.

(** The constructive Cauchy real numbers, ie the Cauchy sequences
    of rational numbers.

    Cauchy reals are Cauchy sequences of rational numbers,
    equipped with explicit moduli of convergence and
    an equivalence relation (the difference converges to zero).

    Without convergence moduli, we would fail to prove that a Cauchy
    sequence of constructive reals converges.

    Because of the Specker sequences (increasing, computable
    and bounded sequences of rationals that do not converge
    to a computable real number), constructive reals do not
    follow the least upper bound principle.

    The double quantification on p q is needed to avoid
    forall un, QSeqEquiv un (fun _ => un O) (fun q => O)
    which says nothing about the limit of un.

    We define sequences as positive -> Q instead of nat -> Q,
    so that we can compute arguments like 2^n fast.

    WARNING: this module is not meant to be imported directly,
    please import `Reals.Abstract.ConstructiveReals` instead.

    WARNING: this file is experimental and likely to change in future releases.
 *)
Definition QCauchySeq (un : positive -> Q)
  : Prop
  := forall (k : positive) (p q : positive),
      Pos.le k p
      -> Pos.le k q
      -> Qlt (Qabs (un p - un q)) (1 # k).

(* A Cauchy real is a Cauchy sequence with the standard modulus *)
Definition CReal : Set
  := { x : (positive -> Q) | QCauchySeq x }.

Declare Scope CReal_scope.

(* Declare Scope R_scope with Key R *)
Delimit Scope CReal_scope with CReal.

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope CReal_scope with CReal.

Local Open Scope CReal_scope.


(* So QSeqEquiv is the equivalence relation of this constructive pre-order *)
Definition CRealLt (x y : CReal) : Set
  := { n : positive |  Qlt (2 # n) (proj1_sig y n - proj1_sig x n) }.

Definition CRealLtProp (x y : CReal) : Prop
  := exists n : positive, Qlt (2 # n) (proj1_sig y n - proj1_sig x n).

Definition CRealGt (x y : CReal) := CRealLt y x.
Definition CReal_appart (x y : CReal) := sum (CRealLt x y) (CRealLt y x).

Infix "<" := CRealLt : CReal_scope.
Infix ">" := CRealGt : CReal_scope.
Infix "#" := CReal_appart : CReal_scope.

(* This Prop can be extracted as a sigma type *)
Lemma CRealLtEpsilon : forall x y : CReal,
    CRealLtProp x y -> x < y.
Proof.
  intros. unfold CRealLtProp in H.
  (* Convert to nat to use indefinite description. *)
  assert (exists n : nat, lt O n /\ Qlt (2 # Pos.of_nat n)
                                (proj1_sig y (Pos.of_nat n) - proj1_sig x (Pos.of_nat n))).
  { destruct H as [n maj]. exists (Pos.to_nat n). split. apply Pos2Nat.is_pos.
    rewrite Pos2Nat.id. exact maj. }
  clear H.
  apply constructive_indefinite_ground_description_nat in H0.
  destruct H0 as [n maj]. exists (Pos.of_nat n). exact (proj2 maj).
  intro n. destruct n. right.
  intros [abs _]. inversion abs.
  destruct (Qlt_le_dec (2 # Pos.of_nat (S n))
                       (proj1_sig y (Pos.of_nat (S n)) - proj1_sig x (Pos.of_nat (S n)))).
  left. split. apply le_n_S, le_0_n. apply q.
  right. intros [_ abs].
  apply (Qlt_not_le (2 # Pos.of_nat (S n))
                    (proj1_sig y (Pos.of_nat (S n)) - proj1_sig x (Pos.of_nat (S n)))); assumption.
Qed.

Lemma CRealLtForget : forall x y : CReal,
    x < y -> CRealLtProp x y.
Proof.
  intros. destruct H. exists x0. exact q.
Qed.

(* CRealLt is decided by the LPO in Type,
   which is a non-constructive oracle. *)
Lemma CRealLt_lpo_dec : forall x y : CReal,
    (forall (P : nat -> Prop), (forall n:nat, {P n} + {~P n})
                    -> {n | ~P n} + {forall n, P n})
    -> CRealLt x y + (CRealLt x y -> False).
Proof.
  intros x y lpo.
  destruct (lpo (fun n:nat => Qle (proj1_sig y (Pos.of_nat (S n)) - proj1_sig x (Pos.of_nat (S n)))
                             (2 # Pos.of_nat (S n)))).
  - intro n. destruct (Qlt_le_dec (2 # Pos.of_nat (S n))
                                  (proj1_sig y (Pos.of_nat (S n)) - proj1_sig x (Pos.of_nat (S n)))).
    right. apply Qlt_not_le. exact q. left. exact q.
  - left. destruct s as [n nmaj]. exists (Pos.of_nat (S n)).
    apply Qnot_le_lt. exact nmaj.
  - right. intro abs. destruct abs as [n majn].
    specialize (q (pred (Pos.to_nat n))).
    replace (S (pred (Pos.to_nat n))) with (Pos.to_nat n) in q.
    rewrite Pos2Nat.id in q.
    pose proof (Qle_not_lt _ _ q). contradiction.
    symmetry. apply Nat.succ_pred. intro abs.
    pose proof (Pos2Nat.is_pos n). rewrite abs in H. inversion H.
Qed.

(* Alias the large order *)
Definition CRealLe (x y : CReal) : Prop
  := CRealLt y x -> False.

Definition CRealGe (x y : CReal) := CRealLe y x.

Infix "<=" := CRealLe : CReal_scope.
Infix ">=" := CRealGe : CReal_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : CReal_scope.
Notation "x <= y < z"  := (prod (x <= y) (y < z)) : CReal_scope.
Notation "x < y < z"   := (prod (x < y) (y < z)) : CReal_scope.
Notation "x < y <= z"  := (prod (x < y) (y <= z)) : CReal_scope.

(* Alias the quotient order equality *)
Definition CRealEq (x y : CReal) : Prop
  := (CRealLe y x) /\ (CRealLe x y).

Infix "==" := CRealEq : CReal_scope.

Lemma CRealLe_not_lt : forall x y : CReal,
    (forall n:positive, Qle (proj1_sig x n - proj1_sig y n) (2 # n))
    <-> x <= y.
Proof.
  intros. split.
  - intros. intro H0. destruct H0 as [n H0]. specialize (H n).
    apply (Qle_not_lt (2 # n) (2 # n)). apply Qle_refl.
    apply (Qlt_le_trans _ (proj1_sig x n - proj1_sig y n)).
    assumption. assumption.
  - intros.
    destruct (Qlt_le_dec (2 # n) (proj1_sig x n - proj1_sig y n)).
    exfalso. apply H. exists n. assumption. assumption.
Qed.

Lemma CRealEq_diff : forall (x y : CReal),
    CRealEq x y
    <-> forall n:positive, Qle (Qabs (proj1_sig x n - proj1_sig y n)) (2 # n).
Proof.
  intros. split.
  - intros. destruct H. apply Qabs_case. intro.
    pose proof (CRealLe_not_lt x y) as [_ H2]. apply H2. assumption.
    intro. pose proof (CRealLe_not_lt y x) as [_ H2].
    setoid_replace (- (proj1_sig x n - proj1_sig y n))
      with (proj1_sig y n - proj1_sig x n).
    apply H2. assumption. ring.
  - intros. split.
    + apply CRealLe_not_lt. intro n. specialize (H n).
      rewrite Qabs_Qminus in H.
      apply (Qle_trans _ (Qabs (proj1_sig y n - proj1_sig x n))).
      apply Qle_Qabs. apply H.
    + apply CRealLe_not_lt. intro n. specialize (H n).
      apply (Qle_trans _ (Qabs (proj1_sig x n - proj1_sig y n))).
      apply Qle_Qabs. apply H.
Qed.

(* Extend separation to all indices above *)
Lemma CRealLt_aboveSig : forall (x y : CReal) (n : positive),
    (Qlt (2 # n)
         (proj1_sig y n - proj1_sig x n))
    -> let (k, _) := Qarchimedean (/(proj1_sig y n - proj1_sig x n - (2#n)))
      in forall p:positive,
          Pos.le (Pos.max n (2*k)) p
          -> Qlt (2 # (Pos.max n (2*k)))
                (proj1_sig y p - proj1_sig x p).
Proof.
  intros [xn limx] [yn limy] n maj.
  unfold proj1_sig; unfold proj1_sig in maj.
  pose (yn n - xn n) as dn.
  destruct (Qarchimedean (/(yn n - xn n - (2#n)))) as [k kmaj].
  assert (0 < yn n - xn n - (2 # n))%Q as H0.
  { rewrite <- (Qplus_opp_r (2#n)). apply Qplus_lt_l. assumption. }
  intros. remember (yn p - xn p) as dp.
  rewrite <- (Qplus_0_r dp). rewrite <- (Qplus_opp_r dn).
  rewrite (Qplus_comm dn). rewrite Qplus_assoc.
  assert (Qlt (Qabs (dp - dn)) (2#n)).
  { rewrite Heqdp. unfold dn.
    setoid_replace (yn p - xn p - (yn n - xn n))
      with (yn p - yn n + (xn n - xn p)).
    apply (Qle_lt_trans _ (Qabs (yn p - yn n) + Qabs (xn n - xn p))).
    apply Qabs_triangle.
    setoid_replace (2#n)%Q with ((1#n) + (1#n))%Q.
    apply Qplus_lt_le_compat. apply limy.
    apply (Pos.le_trans _ (Pos.max n (2 * k))).
    apply Pos.le_max_l. assumption.
    apply Pos.le_refl. apply Qlt_le_weak. apply limx. apply Pos.le_refl.
    apply (Pos.le_trans _ (Pos.max n (2 * k))).
    apply Pos.le_max_l. assumption.
    rewrite Qinv_plus_distr. reflexivity. ring. }
  apply (Qle_lt_trans _ (-(2#n) + dn)).
  rewrite Qplus_comm. unfold dn. apply Qlt_le_weak.
  apply (Qle_lt_trans _ (2 # (2 * k))). apply Pos.le_max_r.
  setoid_replace (2 # 2 * k)%Q with (1 # k)%Q. 2: reflexivity.
  setoid_replace (Z.pos k # 1)%Q with (/(1#k))%Q in kmaj. 2: reflexivity.
  apply Qinv_lt_contravar. reflexivity. apply H0. apply kmaj.
  apply Qplus_lt_l. rewrite <- Qplus_0_r. rewrite <- (Qplus_opp_r dn).
  rewrite Qplus_assoc. apply Qplus_lt_l. rewrite Qplus_comm.
  rewrite <- (Qplus_0_r dp). rewrite <- (Qplus_opp_r (2#n)).
  rewrite Qplus_assoc. apply Qplus_lt_l.
  rewrite <- (Qplus_0_l dn). rewrite <- (Qplus_opp_r dp).
  rewrite <- Qplus_assoc. apply Qplus_lt_r. rewrite Qplus_comm.
  apply (Qle_lt_trans _ (Qabs (dp - dn))). rewrite Qabs_Qminus.
  unfold Qminus. apply Qle_Qabs. assumption.
Qed.

Lemma CRealLt_above : forall (x y : CReal),
    CRealLt x y
    -> { k : positive | forall p:positive,
          Pos.le k p -> Qlt (2 # k) (proj1_sig y p - proj1_sig x p) }.
Proof.
  intros x y [n maj].
  pose proof (CRealLt_aboveSig x y n maj).
  destruct (Qarchimedean (/ (proj1_sig y n - proj1_sig x n - (2 # n))))
    as [k kmaj].
  exists (Pos.max n (2*k)). apply H.
Qed.

(* The CRealLt index separates the Cauchy sequences *)
Lemma CRealLt_above_same : forall (x y : CReal) (n : positive),
    Qlt (2 # n)
        (proj1_sig y n - proj1_sig x n)
    -> forall p:positive, Pos.le n p -> Qlt (proj1_sig x p) (proj1_sig y p).
Proof.
  intros [xn limx] [yn limy] n inf p H.
  simpl. simpl in inf.
  apply (Qplus_lt_l _ _ (- xn n)).
  apply (Qle_lt_trans _ (Qabs (xn p + - xn n))).
  apply Qle_Qabs. apply (Qlt_trans _ (1#n)).
  apply limx. exact H. apply Pos.le_refl.
  rewrite <- (Qplus_0_r (yn p)).
  rewrite <- (Qplus_opp_r (yn n)).
  rewrite (Qplus_comm (yn n)). rewrite Qplus_assoc.
  rewrite <- Qplus_assoc.
  setoid_replace (1#n)%Q with (-(1#n) + (2#n))%Q. apply Qplus_lt_le_compat.
  apply (Qplus_lt_l _ _ (1#n)). rewrite Qplus_opp_r.
  apply (Qplus_lt_r _ _ (yn n + - yn p)).
  ring_simplify.
  setoid_replace (yn n + (-1 # 1) * yn p) with (yn n - yn p).
  apply (Qle_lt_trans _ (Qabs (yn n - yn p))).
  apply Qle_Qabs. apply limy. apply Pos.le_refl. assumption.
  field. apply Qle_lteq. left. assumption.
  rewrite Qplus_comm. rewrite Qinv_minus_distr.
  reflexivity.
Qed.

Lemma CRealLt_asym : forall x y : CReal, x < y -> x <= y.
Proof.
  intros x y H [n q].
  apply CRealLt_above in H. destruct H as [p H].
  pose proof (CRealLt_above_same y x n q).
  apply (Qlt_not_le (proj1_sig y (Pos.max n p))
                    (proj1_sig x (Pos.max n p))).
  apply H0. apply Pos.le_max_l.
  apply Qlt_le_weak. apply (Qplus_lt_l _ _ (-proj1_sig x (Pos.max n p))).
  rewrite Qplus_opp_r. apply (Qlt_trans _ (2#p)).
  unfold Qlt. simpl. unfold Z.lt. auto. apply H. apply Pos.le_max_r.
Qed.

Lemma CRealLt_irrefl : forall x:CReal, x < x -> False.
Proof.
  intros x abs. exact (CRealLt_asym x x abs abs).
Qed.

Lemma CRealLe_refl : forall x : CReal, x <= x.
Proof.
  intros. intro abs.
  pose proof (CRealLt_asym x x abs). contradiction.
Qed.

Lemma CRealEq_refl : forall x : CReal, x == x.
Proof.
  intros. split; apply CRealLe_refl.
Qed.

Lemma CRealEq_sym : forall x y : CReal, CRealEq x y -> CRealEq y x.
Proof.
  intros. destruct H. split; intro abs; contradiction.
Qed.

Lemma CRealLt_dec : forall x y z : CReal,
    x < y -> sum (x < z) (z < y).
Proof.
  intros [xn limx] [yn limy] [zn limz] [n inf].
  unfold proj1_sig in inf.
  remember (yn n - xn n - (2 # n)) as eps.
  assert (Qlt 0 eps) as epsPos.
  { subst eps. unfold Qminus. apply (Qlt_minus_iff (2#n)). assumption. }
  destruct (Qarchimedean (/eps)) as [k kmaj].
  destruct (Qlt_le_dec ((yn n + xn n) / (2#1))
                       (zn (Pos.max n (4 * k))))
    as [decMiddle|decMiddle].
  - left. exists (Pos.max n (4 * k)). unfold proj1_sig. unfold Qminus.
    rewrite <- (Qplus_0_r (zn (Pos.max n (4 * k)))).
    rewrite <- (Qplus_opp_r (xn n)).
    rewrite (Qplus_comm (xn n)). rewrite Qplus_assoc.
    rewrite <- Qplus_assoc. rewrite <- Qplus_0_r.
    rewrite <- (Qplus_opp_r (1#n)). rewrite Qplus_assoc.
    apply Qplus_lt_le_compat.
    + apply (Qplus_lt_l _ _ (- xn n)) in decMiddle.
      apply (Qlt_trans _ ((yn n + xn n) / (2 # 1) + - xn n)).
      setoid_replace ((yn n + xn n) / (2 # 1) - xn n)
        with ((yn n - xn n) / (2 # 1)).
      apply Qlt_shift_div_l. unfold Qlt. simpl. unfold Z.lt. auto.
      rewrite Qmult_plus_distr_l.
      setoid_replace ((1 # n) * (2 # 1))%Q with (2#n)%Q.
      apply (Qplus_lt_l _ _ (-(2#n))). rewrite <- Qplus_assoc.
      rewrite Qplus_opp_r. unfold Qminus. unfold Qminus in Heqeps.
      rewrite <- Heqeps. rewrite Qplus_0_r.
      apply (Qle_lt_trans _ (1 # k)). unfold Qle.
      simpl. rewrite Pos.mul_1_r. rewrite Pos2Z.inj_max.
      apply Z.le_max_r.
      setoid_replace (Z.pos k # 1)%Q with (/(1#k))%Q in kmaj. 2: reflexivity.
      apply Qinv_lt_contravar. reflexivity. apply epsPos. apply kmaj.
      unfold Qeq. simpl. rewrite Pos.mul_1_r. reflexivity.
      field. assumption.
    + setoid_replace (xn n + - xn (Pos.max n (4 * k)))
        with (-(xn (Pos.max n (4 * k)) - xn n)).
      apply Qopp_le_compat.
      apply (Qle_trans _ (Qabs (xn (Pos.max n (4 * k)) - xn n))).
      apply Qle_Qabs. apply Qle_lteq. left. apply limx. apply Pos.le_max_l.
      apply Pos.le_refl. ring.
  - right. exists (Pos.max n (4 * k)). unfold proj1_sig. unfold Qminus.
    rewrite <- (Qplus_0_r (yn (Pos.max n (4 * k)))).
    rewrite <- (Qplus_opp_r (yn n)).
    rewrite (Qplus_comm (yn n)). rewrite Qplus_assoc.
    rewrite <- Qplus_assoc. rewrite <- Qplus_0_l.
    rewrite <- (Qplus_opp_r (1#n)). rewrite (Qplus_comm (1#n)).
    rewrite <- Qplus_assoc. apply Qplus_lt_le_compat.
    + apply (Qplus_lt_r _ _ (yn n - yn (Pos.max n (4 * k)) + (1#n)))
      ; ring_simplify.
      setoid_replace (-1 * yn (Pos.max n (4 * k)))
        with (- yn (Pos.max n (4 * k))). 2: ring.
      apply (Qle_lt_trans _ (Qabs (yn n - yn (Pos.max n (4 * k))))).
      apply Qle_Qabs. apply limy. apply Pos.le_refl. apply Pos.le_max_l.
    + apply Qopp_le_compat in decMiddle.
      apply (Qplus_le_r _ _ (yn n)) in decMiddle.
      apply (Qle_trans _ (yn n + - ((yn n + xn n) / (2 # 1)))).
      setoid_replace (yn n + - ((yn n + xn n) / (2 # 1)))
        with ((yn n - xn n) / (2 # 1)).
      apply Qle_shift_div_l. unfold Qlt. simpl. unfold Z.lt. auto.
      rewrite Qmult_plus_distr_l.
      setoid_replace ((1 # n) * (2 # 1))%Q with (2#n)%Q.
      apply (Qplus_le_r _ _ (-(2#n))). rewrite Qplus_assoc.
      rewrite Qplus_opp_r. rewrite Qplus_0_l. rewrite (Qplus_comm (-(2#n))).
      unfold Qminus in Heqeps. unfold Qminus. rewrite <- Heqeps.
      apply (Qle_trans _ (1 # k)). unfold Qle.
      simpl. rewrite Pos.mul_1_r. rewrite Pos2Z.inj_max.
      apply Z.le_max_r. apply Qle_lteq. left.
      setoid_replace (Z.pos k # 1)%Q with (/(1#k))%Q in kmaj. 2: reflexivity.
      apply Qinv_lt_contravar. reflexivity. apply epsPos. apply kmaj.
      unfold Qeq. simpl. rewrite Pos.mul_1_r. reflexivity.
      field. assumption.
Defined.

Definition linear_order_T x y z := CRealLt_dec x z y.

Lemma CReal_le_lt_trans : forall x y z : CReal,
    x <= y -> y < z -> x < z.
Proof.
  intros.
  destruct (linear_order_T y x z H0). contradiction. apply c.
Defined.

Lemma CReal_lt_le_trans : forall x y z : CReal,
    x < y -> y <= z -> x < z.
Proof.
  intros.
  destruct (linear_order_T x z y H). apply c. contradiction.
Defined.

Lemma CReal_le_trans : forall x y z : CReal,
    x <= y -> y <= z -> x <= z.
Proof.
  intros. intro abs. apply H0.
  apply (CReal_lt_le_trans _ x); assumption.
Qed.

Lemma CReal_lt_trans : forall x y z : CReal,
    x < y -> y < z -> x < z.
Proof.
  intros. apply (CReal_lt_le_trans _ y _ H).
  apply CRealLt_asym. exact H0.
Defined.

Lemma CRealEq_trans : forall x y z : CReal,
    CRealEq x y -> CRealEq y z -> CRealEq x z.
Proof.
  intros. destruct H,H0. split.
  - intro abs. destruct (CRealLt_dec _ _ y abs); contradiction.
  - intro abs. destruct (CRealLt_dec _ _ y abs); contradiction.
Qed.

Add Parametric Relation : CReal CRealEq
    reflexivity proved by CRealEq_refl
    symmetry proved by CRealEq_sym
    transitivity proved by CRealEq_trans
      as CRealEq_rel.

Instance CRealEq_relT : CRelationClasses.Equivalence CRealEq.
Proof.
  split. exact CRealEq_refl. exact CRealEq_sym. exact CRealEq_trans.
Qed.

Instance CRealLt_morph
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRelationClasses.iffT)) CRealLt.
Proof.
  intros x y H x0 y0 H0. destruct H, H0. split.
  - intro. destruct (CRealLt_dec x x0 y). assumption.
    contradiction. destruct (CRealLt_dec y x0 y0).
    assumption. assumption. contradiction.
  - intro. destruct (CRealLt_dec y y0 x). assumption.
    contradiction. destruct (CRealLt_dec x y0 x0).
    assumption. assumption. contradiction.
Qed.

Instance CRealGt_morph
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRelationClasses.iffT)) CRealGt.
Proof.
  intros x y H x0 y0 H0. apply CRealLt_morph; assumption.
Qed.

Instance CReal_appart_morph
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRelationClasses.iffT)) CReal_appart.
Proof.
  split.
  - intros. destruct H1. left. rewrite <- H0, <- H. exact c.
    right. rewrite <- H0, <- H. exact c.
  - intros. destruct H1. left. rewrite H0, H. exact c.
    right. rewrite H0, H. exact c.
Qed.

Add Parametric Morphism : CRealLtProp
    with signature CRealEq ==> CRealEq ==> iff
      as CRealLtProp_morph.
Proof.
  intros x y H x0 y0 H0. split.
  - intro. apply CRealLtForget. apply CRealLtEpsilon in H1.
    rewrite <- H, <- H0. exact H1.
  - intro. apply CRealLtForget. apply CRealLtEpsilon in H1.
    rewrite H, H0. exact H1.
Qed.

Add Parametric Morphism : CRealLe
    with signature CRealEq ==> CRealEq ==> iff
      as CRealLe_morph.
Proof.
  intros. split.
  - intros H1 H2. unfold CRealLe in H1.
    rewrite <- H0 in H2. rewrite <- H in H2. contradiction.
  - intros H1 H2. unfold CRealLe in H1.
    rewrite H0 in H2. rewrite H in H2. contradiction.
Qed.

Add Parametric Morphism : CRealGe
    with signature CRealEq ==> CRealEq ==> iff
      as CRealGe_morph.
Proof.
  intros. unfold CRealGe. apply CRealLe_morph; assumption.
Qed.

Lemma CRealLt_proper_l : forall x y z : CReal,
    CRealEq x y
    -> CRealLt x z -> CRealLt y z.
Proof.
  intros. apply (CRealLt_morph x y H z z).
  apply CRealEq_refl. apply H0.
Qed.

Lemma CRealLt_proper_r : forall x y z : CReal,
    CRealEq x y
    -> CRealLt z x -> CRealLt z y.
Proof.
  intros. apply (CRealLt_morph z z (CRealEq_refl z) x y).
  apply H. apply H0.
Qed.

Lemma CRealLe_proper_l : forall x y z : CReal,
    CRealEq x y
    -> CRealLe x z -> CRealLe y z.
Proof.
  intros. apply (CRealLe_morph x y H z z).
  apply CRealEq_refl. apply H0.
Qed.

Lemma CRealLe_proper_r : forall x y z : CReal,
    CRealEq x y
    -> CRealLe z x -> CRealLe z y.
Proof.
  intros. apply (CRealLe_morph z z (CRealEq_refl z) x y).
  apply H. apply H0.
Qed.



(* Injection of Q into CReal *)

Lemma ConstCauchy : forall q : Q, QCauchySeq (fun _ => q).
Proof.
  intros. intros k p r H H0.
  unfold Qminus. rewrite Qplus_opp_r. unfold Qlt. simpl.
  unfold Z.lt. auto.
Qed.

Definition inject_Q : Q -> CReal.
Proof.
  intro q. exists (fun n => q). apply ConstCauchy.
Defined.

Definition inject_Z : Z -> CReal
  := fun n => inject_Q (n # 1).

Notation "0" := (inject_Q 0) : CReal_scope.
Notation "1" := (inject_Q 1) : CReal_scope.
Notation "2" := (inject_Q 2) : CReal_scope.

Lemma CRealLt_0_1 : CRealLt (inject_Q 0) (inject_Q 1).
Proof.
  exists 3%positive. reflexivity.
Qed.

Lemma CReal_injectQPos : forall q : Q,
    Qlt 0 q -> CRealLt (inject_Q 0) (inject_Q q).
Proof.
  intros. destruct (Qarchimedean ((2#1) / q)).
  exists x. simpl. unfold Qminus. rewrite Qplus_0_r.
  apply (Qmult_lt_compat_r _ _ q) in q0. 2: apply H.
  unfold Qdiv in q0.
  rewrite <- Qmult_assoc in q0. rewrite <- (Qmult_comm q) in q0.
  rewrite Qmult_inv_r in q0. rewrite Qmult_1_r in q0.
  unfold Qlt; simpl. unfold Qlt in q0; simpl in q0.
  rewrite Z.mul_1_r in q0. destruct q; simpl. simpl in q0.
  destruct Qnum. apply q0.
  rewrite <- Pos2Z.inj_mul. rewrite Pos.mul_comm. apply q0.
  inversion H. intro abs. rewrite abs in H. apply (Qlt_irrefl 0 H).
Qed.

(* A rational number has a constant Cauchy sequence realizing it
   as a real number, which increases the precision of the majoration
   by a factor 2. *)
Lemma CRealLtQ : forall (x : CReal) (q : Q),
    CRealLt x (inject_Q q)
    -> forall p:positive, Qlt (proj1_sig x p) (q + (1#p)).
Proof.
  intros [xn cau] q maj p. simpl.
  destruct (Qlt_le_dec (xn p) (q + (1 # p))). assumption.
  exfalso.
  apply CRealLt_above in maj.
  destruct maj as [k maj]; simpl in maj.
  specialize (maj (Pos.max k p) (Pos.le_max_l _ _)).
  specialize (cau p p (Pos.max k p) (Pos.le_refl _)).
  pose proof (Qplus_lt_le_compat (2#k) (q - xn (Pos.max k p))
                                 (q + (1 # p)) (xn p) maj q0).
  rewrite Qplus_comm in H. unfold Qminus in H. rewrite <- Qplus_assoc in H.
  rewrite <- Qplus_assoc in H. apply Qplus_lt_r in H.
  rewrite <- (Qplus_lt_r _ _ (xn p)) in maj.
  apply (Qlt_not_le (1#p) ((1 # p) + (2 # k))).
  rewrite <- (Qplus_0_r (1#p)). rewrite <- Qplus_assoc.
  apply Qplus_lt_r. reflexivity.
  apply Qlt_le_weak.
  apply (Qlt_trans _ (- xn (Pos.max k p) + xn p) _ H).
  rewrite Qplus_comm.
  apply (Qle_lt_trans _ (Qabs (xn p - xn (Pos.max k p)))).
  apply Qle_Qabs. apply cau. apply Pos.le_max_r.
Qed.

Lemma CRealLtQopp : forall (x : CReal) (q : Q),
    CRealLt (inject_Q q) x
    -> forall p:positive, Qlt (q - (1#p)) (proj1_sig x p).
Proof.
  intros [xn cau] q maj p. simpl.
  destruct (Qlt_le_dec (q - (1 # p)) (xn p)). assumption.
  exfalso.
  apply CRealLt_above in maj.
  destruct maj as [k maj]; simpl in maj.
  specialize (maj (Pos.max k p) (Pos.le_max_l _ _)).
  specialize (cau p (Pos.max k p) p).
  pose proof (Qplus_lt_le_compat (2#k) (xn (Pos.max k p) - q)
                                 (xn p) (q - (1 # p)) maj q0).
  unfold Qminus in H. rewrite <- Qplus_assoc in H.
  rewrite (Qplus_assoc (-q)) in H. rewrite (Qplus_comm (-q)) in H.
  rewrite Qplus_opp_r in H. rewrite Qplus_0_l in H.
  apply (Qplus_lt_l _ _ (1#p)) in H.
  rewrite <- (Qplus_assoc (xn (Pos.max k p))) in H.
  rewrite (Qplus_comm (-(1#p))) in H. rewrite Qplus_opp_r in H.
  rewrite Qplus_0_r in H. rewrite Qplus_comm in H.
  rewrite Qplus_assoc in H. apply (Qplus_lt_l _ _ (- xn p)) in H.
  rewrite <- Qplus_assoc in H. rewrite Qplus_opp_r in H. rewrite Qplus_0_r in H.
  apply (Qlt_not_le (1#p) ((1 # p) + (2 # k))).
  rewrite <- (Qplus_0_r (1#p)). rewrite <- Qplus_assoc.
  apply Qplus_lt_r. reflexivity.
  apply Qlt_le_weak.
  apply (Qlt_trans _ (xn (Pos.max k p) - xn p) _ H).
  apply (Qle_lt_trans _ (Qabs (xn (Pos.max k p) - xn p))).
  apply Qle_Qabs. apply cau.
  apply Pos.le_max_r. apply Pos.le_refl.
Qed.

Lemma inject_Q_compare : forall (x : CReal) (p : positive),
    x <= inject_Q (proj1_sig x p + (1#p)).
Proof.
  intros. intros [n nmaj].
  destruct x as [xn xcau]; simpl in nmaj.
  apply (Qplus_lt_l _ _ (1#p)) in nmaj.
  ring_simplify in nmaj.
  destruct (Pos.max_dec p n).
  - apply Pos.max_l_iff in e.
    specialize (xcau n n p (Pos.le_refl _) e).
    apply (Qlt_le_trans _ _ (Qabs (xn n + -1 * xn p))) in nmaj.
    2: apply Qle_Qabs.
    apply (Qlt_trans _ _ _ nmaj) in xcau.
    apply (Qplus_lt_l _ _ (-(1#n)-(1#p))) in xcau. ring_simplify in xcau.
    setoid_replace ((2 # n) + -1 * (1 # n)) with (1#n)%Q in xcau.
    discriminate xcau. setoid_replace (-1 * (1 # n)) with (-1#n)%Q. 2: reflexivity.
    rewrite Qinv_plus_distr. reflexivity.
  - apply Pos.max_r_iff in e.
    specialize (xcau p n p e (Pos.le_refl _)).
    apply (Qlt_le_trans _ _ (Qabs (xn n + -1 * xn p))) in nmaj.
    2: apply Qle_Qabs.
    apply (Qlt_trans _ _ _ nmaj) in xcau.
    apply (Qplus_lt_l _ _ (-(1#p))) in xcau. ring_simplify in xcau. discriminate.
Qed.


Add Parametric Morphism : inject_Q
    with signature Qeq ==> CRealEq
      as inject_Q_morph.
Proof.
  split.
  - intros [n abs]. simpl in abs. rewrite H in abs.
    unfold Qminus in abs. rewrite Qplus_opp_r in abs. discriminate abs.
  - intros [n abs]. simpl in abs. rewrite H in abs.
    unfold Qminus in abs. rewrite Qplus_opp_r in abs. discriminate abs.
Qed.

Instance inject_Q_morph_T
  : CMorphisms.Proper
      (CMorphisms.respectful Qeq CRealEq) inject_Q.
Proof.
  split.
  - intros [n abs]. simpl in abs. rewrite H in abs.
    unfold Qminus in abs. rewrite Qplus_opp_r in abs. discriminate abs.
  - intros [n abs]. simpl in abs. rewrite H in abs.
    unfold Qminus in abs. rewrite Qplus_opp_r in abs. discriminate abs.
Qed.



(* Algebraic operations *)

Lemma CReal_plus_cauchy
  : forall (x y : CReal),
    QCauchySeq (fun n : positive => Qred (proj1_sig x (2 * n)%positive
                                       + proj1_sig y (2 * n)%positive)).
Proof.
  destruct x as [xn limx], y as [yn limy]; unfold proj1_sig.
  intros n p q H H0.
  rewrite Qred_correct, Qred_correct.
  setoid_replace (xn (2 * p)%positive + yn (2 * p)%positive
                        - (xn (2 * q)%positive + yn (2 * q)%positive))
    with (xn (2 * p)%positive - xn (2 * q)%positive
          + (yn (2 * p)%positive - yn (2 * q)%positive)).
  2: ring.
  apply (Qle_lt_trans _ _ _ (Qabs_triangle _ _)).
  setoid_replace (1#n)%Q with ((1#2*n) + (1#2*n))%Q.
  apply Qplus_lt_le_compat.
  - apply limx. unfold id. apply Pos.mul_le_mono_l, H.
    unfold id. apply Pos.mul_le_mono_l, H0.
  - apply Qlt_le_weak, limy.
    unfold id. apply Pos.mul_le_mono_l, H.
    unfold id. apply Pos.mul_le_mono_l, H0.
  - rewrite Qinv_plus_distr. unfold Qeq. reflexivity.
Qed.

(* We reduce the rational numbers to accelerate calculations. *)
Definition CReal_plus (x y : CReal) : CReal
  := exist _ (fun n : positive => Qred (proj1_sig x (2 * n)%positive
                                     + proj1_sig y (2 * n)%positive))
           (CReal_plus_cauchy x y).

Infix "+" := CReal_plus : CReal_scope.

Definition CReal_opp (x : CReal) : CReal.
Proof.
  destruct x as [xn limx].
  exists (fun n : positive => - xn n).
  intros k p q H H0. unfold Qminus. rewrite Qopp_involutive.
  rewrite Qplus_comm. apply limx; assumption.
Defined.

Notation "- x" := (CReal_opp x) : CReal_scope.

Definition CReal_minus (x y : CReal) : CReal
  := CReal_plus x (CReal_opp y).

Infix "-" := CReal_minus : CReal_scope.

Lemma belowMultiple : forall n p : positive, Pos.le n (p * n).
Proof.
  intros. apply (Pos.le_trans _ (1*n)). apply Pos.le_refl.
  apply Pos.mul_le_mono_r. destruct p; discriminate.
Qed.

Lemma CReal_plus_assoc : forall (x y z : CReal),
    (x + y) + z == x + (y + z).
Proof.
  intros. apply CRealEq_diff. intro n.
  destruct x as [xn limx], y as [yn limy], z as [zn limz].
  unfold CReal_plus; unfold proj1_sig.
  rewrite Qred_correct, Qred_correct, Qred_correct, Qred_correct.
  setoid_replace (xn (2 * (2 * n))%positive + yn (2 * (2 * n))%positive
                  + zn (2 * n)%positive
                    - (xn (2 * n)%positive + (yn (2 * (2 * n))%positive
                                                    + zn (2 * (2 * n))%positive)))%Q
    with (xn (2 * (2 * n))%positive - xn (2 * n)%positive
          + (zn (2 * n)%positive - zn (2 * (2 * n))%positive))%Q.
  apply (Qle_trans _ (Qabs (xn (2 * (2 * n))%positive - xn (2 * n)%positive)
                      + Qabs (zn (2 * n)%positive - zn (2 * (2 * n))%positive))).
  apply Qabs_triangle.
  rewrite <- (Qinv_plus_distr 1 1 n). apply Qplus_le_compat.
  apply Qle_lteq. left. apply limx. rewrite Pos.mul_assoc.
  apply belowMultiple. apply belowMultiple.
  apply Qle_lteq. left. apply limz. apply belowMultiple.
  rewrite Pos.mul_assoc. apply belowMultiple. simpl. field.
Qed.

Lemma CReal_plus_comm : forall x y : CReal,
    x + y == y + x.
Proof.
  intros [xn limx] [yn limy]. apply CRealEq_diff. intros.
  unfold CReal_plus, proj1_sig. rewrite Qred_correct, Qred_correct.
  setoid_replace (xn (2 * n)%positive + yn (2 * n)%positive
                    - (yn (2 * n)%positive + xn (2 * n)%positive))%Q
    with 0%Q.
  unfold Qle. simpl. unfold Z.le. intro absurd. inversion absurd.
  ring.
Qed.

Lemma CReal_plus_0_l : forall r : CReal,
    inject_Q 0 + r == r.
Proof.
  intro r. split.
  - intros [n maj].
    destruct r as [xn q]; unfold CReal_plus, proj1_sig, inject_Q in maj.
    rewrite Qplus_0_l, Qred_correct in maj.
    specialize (q n n (Pos.mul 2 n) (Pos.le_refl _)).
    apply (Qlt_not_le (2#n) (xn n - xn (2 * n)%positive)).
    assumption.
    apply (Qle_trans _ (Qabs (xn n - xn (2 * n)%positive))).
    apply Qle_Qabs. apply (Qle_trans _ (1#n)). apply Qlt_le_weak. apply q.
    apply belowMultiple.
    unfold Qle, Qnum, Qden. apply Z.mul_le_mono_nonneg_r.
    discriminate. discriminate.
  - intros [n maj].
    destruct r as [xn q]; unfold CReal_plus, proj1_sig, inject_Q in maj.
    rewrite Qplus_0_l, Qred_correct in maj.
    specialize (q n n (Pos.mul 2 n) (Pos.le_refl _)).
    rewrite Qabs_Qminus in q.
    apply (Qlt_not_le (2#n) (xn (Pos.mul 2 n) - xn n)).
    assumption.
    apply (Qle_trans _ (Qabs (xn (Pos.mul 2 n) - xn n))).
    apply Qle_Qabs. apply (Qle_trans _ (1#n)). apply Qlt_le_weak. apply q.
    apply belowMultiple.
    unfold Qle, Qnum, Qden. apply Z.mul_le_mono_nonneg_r.
    discriminate. discriminate.
Qed.

Lemma CReal_plus_0_r : forall r : CReal,
    r + 0 == r.
Proof.
  intro r. rewrite CReal_plus_comm. apply CReal_plus_0_l.
Qed.

Lemma CReal_plus_lt_compat_l :
  forall x y z : CReal, y < z -> x + y < x + z.
Proof.
  intros.
  apply CRealLt_above in H. destruct H as [n maj].
  exists n. specialize (maj (2 * n)%positive).
  setoid_replace (proj1_sig (CReal_plus x z) n
                  - proj1_sig (CReal_plus x y) n)%Q
    with (proj1_sig z (2 * n)%positive - proj1_sig y (2 * n)%positive)%Q.
  apply maj. apply belowMultiple.
  destruct x as [xn limx], y as [yn limy], z as [zn limz];
  unfold CReal_plus, proj1_sig.
  rewrite Qred_correct, Qred_correct. ring.
Qed.

Lemma CReal_plus_lt_compat_r :
  forall x y z : CReal, y < z -> y + x < z + x.
Proof.
  intros. do 2 rewrite <- (CReal_plus_comm x).
  apply CReal_plus_lt_compat_l. assumption.
Qed.

Lemma CReal_plus_lt_reg_l :
  forall x y z : CReal, x + y < x + z -> y < z.
Proof.
  intros. destruct H as [n maj]. exists (2*n)%positive.
  setoid_replace (proj1_sig z (2 * n)%positive - proj1_sig y (2 * n)%positive)%Q
      with (proj1_sig (CReal_plus x z) n - proj1_sig (CReal_plus x y) n)%Q.
  apply (Qle_lt_trans _ (2#n)).
  setoid_replace (2 # 2 * n)%Q with (1 # n)%Q. 2: reflexivity.
  unfold Qle, Qnum, Qden. apply Z.mul_le_mono_nonneg_r.
  discriminate. discriminate.
  apply maj.
  destruct x as [xn limx], y as [yn limy], z as [zn limz];
    unfold CReal_plus, proj1_sig.
  rewrite Qred_correct, Qred_correct. ring.
Qed.

Lemma CReal_plus_lt_reg_r :
  forall x y z : CReal, y + x < z + x -> y < z.
Proof.
  intros x y z H. rewrite (CReal_plus_comm y), (CReal_plus_comm z) in H.
  apply CReal_plus_lt_reg_l in H. exact H.
Qed.

Lemma CReal_plus_le_reg_l :
  forall x y z : CReal, x + y <= x + z -> y <= z.
Proof.
  intros. intro abs. apply H. clear H.
  apply CReal_plus_lt_compat_l. exact abs.
Qed.

Lemma CReal_plus_le_reg_r :
  forall x y z : CReal, y + x <= z + x -> y <= z.
Proof.
  intros. intro abs. apply H. clear H.
  apply CReal_plus_lt_compat_r. exact abs.
Qed.

Lemma CReal_plus_le_compat_l : forall r r1 r2, r1 <= r2 -> r + r1 <= r + r2.
Proof.
  intros. intro abs. apply CReal_plus_lt_reg_l in abs. contradiction.
Qed.

Lemma CReal_plus_le_lt_compat :
  forall r1 r2 r3 r4 : CReal, r1 <= r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros; apply CReal_le_lt_trans with (r2 + r3).
  intro abs. rewrite CReal_plus_comm, (CReal_plus_comm r1) in abs.
  apply CReal_plus_lt_reg_l in abs. contradiction.
  apply CReal_plus_lt_compat_l; exact H0.
Qed.

Lemma CReal_plus_le_compat :
  forall r1 r2 r3 r4 : CReal, r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
  intros; apply CReal_le_trans with (r2 + r3).
  intro abs. rewrite CReal_plus_comm, (CReal_plus_comm r1) in abs.
  apply CReal_plus_lt_reg_l in abs. contradiction.
  apply CReal_plus_le_compat_l; exact H0.
Qed.

Lemma CReal_plus_opp_r : forall x : CReal,
    x + - x == 0.
Proof.
  intros [xn limx]. apply CRealEq_diff. intros.
  unfold CReal_plus, CReal_opp, inject_Q, proj1_sig.
  rewrite Qred_correct.
  setoid_replace (xn (2 * n)%positive + - xn (2 * n)%positive - 0)%Q
    with 0%Q.
  unfold Qle. simpl. unfold Z.le. intro absurd. inversion absurd. ring.
Qed.

Lemma CReal_plus_opp_l : forall x : CReal,
    - x + x == 0.
Proof.
  intro x. rewrite CReal_plus_comm. apply CReal_plus_opp_r.
Qed.

Lemma CReal_plus_proper_r : forall x y z : CReal,
    CRealEq x y -> CRealEq (CReal_plus x z) (CReal_plus y z).
Proof.
  intros. apply (CRealEq_trans _ (CReal_plus z x)).
  apply CReal_plus_comm. apply (CRealEq_trans _ (CReal_plus z y)).
  2: apply CReal_plus_comm.
  split. intro abs. apply CReal_plus_lt_reg_l in abs.
  destruct H. contradiction. intro abs. apply CReal_plus_lt_reg_l in abs.
  destruct H. contradiction.
Qed.

Lemma CReal_plus_proper_l : forall x y z : CReal,
    CRealEq x y -> CRealEq (CReal_plus z x) (CReal_plus z y).
Proof.
  intros. split. intro abs. apply CReal_plus_lt_reg_l in abs.
  destruct H. contradiction. intro abs. apply CReal_plus_lt_reg_l in abs.
  destruct H. contradiction.
Qed.

Add Parametric Morphism : CReal_plus
    with signature CRealEq ==> CRealEq ==> CRealEq
      as CReal_plus_morph.
Proof.
  intros x y H z t H0. apply (CRealEq_trans _ (CReal_plus x t)).
  - destruct H0.
    split. intro abs. apply CReal_plus_lt_reg_l in abs. contradiction.
    intro abs. apply CReal_plus_lt_reg_l in abs. contradiction.
  - apply CReal_plus_proper_r. apply H.
Qed.

Instance CReal_plus_morph_T
  : CMorphisms.Proper
      (CMorphisms.respectful CRealEq (CMorphisms.respectful CRealEq CRealEq)) CReal_plus.
Proof.
  intros x y H z t H0. apply (CRealEq_trans _ (CReal_plus x t)).
  - destruct H0.
    split. intro abs. apply CReal_plus_lt_reg_l in abs. contradiction.
    intro abs. apply CReal_plus_lt_reg_l in abs. contradiction.
  - apply CReal_plus_proper_r. apply H.
Qed.

Lemma CReal_plus_eq_reg_l : forall (r r1 r2 : CReal),
    r + r1 == r + r2 -> r1 == r2.
Proof.
  intros. destruct H. split.
  - intro abs. apply (CReal_plus_lt_compat_l r) in abs. contradiction.
  - intro abs. apply (CReal_plus_lt_compat_l r) in abs. contradiction.
Qed.

Lemma CReal_opp_0 : -0 == 0.
Proof.
  apply (CReal_plus_eq_reg_l 0).
  rewrite CReal_plus_0_r, CReal_plus_opp_r. reflexivity.
Qed.

Lemma CReal_opp_plus_distr : forall r1 r2, - (r1 + r2) == - r1 + - r2.
Proof.
  intros. apply (CReal_plus_eq_reg_l (r1+r2)).
  rewrite CReal_plus_opp_r, (CReal_plus_comm (-r1)), CReal_plus_assoc.
  rewrite <- (CReal_plus_assoc r2), CReal_plus_opp_r, CReal_plus_0_l.
  rewrite CReal_plus_opp_r. reflexivity.
Qed.

Lemma CReal_opp_involutive : forall x:CReal, --x == x.
Proof.
  intros. apply (CReal_plus_eq_reg_l (-x)).
  rewrite CReal_plus_opp_l, CReal_plus_opp_r. reflexivity.
Qed.

Lemma CReal_opp_gt_lt_contravar : forall r1 r2, r1 > r2 -> - r1 < - r2.
Proof.
  unfold CRealGt; intros.
  apply (CReal_plus_lt_reg_l (r2 + r1)).
  rewrite CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_r.
  rewrite CReal_plus_comm, <- CReal_plus_assoc, CReal_plus_opp_l.
  rewrite CReal_plus_0_l. exact H.
Qed.

Lemma CReal_opp_ge_le_contravar : forall r1 r2, r1 >= r2 -> - r1 <= - r2.
Proof.
  intros. intro abs. apply H. clear H.
  apply (CReal_plus_lt_reg_r (-r1-r2)).
  unfold CReal_minus. rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
  rewrite (CReal_plus_comm (-r1)), <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
  exact abs.
Qed.

Lemma inject_Q_plus : forall q r : Q,
    inject_Q (q + r) == inject_Q q + inject_Q r.
Proof.
  split.
  - intros [n nmaj]. unfold CReal_plus, inject_Q, proj1_sig in nmaj.
    rewrite Qred_correct in nmaj.
    ring_simplify in nmaj. discriminate.
  - intros [n nmaj]. unfold CReal_plus, inject_Q, proj1_sig in nmaj.
    rewrite Qred_correct in nmaj.
    ring_simplify in nmaj. discriminate.
Qed.

Lemma inject_Q_one : inject_Q 1 == 1.
Proof.
  split.
  - intros [n nmaj]. simpl in nmaj.
    ring_simplify in nmaj. discriminate.
  - intros [n nmaj]. simpl in nmaj.
    ring_simplify in nmaj. discriminate.
Qed.

Lemma inject_Q_lt : forall q r : Q,
    Qlt q r -> inject_Q q < inject_Q r.
Proof.
  intros. destruct (Qarchimedean (/(r-q))).
  exists (2*x)%positive; simpl.
  setoid_replace (2 # x~0)%Q with (/(Z.pos x#1))%Q. 2: reflexivity.
  apply Qlt_shift_inv_r. reflexivity.
  apply (Qmult_lt_l _ _ (r-q)) in q0. rewrite Qmult_inv_r in q0.
  exact q0. intro abs. rewrite Qlt_minus_iff in H.
  unfold Qminus in abs. rewrite abs in H. discriminate H.
  unfold Qminus. rewrite <- Qlt_minus_iff. exact H.
Qed.

Lemma opp_inject_Q : forall q : Q,
    inject_Q (-q) == - inject_Q q.
Proof.
  split.
  - intros [n maj]. simpl in maj. ring_simplify in maj. discriminate.
  - intros [n maj]. simpl in maj. ring_simplify in maj. discriminate.
Qed.

Lemma lt_inject_Q : forall q r : Q,
    inject_Q q < inject_Q r -> Qlt q r.
Proof.
  intros. destruct H. simpl in q0.
  apply Qlt_minus_iff, (Qlt_trans _ (2#x)).
  reflexivity. exact q0.
Qed.

Lemma le_inject_Q : forall q r : Q,
    inject_Q q <= inject_Q r -> Qle q r.
Proof.
  intros. destruct (Qlt_le_dec r q). 2: exact q0.
  exfalso. apply H. clear H. apply inject_Q_lt. exact q0.
Qed.

Lemma inject_Q_le : forall q r : Q,
    Qle q r -> inject_Q q <= inject_Q r.
Proof.
  intros. intros [n maj]. simpl in maj.
  apply (Qlt_not_le _ _ maj). apply (Qle_trans _ 0).
  apply (Qplus_le_l _ _ r). ring_simplify. exact H. discriminate.
Qed.

Lemma inject_Z_plus : forall q r : Z,
    inject_Z (q + r) == inject_Z q + inject_Z r.
Proof.
  intros. unfold inject_Z.
  setoid_replace (q + r # 1)%Q with ((q#1) + (r#1))%Q.
  apply inject_Q_plus. rewrite Qinv_plus_distr. reflexivity.
Qed.

Lemma opp_inject_Z : forall n : Z,
    inject_Z (-n) == - inject_Z n.
Proof.
  intros. unfold inject_Z.
  setoid_replace (-n # 1)%Q with (-(n#1))%Q.
  rewrite opp_inject_Q. reflexivity. reflexivity.
Qed.

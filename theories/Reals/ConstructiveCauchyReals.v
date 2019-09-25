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

Require Import QArith.
Require Import Qabs.
Require Import Qround.
Require Import Logic.ConstructiveEpsilon.
Require CMorphisms.

(** The constructive Cauchy real numbers, ie the Cauchy sequences
    of rational numbers. This file is not supposed to be imported,
    except in Rdefinitions.v, Raxioms.v, Rcomplete_constr.v
    and ConstructiveRIneq.v.

    Constructive real numbers should be considered abstractly,
    forgetting the fact that they are implemented as rational sequences.
    All useful lemmas of this file are exposed in ConstructiveRIneq.v,
    under more abstract names, like Rlt_asym instead of CRealLt_asym.


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
 *)
Definition QSeqEquiv (un vn : nat -> Q) (cvmod : positive -> nat)
  : Prop
  := forall (k : positive) (p q : nat),
      le (cvmod k) p
      -> le (cvmod k) q
      -> Qlt (Qabs (un p - vn q)) (1 # k).

(* A Cauchy sequence is a sequence equivalent to itself.
   If sequences are equivalent, they are both Cauchy and have the same limit. *)
Definition QCauchySeq (un : nat -> Q) (cvmod : positive -> nat) : Prop
  := QSeqEquiv un un cvmod.

Lemma QSeqEquiv_sym : forall (un vn : nat -> Q) (cvmod : positive -> nat),
    QSeqEquiv un vn cvmod
    -> QSeqEquiv vn un cvmod.
Proof.
  intros. intros k p q H0 H1.
  rewrite Qabs_Qminus. apply H; assumption.
Qed.

Lemma factorDenom : forall (a:Z) (b d:positive), (a # (d * b)) == (1#d) * (a#b).
Proof.
  intros. unfold Qeq. simpl. destruct a; reflexivity.
Qed.

Lemma QSeqEquiv_trans : forall (un vn wn : nat -> Q)
                          (cvmod cvmodw : positive -> nat),
    QSeqEquiv un vn cvmod
    -> QSeqEquiv vn wn cvmodw
    -> QSeqEquiv un wn (fun q => max (cvmod (2 * q)%positive) (cvmodw (2 * q)%positive)).
Proof.
  intros. intros k p q H1 H2.
  setoid_replace (un p - wn q) with (un p - vn p + (vn p - wn q)).
  apply (Qle_lt_trans
           _ (Qabs (un p - vn p) + Qabs (vn p - wn q))).
  apply Qabs_triangle. apply (Qlt_le_trans _ ((1 # (2*k)) + (1 # (2*k)))).
  apply Qplus_lt_le_compat.
  - assert ((cvmod (2 * k)%positive <= p)%nat).
    { apply (le_trans _ (max (cvmod (2 * k)%positive) (cvmodw (2 * k)%positive))).
      apply Nat.le_max_l. assumption. }
    apply H. assumption. assumption.
  - apply Qle_lteq. left. apply H0.
    apply (le_trans _ (max (cvmod (2 * k)%positive) (cvmodw (2 * k)%positive))).
    apply Nat.le_max_r. assumption.
    apply (le_trans _ (max (cvmod (2 * k)%positive) (cvmodw (2 * k)%positive))).
    apply Nat.le_max_r. assumption.
  - rewrite (factorDenom _ _ 2). ring_simplify. apply Qle_refl.
  - ring.
Qed.

Definition QSeqEquivEx (un vn : nat -> Q) : Prop
  := exists (cvmod : positive -> nat), QSeqEquiv un vn cvmod.

Lemma QSeqEquivEx_sym : forall (un vn : nat -> Q), QSeqEquivEx un vn -> QSeqEquivEx vn un.
Proof.
  intros. destruct H. exists x. apply QSeqEquiv_sym. apply H.
Qed.

Lemma QSeqEquivEx_trans : forall un vn wn : nat -> Q,
    QSeqEquivEx un vn
    -> QSeqEquivEx vn wn
    -> QSeqEquivEx un wn.
Proof.
  intros. destruct H,H0.
  exists (fun q => max (x (2 * q)%positive) (x0 (2 * q)%positive)).
  apply (QSeqEquiv_trans un vn wn); assumption.
Qed.

Lemma QSeqEquiv_cau_r : forall (un vn : nat -> Q) (cvmod : positive -> nat),
    QSeqEquiv un vn cvmod
    -> QCauchySeq vn (fun k => cvmod (2 * k)%positive).
Proof.
  intros. intros k p q H0 H1.
  setoid_replace (vn p - vn q)
    with (vn p
          - un (cvmod (2 * k)%positive)
          + (un (cvmod (2 * k)%positive) - vn q)).
  - apply (Qle_lt_trans
             _ (Qabs (vn p
                      - un (cvmod (2 * k)%positive))
                + Qabs (un (cvmod (2 * k)%positive) - vn q))).
    apply Qabs_triangle.
    apply (Qlt_le_trans _ ((1 # (2 * k)) + (1 # (2 * k)))).
    apply Qplus_lt_le_compat.
    + rewrite Qabs_Qminus. apply H. apply le_refl. assumption.
    + apply Qle_lteq. left. apply H. apply le_refl. assumption.
    + rewrite (factorDenom _ _ 2). ring_simplify. apply Qle_refl.
  - ring.
Qed.

Fixpoint increasing_modulus (modulus : positive -> nat) (n : nat)
  := match n with
     | O => modulus xH
     | S p => max (modulus (Pos.of_nat n)) (increasing_modulus modulus p)
     end.

Lemma increasing_modulus_inc : forall (modulus : positive -> nat) (n p : nat),
    le (increasing_modulus modulus n)
       (increasing_modulus modulus (p + n)).
Proof.
  induction p.
  - apply le_refl.
  - apply (le_trans _ (increasing_modulus modulus (p + n))).
    apply IHp. simpl. destruct (plus p n). apply Nat.le_max_r. apply Nat.le_max_r.
Qed.

Lemma increasing_modulus_max : forall (modulus : positive -> nat) (p n : nat),
    le n p -> le (modulus (Pos.of_nat n))
                 (increasing_modulus modulus p).
Proof.
  induction p.
  - intros. inversion H. subst n. apply le_refl.
  - intros. simpl. destruct p. simpl.
    + destruct n. apply Nat.le_max_l. apply le_S_n in H.
      inversion H. apply Nat.le_max_l.
    + apply Nat.le_succ_r in H. destruct H.
      apply (le_trans _ (increasing_modulus modulus (S p))).
      2: apply Nat.le_max_r. apply IHp. apply H.
      subst n. apply (le_trans _ (modulus (Pos.succ (Pos.of_nat (S p))))).
      apply le_refl. apply Nat.le_max_l.
Qed.

(* Choice of a standard element in each QSeqEquiv class. *)
Lemma standard_modulus : forall (un : nat -> Q) (cvmod : positive -> nat),
    QCauchySeq un cvmod
    -> (QCauchySeq (fun n => un (increasing_modulus cvmod n)) Pos.to_nat
       /\ QSeqEquiv un (fun n => un (increasing_modulus cvmod n))
                   (fun p => max (cvmod p) (Pos.to_nat p))).
Proof.
  intros. split.
  - intros k p q H0 H1. apply H.
    + apply (le_trans _ (increasing_modulus cvmod (Pos.to_nat k))).
      apply (le_trans _ (cvmod (Pos.of_nat (Pos.to_nat k)))).
      rewrite Pos2Nat.id. apply le_refl.
      destruct (Pos.to_nat k). apply le_refl. apply Nat.le_max_l.
      destruct (Nat.le_exists_sub (Pos.to_nat k) p H0) as [i [H2 H3]]. subst p.
      apply increasing_modulus_inc.
    + apply (le_trans _ (increasing_modulus cvmod (Pos.to_nat k))).
      apply (le_trans _ (cvmod (Pos.of_nat (Pos.to_nat k)))).
      rewrite Pos2Nat.id. apply le_refl.
      destruct (Pos.to_nat k). apply le_refl. apply Nat.le_max_l.
      destruct (Nat.le_exists_sub (Pos.to_nat k) q H1) as [i [H2 H3]]. subst q.
      apply increasing_modulus_inc.
  - intros k p q H0 H1. apply H.
    + apply (le_trans _ (Init.Nat.max (cvmod k) (Pos.to_nat k))).
      apply Nat.le_max_l. assumption.
    + apply (le_trans _ (increasing_modulus cvmod (Pos.to_nat k))).
      apply (le_trans _ (cvmod (Pos.of_nat (Pos.to_nat k)))).
      rewrite Pos2Nat.id. apply le_refl.
      destruct (Pos.to_nat k). apply le_refl. apply Nat.le_max_l.
      assert (le (Pos.to_nat k) q).
      { apply (le_trans _ (Init.Nat.max (cvmod k) (Pos.to_nat k))).
        apply Nat.le_max_r. assumption. }
      destruct (Nat.le_exists_sub (Pos.to_nat k) q H2) as [i [H3 H4]]. subst q.
      apply increasing_modulus_inc.
Qed.

(* A Cauchy real is a Cauchy sequence with the standard modulus *)
Definition CReal : Set
  := { x : (nat -> Q) | QCauchySeq x Pos.to_nat }.

Declare Scope CReal_scope.

(* Declare Scope R_scope with Key R *)
Delimit Scope CReal_scope with CReal.

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope CReal_scope with CReal.

Local Open Scope CReal_scope.


(* So QSeqEquiv is the equivalence relation of this constructive pre-order *)
Definition CRealLt (x y : CReal) : Set
  := { n : positive |  Qlt (2 # n)
                           (proj1_sig y (Pos.to_nat n) - proj1_sig x (Pos.to_nat n)) }.

Definition CRealLtProp (x y : CReal) : Prop
  := exists n : positive, Qlt (2 # n)
                         (proj1_sig y (Pos.to_nat n) - proj1_sig x (Pos.to_nat n)).

Definition CRealGt (x y : CReal) := CRealLt y x.
Definition CReal_appart (x y : CReal) := sum (CRealLt x y) (CRealLt y x).

Infix "<" := CRealLt : CReal_scope.
Infix ">" := CRealGt : CReal_scope.
Infix "#" := CReal_appart : CReal_scope.

(* This Prop can be extracted as a sigma type *)
Lemma CRealLtEpsilon : forall x y : CReal,
    CRealLtProp x y -> x < y.
Proof.
  intros.
  assert (exists n : nat, n <> O
                   /\ Qlt (2 # Pos.of_nat n) (proj1_sig y n - proj1_sig x n)).
  { destruct H as [n maj]. exists (Pos.to_nat n). split.
    intro abs. destruct (Pos2Nat.is_succ n). rewrite H in abs.
    inversion abs. rewrite Pos2Nat.id. apply maj. }
  apply constructive_indefinite_ground_description_nat in H0.
  destruct H0 as [n maj]. exists (Pos.of_nat n).
  rewrite Nat2Pos.id. apply maj. apply maj.
  intro n. destruct n. right.
  intros [abs _]. exact (abs (eq_refl O)).
  destruct (Qlt_le_dec (2 # Pos.of_nat (S n))
                       (proj1_sig y (S n) - proj1_sig x (S n))).
  left. split. discriminate. apply q.
  right. intros [_ abs].
  apply (Qlt_not_le (2 # Pos.of_nat (S n))
                    (proj1_sig y (S n) - proj1_sig x (S n))); assumption.
Qed.

Lemma CRealLtForget : forall x y : CReal,
    x < y -> CRealLtProp x y.
Proof.
  intros. destruct H. exists x0. exact q.
Qed.

(* CRealLt is decided by the LPO in Type,
   which is a non-constructive oracle. *)
Lemma CRealLt_lpo_dec : forall x y : CReal,
    (forall (P : nat -> Prop), (forall n, {P n} + {~P n})
                    -> {n | ~P n} + {forall n, P n})
    -> CRealLt x y + (CRealLt x y -> False).
Proof.
  intros x y lpo.
  destruct (lpo (fun n:nat => Qle (proj1_sig y (S n) - proj1_sig x (S n))
                             (2 # Pos.of_nat (S n)))).
  - intro n. destruct (Qlt_le_dec (2 # Pos.of_nat (S n))
                                  (proj1_sig y (S n) - proj1_sig x (S n))).
    right. apply Qlt_not_le. exact q. left. exact q.
  - left. destruct s as [n nmaj]. exists (Pos.of_nat (S n)).
    rewrite Nat2Pos.id. apply Qnot_le_lt. exact nmaj. discriminate.
  - right. intro abs. destruct abs as [n majn].
    specialize (q (pred (Pos.to_nat n))).
    replace (S (pred (Pos.to_nat n))) with (Pos.to_nat n) in q.
    rewrite Pos2Nat.id in q.
    pose proof (Qle_not_lt _ _ q). contradiction.
    symmetry. apply Nat.succ_pred. intro abs.
    pose proof (Pos2Nat.is_pos n). rewrite abs in H. inversion H.
Qed.

(* Alias the quotient order equality *)
Definition CRealEq (x y : CReal) : Prop
  := (CRealLt x y -> False) /\ (CRealLt y x -> False).

Infix "==" := CRealEq : CReal_scope.

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

Lemma CRealLe_not_lt : forall x y : CReal,
    (forall n:positive, Qle (proj1_sig x (Pos.to_nat n) - proj1_sig y (Pos.to_nat n))
                       (2 # n))
    <-> x <= y.
Proof.
  intros. split.
  - intros. intro H0. destruct H0 as [n H0]. specialize (H n).
    apply (Qle_not_lt (2 # n) (2 # n)). apply Qle_refl.
    apply (Qlt_le_trans _ (proj1_sig x (Pos.to_nat n) - proj1_sig y (Pos.to_nat n))).
    assumption. assumption.
  - intros.
    destruct (Qlt_le_dec (2 # n) (proj1_sig x (Pos.to_nat n) - proj1_sig y (Pos.to_nat n))).
    exfalso. apply H. exists n. assumption. assumption.
Qed.

Lemma CRealEq_diff : forall (x y : CReal),
    CRealEq x y
    <-> forall n:positive, Qle (Qabs (proj1_sig x (Pos.to_nat n) - proj1_sig y (Pos.to_nat n)))
                        (2 # n).
Proof.
  intros. split.
  - intros. destruct H. apply Qabs_case. intro.
    pose proof (CRealLe_not_lt x y) as [_ H2]. apply H2. assumption.
    intro. pose proof (CRealLe_not_lt y x) as [_ H2].
    setoid_replace (- (proj1_sig x (Pos.to_nat n) - proj1_sig y (Pos.to_nat n)))
      with (proj1_sig y (Pos.to_nat n) - proj1_sig x (Pos.to_nat n)).
    apply H2. assumption. ring.
  - intros. split. apply CRealLe_not_lt. intro n. specialize (H n).
    rewrite Qabs_Qminus in H.
    apply (Qle_trans _ (Qabs (proj1_sig y (Pos.to_nat n) - proj1_sig x (Pos.to_nat n)))).
    apply Qle_Qabs. apply H.
    apply CRealLe_not_lt. intro n. specialize (H n).
    apply (Qle_trans _ (Qabs (proj1_sig x (Pos.to_nat n) - proj1_sig y (Pos.to_nat n)))).
    apply Qle_Qabs. apply H.
Qed.

(* The equality on Cauchy reals is just QSeqEquiv,
   which is independant of the convergence modulus. *)
Lemma CRealEq_modindep : forall (x y : CReal),
    QSeqEquivEx (proj1_sig x) (proj1_sig y)
    <-> forall n:positive,
      Qle (Qabs (proj1_sig x (Pos.to_nat n) - proj1_sig y (Pos.to_nat n))) (2 # n).
Proof.
  assert (forall x y: CReal, QSeqEquivEx (proj1_sig x) (proj1_sig y) -> x <= y ).
  { intros [xn limx] [yn limy] [cvmod H] [n abs]. simpl in abs, H.
    pose (xn (Pos.to_nat n) - yn (Pos.to_nat n) - (2#n)) as eps.
    destruct (Qarchimedean (/eps)) as [k maj].
    remember (max (cvmod k) (Pos.to_nat n)) as p.
    assert (le (cvmod k) p).
    { rewrite Heqp. apply Nat.le_max_l. }
    assert (Pos.to_nat n <= p)%nat.
    { rewrite Heqp. apply Nat.le_max_r. }
    specialize (H k p p H0 H0).
    setoid_replace (Z.pos k #1)%Q with (/ (1#k)) in maj. 2: reflexivity.
    apply Qinv_lt_contravar in maj. 2: reflexivity. unfold eps in maj.
    clear abs. (* less precise majoration *)
    apply (Qplus_lt_r _ _ (2#n)) in maj. ring_simplify in maj.
    apply (Qlt_not_le _ _ maj). clear maj.
    setoid_replace (xn (Pos.to_nat n) + -1 * yn (Pos.to_nat n))
      with (xn (Pos.to_nat n) - xn p + (xn p - yn p + (yn p - yn (Pos.to_nat n)))).
    2: ring.
    setoid_replace (2 # n)%Q with ((1 # n) + (1#n)).
    rewrite <- Qplus_assoc.
    apply Qplus_le_compat. apply (Qle_trans _ _ _ (Qle_Qabs _)).
    apply Qlt_le_weak. apply limx. apply le_refl. assumption.
    rewrite (Qplus_comm (1#n)).
    apply Qplus_le_compat. apply (Qle_trans _ _ _ (Qle_Qabs _)).
    apply Qlt_le_weak. exact H.
    apply (Qle_trans _ _ _ (Qle_Qabs _)). apply Qlt_le_weak. apply limy.
    assumption. apply le_refl. ring_simplify. reflexivity.
    unfold eps. unfold Qminus. rewrite <- Qlt_minus_iff. exact abs. }
  split.
  - rewrite <- CRealEq_diff. intros. split.
    apply H, QSeqEquivEx_sym. exact H0. apply H. exact H0.
  - clear H. intros. destruct x as [xn limx], y as [yn limy].
    exists (fun q => Pos.to_nat (2 * (3 * q))). intros k p q H0 H1.
    unfold proj1_sig. specialize (H (2 * (3 * k))%positive).
    assert ((Pos.to_nat (3 * k) <= Pos.to_nat (2 * (3 * k)))%nat).
    { generalize (3 * k)%positive. intros. rewrite Pos2Nat.inj_mul.
      rewrite <- (mult_1_l (Pos.to_nat p0)). apply Nat.mul_le_mono_nonneg.
      auto. unfold Pos.to_nat. simpl. auto.
      apply (le_trans 0 1). auto. apply Pos2Nat.is_pos. rewrite mult_1_l.
      apply le_refl. }
    setoid_replace (xn p - yn q)
      with (xn p - xn (Pos.to_nat (2 * (3 * k)))
            + (xn (Pos.to_nat (2 * (3 * k))) - yn (Pos.to_nat (2 * (3 * k)))
               + (yn (Pos.to_nat (2 * (3 * k))) - yn q))).
    setoid_replace (1 # k)%Q with ((1 # 3 * k) + ((1 # 3 * k) + (1 # 3 * k))).
    apply (Qle_lt_trans
             _ (Qabs (xn p - xn (Pos.to_nat (2 * (3 * k))))
                + (Qabs (xn (Pos.to_nat (2 * (3 * k))) - yn (Pos.to_nat (2 * (3 * k)))
                         + (yn (Pos.to_nat (2 * (3 * k))) - yn q))))).
    apply Qabs_triangle. apply Qplus_lt_le_compat.
    apply limx. apply (le_trans _ (Pos.to_nat (2 * (3 * k)))). assumption. assumption.
    assumption.
    apply (Qle_trans
             _ (Qabs (xn (Pos.to_nat (2 * (3 * k))) - yn (Pos.to_nat (2 * (3 * k))))
                + Qabs (yn (Pos.to_nat (2 * (3 * k))) - yn q))).
    apply Qabs_triangle. apply Qplus_le_compat.
    setoid_replace (1 # 3 * k)%Q with (2 # 2 * (3 * k))%Q. apply H.
    rewrite (factorDenom _ _ 3). rewrite (factorDenom _ _ 2). rewrite (factorDenom _ _ 3).
    rewrite Qmult_assoc. rewrite (Qmult_comm (1#2)).
    rewrite <- Qmult_assoc. apply Qmult_comp. reflexivity.
    unfold Qeq. reflexivity.
    apply Qle_lteq. left. apply limy. assumption.
    apply (le_trans _ (Pos.to_nat (2 * (3 * k)))). assumption. assumption.
    rewrite (factorDenom _ _ 3). ring_simplify. reflexivity. field.
Qed.

(* Extend separation to all indices above *)
Lemma CRealLt_aboveSig : forall (x y : CReal) (n : positive),
    (Qlt (2 # n)
         (proj1_sig y (Pos.to_nat n) - proj1_sig x (Pos.to_nat n)))
    -> let (k, _) := Qarchimedean (/(proj1_sig y (Pos.to_nat n) - proj1_sig x (Pos.to_nat n) - (2#n)))
      in forall p:positive,
          Pos.le (Pos.max n (2*k)) p
          -> Qlt (2 # (Pos.max n (2*k)))
                (proj1_sig y (Pos.to_nat p) - proj1_sig x (Pos.to_nat p)).
Proof.
  intros [xn limx] [yn limy] n maj.
  unfold proj1_sig; unfold proj1_sig in maj.
  pose (yn (Pos.to_nat n) - xn (Pos.to_nat n)) as dn.
  destruct (Qarchimedean (/(yn (Pos.to_nat n) - xn (Pos.to_nat n) - (2#n)))) as [k kmaj].
  assert (0 < yn (Pos.to_nat n) - xn (Pos.to_nat n) - (2 # n))%Q as H0.
  { rewrite <- (Qplus_opp_r (2#n)). apply Qplus_lt_l. assumption. }
  intros.
  remember (yn (Pos.to_nat p) - xn (Pos.to_nat p)) as dp.

  rewrite <- (Qplus_0_r dp). rewrite <- (Qplus_opp_r dn).
  rewrite (Qplus_comm dn). rewrite Qplus_assoc.
  assert (Qlt (Qabs (dp - dn)) (2#n)).
  { rewrite Heqdp. unfold dn.
    setoid_replace (yn (Pos.to_nat p) - xn (Pos.to_nat p) - (yn (Pos.to_nat n) - xn (Pos.to_nat n)))
      with (yn (Pos.to_nat p) - yn (Pos.to_nat n)
            + (xn (Pos.to_nat n) - xn (Pos.to_nat p))).
    apply (Qle_lt_trans _ (Qabs (yn (Pos.to_nat p) - yn (Pos.to_nat n))
                           + Qabs (xn (Pos.to_nat n) - xn (Pos.to_nat p)))).
    apply Qabs_triangle.
    setoid_replace (2#n)%Q with ((1#n) + (1#n))%Q.
    apply Qplus_lt_le_compat. apply limy.
    apply Pos2Nat.inj_le. apply (Pos.le_trans _ (Pos.max n (2 * k))).
    apply Pos.le_max_l. assumption.
    apply le_refl. apply Qlt_le_weak. apply limx. apply le_refl.
    apply Pos2Nat.inj_le. apply (Pos.le_trans _ (Pos.max n (2 * k))).
    apply Pos.le_max_l. assumption.
    rewrite Qinv_plus_distr. reflexivity. field. }
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
          Pos.le k p -> Qlt (2 # k) (proj1_sig y (Pos.to_nat p)
                                    - proj1_sig x (Pos.to_nat p)) }.
Proof.
  intros x y [n maj].
  pose proof (CRealLt_aboveSig x y n maj).
  destruct (Qarchimedean (/ (proj1_sig y (Pos.to_nat n) - proj1_sig x (Pos.to_nat n) - (2 # n))))
    as [k kmaj].
  exists (Pos.max n (2*k)). apply H.
Qed.

(* The CRealLt index separates the Cauchy sequences *)
Lemma CRealLt_above_same : forall (x y : CReal) (n : positive),
    Qlt (2 # n)
        (proj1_sig y (Pos.to_nat n) - proj1_sig x (Pos.to_nat n))
    -> forall p:positive, Pos.le n p
                    -> Qlt (proj1_sig x (Pos.to_nat p)) (proj1_sig y (Pos.to_nat p)).
Proof.
  intros [xn limx] [yn limy] n inf p H.
  simpl. simpl in inf.
  apply (Qplus_lt_l _ _ (- xn (Pos.to_nat n))).
  apply (Qle_lt_trans _ (Qabs (xn (Pos.to_nat p) + - xn (Pos.to_nat n)))).
  apply Qle_Qabs. apply (Qlt_trans _ (1#n)).
  apply limx. apply Pos2Nat.inj_le. assumption. apply le_refl.
  rewrite <- (Qplus_0_r (yn (Pos.to_nat p))).
  rewrite <- (Qplus_opp_r (yn (Pos.to_nat n))).
  rewrite (Qplus_comm (yn (Pos.to_nat n))). rewrite Qplus_assoc.
  rewrite <- Qplus_assoc.
  setoid_replace (1#n)%Q with (-(1#n) + (2#n))%Q. apply Qplus_lt_le_compat.
  apply (Qplus_lt_l _ _ (1#n)). rewrite Qplus_opp_r.
  apply (Qplus_lt_r _ _ (yn (Pos.to_nat n) + - yn (Pos.to_nat p))).
  ring_simplify.
  setoid_replace (yn (Pos.to_nat n) + (-1 # 1) * yn (Pos.to_nat p))
    with (yn (Pos.to_nat n) - yn (Pos.to_nat p)).
  apply (Qle_lt_trans _ (Qabs (yn (Pos.to_nat n) - yn (Pos.to_nat p)))).
  apply Qle_Qabs. apply limy. apply le_refl. apply Pos2Nat.inj_le. assumption.
  field. apply Qle_lteq. left. assumption.
  rewrite Qplus_comm. rewrite Qinv_minus_distr.
  reflexivity.
Qed.

Lemma CRealLt_asym : forall x y : CReal, x < y -> x <= y.
Proof.
  intros x y H [n q].
  apply CRealLt_above in H. destruct H as [p H].
  pose proof (CRealLt_above_same y x n q).
  apply (Qlt_not_le (proj1_sig y (Pos.to_nat (Pos.max n p)))
                    (proj1_sig x (Pos.to_nat (Pos.max n p)))).
  apply H0. apply Pos.le_max_l.
  apply Qlt_le_weak. apply (Qplus_lt_l _ _ (-proj1_sig x (Pos.to_nat (Pos.max n p)))).
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
  remember (yn (Pos.to_nat n) - xn (Pos.to_nat n) - (2 # n)) as eps.
  assert (Qlt 0 eps) as epsPos.
  { subst eps. unfold Qminus. apply (Qlt_minus_iff (2#n)). assumption. }
  assert (forall n p, Pos.to_nat n <= Pos.to_nat (Pos.max n p))%nat.
  { intros. apply Pos2Nat.inj_le. unfold Pos.max. unfold Pos.le.
    destruct (n0 ?= p)%positive eqn:des.
    rewrite des. discriminate. rewrite des. discriminate.
    unfold Pos.compare. rewrite Pos.compare_cont_refl. discriminate. }
  destruct (Qarchimedean (/eps)) as [k kmaj].
  destruct (Qlt_le_dec ((yn (Pos.to_nat n) + xn (Pos.to_nat n)) / (2#1))
                       (zn (Pos.to_nat (Pos.max n (4 * k)))))
    as [decMiddle|decMiddle].
  - left. exists (Pos.max n (4 * k)). unfold proj1_sig. unfold Qminus.
    rewrite <- (Qplus_0_r (zn (Pos.to_nat (Pos.max n (4 * k))))).
    rewrite <- (Qplus_opp_r (xn (Pos.to_nat n))).
    rewrite (Qplus_comm (xn (Pos.to_nat n))). rewrite Qplus_assoc.
    rewrite <- Qplus_assoc. rewrite <- Qplus_0_r.
    rewrite <- (Qplus_opp_r (1#n)). rewrite Qplus_assoc.
    apply Qplus_lt_le_compat.
    + apply (Qplus_lt_l _ _ (- xn (Pos.to_nat n))) in decMiddle.
      apply (Qlt_trans _ ((yn (Pos.to_nat n) + xn (Pos.to_nat n)) / (2 # 1)
                          + - xn (Pos.to_nat n))).
      setoid_replace ((yn (Pos.to_nat n) + xn (Pos.to_nat n)) / (2 # 1)
                      - xn (Pos.to_nat n))
        with ((yn (Pos.to_nat n) - xn (Pos.to_nat n)) / (2 # 1)).
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
    + setoid_replace (xn (Pos.to_nat n) + - xn (Pos.to_nat (Pos.max n (4 * k))))
        with (-(xn (Pos.to_nat (Pos.max n (4 * k))) - xn (Pos.to_nat n))).
      apply Qopp_le_compat.
      apply (Qle_trans _ (Qabs (xn (Pos.to_nat (Pos.max n (4 * k))) - xn (Pos.to_nat n)))).
      apply Qle_Qabs. apply Qle_lteq. left. apply limx. apply H.
      apply le_refl. field.
  - right. exists (Pos.max n (4 * k)). unfold proj1_sig. unfold Qminus.
    rewrite <- (Qplus_0_r (yn (Pos.to_nat (Pos.max n (4 * k))))).
    rewrite <- (Qplus_opp_r (yn (Pos.to_nat n))).
    rewrite (Qplus_comm (yn (Pos.to_nat n))). rewrite Qplus_assoc.
    rewrite <- Qplus_assoc. rewrite <- Qplus_0_l.
    rewrite <- (Qplus_opp_r (1#n)). rewrite (Qplus_comm (1#n)).
    rewrite <- Qplus_assoc. apply Qplus_lt_le_compat.
    + apply (Qplus_lt_r _ _ (yn (Pos.to_nat n) - yn (Pos.to_nat (Pos.max n (4 * k))) + (1#n)))
      ; ring_simplify.
      setoid_replace (-1 * yn (Pos.to_nat (Pos.max n (4 * k))))
        with (- yn (Pos.to_nat (Pos.max n (4 * k)))). 2: ring.
      apply (Qle_lt_trans _ (Qabs (yn (Pos.to_nat n)
                                   - yn (Pos.to_nat (Pos.max n (4 * k)))))).
      apply Qle_Qabs. apply limy. apply le_refl. apply H.
    + apply Qopp_le_compat in decMiddle.
      apply (Qplus_le_r _ _ (yn (Pos.to_nat n))) in decMiddle.
      apply (Qle_trans _ (yn (Pos.to_nat n) + - ((yn (Pos.to_nat n) + xn (Pos.to_nat n)) / (2 # 1)))).
      setoid_replace (yn (Pos.to_nat n) + - ((yn (Pos.to_nat n) + xn (Pos.to_nat n)) / (2 # 1)))
        with ((yn (Pos.to_nat n) - xn (Pos.to_nat n)) / (2 # 1)).
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

Lemma ConstCauchy : forall q : Q,
    QCauchySeq (fun _ => q) Pos.to_nat.
Proof.
  intros. intros k p r H H0.
  unfold Qminus. rewrite Qplus_opp_r. unfold Qlt. simpl.
  unfold Z.lt. auto.
Qed.

Definition inject_Q : Q -> CReal.
Proof.
  intro q. exists (fun n => q). apply ConstCauchy.
Defined.

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
    -> forall p:positive, Qlt (proj1_sig x (Pos.to_nat p)) (q + (1#p)).
Proof.
  intros [xn cau] q maj p. simpl.
  destruct (Qlt_le_dec (xn (Pos.to_nat p)) (q + (1 # p))). assumption.
  exfalso.
  apply CRealLt_above in maj.
  destruct maj as [k maj]; simpl in maj.
  specialize (maj (Pos.max k p) (Pos.le_max_l _ _)).
  specialize (cau p (Pos.to_nat p) (Pos.to_nat (Pos.max k p)) (le_refl _)).
  pose proof (Qplus_lt_le_compat (2#k) (q - xn (Pos.to_nat (Pos.max k p)))
                                 (q + (1 # p)) (xn (Pos.to_nat p)) maj q0).
  rewrite Qplus_comm in H. unfold Qminus in H. rewrite <- Qplus_assoc in H.
  rewrite <- Qplus_assoc in H. apply Qplus_lt_r in H.
  rewrite <- (Qplus_lt_r _ _ (xn (Pos.to_nat p))) in maj.
  apply (Qlt_not_le (1#p) ((1 # p) + (2 # k))).
  rewrite <- (Qplus_0_r (1#p)). rewrite <- Qplus_assoc.
  apply Qplus_lt_r. reflexivity.
  apply Qlt_le_weak.
  apply (Qlt_trans _ (- xn (Pos.to_nat (Pos.max k p)) + xn (Pos.to_nat p)) _ H).
  rewrite Qplus_comm.
  apply (Qle_lt_trans _ (Qabs (xn (Pos.to_nat p) - xn (Pos.to_nat (Pos.max k p))))).
  apply Qle_Qabs. apply cau. apply Pos2Nat.inj_le. apply Pos.le_max_r.
Qed.

Lemma CRealLtQopp : forall (x : CReal) (q : Q),
    CRealLt (inject_Q q) x
    -> forall p:positive, Qlt (q - (1#p)) (proj1_sig x (Pos.to_nat p)).
Proof.
  intros [xn cau] q maj p. simpl.
  destruct (Qlt_le_dec (q - (1 # p)) (xn (Pos.to_nat p))). assumption.
  exfalso.
  apply CRealLt_above in maj.
  destruct maj as [k maj]; simpl in maj.
  specialize (maj (Pos.max k p) (Pos.le_max_l _ _)).
  specialize (cau p (Pos.to_nat (Pos.max k p)) (Pos.to_nat p)).
  pose proof (Qplus_lt_le_compat (2#k) (xn (Pos.to_nat (Pos.max k p)) - q)
                                 (xn (Pos.to_nat p)) (q - (1 # p)) maj q0).
  unfold Qminus in H. rewrite <- Qplus_assoc in H.
  rewrite (Qplus_assoc (-q)) in H. rewrite (Qplus_comm (-q)) in H.
  rewrite Qplus_opp_r in H. rewrite Qplus_0_l in H.
  apply (Qplus_lt_l _ _ (1#p)) in H.
  rewrite <- (Qplus_assoc (xn (Pos.to_nat (Pos.max k p)))) in H.
  rewrite (Qplus_comm (-(1#p))) in H. rewrite Qplus_opp_r in H.
  rewrite Qplus_0_r in H. rewrite Qplus_comm in H.
  rewrite Qplus_assoc in H. apply (Qplus_lt_l _ _ (- xn (Pos.to_nat p))) in H.
  rewrite <- Qplus_assoc in H. rewrite Qplus_opp_r in H. rewrite Qplus_0_r in H.
  apply (Qlt_not_le (1#p) ((1 # p) + (2 # k))).
  rewrite <- (Qplus_0_r (1#p)). rewrite <- Qplus_assoc.
  apply Qplus_lt_r. reflexivity.
  apply Qlt_le_weak.
  apply (Qlt_trans _ (xn (Pos.to_nat (Pos.max k p)) - xn (Pos.to_nat p)) _ H).
  apply (Qle_lt_trans _ (Qabs (xn (Pos.to_nat (Pos.max k p)) - xn (Pos.to_nat p)))).
  apply Qle_Qabs. apply cau. apply Pos2Nat.inj_le.
  apply Pos.le_max_r. apply le_refl.
Qed.

Lemma inject_Q_compare : forall (x : CReal) (p : positive),
    x <= inject_Q (proj1_sig x (Pos.to_nat p) + (1#p)).
Proof.
  intros. intros [n nmaj].
  destruct x as [xn xcau]; simpl in nmaj.
  apply (Qplus_lt_l _ _ (1#p)) in nmaj.
  ring_simplify in nmaj.
  destruct (Pos.max_dec p n).
  - apply Pos.max_l_iff in e.
    apply Pos2Nat.inj_le in e.
    specialize (xcau n (Pos.to_nat n) (Pos.to_nat p) (le_refl _) e).
    apply (Qlt_le_trans _ _ (Qabs (xn (Pos.to_nat n) + -1 * xn (Pos.to_nat p)))) in nmaj.
    2: apply Qle_Qabs.
    apply (Qlt_trans _ _ _ nmaj) in xcau.
    apply (Qplus_lt_l _ _ (-(1#n)-(1#p))) in xcau. ring_simplify in xcau.
    setoid_replace ((2 # n) + -1 * (1 # n)) with (1#n)%Q in xcau.
    discriminate xcau. setoid_replace (-1 * (1 # n)) with (-1#n)%Q. 2: reflexivity.
    rewrite Qinv_plus_distr. reflexivity.
  - apply Pos.max_r_iff, Pos2Nat.inj_le in e.
    specialize (xcau p (Pos.to_nat n) (Pos.to_nat p) e (le_refl _)).
    apply (Qlt_le_trans _ _ (Qabs (xn (Pos.to_nat n) + -1 * xn (Pos.to_nat p)))) in nmaj.
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
  : forall (xn yn zn : nat -> Q) (cvmod : positive -> nat),
    QSeqEquiv xn yn cvmod
    -> QCauchySeq zn Pos.to_nat
    -> QSeqEquiv (fun n:nat => xn n + zn n) (fun n:nat => yn n + zn n)
                (fun p => max (cvmod (2 * p)%positive)
                           (Pos.to_nat (2 * p)%positive)).
Proof.
  intros. intros p n k H1 H2.
  setoid_replace (xn n + zn n - (yn k + zn k))
    with (xn n - yn k + (zn n - zn k)).
  2: field.
  apply (Qle_lt_trans _ (Qabs (xn n - yn k) + Qabs (zn n - zn k))).
  apply Qabs_triangle.
  setoid_replace (1#p)%Q with ((1#2*p) + (1#2*p))%Q.
  apply Qplus_lt_le_compat.
  - apply H. apply (le_trans _ (Init.Nat.max (cvmod (2 * p)%positive) (Pos.to_nat (2 * p)))).
    apply Nat.le_max_l. apply H1.
    apply (le_trans _ (Init.Nat.max (cvmod (2 * p)%positive) (Pos.to_nat (2 * p)))).
    apply Nat.le_max_l. apply H2.
  - apply Qle_lteq. left. apply H0.
    apply (le_trans _ (Init.Nat.max (cvmod (2 * p)%positive) (Pos.to_nat (2 * p)))).
    apply Nat.le_max_r. apply H1.
    apply (le_trans _ (Init.Nat.max (cvmod (2 * p)%positive) (Pos.to_nat (2 * p)))).
    apply Nat.le_max_r. apply H2.
  - rewrite Qinv_plus_distr. unfold Qeq. reflexivity.
Qed.

Definition CReal_plus (x y : CReal) : CReal.
Proof.
  destruct x as [xn limx], y as [yn limy].
  pose proof (CReal_plus_cauchy xn xn yn Pos.to_nat limx limy).
  exists (fun n : nat => xn (2 * n)%nat + yn (2 * n)%nat).
  intros p k n H0 H1. apply H.
  - rewrite max_l. rewrite Pos2Nat.inj_mul.
    apply Nat.mul_le_mono_nonneg. apply le_0_n. apply le_refl.
    apply le_0_n. apply H0. apply le_refl.
  - rewrite Pos2Nat.inj_mul. rewrite max_l.
    apply Nat.mul_le_mono_nonneg. apply le_0_n. apply le_refl.
    apply le_0_n. apply H1. apply le_refl.
Defined.

Infix "+" := CReal_plus : CReal_scope.

Lemma CReal_plus_nth : forall (x y : CReal) (n : nat),
    proj1_sig (x + y) n = Qplus (proj1_sig x (2*n)%nat) (proj1_sig y (2*n)%nat).
Proof.
  intros. destruct x,y; reflexivity.
Qed.

Lemma CReal_plus_unfold : forall (x y : CReal),
    QSeqEquiv (proj1_sig (CReal_plus x y))
              (fun n : nat => proj1_sig x n + proj1_sig y n)%Q
              (fun p => Pos.to_nat (2 * p)).
Proof.
  intros [xn limx] [yn limy].
  unfold CReal_plus; simpl.
  intros p n k H H0.
  setoid_replace (xn (2 * n)%nat + yn (2 * n)%nat - (xn k + yn k))%Q
    with (xn (2 * n)%nat - xn k + (yn (2 * n)%nat - yn k))%Q.
  2: field.
  apply (Qle_lt_trans _ (Qabs (xn (2 * n)%nat - xn k) + Qabs (yn (2 * n)%nat - yn k))).
  apply Qabs_triangle.
  setoid_replace (1#p)%Q with ((1#2*p) + (1#2*p))%Q.
  apply Qplus_lt_le_compat.
  - apply limx. apply (le_trans _ n). apply H.
    rewrite <- (mult_1_l n). rewrite mult_assoc.
    apply Nat.mul_le_mono_nonneg. auto. simpl. auto.
    apply le_0_n. apply le_refl. apply H0.
  - apply Qlt_le_weak. apply limy. apply (le_trans _ n). apply H.
    rewrite <- (mult_1_l n). rewrite mult_assoc.
    apply Nat.mul_le_mono_nonneg. auto. simpl. auto.
    apply le_0_n. apply le_refl. apply H0.
  - rewrite Qinv_plus_distr. unfold Qeq. reflexivity.
Qed.

Definition CReal_opp (x : CReal) : CReal.
Proof.
  destruct x as [xn limx].
  exists (fun n : nat => - xn n).
  intros k p q H H0. unfold Qminus. rewrite Qopp_involutive.
  rewrite Qplus_comm. apply limx; assumption.
Defined.

Notation "- x" := (CReal_opp x) : CReal_scope.

Definition CReal_minus (x y : CReal) : CReal
  := CReal_plus x (CReal_opp y).

Infix "-" := CReal_minus : CReal_scope.

Lemma belowMultiple : forall n p : nat, lt 0 p -> le n (p * n).
Proof.
  intros. rewrite <- (mult_1_l n). apply Nat.mul_le_mono_nonneg.
  auto. assumption. apply le_0_n. rewrite mult_1_l. apply le_refl.
Qed.

Lemma CReal_plus_assoc : forall (x y z : CReal),
    CRealEq (CReal_plus (CReal_plus x y) z)
            (CReal_plus x (CReal_plus y z)).
Proof.
  intros. apply CRealEq_diff. intro n.
  destruct x as [xn limx], y as [yn limy], z as [zn limz].
  unfold CReal_plus; unfold proj1_sig.
  setoid_replace (xn (2 * (2 * Pos.to_nat n))%nat + yn (2 * (2 * Pos.to_nat n))%nat
                  + zn (2 * Pos.to_nat n)%nat
                    - (xn (2 * Pos.to_nat n)%nat + (yn (2 * (2 * Pos.to_nat n))%nat
                                                    + zn (2 * (2 * Pos.to_nat n))%nat)))%Q
    with (xn (2 * (2 * Pos.to_nat n))%nat - xn (2 * Pos.to_nat n)%nat
          + (zn (2 * Pos.to_nat n)%nat - zn (2 * (2 * Pos.to_nat n))%nat))%Q.
  apply (Qle_trans _ (Qabs (xn (2 * (2 * Pos.to_nat n))%nat - xn (2 * Pos.to_nat n)%nat)
                      + Qabs (zn (2 * Pos.to_nat n)%nat - zn (2 * (2 * Pos.to_nat n))%nat))).
  apply Qabs_triangle.
  rewrite <- (Qinv_plus_distr 1 1 n). apply Qplus_le_compat.
  apply Qle_lteq. left. apply limx. rewrite mult_assoc.
  apply belowMultiple. simpl. auto. apply belowMultiple. auto.
  apply Qle_lteq. left. apply limz. apply belowMultiple. auto.
  rewrite mult_assoc. apply belowMultiple. simpl. auto. field.
Qed.

Lemma CReal_plus_comm : forall x y : CReal,
    x + y == y + x.
Proof.
  intros [xn limx] [yn limy]. apply CRealEq_diff. intros.
  unfold CReal_plus, proj1_sig.
  setoid_replace (xn (2 * Pos.to_nat n)%nat + yn (2 * Pos.to_nat n)%nat
                    - (yn (2 * Pos.to_nat n)%nat + xn (2 * Pos.to_nat n)%nat))%Q
    with 0%Q.
  unfold Qle. simpl. unfold Z.le. intro absurd. inversion absurd.
  field.
Qed.

Lemma CReal_plus_0_l : forall r : CReal,
    CRealEq (CReal_plus (inject_Q 0) r) r.
Proof.
  intro r. assert (forall n:nat, le n (2 * n)).
  { intro n. simpl. rewrite <- (plus_0_r n). rewrite <- plus_assoc.
    apply Nat.add_le_mono_l. apply le_0_n. }
  split.
  - intros [n maj]. destruct r as [xn q]; unfold CReal_plus, proj1_sig, inject_Q in maj.
    rewrite Qplus_0_l in maj.
    specialize (q n (Pos.to_nat n) (mult 2 (Pos.to_nat n)) (le_refl _)).
    apply (Qlt_not_le (2#n) (xn (Pos.to_nat n) - xn (2 * Pos.to_nat n)%nat)).
    assumption.
    apply (Qle_trans _ (Qabs (xn (Pos.to_nat n) - xn (2 * Pos.to_nat n)%nat))).
    apply Qle_Qabs. apply (Qle_trans _ (1#n)). apply Qlt_le_weak. apply q.
    apply H. unfold Qle, Z.le; simpl. apply Pos2Nat.inj_le. rewrite Pos2Nat.inj_xO.
    apply H.
  - intros [n maj]. destruct r as [xn q]; unfold CReal_plus, proj1_sig, inject_Q in maj.
    rewrite Qplus_0_l in maj.
    specialize (q n (Pos.to_nat n) (mult 2 (Pos.to_nat n)) (le_refl _)).
    rewrite Qabs_Qminus in q.
    apply (Qlt_not_le (2#n) (xn (mult 2 (Pos.to_nat n)) - xn (Pos.to_nat n))).
    assumption.
    apply (Qle_trans _ (Qabs (xn (mult 2 (Pos.to_nat n)) - xn (Pos.to_nat n)))).
    apply Qle_Qabs. apply (Qle_trans _ (1#n)). apply Qlt_le_weak. apply q.
    apply H. unfold Qle, Z.le; simpl. apply Pos2Nat.inj_le. rewrite Pos2Nat.inj_xO.
    apply H.
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
  exists n. specialize (maj (xO n)).
  rewrite Pos2Nat.inj_xO in maj.
  setoid_replace (proj1_sig (CReal_plus x z) (Pos.to_nat n)
                  - proj1_sig (CReal_plus x y) (Pos.to_nat n))%Q
    with (proj1_sig z (2 * Pos.to_nat n)%nat - proj1_sig y (2 * Pos.to_nat n)%nat)%Q.
  apply maj. apply Pos2Nat.inj_le.
  rewrite <- (plus_0_r (Pos.to_nat n)). rewrite Pos2Nat.inj_xO.
  simpl. apply Nat.add_le_mono_l. apply le_0_n.
  simpl. destruct x as [xn limx], y as [yn limy], z as [zn limz].
  simpl; ring.
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
  setoid_replace (proj1_sig z (Pos.to_nat (2 * n)) - proj1_sig y (Pos.to_nat (2 * n)))%Q
      with (proj1_sig (CReal_plus x z) (Pos.to_nat n) - proj1_sig (CReal_plus x y) (Pos.to_nat n))%Q.
  apply (Qle_lt_trans _ (2#n)). unfold Qle, Z.le; simpl. apply Pos2Nat.inj_le.
  rewrite <- (plus_0_r (Pos.to_nat n~0)). rewrite (Pos2Nat.inj_xO (n~0)).
  simpl. apply Nat.add_le_mono_l. apply le_0_n.
  apply maj. rewrite Pos2Nat.inj_xO.
  destruct x as [xn limx], y as [yn limy], z as [zn limz].
  simpl; ring.
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
  setoid_replace (xn (2 * Pos.to_nat n)%nat + - xn (2 * Pos.to_nat n)%nat - 0)%Q
    with 0%Q.
  unfold Qle. simpl. unfold Z.le. intro absurd. inversion absurd. field.
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
  - intros [n nmaj]. simpl in nmaj.
    ring_simplify in nmaj. discriminate.
  - intros [n nmaj]. simpl in nmaj.
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

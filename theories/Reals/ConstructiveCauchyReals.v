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

Open Scope Q.

(* The constructive Cauchy real numbers, ie the Cauchy sequences
   of rational numbers. This file is not supposed to be imported,
   except in Rdefinitions.v, Raxioms.v, Rcomplete_constr.v
   and ConstructiveRIneq.v.

   Constructive real numbers should be considered abstractly,
   forgetting the fact that they are implemented as rational sequences.
   All useful lemmas of this file are exposed in ConstructiveRIneq.v,
   under more abstract names, like Rlt_asym instead of CRealLt_asym. *)


(* First some limit results about Q *)
Lemma Qarchimedean : forall q : Q, { p : positive | Qlt q (Z.pos p # 1) }.
Proof.
  intros. destruct q. unfold Qlt. simpl.
  rewrite Zmult_1_r. destruct Qnum.
  - exists xH. reflexivity.
  - exists (p+1)%positive. apply (Z.lt_le_trans _ (Z.pos (p+1))).
    apply Z.lt_succ_diag_r. rewrite Pos2Z.inj_mul.
    rewrite <- (Zmult_1_r (Z.pos (p+1))). apply Z.mul_le_mono_nonneg.
    discriminate. rewrite Zmult_1_r. apply Z.le_refl. discriminate.
    apply Z2Nat.inj_le. discriminate. apply Pos2Z.is_nonneg.
    apply Nat.le_succ_l. apply Nat2Z.inj_lt.
    rewrite Z2Nat.id. apply Pos2Z.is_pos. apply Pos2Z.is_nonneg.
  - exists xH. reflexivity.
Qed.

Lemma Qinv_lt_contravar : forall a b : Q,
    Qlt 0 a -> Qlt 0 b -> (Qlt a b <-> Qlt (/b) (/a)).
Proof.
  intros. split.
  - intro. rewrite <- Qmult_1_l. apply Qlt_shift_div_r. apply H0.
    rewrite <- (Qmult_inv_r a). rewrite Qmult_comm.
    apply Qmult_lt_l. apply Qinv_lt_0_compat.  apply H.
    apply H1. intro abs. rewrite abs in H. apply (Qlt_irrefl 0 H).
  - intro. rewrite <- (Qinv_involutive b). rewrite <- (Qmult_1_l (// b)).
    apply Qlt_shift_div_l. apply Qinv_lt_0_compat. apply H0.
    rewrite <- (Qmult_inv_r a). apply Qmult_lt_l. apply H.
    apply H1. intro abs. rewrite abs in H. apply (Qlt_irrefl 0 H).
Qed.

Lemma Qabs_separation : forall q : Q,
    (forall k:positive, Qlt (Qabs q) (1 # k))
    -> q == 0.
Proof.
  intros. destruct (Qle_lt_or_eq 0 (Qabs q)). apply Qabs_nonneg.
  - exfalso. destruct (Qarchimedean (Qinv (Qabs q))) as [p maj].
    specialize (H p). apply (Qlt_not_le (/ Qabs q) (Z.pos p # 1)).
    apply maj. apply Qlt_le_weak.
    setoid_replace (Z.pos p # 1) with (/(1#p)). 2: reflexivity.
    rewrite <- Qinv_lt_contravar. apply H. apply H0.
    reflexivity.
  - destruct q. unfold Qeq in H0. simpl in H0.
    rewrite Zmult_1_r in H0. replace Qnum with 0%Z. reflexivity.
    destruct (Zabs_dec Qnum). rewrite e. rewrite H0. reflexivity.
    rewrite e. rewrite <- H0. ring.
Qed.

Lemma Qle_limit : forall (a b : Q),
    (forall eps:Q, Qlt 0 eps -> Qlt a (b + eps))
    -> Qle a b.
Proof.
  intros. destruct (Q_dec a b). destruct s.
  apply Qlt_le_weak. assumption. exfalso.
  assert (0 < a - b). unfold Qminus. apply (Qlt_minus_iff b a).
  assumption. specialize (H (a-b) H0).
  apply (Qlt_irrefl a). ring_simplify in H. assumption.
  rewrite q. apply Qle_refl.
Qed.

Lemma Qopp_lt_compat : forall p q, p<q -> -q < -p.
Proof.
  intros (a1,a2) (b1,b2); unfold Qlt; simpl.
  rewrite !Z.mul_opp_l. omega.
Qed.

Lemma Qmult_minus_one : forall q : Q, inject_Z (-1) * q == - q.
Proof.
  intros. field.
Qed.

Lemma Qsub_comm : forall a b : Q, - a + b == b - a.
Proof.
  intros. unfold Qeq. simpl. rewrite Pos.mul_comm. ring.
Qed.

Lemma PosLt_le_total : forall p q, Pos.lt p q \/ Pos.le q p.
Proof.
  intros. destruct (Pos.lt_total p q). left. assumption.
  right. destruct H. subst q. apply Pos.le_refl. unfold Pos.lt in H.
  unfold Pos.le. rewrite H. discriminate.
Qed.




(*
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

Declare Scope R_scope_constr.

(* Declare Scope R_scope with Key R *)
Delimit Scope R_scope_constr with CReal.

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope R_scope_constr with CReal.

Open Scope R_scope_constr.




(* The equality on Cauchy reals is just QSeqEquiv,
   which is independant of the convergence modulus. *)
Lemma CRealEq_modindep : forall (x y : CReal),
    QSeqEquivEx (proj1_sig x) (proj1_sig y)
    <-> forall n:positive, Qle (Qabs (proj1_sig x (Pos.to_nat n) - proj1_sig y (Pos.to_nat n)))
                        (2 # n).
Proof.
  intros [xn limx] [yn limy]. unfold proj1_sig. split.
  - intros [cvmod H] n. unfold proj1_sig in H.
    apply Qle_limit. intros.
    destruct (Qarchimedean (/eps)) as [k maj].
    remember (max (cvmod k) (Pos.to_nat n)) as p.
    assert (le (cvmod k) p).
    { rewrite Heqp. apply Nat.le_max_l. }
    assert (Pos.to_nat n <= p)%nat.
    { rewrite Heqp. apply Nat.le_max_r. }
    specialize (H k p p H1 H1).
    setoid_replace (xn (Pos.to_nat n) - yn (Pos.to_nat n))
      with (xn (Pos.to_nat n) - xn p + (xn p - yn p + (yn p - yn (Pos.to_nat n)))).
    apply (Qle_lt_trans _ (Qabs (xn (Pos.to_nat n) - xn p)
                           + Qabs (xn p - yn p + (yn p - yn (Pos.to_nat n))))).
    apply Qabs_triangle.
    setoid_replace (2 # n) with ((1 # n) + (1#n)). rewrite <- Qplus_assoc.
    apply Qplus_lt_le_compat.
    apply limx. apply le_refl. assumption.
    apply (Qle_trans _ (Qabs (xn p - yn p) + Qabs (yn p - yn (Pos.to_nat n)))).
    apply Qabs_triangle. rewrite (Qplus_comm (1#n)). apply Qplus_le_compat.
    apply Qle_lteq. left. apply (Qlt_trans _ (1 # k)).
    assumption.
    setoid_replace (Z.pos k #1) with (/ (1#k)) in maj. 2: reflexivity.
    apply Qinv_lt_contravar. reflexivity. apply H0. apply maj.
    apply Qle_lteq. left.
    apply limy. assumption. apply le_refl.
    ring_simplify. reflexivity. field.
  - intros. exists (fun q => Pos.to_nat (2 * (3 * q))). intros k p q H0 H1.
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
    setoid_replace (1 # k) with ((1 # 3 * k) + ((1 # 3 * k) + (1 # 3 * k))).
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
    setoid_replace (1 # 3 * k) with (2 # 2 * (3 * k)). apply H.
    rewrite (factorDenom _ _ 3). rewrite (factorDenom _ _ 2). rewrite (factorDenom _ _ 3).
    rewrite Qmult_assoc. rewrite (Qmult_comm (1#2)).
    rewrite <- Qmult_assoc. apply Qmult_comp. reflexivity.
    unfold Qeq. reflexivity.
    apply Qle_lteq. left. apply limy. assumption.
    apply (le_trans _ (Pos.to_nat (2 * (3 * k)))). assumption. assumption.
    rewrite (factorDenom _ _ 3). ring_simplify. reflexivity. field.
Qed.


(* So QSeqEquiv is the equivalence relation of this constructive pre-order *)
Definition CRealLt (x y : CReal) : Prop
  := exists n : positive, Qlt (2 # n)
                         (proj1_sig y (Pos.to_nat n) - proj1_sig x (Pos.to_nat n)).

Definition CRealGt (x y : CReal) := CRealLt y x.
Definition CReal_appart (x y : CReal) := CRealLt x y \/ CRealLt y x.

Infix "<" := CRealLt : R_scope_constr.
Infix ">" := CRealGt : R_scope_constr.
Infix "#" := CReal_appart : R_scope_constr.

(* This Prop can be extracted as a sigma type *)
Lemma CRealLtEpsilon : forall x y : CReal,
    x < y
    -> { n : positive | Qlt (2 # n)
                           (proj1_sig y (Pos.to_nat n) - proj1_sig x (Pos.to_nat n)) }.
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

(* Alias the quotient order equality *)
Definition CRealEq (x y : CReal) : Prop
  := ~CRealLt x y /\ ~CRealLt y x.

Infix "==" := CRealEq : R_scope_constr.

(* Alias the large order *)
Definition CRealLe (x y : CReal) : Prop
  := ~CRealLt y x.

Definition CRealGe (x y : CReal) := CRealLe y x.

Infix "<=" := CRealLe : R_scope_constr.
Infix ">=" := CRealGe : R_scope_constr.

Notation "x <= y <= z" := (x <= y /\ y <= z) : R_scope_constr.
Notation "x <= y < z"  := (x <= y /\ y <  z) : R_scope_constr.
Notation "x < y < z"   := (x <  y /\ y <  z) : R_scope_constr.
Notation "x < y <= z"  := (x <  y /\ y <= z) : R_scope_constr.

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
    -> exists k : positive, forall p:positive,
          Pos.le k p -> Qlt (2 # k) (proj1_sig y (Pos.to_nat p) - proj1_sig x (Pos.to_nat p)).
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
  destruct (PosLt_le_total n p).
  - apply (Qlt_not_le (proj1_sig y (Pos.to_nat p)) (proj1_sig x (Pos.to_nat p))).
    apply H0. unfold Pos.le. unfold Pos.lt in H1. rewrite H1. discriminate.
    apply Qlt_le_weak. apply (Qplus_lt_l _ _ (-proj1_sig x (Pos.to_nat p))).
    rewrite Qplus_opp_r. apply (Qlt_trans _ (2#p)).
    unfold Qlt. simpl. unfold Z.lt. auto. apply H. apply Pos.le_refl.
  - apply (Qlt_not_le (proj1_sig y (Pos.to_nat n)) (proj1_sig x (Pos.to_nat n))).
    apply H0. apply Pos.le_refl. apply Qlt_le_weak.
    apply (Qplus_lt_l _ _ (-proj1_sig x (Pos.to_nat n))).
    rewrite Qplus_opp_r. apply (Qlt_trans _ (2#p)).
    unfold Qlt. simpl. unfold Z.lt. auto. apply H. assumption.
Qed.

Lemma CRealLt_irrefl : forall x:CReal, ~(x < x).
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
    CRealLt x y -> { CRealLt x z } + { CRealLt z y }.
Proof.
  intros [xn limx] [yn limy] [zn limz] clt.
  destruct (CRealLtEpsilon _ _ clt) as [n inf].
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
    + apply (Qplus_lt_l _ _ (1#n)). rewrite Qplus_opp_r.
      apply (Qplus_lt_r _ _ (yn (Pos.to_nat n) - yn (Pos.to_nat (Pos.max n (4 * k))))).
      ring_simplify. rewrite Qmult_minus_one.
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
Qed.

Definition linear_order_T x y z := CRealLt_dec x z y.

Lemma CRealLe_Lt_trans : forall x y z : CReal,
    x <= y -> y < z -> x < z.
Proof.
  intros.
  destruct (linear_order_T y x z H0). contradiction. apply c.
Qed.

Lemma CRealLt_Le_trans : forall x y z : CReal,
    CRealLt x y
    -> CRealLe y z -> CRealLt x z.
Proof.
  intros.
  destruct (linear_order_T x z y H). apply c. contradiction.
Qed.

Lemma CRealLt_trans : forall x y z : CReal,
    x < y -> y < z -> x < z.
Proof.
  intros. apply (CRealLt_Le_trans _ y _ H).
  apply CRealLt_asym. exact H0.
Qed.

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

Add Parametric Morphism : CRealLt
    with signature CRealEq ==> CRealEq ==> iff
      as CRealLt_morph.
Proof.
  intros. destruct H, H0. split.
  - intro. destruct (CRealLt_dec x x0 y). assumption.
    contradiction. destruct (CRealLt_dec y x0 y0).
    assumption. assumption. contradiction.
  - intro. destruct (CRealLt_dec y y0 x). assumption.
    contradiction. destruct (CRealLt_dec x y0 x0).
    assumption. assumption. contradiction.
Qed.

Add Parametric Morphism : CRealGt
    with signature CRealEq ==> CRealEq ==> iff
      as CRealGt_morph.
Proof.
  intros. unfold CRealGt. apply CRealLt_morph; assumption.
Qed.

Add Parametric Morphism : CReal_appart
    with signature CRealEq ==> CRealEq ==> iff
      as CReal_appart_morph.
Proof.
  split.
  - intros. destruct H1. left. rewrite <- H0, <- H. exact H1.
    right. rewrite <- H0, <- H. exact H1.
  - intros. destruct H1. left. rewrite H0, H. exact H1.
    right. rewrite H0, H. exact H1.
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

Notation "0" := (inject_Q 0) : R_scope_constr.
Notation "1" := (inject_Q 1) : R_scope_constr.

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

Infix "+" := CReal_plus : R_scope_constr.

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
  rewrite Qsub_comm. apply limx; assumption.
Defined.

Notation "- x" := (CReal_opp x) : R_scope_constr.

Definition CReal_minus (x y : CReal) : CReal
  := CReal_plus x (CReal_opp y).

Infix "-" := CReal_minus : R_scope_constr.

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

Lemma CReal_plus_lt_compat_l :
  forall x y z : CReal,
    CRealLt y z
    -> CRealLt (CReal_plus x y) (CReal_plus x z).
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

Lemma CReal_plus_lt_reg_l :
  forall x y z : CReal,
    CRealLt (CReal_plus x y) (CReal_plus x z)
    -> CRealLt y z.
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

Lemma CReal_plus_opp_r : forall x : CReal,
    x + - x == 0.
Proof.
  intros [xn limx]. apply CRealEq_diff. intros.
  unfold CReal_plus, CReal_opp, inject_Q, proj1_sig.
  setoid_replace (xn (2 * Pos.to_nat n)%nat + - xn (2 * Pos.to_nat n)%nat - 0)%Q
    with 0%Q.
  unfold Qle. simpl. unfold Z.le. intro absurd. inversion absurd. field.
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

Lemma CReal_plus_eq_reg_l : forall (r r1 r2 : CReal),
    CRealEq (CReal_plus r r1) (CReal_plus r r2)
    -> CRealEq r1 r2.
Proof.
  intros. destruct H. split.
  - intro abs. apply (CReal_plus_lt_compat_l r) in abs. contradiction.
  - intro abs. apply (CReal_plus_lt_compat_l r) in abs. contradiction.
Qed.

Fixpoint BoundFromZero (qn : nat -> Q) (k : nat) (A : positive) {struct k}
  : (forall n:nat, le k n -> Qlt (Qabs (qn n)) (Z.pos A # 1))
    -> { B : positive | forall n:nat, Qlt (Qabs (qn n)) (Z.pos B # 1) }.
Proof.
  intro H. destruct k.
  - exists A. intros. apply H. apply le_0_n.
  - destruct (Qarchimedean (Qabs (qn k))) as [a maj].
    apply (BoundFromZero qn k (Pos.max A a)).
    intros n H0. destruct (Nat.le_gt_cases n k).
    + pose proof (Nat.le_antisymm n k H1 H0). subst k.
      apply (Qlt_le_trans _ (Z.pos a # 1)). apply maj.
      unfold Qle; simpl. rewrite Pos.mul_1_r. rewrite Pos.mul_1_r.
      apply Pos.le_max_r.
    + apply (Qlt_le_trans _ (Z.pos A # 1)). apply H.
      apply H1. unfold Qle; simpl. rewrite Pos.mul_1_r. rewrite Pos.mul_1_r.
      apply Pos.le_max_l.
Qed.

Lemma QCauchySeq_bounded (qn : nat -> Q) (cvmod : positive -> nat)
  : QCauchySeq qn cvmod
    -> { A : positive | forall n:nat, Qlt (Qabs (qn n)) (Z.pos A # 1) }.
Proof.
  intros. remember (Zplus (Qnum (Qabs (qn (cvmod xH)))) 1) as z.
  assert (Z.lt 0 z) as zPos.
  { subst z. assert (Qle 0 (Qabs (qn (cvmod 1%positive)))).
    apply Qabs_nonneg. destruct (Qabs (qn (cvmod 1%positive))). simpl.
    unfold Qle in H0. simpl in H0. rewrite Zmult_1_r in H0.
    apply (Z.lt_le_trans 0 1). unfold Z.lt. auto.
    rewrite <- (Zplus_0_l 1). rewrite Zplus_assoc. apply Zplus_le_compat_r.
    rewrite Zplus_0_r. assumption. }
  assert { A : positive | forall n:nat,
          le (cvmod xH) n -> Qlt ((Qabs (qn n)) * (1#A)) 1 }.
  destruct z eqn:des.
  - exfalso. apply (Z.lt_irrefl 0). assumption.
  - exists p. intros. specialize (H xH (cvmod xH) n (le_refl _) H0).
    assert (Qlt (Qabs (qn n)) (Qabs (qn (cvmod 1%positive)) + 1)).
    { apply (Qplus_lt_l _ _ (-Qabs (qn (cvmod 1%positive)))).
      rewrite <- (Qplus_comm 1). rewrite <- Qplus_assoc. rewrite Qplus_opp_r.
      rewrite Qplus_0_r. apply (Qle_lt_trans _ (Qabs (qn n - qn (cvmod 1%positive)))).
      apply Qabs_triangle_reverse. rewrite Qabs_Qminus. assumption. }
    apply (Qlt_le_trans _ ((Qabs (qn (cvmod 1%positive)) + 1) * (1#p))).
    apply Qmult_lt_r. unfold Qlt. simpl. unfold Z.lt. auto. assumption.
    unfold Qle. simpl. rewrite Zmult_1_r. rewrite Zmult_1_r. rewrite Zmult_1_r.
    rewrite Pos.mul_1_r. rewrite Pos2Z.inj_mul. rewrite Heqz.
    destruct (Qabs (qn (cvmod 1%positive))) eqn:desAbs.
    rewrite Z.mul_add_distr_l. rewrite Zmult_1_r.
    apply Zplus_le_compat_r. rewrite <- (Zmult_1_l (QArith_base.Qnum (Qnum # Qden))).
    rewrite Zmult_assoc. apply Zmult_le_compat_r. rewrite Zmult_1_r.
    simpl. unfold Z.le. rewrite <- Pos2Z.inj_compare.
    unfold Pos.compare. destruct Qden; discriminate.
    simpl. assert (Qle 0 (Qnum # Qden)). rewrite <- desAbs.
    apply Qabs_nonneg. unfold Qle in H2. simpl in H2. rewrite Zmult_1_r in H2.
    assumption.
  - exfalso. inversion zPos.
  - destruct H0. apply (BoundFromZero _ (cvmod xH) x). intros n H0.
    specialize (q n H0). setoid_replace (Z.pos x # 1)%Q with (/(1#x))%Q.
    rewrite <- (Qmult_1_l (/(1#x))). apply Qlt_shift_div_l.
    reflexivity. apply q. reflexivity.
Qed.

Lemma CReal_mult_cauchy
  : forall (xn yn zn : nat -> Q) (Ay Az : positive) (cvmod : positive -> nat),
    QSeqEquiv xn yn cvmod
    -> QCauchySeq zn Pos.to_nat
    -> (forall n:nat, Qlt (Qabs (yn n)) (Z.pos Ay # 1))
    -> (forall n:nat, Qlt (Qabs (zn n)) (Z.pos Az # 1))
    -> QSeqEquiv (fun n:nat => xn n * zn n) (fun n:nat => yn n * zn n)
                (fun p => max (cvmod (2 * (Pos.max Ay Az) * p)%positive)
                           (Pos.to_nat (2 * (Pos.max Ay Az) * p)%positive)).
Proof.
  intros xn yn zn Ay Az cvmod limx limz majy majz.
  remember (Pos.mul 2 (Pos.max Ay Az)) as z.
  intros k p q H H0.
  assert (Pos.to_nat k <> O) as kPos.
  { intro absurd. pose proof (Pos2Nat.is_pos k).
    rewrite absurd in H1. inversion H1. }
  setoid_replace (xn p * zn p - yn q * zn q)%Q
    with ((xn p - yn q) * zn p + yn q * (zn p - zn q))%Q.
  2: ring.
  apply (Qle_lt_trans _ (Qabs ((xn p - yn q) * zn p)
                         + Qabs (yn q * (zn p - zn q)))).
  apply Qabs_triangle. rewrite Qabs_Qmult. rewrite Qabs_Qmult.
  setoid_replace (1#k)%Q with ((1#2*k) + (1#2*k))%Q.
  apply Qplus_lt_le_compat.
  - apply (Qle_lt_trans _ ((1#z * k) * Qabs (zn p)%nat)).
    + apply Qmult_le_compat_r. apply Qle_lteq. left. apply limx.
      apply (le_trans _ (Init.Nat.max (cvmod (z * k)%positive) (Pos.to_nat (z * k)))).
      apply Nat.le_max_l. assumption.
      apply (le_trans _ (Init.Nat.max (cvmod (z * k)%positive) (Pos.to_nat (z * k)))).
      apply Nat.le_max_l. assumption. apply Qabs_nonneg.
    + subst z. rewrite <- (Qmult_1_r (1 # 2 * k)).
      rewrite <- Pos.mul_assoc. rewrite <- (Pos.mul_comm k). rewrite Pos.mul_assoc.
      rewrite (factorDenom _ _ (2 * k)). rewrite <- Qmult_assoc.
      apply Qmult_lt_l. unfold Qlt. simpl. unfold Z.lt. auto.
      apply (Qle_lt_trans _ (Qabs (zn p)%nat * (1 # Az))).
      rewrite <- (Qmult_comm (1 # Az)). apply Qmult_le_compat_r.
      unfold Qle. simpl. rewrite Pos2Z.inj_max. apply Z.le_max_r.
      apply Qabs_nonneg. rewrite <- (Qmult_inv_r (1#Az)).
      rewrite Qmult_comm. apply Qmult_lt_l. reflexivity.
      setoid_replace (/(1#Az))%Q with (Z.pos Az # 1)%Q. apply majz.
      reflexivity. intro abs. inversion abs.
  - apply (Qle_trans _ ((1 # z * k) * Qabs (yn q)%nat)).
    + rewrite Qmult_comm. apply Qmult_le_compat_r. apply Qle_lteq.
      left. apply limz.
      apply (le_trans _ (max (cvmod (z * k)%positive)
                             (Pos.to_nat (z * k)%positive))).
      apply Nat.le_max_r. assumption.
      apply (le_trans _ (max (cvmod (z * k)%positive)
                             (Pos.to_nat (z * k)%positive))).
      apply Nat.le_max_r. assumption. apply Qabs_nonneg.
    + subst z. rewrite <- (Qmult_1_r (1 # 2 * k)).
      rewrite <- Pos.mul_assoc. rewrite <- (Pos.mul_comm k). rewrite Pos.mul_assoc.
      rewrite (factorDenom _ _ (2 * k)). rewrite <- Qmult_assoc.
      apply Qle_lteq. left.
      apply Qmult_lt_l. unfold Qlt. simpl. unfold Z.lt. auto.
      apply (Qle_lt_trans _ (Qabs (yn q)%nat * (1 # Ay))).
      rewrite <- (Qmult_comm (1 # Ay)). apply Qmult_le_compat_r.
      unfold Qle. simpl. rewrite Pos2Z.inj_max. apply Z.le_max_l.
      apply Qabs_nonneg. rewrite <- (Qmult_inv_r (1#Ay)).
      rewrite Qmult_comm. apply Qmult_lt_l. reflexivity.
      setoid_replace (/(1#Ay))%Q with (Z.pos Ay # 1)%Q. apply majy.
      reflexivity. intro abs. inversion abs.
  - rewrite Qinv_plus_distr. unfold Qeq. reflexivity.
Qed.

Lemma linear_max : forall (p Ax Ay : positive) (i : nat),
  le (Pos.to_nat p) i
  -> (Init.Nat.max (Pos.to_nat (2 * Pos.max Ax Ay * p))
                 (Pos.to_nat (2 * Pos.max Ax Ay * p)) <= Pos.to_nat (2 * Pos.max Ax Ay) * i)%nat.
Proof.
  intros. rewrite max_l. 2: apply le_refl.
  rewrite Pos2Nat.inj_mul. apply Nat.mul_le_mono_nonneg.
  apply le_0_n. apply le_refl. apply le_0_n. apply H.
Qed.

Definition CReal_mult (x y : CReal) : CReal.
Proof.
  destruct x as [xn limx]. destruct y as [yn limy].
  destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
  destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
  pose proof (CReal_mult_cauchy xn xn yn Ax Ay Pos.to_nat limx limy majx majy).
  exists (fun n : nat => xn (Pos.to_nat (2 * Pos.max Ax Ay)* n)%nat
               * yn (Pos.to_nat (2 * Pos.max Ax Ay) * n)%nat).
  intros p n k H0 H1.
  apply H; apply linear_max; assumption.
Defined.

Infix "*" := CReal_mult : R_scope_constr.

Lemma CReal_mult_unfold : forall x y : CReal,
    QSeqEquivEx (proj1_sig (CReal_mult x y))
                (fun n : nat => proj1_sig x n * proj1_sig y n)%Q.
Proof.
  intros [xn limx] [yn limy]. unfold CReal_mult ; simpl.
  destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
  destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
  simpl.
  pose proof (CReal_mult_cauchy xn xn yn Ax Ay Pos.to_nat limx limy majx majy).
  exists (fun p : positive =>
         Init.Nat.max (Pos.to_nat (2 * Pos.max Ax Ay * p))
           (Pos.to_nat (2 * Pos.max Ax Ay * p))).
  intros p n k H0 H1. rewrite max_l in H0, H1.
  2: apply le_refl. 2: apply le_refl.
  apply H. apply linear_max.
  apply (le_trans _ (Pos.to_nat (2 * Pos.max Ax Ay * p))).
  rewrite <- (mult_1_l (Pos.to_nat p)). rewrite Pos2Nat.inj_mul.
  apply Nat.mul_le_mono_nonneg. auto. apply Pos2Nat.is_pos.
  apply le_0_n. apply le_refl. apply H0. rewrite max_l.
  apply H1. apply le_refl.
Qed.

Lemma CReal_mult_assoc_bounded_r : forall (xn yn zn : nat -> Q),
    QSeqEquivEx xn yn (* both are Cauchy with same limit *)
    -> QSeqEquiv zn zn Pos.to_nat
    -> QSeqEquivEx (fun n => xn n * zn n)%Q (fun n => yn n * zn n)%Q.
Proof.
  intros. destruct H as [cvmod cveq].
  destruct (QCauchySeq_bounded yn (fun k => cvmod (2 * k)%positive)
                               (QSeqEquiv_cau_r xn yn cvmod cveq))
    as [Ay majy].
  destruct (QCauchySeq_bounded zn Pos.to_nat H0) as [Az majz].
  exists (fun p => max (cvmod (2 * (Pos.max Ay Az) * p)%positive)
               (Pos.to_nat (2 * (Pos.max Ay Az) * p)%positive)).
  apply CReal_mult_cauchy; assumption.
Qed.

Lemma CReal_mult_assoc : forall x y z : CReal,
    CRealEq (CReal_mult (CReal_mult x y) z)
            (CReal_mult x (CReal_mult y z)).
Proof.
  intros. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig y n * proj1_sig z n)%Q).
  - apply (QSeqEquivEx_trans _ (fun n => proj1_sig (CReal_mult x y) n * proj1_sig z n)%Q).
    apply CReal_mult_unfold.
    destruct x as [xn limx], y as [yn limy], z as [zn limz]; unfold CReal_mult; simpl.
    destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
    destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
    destruct (QCauchySeq_bounded zn Pos.to_nat limz) as [Az majz].
    apply CReal_mult_assoc_bounded_r. 2: apply limz.
    simpl.
    pose proof (CReal_mult_cauchy xn xn yn Ax Ay Pos.to_nat limx limy majx majy).
    exists (fun p : positive =>
         Init.Nat.max (Pos.to_nat (2 * Pos.max Ax Ay * p))
                      (Pos.to_nat (2 * Pos.max Ax Ay * p))).
    intros p n k H0 H1. rewrite max_l in H0, H1.
    2: apply le_refl. 2: apply le_refl.
    apply H. apply linear_max.
    apply (le_trans _ (Pos.to_nat (2 * Pos.max Ax Ay * p))).
    rewrite <- (mult_1_l (Pos.to_nat p)). rewrite Pos2Nat.inj_mul.
    apply Nat.mul_le_mono_nonneg. auto. apply Pos2Nat.is_pos.
    apply le_0_n. apply le_refl. apply H0. rewrite max_l.
    apply H1. apply le_refl.
  - apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig (CReal_mult y z) n)%Q).
    2: apply QSeqEquivEx_sym; apply CReal_mult_unfold.
    destruct x as [xn limx], y as [yn limy], z as [zn limz]; unfold CReal_mult; simpl.
    destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
    destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
    destruct (QCauchySeq_bounded zn Pos.to_nat limz) as [Az majz].
    simpl.
    pose proof (CReal_mult_assoc_bounded_r (fun n0 : nat => yn n0 * zn n0)%Q (fun n : nat =>
          yn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat
          * zn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat)%Q xn)
      as [cvmod cveq].

    pose proof (CReal_mult_cauchy yn yn zn Ay Az Pos.to_nat limy limz majy majz).
    exists (fun p : positive =>
         Init.Nat.max (Pos.to_nat (2 * Pos.max Ay Az * p))
                      (Pos.to_nat (2 * Pos.max Ay Az * p))).
    intros p n k H0 H1. rewrite max_l in H0, H1.
    2: apply le_refl. 2: apply le_refl.
    apply H. rewrite max_l. apply H0. apply le_refl.
    apply linear_max.
    apply (le_trans _ (Pos.to_nat (2 * Pos.max Ay Az * p))).
    rewrite <- (mult_1_l (Pos.to_nat p)). rewrite Pos2Nat.inj_mul.
    apply Nat.mul_le_mono_nonneg. auto. apply Pos2Nat.is_pos.
    apply le_0_n. apply le_refl. apply H1.
    apply limx.
    exists cvmod. intros p k n H1 H2. specialize (cveq p k n H1 H2).
    setoid_replace (xn k * yn k * zn k -
     xn n *
     (yn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat *
      zn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat))%Q
      with ((fun n : nat => yn n * zn n * xn n) k -
            (fun n : nat =>
             yn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat *
             zn (Pos.to_nat (Pos.max Ay Az)~0 * n)%nat *
             xn n) n)%Q.
    apply cveq. ring.
Qed.

Lemma CReal_mult_comm : forall x y : CReal,
    CRealEq (CReal_mult x y) (CReal_mult y x).
Proof.
  intros. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig y n * proj1_sig x n)%Q).
  destruct x as [xn limx], y as [yn limy]; simpl.
  2: apply QSeqEquivEx_sym; apply CReal_mult_unfold.
  destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
  destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy]; simpl.
  apply QSeqEquivEx_sym.

  pose proof (CReal_mult_cauchy yn yn xn Ay Ax Pos.to_nat limy limx majy majx).
  exists (fun p : positive =>
       Init.Nat.max (Pos.to_nat (2 * Pos.max Ay Ax * p))
                    (Pos.to_nat (2 * Pos.max Ay Ax * p))).
  intros p n k H0 H1. rewrite max_l in H0, H1.
  2: apply le_refl. 2: apply le_refl.
  rewrite (Qmult_comm (xn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat)).
  apply (H p n). rewrite max_l. apply H0. apply le_refl.
  rewrite max_l. apply (le_trans _ k). apply H1.
  rewrite <- (mult_1_l k). rewrite mult_assoc.
  apply Nat.mul_le_mono_nonneg. auto. rewrite mult_1_r.
  apply Pos2Nat.is_pos. apply le_0_n. apply le_refl.
  apply le_refl.
Qed.

(* Axiom Rmult_eq_compat_l *)
Lemma CReal_mult_proper_l : forall x y z : CReal,
    CRealEq y z -> CRealEq (CReal_mult x y) (CReal_mult x z).
Proof.
  intros. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig y n)%Q).
  apply CReal_mult_unfold.
  rewrite CRealEq_diff in H. rewrite <- CRealEq_modindep in H.
  apply QSeqEquivEx_sym.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n * proj1_sig z n)%Q).
  apply CReal_mult_unfold.
  destruct x as [xn limx], y as [yn limy], z as [zn limz]; simpl.
  destruct H. simpl in H.
  destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
  destruct (QCauchySeq_bounded zn Pos.to_nat limz) as [Az majz].
  pose proof (CReal_mult_cauchy yn zn xn Az Ax x H limx majz majx).
  apply QSeqEquivEx_sym.
  exists (fun p : positive =>
       Init.Nat.max (x (2 * Pos.max Az Ax * p)%positive)
                    (Pos.to_nat (2 * Pos.max Az Ax * p))).
  intros p n k H1 H2. specialize (H0 p n k H1 H2).
  setoid_replace (xn n * yn n - xn k * zn k)%Q
    with (yn n * xn n - zn k * xn k)%Q.
  apply H0. ring.
Qed.

Lemma CReal_mult_lt_0_compat : forall x y : CReal,
    CRealLt (inject_Q 0) x
    -> CRealLt (inject_Q 0) y
    -> CRealLt (inject_Q 0) (CReal_mult x y).
Proof.
  intros. destruct H, H0.
  pose proof (CRealLt_aboveSig (inject_Q 0) x x0 H).
  pose proof (CRealLt_aboveSig (inject_Q 0) y x1 H0).
  destruct x as [xn limx], y as [yn limy].
  simpl in H, H1, H2. simpl.
  destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
  destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
  destruct (Qarchimedean (/ (xn (Pos.to_nat x0) - 0 - (2 # x0)))).
  destruct (Qarchimedean (/ (yn (Pos.to_nat x1) - 0 - (2 # x1)))).
  exists (Pos.max x0 x~0 * Pos.max x1 x2~0)%positive.
  simpl. unfold Qminus. rewrite Qplus_0_r.
  rewrite <- Pos2Nat.inj_mul.
  unfold Qminus in H1, H2.
  specialize (H1 ((Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0))%positive).
  assert (Pos.max x1 x2~0 <= (Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0))%positive.
  { apply Pos2Nat.inj_le.
    rewrite Pos.mul_assoc. rewrite Pos2Nat.inj_mul.
    rewrite <- (mult_1_l (Pos.to_nat (Pos.max x1 x2~0))).
    rewrite mult_assoc. apply Nat.mul_le_mono_nonneg. auto.
    rewrite mult_1_r. apply Pos2Nat.is_pos. apply le_0_n.
    apply le_refl. }
  specialize (H2 ((Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0))%positive H3).
  rewrite Qplus_0_r in H1, H2.
  apply (Qlt_trans _ ((2 # Pos.max x0 x~0) * (2 # Pos.max x1 x2~0))).
  unfold Qlt; simpl. assert (forall p : positive, (Z.pos p < Z.pos p~0)%Z).
  intro p. rewrite <- (Z.mul_1_l (Z.pos p)).
  replace (Z.pos p~0) with (2 * Z.pos p)%Z. apply Z.mul_lt_mono_pos_r.
  apply Pos2Z.is_pos. reflexivity. reflexivity.
  apply H4.
  apply (Qlt_trans _ ((2 # Pos.max x0 x~0) * (yn (Pos.to_nat ((Pos.max Ax Ay)~0 * (Pos.max x0 x~0 * Pos.max x1 x2~0)))))).
  apply Qmult_lt_l. reflexivity. apply H2. apply Qmult_lt_r.
  apply (Qlt_trans 0 (2 # Pos.max x1 x2~0)). reflexivity. apply H2.
  apply H1. rewrite Pos.mul_comm. apply Pos2Nat.inj_le.
  rewrite <- Pos.mul_assoc. rewrite Pos2Nat.inj_mul.
  rewrite <- (mult_1_r (Pos.to_nat (Pos.max x0 x~0))).
  rewrite <- mult_assoc. apply Nat.mul_le_mono_nonneg.
  apply le_0_n. apply le_refl. auto.
  rewrite mult_1_l. apply Pos2Nat.is_pos.
Qed.

Lemma CReal_mult_plus_distr_l : forall r1 r2 r3 : CReal,
    CRealEq (CReal_mult r1 (CReal_plus r2 r3))
            (CReal_plus (CReal_mult r1 r2) (CReal_mult r1 r3)).
Proof.
  intros x y z. apply CRealEq_diff. apply CRealEq_modindep.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n
                                    * (proj1_sig (CReal_plus y z) n))%Q).
  apply CReal_mult_unfold.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig (CReal_mult x y) n
                                    + proj1_sig (CReal_mult x z) n))%Q.
  2: apply QSeqEquivEx_sym; exists (fun p => Pos.to_nat (2 * p))
  ; apply CReal_plus_unfold.
  apply (QSeqEquivEx_trans _ (fun n => proj1_sig x n
                                    * (proj1_sig y n + proj1_sig z n))%Q).
  - pose proof (CReal_plus_unfold y z).
    destruct x as [xn limx], y as [yn limy], z as [zn limz]; simpl; simpl in H.
    destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
    destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
    destruct (QCauchySeq_bounded zn Pos.to_nat limz) as [Az majz].
    pose proof (CReal_mult_cauchy (fun n => yn (n + (n + 0))%nat + zn (n + (n + 0))%nat)%Q
                                  (fun n => yn n + zn n)%Q
                                  xn (Ay + Az) Ax
                                  (fun p => Pos.to_nat (2 * p)) H limx).
    exists (fun p : positive => (Pos.to_nat (2 * (2 * Pos.max (Ay + Az) Ax * p)))).
    intros p n k H1 H2.
    setoid_replace (xn n * (yn (n + (n + 0))%nat + zn (n + (n + 0))%nat) - xn k * (yn k + zn k))%Q
      with ((yn (n + (n + 0))%nat + zn (n + (n + 0))%nat) * xn n - (yn k + zn k) * xn k)%Q.
    2: ring.
    assert (Pos.to_nat (2 * Pos.max (Ay + Az) Ax * p) <=
            Pos.to_nat 2 * Pos.to_nat (2 * Pos.max (Ay + Az) Ax * p))%nat.
    { rewrite (Pos2Nat.inj_mul 2).
      rewrite <- (mult_1_l (Pos.to_nat (2 * Pos.max (Ay + Az) Ax * p))).
      rewrite mult_assoc. apply Nat.mul_le_mono_nonneg. auto.
      simpl. auto. apply le_0_n. apply le_refl. }
    apply H0. intro n0. apply (Qle_lt_trans _ (Qabs (yn n0) + Qabs (zn n0))).
    apply Qabs_triangle. rewrite Pos2Z.inj_add.
    rewrite <- Qinv_plus_distr. apply Qplus_lt_le_compat.
    apply majy. apply Qlt_le_weak. apply majz.
    apply majx. rewrite max_l.
    apply H1. rewrite (Pos2Nat.inj_mul 2). apply H3.
    rewrite max_l. apply H2. rewrite (Pos2Nat.inj_mul 2).
    apply H3.
  - destruct x as [xn limx], y as [yn limy], z as [zn limz]; simpl.
    destruct (QCauchySeq_bounded xn Pos.to_nat limx) as [Ax majx].
    destruct (QCauchySeq_bounded yn Pos.to_nat limy) as [Ay majy].
    destruct (QCauchySeq_bounded zn Pos.to_nat limz) as [Az majz].
    simpl.
    exists (fun p : positive => (Pos.to_nat (2 * (Pos.max (Pos.max Ax Ay) Az) * (2 * p)))).
    intros p n k H H0.
    setoid_replace (xn n * (yn n + zn n) -
     (xn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat *
      yn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat +
      xn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat *
      zn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat))%Q
      with (xn n * yn n - (xn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat *
                           yn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat)
            + (xn n * zn n - xn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat *
                             zn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat))%Q.
    2: ring.
    apply (Qle_lt_trans _ (Qabs (xn n * yn n - (xn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat *
                                                yn (Pos.to_nat (Pos.max Ax Ay)~0 * k)%nat))
                           + Qabs (xn n * zn n - xn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat *
                             zn (Pos.to_nat (Pos.max Ax Az)~0 * k)%nat))).
    apply Qabs_triangle.
    setoid_replace (1#p)%Q with ((1#2*p) + (1#2*p))%Q.
    apply Qplus_lt_le_compat.
    + pose proof (CReal_mult_cauchy xn xn yn Ax Ay Pos.to_nat limx limy).
      apply H1. apply majx. apply majy. rewrite max_l.
      apply (le_trans _ (Pos.to_nat (2 * Pos.max (Pos.max Ax Ay) Az * (2 * p)))).
      rewrite (Pos.mul_comm 2). rewrite <- Pos.mul_assoc.
      rewrite <- (Pos.mul_comm (Pos.max (Pos.max Ax Ay) Az)).
      rewrite <- Pos.mul_assoc.
      rewrite Pos2Nat.inj_mul.
      rewrite (Pos2Nat.inj_mul (Pos.max (Pos.max Ax Ay) Az)).
      apply Nat.mul_le_mono_nonneg. apply le_0_n.
      apply Pos2Nat.inj_le. apply Pos.le_max_l.
      apply le_0_n. apply le_refl. apply H. apply le_refl.
      rewrite max_l. apply (le_trans _ k).
      apply (le_trans _ (Pos.to_nat (2 * Pos.max (Pos.max Ax Ay) Az * (2 * p)))).
      rewrite (Pos.mul_comm 2). rewrite <- Pos.mul_assoc.
      rewrite <- (Pos.mul_comm (Pos.max (Pos.max Ax Ay) Az)).
      rewrite <- Pos.mul_assoc.
      rewrite Pos2Nat.inj_mul.
      rewrite (Pos2Nat.inj_mul (Pos.max (Pos.max Ax Ay) Az)).
      apply Nat.mul_le_mono_nonneg. apply le_0_n.
      apply Pos2Nat.inj_le. apply Pos.le_max_l.
      apply le_0_n. apply le_refl. apply H0.
      rewrite <- (mult_1_l k). rewrite mult_assoc.
      apply Nat.mul_le_mono_nonneg. auto.
      rewrite mult_1_r. apply Pos2Nat.is_pos. apply le_0_n.
      apply le_refl. apply le_refl.
    + apply Qlt_le_weak.
      pose proof (CReal_mult_cauchy xn xn zn Ax Az Pos.to_nat limx limz).
      apply H1. apply majx. apply majz. rewrite max_l. 2: apply le_refl.
      apply (le_trans _ (Pos.to_nat (2 * Pos.max (Pos.max Ax Ay) Az * (2 * p)))).
      rewrite (Pos.mul_comm 2). rewrite <- Pos.mul_assoc.
      rewrite <- (Pos.mul_comm (Pos.max (Pos.max Ax Ay) Az)).
      rewrite <- Pos.mul_assoc.
      rewrite Pos2Nat.inj_mul.
      rewrite (Pos2Nat.inj_mul (Pos.max (Pos.max Ax Ay) Az)).
      apply Nat.mul_le_mono_nonneg. apply le_0_n.
      rewrite <- Pos.max_assoc. rewrite (Pos.max_comm Ay Az).
      rewrite Pos.max_assoc. apply Pos2Nat.inj_le. apply Pos.le_max_l.
      apply le_0_n. apply le_refl. apply H.
      rewrite max_l. apply (le_trans _ k).
      apply (le_trans _ (Pos.to_nat (2 * Pos.max (Pos.max Ax Ay) Az * (2 * p)))).
      rewrite (Pos.mul_comm 2). rewrite <- Pos.mul_assoc.
      rewrite <- (Pos.mul_comm (Pos.max (Pos.max Ax Ay) Az)).
      rewrite <- Pos.mul_assoc.
      rewrite Pos2Nat.inj_mul.
      rewrite (Pos2Nat.inj_mul (Pos.max (Pos.max Ax Ay) Az)).
      apply Nat.mul_le_mono_nonneg. apply le_0_n.
      rewrite <- Pos.max_assoc. rewrite (Pos.max_comm Ay Az).
      rewrite Pos.max_assoc. apply Pos2Nat.inj_le. apply Pos.le_max_l.
      apply le_0_n. apply le_refl. apply H0.
      rewrite <- (mult_1_l k). rewrite mult_assoc.
      apply Nat.mul_le_mono_nonneg. auto.
      rewrite mult_1_r. apply Pos2Nat.is_pos. apply le_0_n.
      apply le_refl. apply le_refl.
    + rewrite Qinv_plus_distr. unfold Qeq. reflexivity.
Qed.

Lemma CReal_mult_1_l : forall r: CReal, 1 * r == r.
Proof.
  intros [rn limr]. split.
  - intros [m maj]. simpl in maj.
    destruct (QCauchySeq_bounded (fun _ : nat => 1%Q) Pos.to_nat (ConstCauchy 1)).
    destruct (QCauchySeq_bounded rn Pos.to_nat limr).
    simpl in maj. rewrite Qmult_1_l in maj.
    specialize (limr m).
    apply (Qlt_not_le (2 # m) (1 # m)).
    apply (Qlt_trans _ (rn (Pos.to_nat m) - rn (Pos.to_nat (Pos.max x x0)~0 * Pos.to_nat m)%nat)).
    apply maj.
    apply (Qle_lt_trans _ (Qabs (rn (Pos.to_nat m) - rn (Pos.to_nat (Pos.max x x0)~0 * Pos.to_nat m)%nat))).
    apply Qle_Qabs. apply limr. apply le_refl.
    rewrite <- (mult_1_l (Pos.to_nat m)). rewrite mult_assoc.
    apply Nat.mul_le_mono_nonneg. auto. rewrite mult_1_r.
    apply Pos2Nat.is_pos. apply le_0_n. apply le_refl.
    apply Z.mul_le_mono_nonneg. discriminate. discriminate.
    discriminate. apply Z.le_refl.
  - intros [m maj]. simpl in maj.
    destruct (QCauchySeq_bounded (fun _ : nat => 1%Q) Pos.to_nat (ConstCauchy 1)).
    destruct (QCauchySeq_bounded rn Pos.to_nat limr).
    simpl in maj. rewrite Qmult_1_l in maj.
    specialize (limr m).
    apply (Qlt_not_le (2 # m) (1 # m)).
    apply (Qlt_trans _ (rn (Pos.to_nat (Pos.max x x0)~0 * Pos.to_nat m)%nat - rn (Pos.to_nat m))).
    apply maj.
    apply (Qle_lt_trans _ (Qabs (rn (Pos.to_nat (Pos.max x x0)~0 * Pos.to_nat m)%nat - rn (Pos.to_nat m)))).
    apply Qle_Qabs. apply limr.
    rewrite <- (mult_1_l (Pos.to_nat m)). rewrite mult_assoc.
    apply Nat.mul_le_mono_nonneg. auto. rewrite mult_1_r.
    apply Pos2Nat.is_pos. apply le_0_n. apply le_refl.
    apply le_refl. apply Z.mul_le_mono_nonneg. discriminate. discriminate.
    discriminate. apply Z.le_refl.
Qed.

Lemma CReal_isRingExt : ring_eq_ext CReal_plus CReal_mult CReal_opp CRealEq.
Proof.
  split.
  - intros x y H z t H0. apply CReal_plus_morph; assumption.
  - intros x y H z t H0. apply (CRealEq_trans _ (CReal_mult x t)).
    apply CReal_mult_proper_l. apply H0.
    apply (CRealEq_trans _ (CReal_mult t x)). apply CReal_mult_comm.
    apply (CRealEq_trans _ (CReal_mult t y)).
    apply CReal_mult_proper_l. apply H.  apply CReal_mult_comm.
  - intros x y H. apply (CReal_plus_eq_reg_l x).
    apply (CRealEq_trans _ (inject_Q 0)). apply CReal_plus_opp_r.
    apply (CRealEq_trans _ (CReal_plus y (CReal_opp y))).
    apply CRealEq_sym. apply CReal_plus_opp_r.
    apply CReal_plus_proper_r. apply CRealEq_sym. apply H.
Qed.

Lemma CReal_isRing : ring_theory (inject_Q 0) (inject_Q 1)
                                 CReal_plus CReal_mult
                                 CReal_minus CReal_opp
                                 CRealEq.
Proof.
  intros. split.
  - apply CReal_plus_0_l.
  - apply CReal_plus_comm.
  - intros x y z. symmetry. apply CReal_plus_assoc.
  - apply CReal_mult_1_l.
  - apply CReal_mult_comm.
  - intros x y z. symmetry. apply CReal_mult_assoc.
  - intros x y z. rewrite <- (CReal_mult_comm z).
    rewrite CReal_mult_plus_distr_l.
    apply (CRealEq_trans _ (CReal_plus (CReal_mult x z) (CReal_mult z y))).
    apply CReal_plus_proper_r. apply CReal_mult_comm.
    apply CReal_plus_proper_l. apply CReal_mult_comm.
  - intros x y. apply CRealEq_refl.
  - apply CReal_plus_opp_r.
Qed.

Add Parametric Morphism : CReal_mult
    with signature CRealEq ==> CRealEq ==> CRealEq
      as CReal_mult_morph.
Proof.
  apply CReal_isRingExt.
Qed.

Add Parametric Morphism : CReal_opp
    with signature CRealEq ==> CRealEq
      as CReal_opp_morph.
Proof.
  apply (Ropp_ext CReal_isRingExt).
Qed.

Add Parametric Morphism : CReal_minus
    with signature CRealEq ==> CRealEq ==> CRealEq
      as CReal_minus_morph.
Proof.
  intros. unfold CReal_minus. rewrite H,H0. reflexivity.
Qed.

Add Ring CRealRing : CReal_isRing.

(**********)
Lemma CReal_mult_0_l : forall r, 0 * r == 0.
Proof.
  intro; ring.
Qed.

(**********)
Lemma CReal_mult_1_r : forall r, r * 1 == r.
Proof.
  intro; ring.
Qed.

Lemma CReal_opp_mult_distr_l
  : forall r1 r2 : CReal, CRealEq (CReal_opp (CReal_mult r1 r2))
                              (CReal_mult (CReal_opp r1) r2).
Proof.
  intros. ring.
Qed.

Lemma CReal_mult_lt_compat_l : forall x y z : CReal,
    CRealLt (inject_Q 0) x
    -> CRealLt y z
    -> CRealLt (CReal_mult x y) (CReal_mult x z).
Proof.
  intros. apply (CReal_plus_lt_reg_l
                   (CReal_opp (CReal_mult x y))).
  rewrite CReal_plus_comm. pose proof CReal_plus_opp_r.
  unfold CReal_minus in H1. rewrite H1.
  rewrite CReal_mult_comm, CReal_opp_mult_distr_l, CReal_mult_comm.
  rewrite <- CReal_mult_plus_distr_l.
  apply CReal_mult_lt_0_compat. exact H.
  apply (CReal_plus_lt_reg_l y).
  rewrite CReal_plus_comm, CReal_plus_0_l.
  rewrite <- CReal_plus_assoc, H1, CReal_plus_0_l. exact H0.
Qed.

Lemma CReal_mult_eq_reg_l : forall (r r1 r2 : CReal),
    r # 0
    -> CRealEq (CReal_mult r r1) (CReal_mult r r2)
    -> CRealEq r1 r2.
Proof.
  intros. destruct H; split.
  - intro abs. apply (CReal_mult_lt_compat_l (-r)) in abs.
    rewrite <- CReal_opp_mult_distr_l, <- CReal_opp_mult_distr_l, H0 in abs.
    exact (CRealLt_irrefl _ abs). apply (CReal_plus_lt_reg_l r).
    rewrite CReal_plus_opp_r, CReal_plus_comm, CReal_plus_0_l. exact H.
  - intro abs. apply (CReal_mult_lt_compat_l (-r)) in abs.
    rewrite <- CReal_opp_mult_distr_l, <- CReal_opp_mult_distr_l, H0 in abs.
    exact (CRealLt_irrefl _ abs). apply (CReal_plus_lt_reg_l r).
    rewrite CReal_plus_opp_r, CReal_plus_comm, CReal_plus_0_l. exact H.
  - intro abs. apply (CReal_mult_lt_compat_l r) in abs. rewrite H0 in abs.
    exact (CRealLt_irrefl _ abs). exact H.
  - intro abs. apply (CReal_mult_lt_compat_l r) in abs. rewrite H0 in abs.
    exact (CRealLt_irrefl _ abs). exact H.
Qed.



(*********************************************************)
(** * Field                                              *)
(*********************************************************)

(**********)
Fixpoint INR (n:nat) : CReal :=
  match n with
  | O => 0
  | S O => 1
  | S n => INR n + 1
  end.
Arguments INR n%nat.

(* compact representation for 2*p *)
Fixpoint IPR_2 (p:positive) : CReal :=
  match p with
  | xH => 1 + 1
  | xO p => (1 + 1) * IPR_2 p
  | xI p => (1 + 1) * (1 + IPR_2 p)
  end.

Definition IPR (p:positive) : CReal :=
  match p with
  | xH => 1
  | xO p => IPR_2 p
  | xI p => 1 + IPR_2 p
  end.
Arguments IPR p%positive : simpl never.

(**********)
Definition IZR (z:Z) : CReal :=
  match z with
  | Z0 => 0
  | Zpos n => IPR n
  | Zneg n => - IPR n
  end.
Arguments IZR z%Z : simpl never.

Notation "2" := (IZR 2) : R_scope_constr.

(**********)
Lemma S_INR : forall n:nat, INR (S n) == INR n + 1.
Proof.
  intro; destruct n. rewrite CReal_plus_0_l. reflexivity. reflexivity.
Qed.

Lemma lt_INR : forall n m:nat, (n < m)%nat -> INR n < INR m.
Proof.
  induction m.
  - intros. inversion H.
  - intros. unfold lt in H. apply le_S_n in H. destruct m.
    inversion H. apply CRealLt_0_1. apply Nat.le_succ_r in H. destruct H.
    rewrite S_INR. apply (CRealLt_trans _ (INR (S m) + 0)).
    rewrite CReal_plus_comm, CReal_plus_0_l. apply IHm.
    apply le_n_S. exact H.
    apply CReal_plus_lt_compat_l. exact CRealLt_0_1.
    subst n. rewrite (S_INR (S m)). rewrite <- (CReal_plus_0_l).
    rewrite (CReal_plus_comm 0), CReal_plus_assoc.
    apply CReal_plus_lt_compat_l. rewrite CReal_plus_0_l.
    exact CRealLt_0_1.
Qed.

(**********)
Lemma S_O_plus_INR : forall n:nat, INR (1 + n) == INR 1 + INR n.
Proof.
  intros; destruct n.
  - rewrite CReal_plus_comm, CReal_plus_0_l. reflexivity.
  - rewrite CReal_plus_comm. reflexivity.
Qed.

(**********)
Lemma plus_INR : forall n m:nat, INR (n + m) == INR n + INR m.
Proof.
  intros n m; induction  n as [| n Hrecn].
  - rewrite CReal_plus_0_l. reflexivity.
  - replace (S n + m)%nat with (S (n + m)); auto with arith.
    repeat rewrite S_INR.
    rewrite Hrecn; ring.
Qed.

(**********)
Lemma minus_INR : forall n m:nat, (m <= n)%nat -> INR (n - m) == INR n - INR m.
Proof.
  intros n m le; pattern m, n; apply le_elim_rel.
  intros. rewrite <- minus_n_O. unfold CReal_minus.
  unfold INR. ring.
  intros; repeat rewrite S_INR; simpl.
  unfold CReal_minus. rewrite H0. ring. exact le.
Qed.

(*********)
Lemma mult_INR : forall n m:nat, INR (n * m) == INR n * INR m.
Proof.
  intros n m; induction  n as [| n Hrecn].
  - rewrite CReal_mult_0_l. reflexivity.
  - intros; repeat rewrite S_INR; simpl.
    rewrite plus_INR. rewrite Hrecn; ring.
Qed.

(**********)
Lemma IZN : forall n:Z, (0 <= n)%Z ->  exists m : nat, n = Z.of_nat m.
Proof.
  intros z; idtac; apply Z_of_nat_complete; assumption.
Qed.

Lemma INR_IPR : forall p, INR (Pos.to_nat p) == IPR p.
Proof.
  assert (H: forall p, 2 * INR (Pos.to_nat p) == IPR_2 p).
  { induction p as [p|p|].
    - unfold IPR_2; rewrite Pos2Nat.inj_xI, S_INR, mult_INR, <- IHp.
      rewrite CReal_plus_comm. reflexivity.
    - unfold IPR_2; now rewrite Pos2Nat.inj_xO, mult_INR, <- IHp.
    - apply CReal_mult_1_r. }
  intros [p|p|] ; unfold IPR.
  rewrite Pos2Nat.inj_xI, S_INR, mult_INR, <- H.
  apply CReal_plus_comm.
  now rewrite Pos2Nat.inj_xO, mult_INR, <- H.
  easy.
Qed.

Lemma IPR_pos : forall p:positive, 0 < IPR p.
Proof.
  intro p. rewrite <- INR_IPR. apply (lt_INR 0), Pos2Nat.is_pos.
Qed.

(**********)
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
  - rewrite CReal_plus_0_l. reflexivity.
  - rewrite CReal_plus_0_l. rewrite Z.add_0_l. reflexivity.
  - rewrite CReal_plus_0_l. reflexivity.
  - rewrite CReal_plus_comm,CReal_plus_0_l. reflexivity.
  - rewrite <- Pos2Z.inj_add. unfold IZR. apply plus_IPR.
  - apply plus_IZR_NEG_POS.
  - rewrite CReal_plus_comm,CReal_plus_0_l, Z.add_0_r. reflexivity.
  - rewrite Z.add_comm; rewrite CReal_plus_comm; apply plus_IZR_NEG_POS.
  - simpl. unfold IZR. rewrite <- 3!INR_IPR, Pos2Nat.inj_add, plus_INR.
    ring.
Qed.


Lemma CReal_iterate_one : forall (n : nat),
    IZR (Z.of_nat n) == inject_Q (Z.of_nat n # 1).
Proof.
  induction n.
  - apply CRealEq_refl.
  - replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z.
    rewrite plus_IZR.
    rewrite IHn. clear IHn. apply CRealEq_diff. intro k. simpl.
    rewrite Z.mul_1_r. rewrite Z.mul_1_r. rewrite Z.mul_1_r.
    rewrite Z.add_opp_diag_r. discriminate.
    replace (S n) with (1 + n)%nat. 2: reflexivity.
    rewrite (Nat2Z.inj_add 1 n). reflexivity.
Qed.

(* The constant sequences of rationals are CRealEq to
   the rational operations on the unity. *)
Lemma FinjectZ_CReal : forall z : Z,
    IZR z == inject_Q (z # 1).
Proof.
  intros. destruct z.
  - apply CRealEq_refl.
  - simpl. pose proof (CReal_iterate_one (Pos.to_nat p)).
    rewrite positive_nat_Z in H. apply H.
  - simpl. apply (CReal_plus_eq_reg_l (IZR (Z.pos p))).
    pose proof CReal_plus_opp_r. rewrite H.
    pose proof (CReal_iterate_one (Pos.to_nat p)).
    rewrite positive_nat_Z in H0. rewrite H0.
    apply CRealEq_diff. intro n. simpl. rewrite Z.pos_sub_diag.
    discriminate.
Qed.


(* Axiom Rarchimed_constr *)
Lemma Rarchimedean
  : forall x:CReal,
    { n:Z | x < IZR n /\ IZR n < x+2 }.
Proof.
  (* Locate x within 1/4 and pick the first integer above this interval. *)
  intros [xn limx].
  pose proof (Qlt_floor (xn 4%nat + (1#4))). unfold inject_Z in H.
  pose proof (Qfloor_le (xn 4%nat + (1#4))). unfold inject_Z in H0.
  remember (Qfloor (xn 4%nat + (1#4)))%Z as n.
  exists (n+1)%Z. split.
  - rewrite FinjectZ_CReal.
    assert (Qlt 0 ((n + 1 # 1) - (xn 4%nat + (1 # 4)))) as epsPos.
    { unfold Qminus. rewrite <- Qlt_minus_iff. exact H. }
    destruct (Qarchimedean (/((1#2)*((n + 1 # 1) - (xn 4%nat + (1 # 4)))))) as [k kmaj].
    exists (Pos.max 4 k). simpl.
    apply (Qlt_trans _ ((n + 1 # 1) - (xn 4%nat + (1 # 4)))).
    + setoid_replace (Z.pos k # 1)%Q with (/(1#k))%Q in kmaj. 2: reflexivity.
      rewrite <- Qinv_lt_contravar in kmaj. 2: reflexivity.
      apply (Qle_lt_trans _ (2#k)).
      rewrite <- (Qmult_le_l _ _ (1#2)).
      setoid_replace ((1 # 2) * (2 # k))%Q with (1#k)%Q. 2: reflexivity.
      setoid_replace ((1 # 2) * (2 # Pos.max 4 k))%Q with (1#Pos.max 4 k)%Q. 2: reflexivity.
      unfold Qle; simpl. apply Pos2Z.pos_le_pos. apply Pos.le_max_r.
      reflexivity.
      rewrite <- (Qmult_lt_l _ _ (1#2)).
      setoid_replace ((1 # 2) * (2 # k))%Q with (1#k)%Q. exact kmaj.
      reflexivity. reflexivity. rewrite <- (Qmult_0_r (1#2)).
      rewrite Qmult_lt_l. exact epsPos. reflexivity.
    + rewrite <- (Qplus_lt_r _ _ (xn (Pos.to_nat (Pos.max 4 k)) - (n + 1 # 1) + (1#4))).
      ring_simplify.
      apply (Qle_lt_trans _ (Qabs (xn (Pos.to_nat (Pos.max 4 k)) - xn 4%nat))).
      apply Qle_Qabs. apply limx.
      rewrite Pos2Nat.inj_max. apply Nat.le_max_l. apply le_refl.
  - apply (CReal_plus_lt_reg_l (-IZR 2)). ring_simplify.
    do 2 rewrite FinjectZ_CReal.
    exists 4%positive. simpl.
    rewrite <- Qinv_plus_distr.
    rewrite <- (Qplus_lt_r _ _ ((n#1) - (1#2))). ring_simplify.
    apply (Qle_lt_trans _ (xn 4%nat + (1 # 4)) _ H0).
    unfold Pos.to_nat; simpl.
    rewrite <- (Qplus_lt_r _ _ (-xn 4%nat)). ring_simplify.
    reflexivity.
Qed.

Lemma CRealLtDisjunctEpsilon : forall a b c d : CReal,
    (CRealLt a b \/ CRealLt c d) -> { CRealLt a b } + { CRealLt c d }.
Proof.
  intros.
  assert (exists n : nat, n <> O /\
             (Qlt (2 # Pos.of_nat n) (proj1_sig b n - proj1_sig a n)
              \/ Qlt (2 # Pos.of_nat n) (proj1_sig d n - proj1_sig c n))).
  { destruct H. destruct H as [n maj]. exists (Pos.to_nat n). split.
    intro abs. destruct (Pos2Nat.is_succ n). rewrite H in abs.
    inversion abs. left. rewrite Pos2Nat.id. apply maj.
    destruct H as [n maj]. exists (Pos.to_nat n). split.
    intro abs. destruct (Pos2Nat.is_succ n). rewrite H in abs.
    inversion abs. right. rewrite Pos2Nat.id. apply maj. }
  apply constructive_indefinite_ground_description_nat in H0.
  - destruct H0 as [n [nPos maj]].
    destruct (Qlt_le_dec (2 # Pos.of_nat n)
                         (proj1_sig b n - proj1_sig a n)).
    left. exists (Pos.of_nat n). rewrite Nat2Pos.id. apply q. apply nPos.
    assert (2 # Pos.of_nat n < proj1_sig d n - proj1_sig c n)%Q.
    destruct maj. exfalso.
    apply (Qlt_not_le (2 # Pos.of_nat n) (proj1_sig b n - proj1_sig a n)); assumption.
    assumption. clear maj. right. exists (Pos.of_nat n). rewrite Nat2Pos.id.
    apply H0. apply nPos.
  - clear H0. clear H. intro n. destruct n. right.
    intros [abs _]. exact (abs (eq_refl O)).
    destruct (Qlt_le_dec (2 # Pos.of_nat (S n)) (proj1_sig b (S n) - proj1_sig a (S n))).
    left. split. discriminate. left. apply q.
    destruct (Qlt_le_dec (2 # Pos.of_nat (S n)) (proj1_sig d (S n) - proj1_sig c (S n))).
    left. split. discriminate. right. apply q0.
    right. intros [_ [abs|abs]].
    apply (Qlt_not_le (2 # Pos.of_nat (S n))
                      (proj1_sig b (S n) - proj1_sig a (S n))); assumption.
    apply (Qlt_not_le (2 # Pos.of_nat (S n))
                      (proj1_sig d (S n) - proj1_sig c (S n))); assumption.
Qed.

Lemma CRealShiftReal : forall (x : CReal) (k : nat),
    QCauchySeq (fun n => proj1_sig x (plus n k)) Pos.to_nat.
Proof.
  intros x k n p q H H0.
  destruct x as [xn cau]; unfold proj1_sig.
  destruct k. rewrite plus_0_r. rewrite plus_0_r. apply cau; assumption.
  specialize (cau (n + Pos.of_nat (S k))%positive (p + S k)%nat (q + S k)%nat).
  apply (Qlt_trans _ (1 # n + Pos.of_nat (S k))).
  apply cau. rewrite Pos2Nat.inj_add. rewrite Nat2Pos.id.
  apply Nat.add_le_mono_r. apply H. discriminate.
  rewrite Pos2Nat.inj_add. rewrite Nat2Pos.id.
  apply Nat.add_le_mono_r. apply H0. discriminate.
  apply Pos2Nat.inj_lt; simpl. rewrite Pos2Nat.inj_add.
  rewrite <- (plus_0_r (Pos.to_nat n)). rewrite <- plus_assoc.
  apply Nat.add_lt_mono_l. apply Pos2Nat.is_pos.
Qed.

Lemma CRealShiftEqual : forall (x : CReal) (k : nat),
    CRealEq x (exist _ (fun n => proj1_sig x (plus n k)) (CRealShiftReal x k)).
Proof.
  intros. split.
  - intros [n maj]. destruct x as [xn cau]; simpl in maj.
    specialize (cau n (Pos.to_nat n + k)%nat (Pos.to_nat n)).
    apply Qlt_not_le in maj. apply maj. clear maj.
    apply (Qle_trans _ (Qabs (xn (Pos.to_nat n + k)%nat - xn (Pos.to_nat n)))).
    apply Qle_Qabs. apply (Qle_trans _ (1#n)). apply Zlt_le_weak.
    apply cau. rewrite <- (plus_0_r (Pos.to_nat n)).
    rewrite <- plus_assoc. apply Nat.add_le_mono_l. apply le_0_n.
    apply le_refl. apply Z.mul_le_mono_pos_r. apply Pos2Z.is_pos.
    discriminate.
  - intros [n maj]. destruct x as [xn cau]; simpl in maj.
    specialize (cau n (Pos.to_nat n) (Pos.to_nat n + k)%nat).
    apply Qlt_not_le in maj. apply maj. clear maj.
    apply (Qle_trans _ (Qabs (xn (Pos.to_nat n) - xn (Pos.to_nat n + k)%nat))).
    apply Qle_Qabs. apply (Qle_trans _ (1#n)). apply Zlt_le_weak.
    apply cau. apply le_refl. rewrite <- (plus_0_r (Pos.to_nat n)).
    rewrite <- plus_assoc. apply Nat.add_le_mono_l. apply le_0_n.
    apply Z.mul_le_mono_pos_r. apply Pos2Z.is_pos. discriminate.
Qed.

(* Find an equal negative real number, which rational sequence
   stays below 0, so that it can be inversed. *)
Definition CRealNegShift (x : CReal)
  : CRealLt x (inject_Q 0)
    -> { y : prod positive CReal | CRealEq x (snd y)
                                   /\ forall n:nat, Qlt (proj1_sig (snd y) n) (-1 # fst y) }.
Proof.
  intro xNeg. apply CRealLtEpsilon in xNeg.
  pose proof (CRealLt_aboveSig x (inject_Q 0)).
  pose proof (CRealShiftReal x).
  pose proof (CRealShiftEqual x).
  destruct xNeg as [n maj], x as [xn cau]; simpl in maj.
  specialize (H n maj); simpl in H.
  destruct (Qarchimedean (/ (0 - xn (Pos.to_nat n) - (2 # n)))) as [a _].
  remember (Pos.max n a~0) as k.
  clear Heqk. clear maj. clear n.
  exists (pair k
          (exist _ (fun n => xn (plus n (Pos.to_nat k))) (H0 (Pos.to_nat k)))).
  split. apply H1. intro n. simpl. apply Qlt_minus_iff.
  destruct n.
  - specialize (H k).
    unfold Qminus in H. rewrite Qplus_0_l in H. apply Qlt_minus_iff in H.
    unfold Qminus. rewrite Qplus_comm.
    apply (Qlt_trans _ (- xn (Pos.to_nat k)%nat - (2 #k))). apply H.
    unfold Qminus. simpl. apply Qplus_lt_r.
    apply Z.mul_lt_mono_pos_r. simpl. apply Pos2Z.is_pos.
    reflexivity. apply Pos.le_refl.
  - apply (Qlt_trans _ (-(2 # k) - xn (S n + Pos.to_nat k)%nat)).
    rewrite <- (Nat2Pos.id (S n)). rewrite <- Pos2Nat.inj_add.
    specialize (H (Pos.of_nat (S n) + k)%positive).
    unfold Qminus in H. rewrite Qplus_0_l in H. apply Qlt_minus_iff in H.
    unfold Qminus. rewrite Qplus_comm. apply H. apply Pos2Nat.inj_le.
    rewrite <- (plus_0_l (Pos.to_nat k)). rewrite Pos2Nat.inj_add.
    apply Nat.add_le_mono_r. apply le_0_n. discriminate.
    apply Qplus_lt_l.
    apply Z.mul_lt_mono_pos_r. simpl. apply Pos2Z.is_pos.
    reflexivity.
Qed.

Definition CRealPosShift (x : CReal)
  : CRealLt (inject_Q 0) x
    -> { y : prod positive CReal | CRealEq x (snd y)
                                   /\ forall n:nat, Qlt (1 # fst y) (proj1_sig (snd y) n) }.
Proof.
  intro xPos. apply CRealLtEpsilon in xPos.
  pose proof (CRealLt_aboveSig (inject_Q 0) x).
  pose proof (CRealShiftReal x).
  pose proof (CRealShiftEqual x).
  destruct xPos as [n maj], x as [xn cau]; simpl in maj.
  simpl in H. specialize (H n).
  destruct (Qarchimedean (/ (xn (Pos.to_nat n) - 0 - (2 # n)))) as [a _].
  specialize (H maj); simpl in H.
  remember (Pos.max n a~0) as k.
  clear Heqk. clear maj. clear n.
  exists (pair k
               (exist _ (fun n => xn (plus n (Pos.to_nat k))) (H0 (Pos.to_nat k)))).
  split. apply H1. intro n. simpl. apply Qlt_minus_iff.
  destruct n.
  - specialize (H k).
    unfold Qminus in H. rewrite Qplus_0_r in H.
    simpl. rewrite <- Qlt_minus_iff.
    apply (Qlt_trans _ (2 #k)).
    apply Z.mul_lt_mono_pos_r. simpl. apply Pos2Z.is_pos.
    reflexivity. apply H. apply Pos.le_refl.
  - rewrite <- Qlt_minus_iff. apply (Qlt_trans _ (2 # k)).
    apply Z.mul_lt_mono_pos_r. simpl. apply Pos2Z.is_pos.
    reflexivity. specialize (H (Pos.of_nat (S n) + k)%positive).
    unfold Qminus in H. rewrite Qplus_0_r in H.
    rewrite Pos2Nat.inj_add in H. rewrite Nat2Pos.id in H.
    apply H. apply Pos2Nat.inj_le.
    rewrite <- (plus_0_l (Pos.to_nat k)). rewrite Pos2Nat.inj_add.
    apply Nat.add_le_mono_r. apply le_0_n. discriminate.
Qed.

Lemma CReal_inv_neg : forall (yn : nat -> Q) (k : positive),
    (QCauchySeq yn Pos.to_nat)
    -> (forall n : nat, yn n < -1 # k)%Q
    -> QCauchySeq (fun n : nat => / yn (Pos.to_nat k ^ 2 * n)%nat) Pos.to_nat.
Proof.
  (* Prove the inverse sequence is Cauchy *)
  intros yn k cau maj n p q H0 H1.
  setoid_replace (/ yn (Pos.to_nat k ^ 2 * p)%nat -
                  / yn (Pos.to_nat k ^ 2 * q)%nat)%Q
    with ((yn (Pos.to_nat k ^ 2 * q)%nat -
           yn (Pos.to_nat k ^ 2 * p)%nat)
            / (yn (Pos.to_nat k ^ 2 * q)%nat *
               yn (Pos.to_nat k ^ 2 * p)%nat)).
  + apply (Qle_lt_trans _ (Qabs (yn (Pos.to_nat k ^ 2 * q)%nat
                                 - yn (Pos.to_nat k ^ 2 * p)%nat)
                                / (1 # (k^2)))).
    assert (1 # k ^ 2
            < Qabs (yn (Pos.to_nat k ^ 2 * q)%nat * yn (Pos.to_nat k ^ 2 * p)%nat))%Q.
    { rewrite Qabs_Qmult. unfold "^"%positive; simpl.
      rewrite factorDenom. rewrite Pos.mul_1_r.
      apply (Qlt_trans _ ((1#k) * Qabs (yn (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat))).
      apply Qmult_lt_l. reflexivity. rewrite Qabs_neg.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat).
      apply Qlt_minus_iff in maj. apply Qlt_minus_iff.
      rewrite Qplus_comm. setoid_replace (-(1#k))%Q with (-1 # k)%Q. apply maj.
      reflexivity. apply (Qle_trans _ (-1 # k)). apply Zlt_le_weak.
      apply maj. discriminate.
      apply Qmult_lt_r. apply (Qlt_trans 0 (1#k)). reflexivity.
      rewrite Qabs_neg.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat).
      apply Qlt_minus_iff in maj. apply Qlt_minus_iff.
      rewrite Qplus_comm. setoid_replace (-(1#k))%Q with (-1 # k)%Q. apply maj.
      reflexivity. apply (Qle_trans _ (-1 # k)). apply Zlt_le_weak.
      apply maj. discriminate.
      rewrite Qabs_neg.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * q)%nat).
      apply Qlt_minus_iff in maj. apply Qlt_minus_iff.
      rewrite Qplus_comm. setoid_replace (-(1#k))%Q with (-1 # k)%Q. apply maj.
      reflexivity. apply (Qle_trans _ (-1 # k)). apply Zlt_le_weak.
      apply maj. discriminate. }
    unfold Qdiv. rewrite Qabs_Qmult. rewrite Qabs_Qinv.
    rewrite Qmult_comm. rewrite <- (Qmult_comm (/ (1 # k ^ 2))).
    apply Qmult_le_compat_r. apply Qlt_le_weak.
    rewrite <- Qmult_1_l. apply Qlt_shift_div_r.
    apply (Qlt_trans 0 (1 # k ^ 2)). reflexivity. apply H.
    rewrite Qmult_comm. apply Qlt_shift_div_l.
    reflexivity. rewrite Qmult_1_l. apply H.
    apply Qabs_nonneg. simpl in maj.
    specialize (cau (n * (k^2))%positive
                    (Pos.to_nat k ^ 2 * q)%nat
                    (Pos.to_nat k ^ 2 * p)%nat).
    apply Qlt_shift_div_r. reflexivity.
    apply (Qlt_le_trans _ (1 # n * k ^ 2)). apply cau.
    rewrite Pos2Nat.inj_mul. rewrite mult_comm.
    unfold "^"%positive. simpl. rewrite Pos2Nat.inj_mul.
    rewrite <- mult_assoc. rewrite <- mult_assoc.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    rewrite (mult_1_r). rewrite Pos.mul_1_r.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    apply (le_trans _ (q+0)). rewrite plus_0_r. assumption.
    rewrite plus_0_r. apply le_refl.
    rewrite Pos2Nat.inj_mul. rewrite mult_comm.
    unfold "^"%positive; simpl. rewrite Pos2Nat.inj_mul.
    rewrite <- mult_assoc. rewrite <- mult_assoc.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    rewrite (mult_1_r). rewrite Pos.mul_1_r.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    apply (le_trans _ (p+0)). rewrite plus_0_r. assumption.
    rewrite plus_0_r. apply le_refl.
    rewrite factorDenom. apply Qle_refl.
  + field. split. intro abs.
    specialize (maj (Pos.to_nat k ^ 2 * p)%nat).
    rewrite abs in maj. inversion maj.
    intro abs.
    specialize (maj (Pos.to_nat k ^ 2 * q)%nat).
    rewrite abs in maj. inversion maj.
Qed.

Lemma CReal_inv_pos : forall (yn : nat -> Q) (k : positive),
    (QCauchySeq yn Pos.to_nat)
    -> (forall n : nat, 1 # k < yn n)%Q
    -> QCauchySeq (fun n : nat => / yn (Pos.to_nat k ^ 2 * n)%nat) Pos.to_nat.
Proof.
  intros yn k cau maj n p q H0 H1.
  setoid_replace (/ yn (Pos.to_nat k ^ 2 * p)%nat -
                  / yn (Pos.to_nat k ^ 2 * q)%nat)%Q
    with ((yn (Pos.to_nat k ^ 2 * q)%nat -
           yn (Pos.to_nat k ^ 2 * p)%nat)
            / (yn (Pos.to_nat k ^ 2 * q)%nat *
               yn (Pos.to_nat k ^ 2 * p)%nat)).
  + apply (Qle_lt_trans _ (Qabs (yn (Pos.to_nat k ^ 2 * q)%nat
                                 - yn (Pos.to_nat k ^ 2 * p)%nat)
                                / (1 # (k^2)))).
    assert (1 # k ^ 2
            < Qabs (yn (Pos.to_nat k ^ 2 * q)%nat * yn (Pos.to_nat k ^ 2 * p)%nat))%Q.
    { rewrite Qabs_Qmult. unfold "^"%positive; simpl.
      rewrite factorDenom. rewrite Pos.mul_1_r.
      apply (Qlt_trans _ ((1#k) * Qabs (yn (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat))).
      apply Qmult_lt_l. reflexivity. rewrite Qabs_pos.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat).
      apply maj. apply (Qle_trans _ (1 # k)).
      discriminate. apply Zlt_le_weak. apply maj.
      apply Qmult_lt_r. apply (Qlt_trans 0 (1#k)). reflexivity.
      rewrite Qabs_pos.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * p)%nat).
      apply maj. apply (Qle_trans _ (1 # k)). discriminate.
      apply Zlt_le_weak. apply maj.
      rewrite Qabs_pos.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1) * q)%nat).
      apply maj. apply (Qle_trans _ (1 # k)). discriminate.
      apply Zlt_le_weak. apply maj. }
    unfold Qdiv. rewrite Qabs_Qmult. rewrite Qabs_Qinv.
    rewrite Qmult_comm. rewrite <- (Qmult_comm (/ (1 # k ^ 2))).
    apply Qmult_le_compat_r. apply Qlt_le_weak.
    rewrite <- Qmult_1_l. apply Qlt_shift_div_r.
    apply (Qlt_trans 0 (1 # k ^ 2)). reflexivity. apply H.
    rewrite Qmult_comm. apply Qlt_shift_div_l.
    reflexivity. rewrite Qmult_1_l. apply H.
    apply Qabs_nonneg. simpl in maj.
    specialize (cau (n * (k^2))%positive
                    (Pos.to_nat k ^ 2 * q)%nat
                    (Pos.to_nat k ^ 2 * p)%nat).
    apply Qlt_shift_div_r. reflexivity.
    apply (Qlt_le_trans _ (1 # n * k ^ 2)). apply cau.
    rewrite Pos2Nat.inj_mul. rewrite mult_comm.
    unfold "^"%positive. simpl. rewrite Pos2Nat.inj_mul.
    rewrite <- mult_assoc. rewrite <- mult_assoc.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    rewrite (mult_1_r). rewrite Pos.mul_1_r.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    apply (le_trans _ (q+0)). rewrite plus_0_r. assumption.
    rewrite plus_0_r. apply le_refl.
    rewrite Pos2Nat.inj_mul. rewrite mult_comm.
    unfold "^"%positive; simpl. rewrite Pos2Nat.inj_mul.
    rewrite <- mult_assoc. rewrite <- mult_assoc.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    rewrite (mult_1_r). rewrite Pos.mul_1_r.
    apply Nat.mul_le_mono_nonneg_l. apply le_0_n.
    apply (le_trans _ (p+0)). rewrite plus_0_r. assumption.
    rewrite plus_0_r. apply le_refl.
    rewrite factorDenom. apply Qle_refl.
  + field. split. intro abs.
    specialize (maj (Pos.to_nat k ^ 2 * p)%nat).
    rewrite abs in maj. inversion maj.
    intro abs.
    specialize (maj (Pos.to_nat k ^ 2 * q)%nat).
    rewrite abs in maj. inversion maj.
Qed.

Definition CReal_inv (x : CReal) (xnz : x # 0) : CReal.
Proof.
  apply CRealLtDisjunctEpsilon in xnz. destruct xnz as [xNeg | xPos].
  - destruct (CRealNegShift x xNeg) as [[k y] [_ maj]].
    destruct y as [yn cau]; unfold proj1_sig, snd, fst in maj.
    exists (fun n => Qinv (yn (mult (Pos.to_nat k^2) n))).
    apply (CReal_inv_neg yn). apply cau. apply maj.
  - destruct (CRealPosShift x xPos) as [[k y] [_ maj]].
    destruct y as [yn cau]; unfold proj1_sig, snd, fst in maj.
    exists (fun n => Qinv (yn (mult (Pos.to_nat k^2) n))).
    apply (CReal_inv_pos yn). apply cau. apply maj.
Defined.

Notation "/ x" := (CReal_inv x) (at level 35, right associativity) : R_scope_constr.

Lemma CReal_inv_0_lt_compat
  : forall (r : CReal) (rnz : r # 0),
    0 < r -> 0 < ((/ r) rnz).
Proof.
  intros. unfold CReal_inv. simpl.
  destruct (CRealLtDisjunctEpsilon r (inject_Q 0) (inject_Q 0) r rnz).
  - exfalso. apply CRealLt_asym in H. contradiction.
  - destruct (CRealPosShift r c) as [[k rpos] [req maj]].
    clear req. clear rnz. destruct rpos as [rn cau]; simpl in maj.
    unfold CRealLt; simpl.
    destruct (Qarchimedean (rn 1%nat)) as [A majA].
    exists (2 * (A + 1))%positive. unfold Qminus. rewrite Qplus_0_r.
    rewrite <- (Qmult_1_l (Qinv (rn (Pos.to_nat k * (Pos.to_nat k * 1) * Pos.to_nat (2 * (A + 1)))%nat))).
    apply Qlt_shift_div_l. apply (Qlt_trans 0 (1#k)). reflexivity.
    apply maj. rewrite <- (Qmult_inv_r (Z.pos A + 1 # 1)).
    setoid_replace (2 # 2 * (A + 1))%Q with (Qinv (Z.pos A + 1 # 1)).
    2: reflexivity.
    rewrite Qmult_comm. apply Qmult_lt_r. reflexivity.
    rewrite mult_1_r. rewrite <- Pos2Nat.inj_mul. rewrite <- Pos2Nat.inj_mul.
    rewrite <- (Qplus_lt_l _ _ (- rn 1%nat)).
    apply (Qle_lt_trans _ (Qabs (rn (Pos.to_nat (k * k * (2 * (A + 1)))) + - rn 1%nat))).
    apply Qle_Qabs. apply (Qlt_le_trans _ 1). apply cau.
    apply Pos2Nat.is_pos. apply le_refl.
    rewrite <- Qinv_plus_distr. rewrite <- (Qplus_comm 1).
    rewrite <- Qplus_0_r. rewrite <- Qplus_assoc. rewrite <- Qplus_assoc.
    rewrite Qplus_le_r. rewrite Qplus_0_l. apply Qlt_le_weak.
    apply Qlt_minus_iff in majA. apply majA.
    intro abs. inversion abs.
Qed.

Lemma CReal_linear_shift : forall (x : CReal) (k : nat),
    le 1 k -> QCauchySeq (fun n => proj1_sig x (k * n)%nat) Pos.to_nat.
Proof.
  intros [xn limx] k lek p n m H H0. unfold proj1_sig.
  apply limx. apply (le_trans _ n). apply H.
  rewrite <- (mult_1_l n). rewrite mult_assoc.
  apply Nat.mul_le_mono_nonneg_r. apply le_0_n.
  rewrite mult_1_r. apply lek. apply (le_trans _ m). apply H0.
  rewrite <- (mult_1_l m). rewrite mult_assoc.
  apply Nat.mul_le_mono_nonneg_r. apply le_0_n.
  rewrite mult_1_r. apply lek.
Qed.

Lemma CReal_linear_shift_eq : forall (x : CReal) (k : nat) (kPos : le 1 k),
    CRealEq x
    (exist (fun n : nat -> Q => QCauchySeq n Pos.to_nat)
           (fun n : nat => proj1_sig x (k * n)%nat) (CReal_linear_shift x k kPos)).
Proof.
  intros. apply CRealEq_diff. intro n.
  destruct x as [xn limx]; unfold proj1_sig.
  specialize (limx n (Pos.to_nat n) (k * Pos.to_nat n)%nat).
  apply (Qle_trans _ (1 # n)). apply Qlt_le_weak. apply limx.
  apply le_refl. rewrite <- (mult_1_l (Pos.to_nat n)).
  rewrite mult_assoc. apply Nat.mul_le_mono_nonneg_r. apply le_0_n.
  rewrite mult_1_r. apply kPos. apply Z.mul_le_mono_nonneg_r.
  discriminate. discriminate.
Qed.

Lemma CReal_inv_l : forall (r:CReal) (rnz : r # 0),
        ((/ r) rnz) * r == 1.
Proof.
  intros. unfold CReal_inv; simpl.
  destruct (CRealLtDisjunctEpsilon r (inject_Q 0) (inject_Q 0) r rnz).
  - (* r < 0 *) destruct (CRealNegShift r c) as [[k rneg] [req maj]].
    simpl in req. apply CRealEq_diff. apply CRealEq_modindep.
    apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : nat, proj1_sig s n < -1 # k) -> CReal) := rneg in
            fun maj0 : forall n : nat, yn n < -1 # k =>
            exist (fun x : nat -> Q => QCauchySeq x Pos.to_nat)
              (fun n : nat => Qinv (yn (Pos.to_nat k * (Pos.to_nat k * 1) * n))%nat)
              (CReal_inv_neg yn k cau maj0)) maj) rneg)))%Q.
    + apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply req.
    + assert (le 1 (Pos.to_nat k * (Pos.to_nat k * 1))%nat). rewrite mult_1_r.
      rewrite <- Pos2Nat.inj_mul. apply Pos2Nat.is_pos.
      apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : nat, proj1_sig s n < -1 # k) -> CReal) := rneg in
            fun maj0 : forall n : nat, yn n < -1 # k =>
            exist (fun x : nat -> Q => QCauchySeq x Pos.to_nat)
              (fun n : nat => Qinv (yn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat))
              (CReal_inv_neg yn k cau maj0)) maj)
                                    (exist _ (fun n => proj1_sig rneg (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat) (CReal_linear_shift rneg _ H)))))%Q.
      apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply CReal_linear_shift_eq.
      destruct r as [rn limr], rneg as [rnn limneg]; simpl.
      destruct (QCauchySeq_bounded
                  (fun n : nat => Qinv (rnn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat))
                  Pos.to_nat (CReal_inv_neg rnn k limneg maj)).
      destruct (QCauchySeq_bounded
            (fun n : nat => rnn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat)
            Pos.to_nat
            (CReal_linear_shift
               (exist (fun x0 : nat -> Q => QCauchySeq x0 Pos.to_nat) rnn limneg)
               (Pos.to_nat k * (Pos.to_nat k * 1)) H)) ; simpl.
      exists (fun n => 1%nat). intros p n m H0 H1. rewrite Qmult_comm.
      rewrite Qmult_inv_r. unfold Qminus. rewrite Qplus_opp_r.
      reflexivity. intro abs.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1)
                       * (Pos.to_nat (Pos.max x x0)~0 * n))%nat).
      simpl in maj. rewrite abs in maj. inversion maj.
  - (* r > 0 *) destruct (CRealPosShift r c) as [[k rneg] [req maj]].
    simpl in req. apply CRealEq_diff. apply CRealEq_modindep.
    apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : nat, 1 # k < proj1_sig s n) -> CReal) := rneg in
            fun maj0 : forall n : nat, 1 # k < yn n =>
            exist (fun x : nat -> Q => QCauchySeq x Pos.to_nat)
              (fun n : nat => Qinv (yn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat))
              (CReal_inv_pos yn k cau maj0)) maj) rneg)))%Q.
    + apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply req.
    + assert (le 1 (Pos.to_nat k * (Pos.to_nat k * 1))%nat). rewrite mult_1_r.
      rewrite <- Pos2Nat.inj_mul. apply Pos2Nat.is_pos.
      apply (QSeqEquivEx_trans _
             (proj1_sig (CReal_mult ((let
              (yn, cau) as s
               return ((forall n : nat, 1 # k < proj1_sig s n) -> CReal) := rneg in
            fun maj0 : forall n : nat, 1 # k < yn n =>
            exist (fun x : nat -> Q => QCauchySeq x Pos.to_nat)
              (fun n : nat => Qinv (yn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat))
              (CReal_inv_pos yn k cau maj0)) maj)
                                    (exist _ (fun n => proj1_sig rneg (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat) (CReal_linear_shift rneg _ H)))))%Q.
      apply CRealEq_modindep. apply CRealEq_diff.
      apply CReal_mult_proper_l. apply CReal_linear_shift_eq.
      destruct r as [rn limr], rneg as [rnn limneg]; simpl.
      destruct (QCauchySeq_bounded
                  (fun n : nat => Qinv (rnn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat))
                  Pos.to_nat (CReal_inv_pos rnn k limneg maj)).
      destruct (QCauchySeq_bounded
            (fun n : nat => rnn (Pos.to_nat k * (Pos.to_nat k * 1) * n)%nat)
            Pos.to_nat
            (CReal_linear_shift
               (exist (fun x0 : nat -> Q => QCauchySeq x0 Pos.to_nat) rnn limneg)
               (Pos.to_nat k * (Pos.to_nat k * 1)) H)) ; simpl.
      exists (fun n => 1%nat). intros p n m H0 H1. rewrite Qmult_comm.
      rewrite Qmult_inv_r. unfold Qminus. rewrite Qplus_opp_r.
      reflexivity. intro abs.
      specialize (maj (Pos.to_nat k * (Pos.to_nat k * 1)
                       * (Pos.to_nat (Pos.max x x0)~0 * n))%nat).
      simpl in maj. rewrite abs in maj. inversion maj.
Qed.

Fixpoint pow (r:CReal) (n:nat) : CReal :=
  match n with
    | O => 1
    | S n => r * (pow r n)
  end.


(**********)
Definition IQR (q:Q) : CReal :=
  match q with
  | Qmake a b => IZR a * (CReal_inv (IPR b)) (or_intror (IPR_pos b))
  end.
Arguments IQR q%Q : simpl never.

Lemma CReal_invQ : forall (b : positive) (pos : Qlt 0 (Z.pos b # 1)),
    CRealEq (CReal_inv (inject_Q (Z.pos b # 1)) (or_intror (CReal_injectQPos (Z.pos b # 1) pos)))
            (inject_Q (1 # b)).
Proof.
  intros.
  apply (CReal_mult_eq_reg_l (inject_Q (Z.pos b # 1))).
  - right. apply CReal_injectQPos. exact pos.
  - rewrite CReal_mult_comm, CReal_inv_l.
    apply CRealEq_diff. intro n. simpl;
    destruct (QCauchySeq_bounded (fun _ : nat => 1 # b)%Q Pos.to_nat (ConstCauchy (1 # b))),
    (QCauchySeq_bounded (fun _ : nat => Z.pos b # 1)%Q Pos.to_nat (ConstCauchy (Z.pos b # 1))); simpl.
    do 2 rewrite Pos.mul_1_r. rewrite Z.pos_sub_diag. discriminate.
Qed.

(* The constant sequences of rationals are CRealEq to
   the rational operations on the unity. *)
Lemma FinjectQ_CReal : forall q : Q,
    IQR q == inject_Q q.
Proof.
  intros [a b]. unfold IQR; simpl.
  pose proof (CReal_iterate_one (Pos.to_nat b)).
  rewrite positive_nat_Z in H. simpl in H.
  assert (0 < Z.pos b # 1)%Q as pos. reflexivity.
  apply (CRealEq_trans _ (CReal_mult (IZR a)
                                     (CReal_inv (inject_Q (Z.pos b # 1)) (or_intror (CReal_injectQPos (Z.pos b # 1) pos))))).
  - apply CReal_mult_proper_l.
    apply (CReal_mult_eq_reg_l (IPR b)).
    right. apply IPR_pos.
    rewrite CReal_mult_comm, CReal_inv_l, H, CReal_mult_comm, CReal_inv_l. reflexivity.
  - rewrite FinjectZ_CReal. rewrite CReal_invQ. apply CRealEq_diff. intro n.
    simpl;
    destruct (QCauchySeq_bounded (fun _ : nat => a # 1)%Q Pos.to_nat (ConstCauchy (a # 1))),
    (QCauchySeq_bounded (fun _ : nat => 1 # b)%Q Pos.to_nat (ConstCauchy (1 # b))); simpl.
    rewrite Z.mul_1_r. rewrite <- Z.mul_add_distr_r.
    rewrite Z.add_opp_diag_r. rewrite Z.mul_0_l. simpl.
    discriminate.
Qed.

Close Scope R_scope_constr.

Close Scope Q.

(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

(** Proof that classical reals are constructive reals with
    extra properties, namely total order, existence of all
    least upper bounds and setoid equivalence simplifying to
    Leibniz equality.

    From this point of view, the quotient Rabst and Rrepr
    between classical Dedekind reals and constructive Cauchy reals
    becomes an isomorphism for the ConstructiveReals structure.

    This allows to apply results from constructive reals to
    classical reals. *)

Require Import QArith_base.
Require Import Znat.
Require Import Rdefinitions.
Require Import Raxioms.
Require Import ConstructiveReals.
Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsMult.
Require Import ConstructiveRcomplete.
Require Import ConstructiveCauchyAbs.
Require Import ConstructiveRealsMorphisms.

Local Open Scope R_scope.

(* Rlt is the transport of CRealLt via Rasbt, Rrepr,
   so it is linear as CRealLt. *)
Lemma RisLinearOrder : isLinearOrder Rlt.
Proof.
  split. 1:split.
  - intros. exact (Rlt_asym _ _ H H0).
  - intros. exact (Rlt_trans _ _ _ H H0).
  - intros. destruct (total_order_T x y).
    + destruct s.
      * left. exact r.
      * right. subst x. exact H.
    + right.
      exact (Rlt_trans _ x _ r H).
Qed.

Lemma RdisjunctEpsilon
  : forall a b c d : R, (a < b)%R \/ (c < d)%R -> (a < b)%R + (c < d)%R.
Proof.
  intros. destruct (total_order_T a b).
  - destruct s.
    + left. exact r.
    + right. destruct H.
      * exfalso. subst a. exact (Rlt_asym b b H H).
      * exact H.
  - right. destruct H.
    + exfalso. exact (Rlt_asym _ _ H r).
    + exact H.
Qed.

(* The constructive equality on R. *)
Definition Req_constr (x y : R) : Prop
  := (x < y -> False) /\ (y < x -> False).

Lemma Req_constr_refl : forall x:R, Req_constr x x.
Proof.
  split.
  - intro H. exact (Rlt_asym _ _ H H).
  - intro H. exact (Rlt_asym _ _ H H).
Qed.

Lemma Req_constr_leibniz : forall x y:R, Req_constr x y -> x = y.
Proof.
  intros. destruct (total_order_T x y). 1:destruct s.
  - exfalso. destruct H. contradiction.
  - exact e.
  - exfalso. destruct H. contradiction.
Qed.

Definition IQR (q : Q) := Rabst (inject_Q q).

Lemma IQR_zero_quot : Req_constr (IQR 0) R0.
Proof.
  unfold IQR. rewrite R0_def. apply Req_constr_refl.
Qed.

(* Not RealField.RTheory, because it uses Leibniz equality. *)
Lemma Rring : ring_theory (IQR 0) (IQR 1) Rplus Rmult
                          (fun x y : R => (x + - y)%R) Ropp Req_constr.
Proof.
  split.
  - intro x. replace (IQR 0 + x) with x.
    + apply Req_constr_refl.
    + apply Rquot1. rewrite Rrepr_plus. unfold IQR. rewrite Rquot2.
      rewrite CReal_plus_0_l. reflexivity.
  - intros. replace (x + y) with (y + x).
    + apply Req_constr_refl.
    + apply Rquot1. do 2 rewrite Rrepr_plus. apply CReal_plus_comm.
  - intros. replace (x + (y + z)) with (x + y + z).
    + apply Req_constr_refl.
    + apply Rquot1.
      do 4 rewrite Rrepr_plus. apply CReal_plus_assoc.
  - intro x. replace (IQR 1 * x) with x.
    + apply Req_constr_refl.
    + unfold IQR.
      apply Rquot1. rewrite Rrepr_mult, Rquot2, CReal_mult_1_l. reflexivity.
  - intros. replace (x * y) with (y * x).
    + apply Req_constr_refl.
    + apply Rquot1. do 2 rewrite Rrepr_mult. apply CReal_mult_comm.
  - intros. replace (x * (y * z)) with (x * y * z).
    + apply Req_constr_refl.
    + apply Rquot1.
      do 4 rewrite Rrepr_mult. apply CReal_mult_assoc.
  - intros. replace ((x + y) * z) with (x * z + y * z).
    + apply Req_constr_refl.
    + apply Rquot1.
      rewrite Rrepr_mult, Rrepr_plus, Rrepr_plus, Rrepr_mult, Rrepr_mult.
      symmetry. apply CReal_mult_plus_distr_r.
  - intros. apply Req_constr_refl.
  - intros. replace (x + - x) with R0.
    + unfold IQR.
      rewrite R0_def. apply Req_constr_refl.
    + apply Rquot1. rewrite Rrepr_plus, Rrepr_opp, CReal_plus_opp_r, Rrepr_0.
      reflexivity.
Qed.

Lemma RringExt : ring_eq_ext Rplus Rmult Ropp Req_constr.
Proof.
  split.
  - intros x y H z t H0. apply Req_constr_leibniz in H.
    apply Req_constr_leibniz in H0. destruct H, H0. apply Req_constr_refl.
  - intros x y H z t H0. apply Req_constr_leibniz in H.
    apply Req_constr_leibniz in H0. destruct H, H0. apply Req_constr_refl.
  - intros x y H. apply Req_constr_leibniz in H. destruct H. apply Req_constr_refl.
Qed.

Lemma Rleft_inverse :
  forall r : R, (sum (r < IQR 0) (IQR 0 < r)) -> Req_constr (/ r * r) (IQR 1).
Proof.
  intros. rewrite Rinv_l.
  - unfold IQR. rewrite <- R1_def. apply Req_constr_refl.
  - destruct H.
    + intro abs. subst r. unfold IQR in r0. rewrite <- R0_def in r0.
      apply (Rlt_asym _ _ r0 r0).
    + intro abs. subst r. unfold IQR in r0. rewrite <- R0_def in r0.
      apply (Rlt_asym _ _ r0 r0).
Qed.

Lemma Rinv_pos : forall r : R, (sum (r < IQR 0) (IQR 0 < r)) -> IQR 0 < r -> IQR 0 < / r.
Proof.
  intros. rewrite Rlt_def. apply CRealLtForget.
  rewrite Rlt_def in H0. apply CRealLtEpsilon in H0.
  unfold IQR in H0. rewrite Rquot2 in H0.
  rewrite (Rrepr_inv r (inr H0)). unfold IQR. rewrite Rquot2.
  apply CReal_inv_0_lt_compat, H0.
Qed.

Lemma Rmult_pos : forall x y : R, IQR 0 < x -> IQR 0 < y -> IQR 0 < x * y.
Proof.
  intros. rewrite Rlt_def. apply CRealLtForget.
  unfold IQR. rewrite Rquot2.
  rewrite Rrepr_mult. apply CReal_mult_lt_0_compat.
  - rewrite Rlt_def in H. apply CRealLtEpsilon in H.
    unfold IQR in H. rewrite Rquot2 in H. exact H.
  - unfold IQR in H0. rewrite Rlt_def in H0. apply CRealLtEpsilon in H0.
    rewrite Rquot2 in H0. exact H0.
Qed.

Lemma Rplus_reg_l : forall r r1 r2, r + r1 < r + r2 -> r1 < r2.
Proof.
  intros. rewrite Rlt_def in H. apply CRealLtEpsilon in H.
  rewrite Rrepr_plus, Rrepr_plus in H.
  apply CReal_plus_lt_reg_l in H. rewrite Rlt_def.
  apply CRealLtForget. exact H.
Qed.

Lemma Rzero_lt_one : IQR 0 < IQR 1.
Proof.
  rewrite Rlt_def. apply CRealLtForget.
  unfold IQR. rewrite Rquot2, Rquot2.
  apply CRealLt_0_1.
Qed.

Lemma plus_IQR : forall q r : Q,
    IQR (q + r) = IQR q + IQR r.
Proof.
  intros. unfold IQR. apply Rquot1.
  rewrite Rquot2, Rrepr_plus, Rquot2, Rquot2. apply inject_Q_plus.
Qed.

Lemma mult_IQR : forall q r : Q,
    IQR (q * r) = IQR q * IQR r.
Proof.
  intros. unfold IQR. apply Rquot1.
  rewrite Rquot2, Rrepr_mult, Rquot2, Rquot2. apply inject_Q_mult.
Qed.

Lemma IQR_lt : forall n m:Q, (n < m)%Q -> IQR n < IQR m.
Proof.
  intros. rewrite Rlt_def. apply CRealLtForget.
  unfold IQR. rewrite Rquot2, Rquot2. apply inject_Q_lt, H.
Qed.

Lemma lt_IQR : forall n m:Q, IQR n < IQR m -> (n < m)%Q.
Proof.
  intros. rewrite Rlt_def in H. apply CRealLtEpsilon in H.
  unfold IQR in H. rewrite Rquot2, Rquot2 in H.
  apply lt_inject_Q, H.
Qed.

Lemma IQR_plus_quot : forall q r : Q, Req_constr (IQR (q + r)) (IQR q + IQR r).
Proof.
  intros. rewrite plus_IQR. apply Req_constr_refl.
Qed.

Lemma IQR_mult_quot : forall q r : Q, Req_constr (IQR (q * r)) (IQR q * IQR r).
Proof.
  intros. rewrite mult_IQR. apply Req_constr_refl.
Qed.

Lemma Rabove_pos : forall x : R, {n : positive & x < IQR (Z.pos n # 1)}.
Proof.
  intros. destruct (Rup_nat (Rrepr x)) as [n nmaj].
  exists (Pos.of_nat n). unfold IQR. rewrite Rlt_def, Rquot2.
  apply CRealLtForget. apply (CReal_lt_le_trans _ _ _ nmaj).
  apply inject_Q_le. unfold Qle, Qnum, Qden.
  do 2 rewrite Z.mul_1_r. destruct n.
  - discriminate.
  - rewrite <- positive_nat_Z. rewrite Nat2Pos.id.
    + apply Z.le_refl.
    + discriminate.
Qed.

Lemma Rarchimedean : forall x y : R, x < y -> {q : Q & ((x < IQR q) * (IQR q < y))%type}.
Proof.
  intros. rewrite Rlt_def in H. apply CRealLtEpsilon in H.
  apply CRealQ_dense in H. destruct H as [q [H2 H3]].
  exists q. split.
  - rewrite Rlt_def. apply CRealLtForget.
    unfold IQR. rewrite Rquot2. exact H2.
  - rewrite Rlt_def. apply CRealLtForget.
    unfold IQR. rewrite Rquot2. exact H3.
Qed.

Lemma RabsLUB : forall x y : R, (y < x -> False) /\ (y < - x -> False) <-> (y < Rabst (CReal_abs (Rrepr x)) -> False).
Proof.
  split.
  - intros. rewrite Rlt_def in H0.
    apply CRealLtEpsilon in H0. rewrite Rquot2 in H0.
    destruct H. apply (CReal_abs_le (Rrepr x) (Rrepr y)). 2: exact H0.
    split.
    + apply (CReal_plus_le_reg_l (Rrepr y - Rrepr x)).
      ring_simplify. intro abs2. apply H1. rewrite Rlt_def.
      apply CRealLtForget. rewrite Rrepr_opp. exact abs2.
    + intro abs2. apply H. rewrite Rlt_def.
      apply CRealLtForget. exact abs2.
  - intros. split.
    + intro abs. apply H.
      rewrite Rlt_def. apply CRealLtForget. rewrite Rquot2.
      rewrite Rlt_def in abs. apply CRealLtEpsilon in abs.
      apply (CReal_lt_le_trans _ _ _ abs). apply CReal_le_abs.
    + intro abs. apply H.
      rewrite Rlt_def. apply CRealLtForget. rewrite Rquot2.
      rewrite Rlt_def in abs. apply CRealLtEpsilon in abs.
      apply (CReal_lt_le_trans _ _ _ abs).
      rewrite <- CReal_abs_opp, Rrepr_opp. apply CReal_le_abs.
Qed.

Lemma Rcomplete : forall xn : nat -> R,
  (forall p : positive,
   {n : nat |
   forall i j : nat,
   (n <= i)%nat -> (n <= j)%nat -> IQR (1 # p) < Rabst (CReal_abs (Rrepr (xn i + - xn j))) -> False}) ->
  {l : R &
  forall p : positive,
  {n : nat |
  forall i : nat, (n <= i)%nat -> IQR (1 # p) < Rabst (CReal_abs (Rrepr (xn i + - l))) -> False}}.
Proof.
  intros. destruct (Rcauchy_complete (fun n => Rrepr (xn n))) as [l llim].
  - intro p. specialize (H p) as [n nmaj]. exists n. intros.
    specialize (nmaj i j H H0). unfold IQR in nmaj.
    intro abs. apply nmaj. rewrite Rlt_def. apply CRealLtForget.
    rewrite Rquot2, Rquot2. apply (CReal_lt_le_trans _ _ _ abs).
    rewrite Rrepr_plus, Rrepr_opp. apply CRealLe_refl.
  - exists (Rabst l). intros. specialize (llim p) as [n nmaj].
    exists n. intros. specialize (nmaj i H0).
    unfold IQR in H1. apply nmaj. rewrite Rlt_def in H1.
    apply CRealLtEpsilon in H1. rewrite Rquot2, Rquot2 in H1.
    apply (CReal_lt_le_trans _ _ _ H1).
    rewrite Rrepr_plus, Rrepr_opp, Rquot2. apply CRealLe_refl.
Qed.

Definition Rabs_quot (x : R) := Rabst (CReal_abs (Rrepr x)).
Definition Rinv_quot (x : R) (xnz : sum (x < IQR 0) (IQR 0 < x)) := Rinv x.
Definition Rlt_epsilon (x y : R) (H : x < y) := H.

Definition DRealConstructive : ConstructiveReals
  := Build_ConstructiveReals
       R Rlt RisLinearOrder Rlt
       Rlt_epsilon Rlt_epsilon
       RdisjunctEpsilon IQR IQR_lt lt_IQR
       Rplus Ropp Rmult
       IQR_plus_quot IQR_mult_quot
       Rring RringExt Rzero_lt_one
       Rplus_lt_compat_l Rplus_reg_l Rmult_pos
       Rinv_quot Rleft_inverse Rinv_pos
       Rarchimedean Rabove_pos
       Rabs_quot RabsLUB Rcomplete.

Definition Rrepr_morphism
  : @ConstructiveRealsMorphism DRealConstructive CRealConstructive.
Proof.
  apply (Build_ConstructiveRealsMorphism
           DRealConstructive CRealConstructive Rrepr).
  - intro q. simpl. unfold IQR. rewrite Rquot2. apply CRealEq_refl.
  - intros. simpl. simpl in H. rewrite Rlt_def in H.
    apply CRealLtEpsilon in H. exact H.
Defined.

Definition Rabst_morphism
  : @ConstructiveRealsMorphism CRealConstructive DRealConstructive.
Proof.
  apply (Build_ConstructiveRealsMorphism
           CRealConstructive DRealConstructive Rabst).
  - intro q. apply Req_constr_refl.
  - intros. simpl. simpl in H. rewrite Rlt_def.
    apply CRealLtForget. rewrite Rquot2, Rquot2. exact H.
Defined.

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*********************************************************)
(**    Lifts of basic operations for classical reals     *)
(*********************************************************)

Require Export ZArith_base.
Require Import ConstructiveCauchyReals.
Require Export Rdefinitions.
Declare Scope R_scope.
Local Open Scope R_scope.

(*********************************************************)
(** *            Field operations                        *)
(*********************************************************)

(*********************************************************)
(** **   Addition                                        *)
(*********************************************************)

Lemma Rrepr_0 : (Rrepr 0 == 0)%CReal.
Proof.
  intros. unfold IZR. rewrite RbaseSymbolsImpl.R0_def, (Rquot2 0). reflexivity.
Qed.

Lemma Rrepr_1 : (Rrepr 1 == 1)%CReal.
Proof.
  intros. unfold IZR, IPR. rewrite RbaseSymbolsImpl.R1_def, (Rquot2 1). reflexivity.
Qed.

Lemma Rrepr_plus : forall x y:R, (Rrepr (x + y) == Rrepr x + Rrepr y)%CReal.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rplus_def, Rquot2. reflexivity.
Qed.

Lemma Rrepr_opp : forall x:R, (Rrepr (- x) == - Rrepr x)%CReal.
Proof.
  intros. rewrite RbaseSymbolsImpl.Ropp_def, Rquot2. reflexivity.
Qed.

Lemma Rrepr_minus : forall x y:R, (Rrepr (x - y) == Rrepr x - Rrepr y)%CReal.
Proof.
  intros. unfold Rminus, CReal_minus.
  rewrite Rrepr_plus, Rrepr_opp. reflexivity.
Qed.

Lemma Rrepr_mult : forall x y:R, (Rrepr (x * y) == Rrepr x * Rrepr y)%CReal.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rmult_def. rewrite Rquot2. reflexivity.
Qed.

Lemma Rrepr_inv : forall (x:R) (xnz : (Rrepr x # 0)%CReal),
    (Rrepr (/ x) == (/ Rrepr x) xnz)%CReal.
Proof.
  intros. rewrite RinvImpl.Rinv_def. destruct (Req_appart_dec x R0).
  - exfalso. subst x. destruct xnz.
    rewrite Rrepr_0 in H. exact (CRealLt_irrefl 0 H).
    rewrite Rrepr_0 in H. exact (CRealLt_irrefl 0 H).
  - rewrite Rquot2. apply (CReal_mult_eq_reg_l (Rrepr x) _ _ xnz).
    rewrite CReal_mult_comm, (CReal_mult_comm (Rrepr x)), CReal_inv_l, CReal_inv_l.
    reflexivity.
Qed.

Lemma Rrepr_le : forall x y:R, x <= y <-> (Rrepr x <= Rrepr y)%CReal.
Proof.
  split.
  - intros [H|H] abs. rewrite RbaseSymbolsImpl.Rlt_def in H.
    exact (CRealLt_asym (Rrepr x) (Rrepr y) H abs).
    destruct H. exact (CRealLt_asym (Rrepr x) (Rrepr x) abs abs).
  - intros. destruct (total_order_T x y). destruct s.
    left. exact r. right. exact e. rewrite RbaseSymbolsImpl.Rlt_def in r. contradiction.
Qed.

Lemma Rrepr_appart : forall x y:R, x <> y <-> (Rrepr x # Rrepr y)%CReal.
Proof.
  split.
  - intros. destruct (total_order_T x y). destruct s.
    left. rewrite RbaseSymbolsImpl.Rlt_def in r. exact r. contradiction.
    right. rewrite RbaseSymbolsImpl.Rlt_def in r. exact r.
  - intros [H|H] abs.
    destruct abs. exact (CRealLt_asym (Rrepr x) (Rrepr x) H H).
    destruct abs. exact (CRealLt_asym (Rrepr x) (Rrepr x) H H).
Qed.


(**********)
Lemma Rplus_comm : forall r1 r2:R, r1 + r2 = r2 + r1.
Proof.
  intros. apply Rquot1. do 2 rewrite Rrepr_plus. apply CReal_plus_comm.
Qed.
Hint Resolve Rplus_comm: real.

(**********)
Lemma Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
Proof.
  intros. apply Rquot1. repeat rewrite Rrepr_plus.
  apply CReal_plus_assoc.
Qed.
Hint Resolve Rplus_assoc: real.

(**********)
Lemma Rplus_opp_r : forall r:R, r + - r = 0.
Proof.
  intros. apply Rquot1. rewrite Rrepr_plus, Rrepr_opp, Rrepr_0.
  apply CReal_plus_opp_r.
Qed.
Hint Resolve Rplus_opp_r: real.

(**********)
Lemma Rplus_0_l : forall r:R, 0 + r = r.
Proof.
  intros. apply Rquot1. rewrite Rrepr_plus, Rrepr_0.
  apply CReal_plus_0_l.
Qed.
Hint Resolve Rplus_0_l: real.

(***********************************************************)
(** **    Multiplication                                   *)
(***********************************************************)

(**********)
Lemma Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
Proof.
  intros. apply Rquot1. do 2 rewrite Rrepr_mult. apply CReal_mult_comm.
Qed.
Hint Resolve Rmult_comm: real.

(**********)
Lemma Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
Proof.
  intros. apply Rquot1. repeat rewrite Rrepr_mult.
  apply CReal_mult_assoc.
Qed.
Hint Resolve Rmult_assoc: real.

(**********)
Lemma Rinv_l : forall r:R, r <> 0 -> / r * r = 1.
Proof.
  intros. rewrite RinvImpl.Rinv_def; destruct (Req_appart_dec r R0).
  - contradiction.
  - apply Rquot1. rewrite Rrepr_mult, Rquot2, Rrepr_1. apply CReal_inv_l.
Qed.
Hint Resolve Rinv_l: real.

(**********)
Lemma Rmult_1_l : forall r:R, 1 * r = r.
Proof.
  intros. apply Rquot1. rewrite Rrepr_mult, Rrepr_1.
  apply CReal_mult_1_l.
Qed.
Hint Resolve Rmult_1_l: real.

(**********)
Lemma R1_neq_R0 : 1 <> 0.
Proof.
  intro abs.
  assert (1 == 0)%CReal.
  { transitivity (Rrepr 1). symmetry.
    replace 1 with (Rabst 1). 2: unfold IZR,IPR; rewrite RbaseSymbolsImpl.R1_def; reflexivity.
    rewrite Rquot2. reflexivity. transitivity (Rrepr 0).
    rewrite abs. reflexivity.
    replace 0 with (Rabst 0).
    2: unfold IZR; rewrite RbaseSymbolsImpl.R0_def; reflexivity.
    rewrite Rquot2. reflexivity. }
  pose proof (CRealLt_morph 0 0 (CRealEq_refl _) 1 0 H).
  apply (CRealLt_irrefl 0). apply H0. apply CRealLt_0_1.
Qed.
Hint Resolve R1_neq_R0: real.

(*********************************************************)
(** **   Distributivity                                  *)
(*********************************************************)

(**********)
Lemma
  Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.
Proof.
  intros. apply Rquot1.
  rewrite Rrepr_mult, Rrepr_plus, Rrepr_plus, Rrepr_mult, Rrepr_mult.
  apply CReal_mult_plus_distr_l.
Qed.
Hint Resolve Rmult_plus_distr_l: real.

(*********************************************************)
(** *    Order                                           *)
(*********************************************************)

(*********************************************************)
(** **   Lower                                           *)
(*********************************************************)

(**********)
Lemma Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.
Proof.
  intros. intro abs. rewrite RbaseSymbolsImpl.Rlt_def in H, abs.
  apply (CRealLt_asym (Rrepr r1) (Rrepr r2)); assumption.
Qed.

(**********)
Lemma Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rlt_def. rewrite RbaseSymbolsImpl.Rlt_def in H, H0.
  apply (CRealLt_trans (Rrepr r1) (Rrepr r2) (Rrepr r3)); assumption.
Qed.

(**********)
Lemma Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rlt_def. rewrite RbaseSymbolsImpl.Rlt_def in H.
  do 2 rewrite Rrepr_plus. apply CReal_plus_lt_compat_l. exact H.
Qed.

(**********)
Lemma Rmult_lt_compat_l : forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rlt_def. rewrite RbaseSymbolsImpl.Rlt_def in H.
  do 2 rewrite Rrepr_mult. apply CReal_mult_lt_compat_l.
  rewrite <- (Rquot2 0). unfold IZR in H. rewrite RbaseSymbolsImpl.R0_def in H. exact H.
  rewrite RbaseSymbolsImpl.Rlt_def in H0. exact H0.
Qed.

Hint Resolve Rlt_asym Rplus_lt_compat_l Rmult_lt_compat_l: real.

(**********************************************************)
(** *    Injection from N to R                            *)
(**********************************************************)

(**********)
Fixpoint INR (n:nat) : R :=
  match n with
  | O => 0
  | S O => 1
  | S n => INR n + 1
  end.
Arguments INR n%nat.

(**********************************************************)
(** *    [R] Archimedean                                  *)
(**********************************************************)

Lemma Rrepr_INR : forall n : nat,
    (Rrepr (INR n) == ConstructiveCauchyReals.INR n)%CReal.
Proof.
  induction n.
  - apply Rrepr_0.
  - simpl. destruct n. apply Rrepr_1.
    rewrite Rrepr_plus, <- IHn, Rrepr_1. reflexivity.
Qed.

Lemma Rrepr_IPR2 : forall n : positive,
    (Rrepr (IPR_2 n) == ConstructiveCauchyReals.IPR_2 n)%CReal.
Proof.
  induction n.
  - unfold IPR_2, ConstructiveCauchyReals.IPR_2.
    rewrite RbaseSymbolsImpl.R1_def, Rrepr_mult, Rrepr_plus, Rrepr_plus, <- IHn.
    unfold IPR_2.
    rewrite Rquot2. rewrite RbaseSymbolsImpl.R1_def. reflexivity.
  - unfold IPR_2, ConstructiveCauchyReals.IPR_2.
    rewrite Rrepr_mult, Rrepr_plus, <- IHn.
    rewrite RbaseSymbolsImpl.R1_def. rewrite Rquot2.
    unfold IPR_2. rewrite RbaseSymbolsImpl.R1_def. reflexivity.
  - unfold IPR_2, ConstructiveCauchyReals.IPR_2.
    rewrite RbaseSymbolsImpl.R1_def.
    rewrite Rrepr_plus, Rquot2. reflexivity.
Qed.

Lemma Rrepr_IPR : forall n : positive,
    (Rrepr (IPR n) == ConstructiveCauchyReals.IPR n)%CReal.
Proof.
  intro n. destruct n.
  - unfold IPR, ConstructiveCauchyReals.IPR.
    rewrite Rrepr_plus, <- Rrepr_IPR2.
    rewrite RbaseSymbolsImpl.R1_def. rewrite Rquot2. reflexivity.
  - unfold IPR, ConstructiveCauchyReals.IPR.
    apply Rrepr_IPR2.
  - unfold IPR. rewrite RbaseSymbolsImpl.R1_def. apply Rquot2.
Qed.

Lemma Rrepr_IZR : forall n : Z,
    (Rrepr (IZR n) == ConstructiveCauchyReals.IZR n)%CReal.
Proof.
  intros [|p|n].
  - unfold IZR. rewrite RbaseSymbolsImpl.R0_def. apply Rquot2.
  - apply Rrepr_IPR.
  - unfold IZR, ConstructiveCauchyReals.IZR.
    rewrite <- Rrepr_IPR, Rrepr_opp. reflexivity.
Qed.

(**********)
Lemma archimed : forall r:R, IZR (up r) > r /\ IZR (up r) - r <= 1.
Proof.
  intro r. unfold up.
  destruct (Rarchimedean (Rrepr r)) as [n nmaj], (total_order_T (IZR n - r) R1).
  destruct s.
  - split. unfold Rgt. rewrite RbaseSymbolsImpl.Rlt_def. rewrite Rrepr_IZR. apply nmaj.
    unfold Rle. left. exact r0.
  - split. unfold Rgt. rewrite RbaseSymbolsImpl.Rlt_def. rewrite Rrepr_IZR. apply nmaj.
    right. exact e.
  - split.
    + unfold Rgt, Z.pred. rewrite RbaseSymbolsImpl.Rlt_def. rewrite Rrepr_IZR, plus_IZR.
      rewrite RbaseSymbolsImpl.Rlt_def in r0. rewrite Rrepr_minus in r0.
      rewrite <- (Rrepr_IZR n).
      unfold ConstructiveCauchyReals.IZR, ConstructiveCauchyReals.IPR.
      apply (CReal_plus_lt_compat_l (Rrepr r - Rrepr R1)) in r0.
      ring_simplify in r0. rewrite RbaseSymbolsImpl.R1_def in r0. rewrite Rquot2 in r0.
      rewrite CReal_plus_comm. exact r0.
    + destruct (total_order_T (IZR (Z.pred n) - r) 1). destruct s.
      left. exact r1. right. exact e.
      exfalso. rewrite <- Rrepr_IZR in nmaj.
      apply (Rlt_asym (IZR n) (r + 2)).
      rewrite RbaseSymbolsImpl.Rlt_def. rewrite Rrepr_plus. rewrite (Rrepr_plus 1 1).
      apply (CRealLt_Le_trans _ (Rrepr r + 2)). apply nmaj.
      unfold IZR, IPR. rewrite RbaseSymbolsImpl.R1_def, Rquot2. apply CRealLe_refl.
      clear nmaj.
      unfold Z.pred in r1. rewrite RbaseSymbolsImpl.Rlt_def in r1.
      rewrite Rrepr_minus, (Rrepr_IZR (n + -1)), plus_IZR,
      <- (Rrepr_IZR n)
        in r1.
      unfold ConstructiveCauchyReals.IZR, ConstructiveCauchyReals.IPR in r1.
      rewrite RbaseSymbolsImpl.Rlt_def, Rrepr_plus.
      apply (CReal_plus_lt_compat_l (Rrepr r + 1)) in r1.
      ring_simplify in r1.
      apply (CRealLe_Lt_trans _ (Rrepr r + Rrepr 1 + 1)). 2: apply r1.
      rewrite (Rrepr_plus 1 1). unfold IZR, IPR.
      rewrite RbaseSymbolsImpl.R1_def, (Rquot2 1), <- CReal_plus_assoc.
      apply CRealLe_refl.
Qed.

(**********************************************************)
(** *    [R] Complete                                     *)
(**********************************************************)

(**********)
Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.

(**********)
Definition bound (E:R -> Prop) :=  exists m : R, is_upper_bound E m.

(**********)
Definition is_lub (E:R -> Prop) (m:R) :=
  is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).

(**********)
(* This axiom can be proved by excluded middle in sort Set.
   For this, define a sequence by dichotomy, using excluded middle
   to know whether the current point majorates E or not.
   Then conclude by the Cauchy-completeness of R, which is proved
   constructively. *)
Axiom
  completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> { m:R | is_lub E m }.

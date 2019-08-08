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
Require Import ConstructiveRIneq.
Require Export Rdefinitions.
Declare Scope R_scope.
Local Open Scope R_scope.

(*********************************************************)
(** *            Field operations                        *)
(*********************************************************)

(*********************************************************)
(** **   Addition                                        *)
(*********************************************************)

Open Scope R_scope_constr.

Lemma Rrepr_0 : Rrepr 0 == CRzero CR.
Proof.
  intros. unfold IZR. rewrite RbaseSymbolsImpl.R0_def, (Rquot2 0). reflexivity.
Qed.

Lemma Rrepr_1 : Rrepr 1 == 1.
Proof.
  intros. unfold IZR, IPR. rewrite RbaseSymbolsImpl.R1_def, (Rquot2 1). reflexivity.
Qed.

Lemma Rrepr_plus : forall x y:R, Rrepr (x + y) == Rrepr x + Rrepr y.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rplus_def, Rquot2. reflexivity.
Qed.

Lemma Rrepr_opp : forall x:R, Rrepr (- x) == - Rrepr x.
Proof.
  intros. rewrite RbaseSymbolsImpl.Ropp_def, Rquot2. reflexivity.
Qed.

Lemma Rrepr_minus : forall x y:R, Rrepr (x - y) == Rrepr x - Rrepr y.
Proof.
  intros. unfold Rminus, CRminus.
  rewrite Rrepr_plus, Rrepr_opp. reflexivity.
Qed.

Lemma Rrepr_mult : forall x y:R, Rrepr (x * y) == Rrepr x * Rrepr y.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rmult_def. rewrite Rquot2. reflexivity.
Qed.

Lemma Rrepr_inv : forall (x:R) (xnz : Rrepr x # 0),
    Rrepr (/ x) == (/ Rrepr x) xnz.
Proof.
  intros. rewrite RinvImpl.Rinv_def. destruct (Req_appart_dec x R0).
  - exfalso. subst x. destruct xnz.
    rewrite Rrepr_0 in H. exact (Rlt_irrefl 0 H).
    rewrite Rrepr_0 in H. exact (Rlt_irrefl 0 H).
  - rewrite Rquot2. apply (Rmult_eq_reg_l (Rrepr x)). 2: exact xnz.
    rewrite Rmult_comm, (Rmult_comm (Rrepr x)), Rinv_l, Rinv_l.
    reflexivity.
Qed.

Lemma Rrepr_le : forall x y:R, (x <= y)%R <-> Rrepr x <= Rrepr y.
Proof.
  split.
  - intros [H|H] abs. rewrite RbaseSymbolsImpl.Rlt_def in H.
    exact (Rlt_asym (Rrepr x) (Rrepr y) H abs).
    destruct H. exact (Rlt_asym (Rrepr x) (Rrepr x) abs abs).
  - intros. destruct (total_order_T x y). destruct s.
    left. exact r. right. exact e. rewrite RbaseSymbolsImpl.Rlt_def in r. contradiction.
Qed.

Lemma Rrepr_appart : forall x y:R, (x <> y)%R <-> Rrepr x # Rrepr y.
Proof.
  split.
  - intros. destruct (total_order_T x y). destruct s.
    left. rewrite RbaseSymbolsImpl.Rlt_def in r. exact r. contradiction.
    right. rewrite RbaseSymbolsImpl.Rlt_def in r. exact r.
  - intros [H|H] abs.
    destruct abs. exact (Rlt_asym (Rrepr x) (Rrepr x) H H).
    destruct abs. exact (Rlt_asym (Rrepr x) (Rrepr x) H H).
Qed.

Close Scope R_scope_constr.


(**********)
Lemma Rplus_comm : forall r1 r2:R, r1 + r2 = r2 + r1.
Proof.
  intros. apply Rquot1. do 2 rewrite Rrepr_plus. apply Rplus_comm.
Qed.
Hint Resolve Rplus_comm: real.

(**********)
Lemma Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
Proof.
  intros. apply Rquot1. repeat rewrite Rrepr_plus.
  apply Rplus_assoc.
Qed.
Hint Resolve Rplus_assoc: real.

(**********)
Lemma Rplus_opp_r : forall r:R, r + - r = 0.
Proof.
  intros. apply Rquot1. rewrite Rrepr_plus, Rrepr_opp, Rrepr_0.
  apply Rplus_opp_r.
Qed.
Hint Resolve Rplus_opp_r: real.

(**********)
Lemma Rplus_0_l : forall r:R, 0 + r = r.
Proof.
  intros. apply Rquot1. rewrite Rrepr_plus, Rrepr_0.
  apply Rplus_0_l.
Qed.
Hint Resolve Rplus_0_l: real.

(***********************************************************)
(** **    Multiplication                                   *)
(***********************************************************)

(**********)
Lemma Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
Proof.
  intros. apply Rquot1. do 2 rewrite Rrepr_mult. apply Rmult_comm.
Qed.
Hint Resolve Rmult_comm: real.

(**********)
Lemma Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
Proof.
  intros. apply Rquot1. repeat rewrite Rrepr_mult.
  apply Rmult_assoc.
Qed.
Hint Resolve Rmult_assoc: real.

(**********)
Lemma Rinv_l : forall r:R, r <> 0 -> / r * r = 1.
Proof.
  intros. rewrite RinvImpl.Rinv_def; destruct (Req_appart_dec r R0).
  - contradiction.
  - apply Rquot1. rewrite Rrepr_mult, Rquot2, Rrepr_1. apply Rinv_l.
Qed.
Hint Resolve Rinv_l: real.

(**********)
Lemma Rmult_1_l : forall r:R, 1 * r = r.
Proof.
  intros. apply Rquot1. rewrite Rrepr_mult, Rrepr_1.
  apply Rmult_1_l.
Qed.
Hint Resolve Rmult_1_l: real.

(**********)
Lemma R1_neq_R0 : 1 <> 0.
Proof.
  intro abs.
  assert (Req (CRone CR) (CRzero CR)).
  { transitivity (Rrepr 1). symmetry.
    replace 1%R with (Rabst (CRone CR)).
    2: unfold IZR,IPR; rewrite RbaseSymbolsImpl.R1_def; reflexivity.
    rewrite Rquot2. reflexivity. transitivity (Rrepr 0).
    rewrite abs. reflexivity.
    replace 0%R with (Rabst (CRzero CR)).
    2: unfold IZR; rewrite RbaseSymbolsImpl.R0_def; reflexivity.
    rewrite Rquot2. reflexivity. }
  pose proof (Rlt_morph (CRzero CR) (CRzero CR) (Req_refl _) (CRone CR) (CRzero CR) H).
  apply (Rlt_irrefl (CRzero CR)). apply H0. apply Rlt_0_1.
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
  apply Rmult_plus_distr_l.
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
  apply (Rlt_asym (Rrepr r1) (Rrepr r2)); assumption.
Qed.

(**********)
Lemma Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rlt_def. rewrite RbaseSymbolsImpl.Rlt_def in H, H0.
  apply (Rlt_trans (Rrepr r1) (Rrepr r2) (Rrepr r3)); assumption.
Qed.

(**********)
Lemma Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rlt_def. rewrite RbaseSymbolsImpl.Rlt_def in H.
  do 2 rewrite Rrepr_plus. apply Rplus_lt_compat_l. exact H.
Qed.

(**********)
Lemma Rmult_lt_compat_l : forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rlt_def. rewrite RbaseSymbolsImpl.Rlt_def in H.
  do 2 rewrite Rrepr_mult. apply Rmult_lt_compat_l.
  rewrite <- (Rquot2 (CRzero CR)). unfold IZR in H. rewrite RbaseSymbolsImpl.R0_def in H. exact H.
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
    Req (Rrepr (INR n)) (ConstructiveRIneq.INR n).
Proof.
  induction n.
  - apply Rrepr_0.
  - simpl. destruct n. apply Rrepr_1.
    rewrite Rrepr_plus, <- IHn, Rrepr_1. reflexivity.
Qed.

Lemma Rrepr_IPR2 : forall n : positive,
    Req (Rrepr (IPR_2 n)) (ConstructiveRIneq.IPR_2 n).
Proof.
  induction n.
  - unfold IPR_2, ConstructiveRIneq.IPR_2.
    rewrite RbaseSymbolsImpl.R1_def, Rrepr_mult, Rrepr_plus, Rrepr_plus, <- IHn.
    unfold IPR_2.
    rewrite Rquot2. rewrite RbaseSymbolsImpl.R1_def. reflexivity.
  - unfold IPR_2, ConstructiveRIneq.IPR_2.
    rewrite Rrepr_mult, Rrepr_plus, <- IHn.
    rewrite RbaseSymbolsImpl.R1_def. rewrite Rquot2.
    unfold IPR_2. rewrite RbaseSymbolsImpl.R1_def. reflexivity.
  - unfold IPR_2, ConstructiveRIneq.IPR_2.
    rewrite RbaseSymbolsImpl.R1_def.
    rewrite Rrepr_plus, Rquot2. reflexivity.
Qed.

Lemma Rrepr_IPR : forall n : positive,
    Req (Rrepr (IPR n)) (ConstructiveRIneq.IPR n).
Proof.
  intro n. destruct n.
  - unfold IPR, ConstructiveRIneq.IPR.
    rewrite Rrepr_plus, <- Rrepr_IPR2.
    rewrite RbaseSymbolsImpl.R1_def. rewrite Rquot2. reflexivity.
  - unfold IPR, ConstructiveRIneq.IPR.
    apply Rrepr_IPR2.
  - unfold IPR. rewrite RbaseSymbolsImpl.R1_def. apply Rquot2.
Qed.

Lemma Rrepr_IZR : forall n : Z,
    Req (Rrepr (IZR n)) (ConstructiveRIneq.IZR n).
Proof.
  intros [|p|n].
  - unfold IZR. rewrite RbaseSymbolsImpl.R0_def. apply Rquot2.
  - apply Rrepr_IPR.
  - unfold IZR, ConstructiveRIneq.IZR.
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
      unfold ConstructiveRIneq.IZR, ConstructiveRIneq.IPR.
      apply (ConstructiveRIneq.Rplus_lt_compat_l (ConstructiveRIneq.Rminus (Rrepr r) (Rrepr R1)))
        in r0.
      ring_simplify in r0. rewrite RbaseSymbolsImpl.R1_def in r0. rewrite Rquot2 in r0.
      rewrite ConstructiveRIneq.Rplus_comm. exact r0.
    + destruct (total_order_T (IZR (Z.pred n) - r) 1). destruct s.
      left. exact r1. right. exact e.
      exfalso. rewrite <- Rrepr_IZR in nmaj.
      apply (Rlt_asym (IZR n) (r + 2)).
      rewrite RbaseSymbolsImpl.Rlt_def. rewrite Rrepr_plus. rewrite (Rrepr_plus 1 1).
      apply (ConstructiveRIneq.Rlt_le_trans
               _ (ConstructiveRIneq.Rplus (Rrepr r) (ConstructiveRIneq.IZR 2))).
      apply nmaj.
      unfold IZR, IPR. rewrite RbaseSymbolsImpl.R1_def, Rquot2. apply Rle_refl.
      clear nmaj.
      unfold Z.pred in r1. rewrite RbaseSymbolsImpl.Rlt_def in r1.
      rewrite Rrepr_minus, (Rrepr_IZR (n + -1)), plus_IZR,
      <- (Rrepr_IZR n)
        in r1.
      unfold ConstructiveRIneq.IZR, ConstructiveRIneq.IPR in r1.
      rewrite RbaseSymbolsImpl.Rlt_def, Rrepr_plus.
      apply (ConstructiveRIneq.Rplus_lt_compat_l
               (ConstructiveRIneq.Rplus (Rrepr r) (CRone CR))) in r1.
      ring_simplify in r1.
      apply (ConstructiveRIneq.Rle_lt_trans
               _ (ConstructiveRIneq.Rplus (ConstructiveRIneq.Rplus (Rrepr r) (Rrepr 1)) (CRone CR))).
      2: apply r1.
      rewrite (Rrepr_plus 1 1). unfold IZR, IPR.
      rewrite RbaseSymbolsImpl.R1_def, (Rquot2 (CRone CR)), <- ConstructiveRIneq.Rplus_assoc.
      apply Rle_refl.
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
Lemma completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> { m:R | is_lub E m }.
Proof.
  intros. pose (fun x:ConstructiveRIneq.R => E (Rabst x)) as Er.
  assert (exists x : ConstructiveRIneq.R, Er x) as Einhab.
  { destruct H0. exists (Rrepr x). unfold Er.
    replace (Rabst (Rrepr x)) with x. exact H0.
    apply Rquot1. rewrite Rquot2. reflexivity. }
  assert (exists x : ConstructiveRIneq.R,
             (forall y:ConstructiveRIneq.R, Er y -> ConstructiveRIneq.Rle y x))
    as Ebound.
  { destruct H. exists (Rrepr x). intros y Ey. rewrite <- (Rquot2 y).
    apply Rrepr_le. apply H. exact Ey. }
  destruct (CR_sig_lub CR
              Er sig_forall_dec sig_not_dec Einhab Ebound).
  exists (Rabst x). split.
  intros y Ey. apply Rrepr_le. rewrite Rquot2. apply a.
  unfold Er. replace (Rabst (Rrepr y)) with y. exact Ey.
  apply Rquot1. rewrite Rquot2. reflexivity.
  intros. destruct a. apply Rrepr_le. rewrite Rquot2.
  apply H3. intros y Ey. rewrite <- (Rquot2 y).
  apply Rrepr_le, H1, Ey.
Qed.

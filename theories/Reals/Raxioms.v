(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file continues Rdefinitions, with more properties of the
   classical reals, including the existence of least upper bounds
   for non-empty and bounded subsets.
   The name "Raxioms" and its contents are kept for backward compatibility,
   when the classical reals were axiomatized. Otherwise we would
   have merged this file into RIneq. *)

(*********************************************************)
(**    Lifts of basic operations for classical reals     *)
(*********************************************************)

Require Export BinInt.
Require Import Znat.
Require Import ClassicalDedekindReals.
Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsMult.
Require Import ConstructiveRcomplete.
Require Import ConstructiveLUB.
Require Export Rdefinitions.
Local Open Scope R_scope.

(*********************************************************)
(** *            Field operations                        *)
(*********************************************************)

(*********************************************************)
(** **   Addition                                        *)
(*********************************************************)

Open Scope CReal_scope.

Lemma Rrepr_0 : Rrepr 0 == 0.
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
  intros. unfold Rminus, CReal_minus.
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
    + rewrite Rrepr_0 in c. exact (CRealLt_irrefl 0 c).
    + rewrite Rrepr_0 in c. exact (CRealLt_irrefl 0 c).
  - rewrite Rquot2. apply (CReal_mult_eq_reg_l (Rrepr x)).
    + exact xnz.
    + rewrite CReal_mult_comm, (CReal_mult_comm (Rrepr x)), CReal_inv_l, CReal_inv_l.
      reflexivity.
Qed.

Lemma Rrepr_le : forall x y:R, (x <= y)%R <-> Rrepr x <= Rrepr y.
Proof.
  split.
  - intros [H|H] abs.
    + rewrite RbaseSymbolsImpl.Rlt_def in H.
      apply CRealLtEpsilon in H.
      exact (CRealLt_asym (Rrepr x) (Rrepr y) H abs).
    + destruct H. exact (CRealLt_asym (Rrepr x) (Rrepr x) abs abs).
  - intros. destruct (total_order_T x y).
    + destruct s.
      * left. exact r.
      * right. exact e.
    + rewrite RbaseSymbolsImpl.Rlt_def in r. apply CRealLtEpsilon in r. contradiction.
Qed.

Lemma Rrepr_appart : forall x y:R,
    (x <> y)%R -> Rrepr x # Rrepr y.
Proof.
  intros. destruct (total_order_T x y).
  - destruct s.
    + left. rewrite RbaseSymbolsImpl.Rlt_def in r.
      apply CRealLtEpsilon. exact r.
    + contradiction.
  - right. rewrite RbaseSymbolsImpl.Rlt_def in r.
    apply CRealLtEpsilon. exact r.
Qed.

Lemma Rappart_repr : forall x y:R,
    Rrepr x # Rrepr y -> (x <> y)%R.
Proof.
  intros x y [H|H] abs.
  - destruct abs. exact (CRealLt_asym (Rrepr x) (Rrepr x) H H).
  - destruct abs. exact (CRealLt_asym (Rrepr x) (Rrepr x) H H).
Qed.

Close Scope CReal_scope.


(**********)
Lemma Rplus_comm : forall r1 r2:R, r1 + r2 = r2 + r1.
Proof.
  intros. apply Rquot1. do 2 rewrite Rrepr_plus. apply CReal_plus_comm.
Qed.
#[global]
Hint Resolve Rplus_comm: real.

(**********)
Lemma Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
Proof.
  intros. apply Rquot1. repeat rewrite Rrepr_plus.
  apply CReal_plus_assoc.
Qed.
#[global]
Hint Resolve Rplus_assoc: real.

(**********)
Lemma Rplus_opp_r : forall r:R, r + - r = 0.
Proof.
  intros. apply Rquot1. rewrite Rrepr_plus, Rrepr_opp, Rrepr_0.
  apply CReal_plus_opp_r.
Qed.
#[global]
Hint Resolve Rplus_opp_r: real.

(**********)
Lemma Rplus_0_l : forall r:R, 0 + r = r.
Proof.
  intros. apply Rquot1. rewrite Rrepr_plus, Rrepr_0.
  apply CReal_plus_0_l.
Qed.
#[global]
Hint Resolve Rplus_0_l: real.

(***********************************************************)
(** **    Multiplication                                   *)
(***********************************************************)

(**********)
Lemma Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.
Proof.
  intros. apply Rquot1. do 2 rewrite Rrepr_mult. apply CReal_mult_comm.
Qed.
#[global]
Hint Resolve Rmult_comm: real.

(**********)
Lemma Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
Proof.
  intros. apply Rquot1. repeat rewrite Rrepr_mult.
  apply CReal_mult_assoc.
Qed.
#[global]
Hint Resolve Rmult_assoc: real.

(**********)
Lemma Rinv_l : forall r:R, r <> 0 -> / r * r = 1.
Proof.
  intros. rewrite RinvImpl.Rinv_def; destruct (Req_appart_dec r R0).
  - contradiction.
  - apply Rquot1. rewrite Rrepr_mult, Rquot2, Rrepr_1. apply CReal_inv_l.
Qed.
#[global]
Hint Resolve Rinv_l: real.

(**********)
Lemma Rmult_1_l : forall r:R, 1 * r = r.
Proof.
  intros. apply Rquot1. rewrite Rrepr_mult, Rrepr_1.
  apply CReal_mult_1_l.
Qed.
#[global]
Hint Resolve Rmult_1_l: real.

(**********)
Lemma R1_neq_R0 : 1 <> 0.
Proof.
  intro abs.
  assert (CRealEq 1%CReal 0%CReal).
  { transitivity (Rrepr 1).
    - symmetry.
      replace 1%R with (Rabst 1%CReal).
      2: unfold IZR,IPR; rewrite RbaseSymbolsImpl.R1_def; reflexivity.
      rewrite Rquot2. reflexivity.
    - transitivity (Rrepr 0).
      + rewrite abs. reflexivity.
      + replace 0%R with (Rabst 0%CReal).
        2: unfold IZR; rewrite RbaseSymbolsImpl.R0_def; reflexivity.
        rewrite Rquot2. reflexivity. }
  pose proof (CRealLt_morph 0%CReal 0%CReal (CRealEq_refl _) 1%CReal 0%CReal H).
  apply (CRealLt_irrefl 0%CReal). apply H0. apply CRealLt_0_1.
Qed.
#[global]
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
#[global]
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
  apply CRealLtEpsilon in H. apply CRealLtEpsilon in abs.
  apply (CRealLt_asym (Rrepr r1) (Rrepr r2)); assumption.
Qed.

(**********)
Lemma Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rlt_def. rewrite RbaseSymbolsImpl.Rlt_def in H, H0.
  apply CRealLtEpsilon in H. apply CRealLtEpsilon in H0.
  apply CRealLtForget.
  apply (CReal_lt_trans (Rrepr r1) (Rrepr r2) (Rrepr r3)); assumption.
Qed.

(**********)
Lemma Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rlt_def. rewrite RbaseSymbolsImpl.Rlt_def in H.
  do 2 rewrite Rrepr_plus. apply CRealLtForget.
  apply CReal_plus_lt_compat_l. apply CRealLtEpsilon. exact H.
Qed.

(**********)
Lemma Rmult_lt_compat_l : forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.
Proof.
  intros. rewrite RbaseSymbolsImpl.Rlt_def. rewrite RbaseSymbolsImpl.Rlt_def in H.
  do 2 rewrite Rrepr_mult. apply CRealLtForget. apply CReal_mult_lt_compat_l.
  - rewrite <- (Rquot2 0%CReal). unfold IZR in H.
    rewrite RbaseSymbolsImpl.R0_def in H. apply CRealLtEpsilon. exact H.
  -  rewrite RbaseSymbolsImpl.Rlt_def in H0. apply CRealLtEpsilon. exact H0.
Qed.

#[global]
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
Arguments INR n%_nat.

(**********************************************************)
(** *    [R] Archimedean                                  *)
(**********************************************************)

Lemma Rrepr_INR : forall n : nat,
    CRealEq (Rrepr (INR n)) (inject_Z (Z.of_nat n)).
Proof.
  induction n.
  - apply Rrepr_0.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z.
    + simpl. destruct n.
      * apply Rrepr_1.
      * rewrite Rrepr_plus,inject_Z_plus, <- IHn, Rrepr_1. reflexivity.
    + replace 1%Z with (Z.of_nat 1).
      * rewrite <- (Nat2Z.inj_add n 1).
        apply f_equal. rewrite Nat.add_comm. reflexivity.
      * reflexivity.
Qed.

Lemma Rrepr_IPR2 : forall n : positive,
    CRealEq (Rrepr (IPR_2 n)) (inject_Z (Z.pos (n~0))).
Proof.
  induction n.
  - simpl. replace (Z.pos n~1~0) with ((Z.pos n~0 + 1) + (Z.pos n~0 + 1))%Z.
    + rewrite RbaseSymbolsImpl.R1_def, Rrepr_mult, inject_Z_plus, inject_Z_plus.
      rewrite Rrepr_plus, Rrepr_plus, <- IHn.
      rewrite Rquot2, CReal_mult_plus_distr_r, CReal_mult_1_l.
      rewrite (CReal_plus_comm 1%CReal). repeat rewrite CReal_plus_assoc.
      apply CReal_plus_morph.
      * reflexivity.
      * reflexivity.
    + repeat rewrite <- Pos2Z.inj_add. apply f_equal.
      rewrite Pos.add_diag. apply f_equal.
      rewrite Pos.add_1_r. reflexivity.
  - simpl. replace (Z.pos n~0~0) with ((Z.pos n~0) + (Z.pos n~0))%Z.
    + rewrite RbaseSymbolsImpl.R1_def, Rrepr_mult, inject_Z_plus.
      rewrite Rrepr_plus, <- IHn.
      rewrite Rquot2, CReal_mult_plus_distr_r, CReal_mult_1_l. reflexivity.
    + rewrite <- Pos2Z.inj_add. apply f_equal.
      rewrite Pos.add_diag. reflexivity.
  - simpl. rewrite Rrepr_plus, RbaseSymbolsImpl.R1_def, Rquot2.
    replace 2%Z with (1 + 1)%Z.
    + rewrite inject_Z_plus. reflexivity.
    + reflexivity.
Qed.

Lemma Rrepr_IPR : forall n : positive,
    CRealEq (Rrepr (IPR n)) (inject_Z (Z.pos n)).
Proof.
  intro n. destruct n.
  - unfold IPR. rewrite Rrepr_plus.
    replace (n~1)%positive with (n~0 + 1)%positive.
    + rewrite Pos2Z.inj_add, inject_Z_plus, <- Rrepr_IPR2, CReal_plus_comm.
      rewrite RbaseSymbolsImpl.R1_def, Rquot2. reflexivity.
    + rewrite Pos.add_1_r. reflexivity.
  - apply Rrepr_IPR2.
  - unfold IPR. rewrite RbaseSymbolsImpl.R1_def. apply Rquot2.
Qed.

Lemma Rrepr_IZR : forall n : Z,
    CRealEq (Rrepr (IZR n)) (inject_Z n).
Proof.
  intros [|p|n].
  - unfold IZR. rewrite RbaseSymbolsImpl.R0_def. apply Rquot2.
  - apply Rrepr_IPR.
  - unfold IZR. rewrite Rrepr_opp, Rrepr_IPR. rewrite <- opp_inject_Z.
    replace (- Z.pos n)%Z with (Z.neg n); reflexivity.
Qed.

(**********)
Lemma archimed : forall r:R, IZR (up r) > r /\ IZR (up r) - r <= 1.
Proof.
  intro r. unfold up.
  destruct (CRealArchimedean (Rrepr r)) as [n nmaj], (total_order_T (IZR n - r) R1).
  1:destruct s.
  - split.
    + unfold Rgt. rewrite RbaseSymbolsImpl.Rlt_def. rewrite Rrepr_IZR.
      apply CRealLtForget. apply nmaj.
    + unfold Rle. left. exact r0.
  - split.
    + unfold Rgt. rewrite RbaseSymbolsImpl.Rlt_def.
      rewrite Rrepr_IZR. apply CRealLtForget. apply nmaj.
    + right. exact e.
  - split.
    + unfold Rgt, Z.pred. rewrite RbaseSymbolsImpl.Rlt_def.
      rewrite Rrepr_IZR, inject_Z_plus.
      rewrite RbaseSymbolsImpl.Rlt_def in r0. rewrite Rrepr_minus in r0.
      rewrite <- (Rrepr_IZR n).
      apply CRealLtForget. apply CRealLtEpsilon in r0.
      unfold CReal_minus in r0.
      apply (CReal_plus_lt_compat_l
               (CReal_plus (Rrepr r) (CReal_opp (Rrepr R1))))
        in r0.
      rewrite CReal_plus_assoc,
        CReal_plus_opp_l,
        CReal_plus_0_r,
        RbaseSymbolsImpl.R1_def, Rquot2,
        CReal_plus_comm,
        CReal_plus_assoc,
        <- (CReal_plus_assoc (CReal_opp (Rrepr r))),
        CReal_plus_opp_l,
        CReal_plus_0_l
        in r0.
      rewrite (opp_inject_Z 1). exact r0.
    + destruct (total_order_T (IZR (Z.pred n) - r) 1).
      * destruct s.
        -- left. exact r1.
        -- right. exact e.
      * exfalso. destruct nmaj as [_ nmaj].
        pose proof Rrepr_IZR as iz.
        rewrite <- iz in nmaj.
        apply (Rlt_asym (IZR n) (r + 2)).
        -- rewrite RbaseSymbolsImpl.Rlt_def. rewrite Rrepr_plus. rewrite (Rrepr_plus 1 1).
           apply CRealLtForget.
           apply (CReal_lt_le_trans _ _ _ nmaj).
           unfold IZR, IPR. rewrite RbaseSymbolsImpl.R1_def, Rquot2.
           rewrite <- (inject_Z_plus 1 1). apply CRealLe_refl.
        -- clear nmaj.
           unfold Z.pred in r1. rewrite RbaseSymbolsImpl.Rlt_def in r1.
           rewrite Rrepr_minus, (Rrepr_IZR (n + -1)) in r1.
           rewrite inject_Z_plus, <- (Rrepr_IZR n) in r1.
           rewrite RbaseSymbolsImpl.Rlt_def, Rrepr_plus.
           apply CRealLtEpsilon in r1.
           apply (CReal_plus_lt_compat_l
                    (CReal_plus (Rrepr r) 1%CReal)) in r1.
           apply CRealLtForget.
           apply (CReal_le_lt_trans
                    _ (CReal_plus (CReal_plus (Rrepr r) (Rrepr 1)) 1%CReal)).
           ++ rewrite (Rrepr_plus 1 1). unfold IZR, IPR.
              rewrite RbaseSymbolsImpl.R1_def, (Rquot2 1%CReal), <- CReal_plus_assoc.
              apply CRealLe_refl.
           ++ rewrite <- (CReal_plus_comm (Rrepr 1)),
                <- CReal_plus_assoc,
                (CReal_plus_comm (Rrepr 1))
                in r1.
              apply (CReal_lt_le_trans _ _ _ r1).
              unfold CReal_minus. rewrite (opp_inject_Z 1).
              rewrite (CReal_plus_comm (Rrepr (IZR n))), CReal_plus_assoc,
                <- (CReal_plus_assoc 1), <- (CReal_plus_assoc 1), CReal_plus_opp_r.
              rewrite CReal_plus_0_l, CReal_plus_comm, CReal_plus_assoc,
                CReal_plus_opp_l, CReal_plus_0_r.
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
Lemma completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> { m:R | is_lub E m }.
Proof.
  intros. pose (fun x:CReal => E (Rabst x)) as Er.
  assert (forall x y : CReal, CRealEq x y -> Er x <-> Er y)
    as Erproper.
  { intros. unfold Er. replace (Rabst x) with (Rabst y).
    - reflexivity.
    - apply Rquot1. do 2 rewrite Rquot2. split; apply H1. }
  assert (exists x : CReal, Er x) as Einhab.
  { destruct H0. exists (Rrepr x). unfold Er.
    replace (Rabst (Rrepr x)) with x.
    - exact H0.
    - apply Rquot1. rewrite Rquot2. reflexivity. }
  assert (exists x : CReal,
             (forall y:CReal, Er y -> CRealLe y x))
    as Ebound.
  { destruct H. exists (Rrepr x). intros y Ey. rewrite <- (Rquot2 y).
    apply Rrepr_le. apply H. exact Ey. }
  destruct (@CR_sig_lub CRealConstructive
                        Er Erproper sig_forall_dec sig_not_dec Einhab Ebound).
  exists (Rabst x). split.
  - intros y Ey. apply Rrepr_le. rewrite Rquot2.
    unfold CRealLe. apply a.
    unfold Er. replace (Rabst (Rrepr y)) with y.
    + exact Ey.
    + apply Rquot1. rewrite Rquot2. reflexivity.
  - intros. destruct a. apply Rrepr_le. rewrite Rquot2.
    unfold CRealLe. apply H3. intros y Ey.
    intros. rewrite <- (Rquot2 y) in H4.
    apply Rrepr_le in H4.
    + exact H4.
    + apply H1, Ey.
Qed.

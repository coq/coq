(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Binary Integers (Pierre Crégut, CNET, Lannion, France) *)

Require Export Arith_base.
Require Import BinPos BinInt BinNat Zcompare Zorder.
Require Import Decidable Peano_dec Min Max Compare_dec.

Open Local Scope Z_scope.

Definition neq (x y:nat) := x <> y.

(************************************************)
(** Properties of the injection from nat into Z *)

Lemma Zpos_P_of_succ_nat : forall n:nat,
 Zpos (P_of_succ_nat n) = Zsucc (Z_of_nat n).
Proof.
  intros [|n]. trivial. apply Zpos_succ_morphism.
Qed.

(** Injection and successor *)

Theorem inj_0 : Z_of_nat 0 = 0.
Proof.
  reflexivity.
Qed.

Theorem inj_S : forall n:nat, Z_of_nat (S n) = Zsucc (Z_of_nat n).
Proof.
  exact Zpos_P_of_succ_nat.
Qed.

(** Injection and comparison *)

Theorem inj_compare : forall n m:nat,
 (Z_of_nat n ?= Z_of_nat m) = nat_compare n m.
Proof.
 induction n; destruct m; trivial.
 rewrite 2 inj_S, Zcompare_succ_compat. now simpl.
Qed.

(** Injection and equality. *)

Theorem inj_eq : forall n m:nat, n = m -> Z_of_nat n = Z_of_nat m.
Proof.
  intros; subst; trivial.
Qed.

Theorem inj_eq_rev : forall n m:nat, Z_of_nat n = Z_of_nat m -> n = m.
Proof.
  intros n m H. apply nat_compare_eq.
  now rewrite <- inj_compare, H, Zcompare_refl.
Qed.

Theorem inj_neq : forall n m:nat, neq n m -> Zne (Z_of_nat n) (Z_of_nat m).
Proof.
  unfold neq, Zne. intros n m H. contradict H. now apply inj_eq_rev.
Qed.

Theorem inj_eq_iff : forall n m:nat, n=m <-> Z_of_nat n = Z_of_nat m.
Proof.
 split; [apply inj_eq | apply inj_eq_rev].
Qed.

(** Injection and order *)

(** Both ways ... *)

Theorem inj_le_iff : forall n m:nat, (n<=m)%nat <-> Z_of_nat n <= Z_of_nat m.
Proof.
 intros. unfold Zle. rewrite inj_compare. apply nat_compare_le.
Qed.

Theorem inj_lt_iff : forall n m:nat, (n<m)%nat <-> Z_of_nat n < Z_of_nat m.
Proof.
 intros. unfold Zlt. rewrite inj_compare. apply nat_compare_lt.
Qed.

Theorem inj_ge_iff : forall n m:nat, (n>=m)%nat <-> Z_of_nat n >= Z_of_nat m.
Proof.
 intros. unfold Zge. rewrite inj_compare. apply nat_compare_ge.
Qed.

Theorem inj_gt_iff : forall n m:nat, (n>m)%nat <-> Z_of_nat n > Z_of_nat m.
Proof.
 intros. unfold Zgt. rewrite inj_compare. apply nat_compare_gt.
Qed.

(** One way ... *)

Theorem inj_le : forall n m:nat, (n <= m)%nat -> Z_of_nat n <= Z_of_nat m.
Proof. apply inj_le_iff. Qed.

Theorem inj_lt : forall n m:nat, (n < m)%nat -> Z_of_nat n < Z_of_nat m.
Proof. apply inj_lt_iff. Qed.

Theorem inj_ge : forall n m:nat, (n >= m)%nat -> Z_of_nat n >= Z_of_nat m.
Proof. apply inj_ge_iff. Qed.

Theorem inj_gt : forall n m:nat, (n > m)%nat -> Z_of_nat n > Z_of_nat m.
Proof. apply inj_gt_iff. Qed.

(** The other way ... *)

Theorem inj_le_rev : forall n m:nat, Z_of_nat n <= Z_of_nat m -> (n <= m)%nat.
Proof. apply inj_le_iff. Qed.

Theorem inj_lt_rev : forall n m:nat, Z_of_nat n < Z_of_nat m -> (n < m)%nat.
Proof. apply inj_lt_iff. Qed.

Theorem inj_ge_rev : forall n m:nat, Z_of_nat n >= Z_of_nat m -> (n >= m)%nat.
Proof. apply inj_ge_iff. Qed.

Theorem inj_gt_rev : forall n m:nat, Z_of_nat n > Z_of_nat m -> (n > m)%nat.
Proof. apply inj_gt_iff. Qed.

(** Injection and usual operations *)

Theorem inj_plus : forall n m:nat, Z_of_nat (n + m) = Z_of_nat n + Z_of_nat m.
Proof.
 induction n as [|n IH]; intros [|m]; simpl; trivial.
 rewrite <- plus_n_O; trivial.
 change (Z_of_nat (S (n + S m)) = Z_of_nat (S n) + Z_of_nat (S m)).
 now rewrite inj_S, IH, 2 inj_S, Zplus_succ_l.
Qed.

Theorem inj_mult : forall n m:nat, Z_of_nat (n * m) = Z_of_nat n * Z_of_nat m.
Proof.
 induction n as [|n IH]; intros m; trivial.
 rewrite inj_S, Zmult_succ_l, <- IH, <- inj_plus.
 simpl. now rewrite plus_comm.
Qed.

Theorem inj_minus1 :
  forall n m:nat, (m <= n)%nat -> Z_of_nat (n - m) = Z_of_nat n - Z_of_nat m.
Proof.
 intros n m H.
 apply (Zplus_reg_l (Z_of_nat m)); unfold Zminus.
 rewrite Zplus_permute, Zplus_opp_r, <- inj_plus, Zplus_0_r.
 f_equal. symmetry. now apply le_plus_minus.
Qed.

Theorem inj_minus2 : forall n m:nat, (m > n)%nat -> Z_of_nat (n - m) = 0.
Proof.
 intros. rewrite not_le_minus_0; auto with arith.
Qed.

Theorem inj_minus : forall n m:nat,
 Z_of_nat (minus n m) = Zmax 0 (Z_of_nat n - Z_of_nat m).
Proof.
 intros n m. unfold Zmax.
 destruct (le_lt_dec m n) as [H|H].
 (* m <= n *)
 rewrite inj_minus1; trivial.
 apply inj_le, Zle_minus_le_0 in H. revert H. unfold Zle.
 case Zcompare_spec; intuition.
 (* n < m *)
 rewrite inj_minus2; trivial.
 apply inj_lt, Zlt_gt in H.
 apply (Zplus_gt_compat_r _ _ (- Z_of_nat m)) in H.
 rewrite Zplus_opp_r in H.
 unfold Zminus. rewrite H; auto.
Qed.

Theorem inj_min : forall n m:nat,
  Z_of_nat (min n m) = Zmin (Z_of_nat n) (Z_of_nat m).
Proof.
 intros n m. unfold Zmin. rewrite inj_compare.
 case nat_compare_spec; intros; f_equal; subst; auto with arith.
Qed.

Theorem inj_max : forall n m:nat,
  Z_of_nat (max n m) = Zmax (Z_of_nat n) (Z_of_nat m).
Proof.
 intros n m. unfold Zmax. rewrite inj_compare.
 case nat_compare_spec; intros; f_equal; subst; auto with arith.
Qed.

(** Composition of injections **)

Lemma Z_of_nat_of_P : forall p, Z_of_nat (nat_of_P p) = Zpos p.
Proof.
 intros p. destruct (nat_of_P_is_S p) as (n,H). rewrite H.
 simpl. f_equal. rewrite <- (nat_of_P_of_succ_nat n) in H.
 symmetry. now apply nat_of_P_inj.
Qed.

(** For compatibility *)
Definition Zpos_eq_Z_of_nat_o_nat_of_P p := eq_sym (Z_of_nat_of_P p).

(******************************************************************)
(** Properties of the injection from N into Z *)

Lemma Z_of_nat_of_N : forall n, Z_of_nat (nat_of_N n) = Z_of_N n.
Proof.
  intros [|n]. trivial.
  simpl. apply Z_of_nat_of_P.
Qed.

Lemma Z_of_N_of_nat : forall n, Z_of_N (N_of_nat n) = Z_of_nat n.
Proof.
 now destruct n.
Qed.

Lemma Z_of_N_eq : forall n m, n = m -> Z_of_N n = Z_of_N m.
Proof.
 intros; f_equal; assumption.
Qed.

Lemma Z_of_N_eq_rev : forall n m, Z_of_N n = Z_of_N m -> n = m.
Proof.
 intros [|n] [|m]; simpl; congruence.
Qed.

Lemma Z_of_N_eq_iff : forall n m, n = m <-> Z_of_N n = Z_of_N m.
Proof.
 split; [apply Z_of_N_eq | apply Z_of_N_eq_rev].
Qed.

Lemma Z_of_N_compare : forall n m,
 Zcompare (Z_of_N n) (Z_of_N m) = Ncompare n m.
Proof.
 intros [|n] [|m]; trivial.
Qed.

Lemma Z_of_N_le_iff : forall n m, (n<=m)%N <-> Z_of_N n <= Z_of_N m.
Proof.
 intros. unfold Zle. now rewrite Z_of_N_compare.
Qed.

Lemma Z_of_N_le : forall n m, (n<=m)%N -> Z_of_N n <= Z_of_N m.
Proof.
 apply Z_of_N_le_iff.
Qed.

Lemma Z_of_N_le_rev : forall n m, Z_of_N n <= Z_of_N m -> (n<=m)%N.
Proof.
 apply Z_of_N_le_iff.
Qed.

Lemma Z_of_N_lt_iff : forall n m, (n<m)%N <-> Z_of_N n < Z_of_N m.
Proof.
 intros. unfold Zlt. now rewrite Z_of_N_compare.
Qed.

Lemma Z_of_N_lt : forall n m, (n<m)%N -> Z_of_N n < Z_of_N m.
Proof.
 apply Z_of_N_lt_iff.
Qed.

Lemma Z_of_N_lt_rev : forall n m, Z_of_N n < Z_of_N m -> (n<m)%N.
Proof.
 apply Z_of_N_lt_iff.
Qed.

Lemma Z_of_N_ge_iff : forall n m, (n>=m)%N <-> Z_of_N n >= Z_of_N m.
Proof.
 intros. unfold Zge. now rewrite Z_of_N_compare.
Qed.

Lemma Z_of_N_ge : forall n m, (n>=m)%N -> Z_of_N n >= Z_of_N m.
Proof.
 apply Z_of_N_ge_iff.
Qed.

Lemma Z_of_N_ge_rev : forall n m, Z_of_N n >= Z_of_N m -> (n>=m)%N.
Proof.
 apply Z_of_N_ge_iff.
Qed.

Lemma Z_of_N_gt_iff : forall n m, (n>m)%N <-> Z_of_N n > Z_of_N m.
Proof.
 intros. unfold Zgt. now rewrite Z_of_N_compare.
Qed.

Lemma Z_of_N_gt : forall n m, (n>m)%N -> Z_of_N n > Z_of_N m.
Proof.
 apply Z_of_N_gt_iff.
Qed.

Lemma Z_of_N_gt_rev : forall n m, Z_of_N n > Z_of_N m -> (n>m)%N.
Proof.
 apply Z_of_N_gt_iff.
Qed.

Lemma Z_of_N_pos : forall p:positive, Z_of_N (Npos p) = Zpos p.
Proof.
 reflexivity.
Qed.

Lemma Z_of_N_abs : forall z:Z, Z_of_N (Zabs_N z) = Zabs z.
Proof.
 now destruct z.
Qed.

Lemma Z_of_N_le_0 : forall n, 0 <= Z_of_N n.
Proof.
 now destruct n.
Qed.

Lemma Z_of_N_plus : forall n m, Z_of_N (n+m) = Z_of_N n + Z_of_N m.
Proof.
 now destruct n, m.
Qed.

Lemma Z_of_N_mult : forall n m, Z_of_N (n*m) = Z_of_N n * Z_of_N m.
Proof.
 now destruct n, m.
Qed.

Lemma Z_of_N_minus : forall n m, Z_of_N (n-m) = Zmax 0 (Z_of_N n - Z_of_N m).
Proof.
 intros [|n] [|m]; simpl; trivial.
 case Pcompare_spec; intros H.
 subst. now rewrite Pminus_mask_diag.
 rewrite Pminus_mask_Lt; trivial.
 unfold Pminus.
 destruct (Pminus_mask_Gt n m (ZC2 _ _ H)) as (q & -> & _); trivial.
Qed.

Lemma Z_of_N_succ : forall n, Z_of_N (Nsucc n) = Zsucc (Z_of_N n).
Proof.
 intros [|n]; simpl; trivial. now rewrite Zpos_succ_morphism.
Qed.

Lemma Z_of_N_min : forall n m, Z_of_N (Nmin n m) = Zmin (Z_of_N n) (Z_of_N m).
Proof.
 intros. unfold Zmin, Nmin. rewrite Z_of_N_compare. now case Ncompare.
Qed.

Lemma Z_of_N_max : forall n m, Z_of_N (Nmax n m) = Zmax (Z_of_N n) (Z_of_N m).
Proof.
 intros. unfold Zmax, Nmax. rewrite Z_of_N_compare.
 case Ncompare_spec; intros; subst; trivial.
Qed.

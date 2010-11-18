(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Arith_base Compare_dec Sumbool Div2 Min Max.
Require Import BinPos BinNat Pnat.

Lemma N_of_nat_of_N : forall a:N, N_of_nat (nat_of_N a) = a.
Proof.
  destruct a as [| p]. reflexivity.
  simpl. elim (nat_of_P_is_S p). intros n H. rewrite H. simpl.
  rewrite <- nat_of_P_of_succ_nat in H.
  rewrite nat_of_P_inj with (1 := H). reflexivity.
Qed.

Lemma nat_of_N_of_nat : forall n:nat, nat_of_N (N_of_nat n) = n.
Proof.
  induction n. trivial.
  intros. simpl. apply nat_of_P_of_succ_nat.
Qed.

Lemma nat_of_N_inj : forall n n', nat_of_N n = nat_of_N n' -> n = n'.
Proof.
  intros n n' H.
  rewrite <- (N_of_nat_of_N n), <- (N_of_nat_of_N n'). now f_equal.
Qed.

Lemma N_of_nat_inj : forall n n', N_of_nat n = N_of_nat n' -> n = n'.
Proof.
  intros n n' H.
  rewrite <- (nat_of_N_of_nat n), <- (nat_of_N_of_nat n'). now f_equal.
Qed.

Hint Rewrite nat_of_N_of_nat N_of_nat_of_N : Nnat.

(** Interaction of this translation and usual operations. *)

Lemma nat_of_Ndouble : forall a, nat_of_N (Ndouble a) = 2*(nat_of_N a).
Proof.
  destruct a; simpl nat_of_N; trivial. apply nat_of_P_xO.
Qed.

Lemma nat_of_Ndouble_plus_one :
  forall a, nat_of_N (Ndouble_plus_one a) = S (2*(nat_of_N a)).
Proof.
  destruct a; simpl nat_of_N; trivial. apply nat_of_P_xI.
Qed.

Lemma nat_of_Nsucc : forall a, nat_of_N (Nsucc a) = S (nat_of_N a).
Proof.
  destruct a; simpl.
  apply nat_of_P_xH.
  apply Psucc_S.
Qed.

Lemma nat_of_Nplus :
  forall a a', nat_of_N (Nplus a a') = (nat_of_N a)+(nat_of_N a').
Proof.
  destruct a; destruct a'; simpl; auto.
  apply Pplus_plus.
Qed.

Lemma nat_of_Nmult :
  forall a a', nat_of_N (Nmult a a') = (nat_of_N a)*(nat_of_N a').
Proof.
  destruct a; destruct a'; simpl; auto.
  apply Pmult_mult.
Qed.

Lemma nat_of_Nminus :
  forall a a', nat_of_N (Nminus a a') = ((nat_of_N a)-(nat_of_N a'))%nat.
Proof.
  intros [|a] [|a']; simpl; auto with arith.
  destruct (Pcompare_spec a a').
  subst. now rewrite Pminus_mask_diag, <- minus_n_n.
  rewrite Pminus_mask_Lt by trivial. apply Plt_lt in H.
  simpl; symmetry; apply not_le_minus_0; auto with arith.
  destruct (Pminus_mask_Gt a a' (ZC2 _ _ H)) as (q & -> & Hq & _).
  simpl. apply plus_minus. now rewrite <- Hq, Pplus_plus.
Qed.

Lemma nat_of_Npred : forall a, nat_of_N (Npred a) = pred (nat_of_N a).
Proof.
 intros. rewrite pred_of_minus, Npred_minus. apply nat_of_Nminus.
Qed.

Lemma nat_of_Ndiv2 :
  forall a, nat_of_N (Ndiv2 a) = div2 (nat_of_N a).
Proof.
  destruct a; simpl in *; auto.
  destruct p; auto.
  rewrite nat_of_P_xI.
  rewrite div2_double_plus_one; auto.
  rewrite nat_of_P_xO.
  rewrite div2_double; auto.
Qed.

Lemma nat_of_Ncompare :
 forall a a', Ncompare a a' = nat_compare (nat_of_N a) (nat_of_N a').
Proof.
  destruct a; destruct a'; simpl; trivial.
  now destruct (nat_of_P_is_S p) as (n,->).
  now destruct (nat_of_P_is_S p) as (n,->).
  apply Pcompare_nat_compare.
Qed.

Lemma nat_of_Nmax :
  forall a a', nat_of_N (Nmax a a') = max (nat_of_N a) (nat_of_N a').
Proof.
  intros; unfold Nmax; rewrite nat_of_Ncompare. symmetry.
  case nat_compare_spec; intros H; try rewrite H; auto with arith.
Qed.

Lemma nat_of_Nmin :
  forall a a', nat_of_N (Nmin a a') = min (nat_of_N a) (nat_of_N a').
Proof.
  intros; unfold Nmin; rewrite nat_of_Ncompare. symmetry.
  case nat_compare_spec; intros H; try rewrite H; auto with arith.
Qed.

Hint Rewrite nat_of_Ndouble nat_of_Ndouble_plus_one
 nat_of_Nsucc nat_of_Nplus nat_of_Nmult nat_of_Nminus
 nat_of_Npred nat_of_Ndiv2 nat_of_Nmax nat_of_Nmin : Nnat.

Lemma N_of_double : forall n, N_of_nat (2*n) = Ndouble (N_of_nat n).
Proof.
  intros. apply nat_of_N_inj. now autorewrite with Nnat.
Qed.

Lemma N_of_double_plus_one :
  forall n, N_of_nat (S (2*n)) = Ndouble_plus_one (N_of_nat n).
Proof.
  intros. apply nat_of_N_inj. now autorewrite with Nnat.
Qed.

Lemma N_of_S : forall n, N_of_nat (S n) = Nsucc (N_of_nat n).
Proof.
  intros. apply nat_of_N_inj. now autorewrite with Nnat.
Qed.

Lemma N_of_pred : forall n, N_of_nat (pred n) = Npred (N_of_nat n).
Proof.
  intros. apply nat_of_N_inj. now autorewrite with Nnat.
Qed.

Lemma N_of_plus :
  forall n n', N_of_nat (n+n') = Nplus (N_of_nat n) (N_of_nat n').
Proof.
  intros. apply nat_of_N_inj. now autorewrite with Nnat.
Qed.

Lemma N_of_minus :
  forall n n', N_of_nat (n-n') = Nminus (N_of_nat n) (N_of_nat n').
Proof.
  intros. apply nat_of_N_inj. now autorewrite with Nnat.
Qed.

Lemma N_of_mult :
  forall n n', N_of_nat (n*n') = Nmult (N_of_nat n) (N_of_nat n').
Proof.
  intros. apply nat_of_N_inj. now autorewrite with Nnat.
Qed.

Lemma N_of_div2 :
  forall n, N_of_nat (div2 n) = Ndiv2 (N_of_nat n).
Proof.
  intros. apply nat_of_N_inj. now autorewrite with Nnat.
Qed.

Lemma N_of_nat_compare :
 forall n n', nat_compare n n' = Ncompare (N_of_nat n) (N_of_nat n').
Proof.
  intros. rewrite nat_of_Ncompare. now autorewrite with Nnat.
Qed.

Lemma N_of_min :
  forall n n', N_of_nat (min n n') = Nmin (N_of_nat n) (N_of_nat n').
Proof.
  intros. apply nat_of_N_inj. now autorewrite with Nnat.
Qed.

Lemma N_of_max :
  forall n n', N_of_nat (max n n') = Nmax (N_of_nat n) (N_of_nat n').
Proof.
  intros. apply nat_of_N_inj. now autorewrite with Nnat.
Qed.

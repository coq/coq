(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Bool.
Require Import Sumbool.
Require Import Arith.
Require Import BinPos.
Require Import BinNat.
Require Import Pnat.
Require Import Nnat.
Require Import Ndigits.

(** A boolean equality over [N] *)

Notation Peqb := Peqb (only parsing). (* Now in [BinPos] *)
Notation Neqb := Neqb (only parsing). (* Now in [BinNat] *)

Notation Peqb_correct := Peqb_refl (only parsing).

Lemma Peqb_complete : forall p p', Peqb p p' = true -> p = p'.
Proof.
  intros. now apply (Peqb_eq p p').
Qed.

Lemma Peqb_Pcompare : forall p p', Peqb p p' = true -> Pcompare p p' Eq = Eq.
Proof.
  intros. now rewrite Pcompare_eq_iff, <- Peqb_eq.
Qed.

Lemma Pcompare_Peqb : forall p p', Pcompare p p' Eq = Eq -> Peqb p p' = true.
Proof.
  intros; now rewrite Peqb_eq, <- Pcompare_eq_iff.
Qed.

Lemma Neqb_correct : forall n, Neqb n n = true.
Proof.
  intros; now rewrite Neqb_eq.
Qed.

Lemma Neqb_Ncompare : forall n n', Neqb n n' = true -> Ncompare n n' = Eq.
Proof.
  intros; now rewrite Ncompare_eq_correct, <- Neqb_eq.
Qed.

Lemma Ncompare_Neqb : forall n n', Ncompare n n' = Eq -> Neqb n n' = true.
Proof.
  intros; now rewrite Neqb_eq, <- Ncompare_eq_correct.
Qed.

Lemma Neqb_complete : forall a a', Neqb a a' = true -> a = a'.
Proof.
  intros; now rewrite <- Neqb_eq.
Qed.

Lemma Neqb_comm : forall a a', Neqb a a' = Neqb a' a.
Proof.
  intros; apply eq_true_iff_eq. rewrite 2 Neqb_eq; auto with *.
Qed.

Lemma Nxor_eq_true :
 forall a a', Nxor a a' = N0 -> Neqb a a' = true.
Proof.
  intros. rewrite (Nxor_eq a a' H). apply Neqb_correct.
Qed.

Lemma Nxor_eq_false :
 forall a a' p, Nxor a a' = Npos p -> Neqb a a' = false.
Proof.
  intros. elim (sumbool_of_bool (Neqb a a')). intro H0.
  rewrite (Neqb_complete a a' H0) in H.
  rewrite (Nxor_nilpotent a') in H. discriminate H.
  trivial.
Qed.

Lemma Nodd_not_double :
 forall a,
   Nodd a -> forall a0, Neqb (Ndouble a0) a = false.
Proof.
  intros. elim (sumbool_of_bool (Neqb (Ndouble a0) a)). intro H0.
  rewrite <- (Neqb_complete _ _ H0) in H.
  unfold Nodd in H.
  rewrite (Ndouble_bit0 a0) in H. discriminate H.
  trivial.
Qed.

Lemma Nnot_div2_not_double :
 forall a a0,
   Neqb (Ndiv2 a) a0 = false -> Neqb a (Ndouble a0) = false.
Proof.
  intros. elim (sumbool_of_bool (Neqb (Ndouble a0) a)). intro H0.
  rewrite <- (Neqb_complete _ _ H0) in H. rewrite (Ndouble_div2 a0) in H.
  rewrite (Neqb_correct a0) in H. discriminate H.
  intro. rewrite Neqb_comm. assumption.
Qed.

Lemma Neven_not_double_plus_one :
 forall a,
   Neven a -> forall a0, Neqb (Ndouble_plus_one a0) a = false.
Proof.
  intros. elim (sumbool_of_bool (Neqb (Ndouble_plus_one a0) a)). intro H0.
  rewrite <- (Neqb_complete _ _ H0) in H.
  unfold Neven in H.
  rewrite (Ndouble_plus_one_bit0 a0) in H.
  discriminate H.
  trivial.
Qed.

Lemma Nnot_div2_not_double_plus_one :
 forall a a0,
   Neqb (Ndiv2 a) a0 = false -> Neqb (Ndouble_plus_one a0) a = false.
Proof.
  intros. elim (sumbool_of_bool (Neqb a (Ndouble_plus_one a0))). intro H0.
  rewrite (Neqb_complete _ _ H0) in H. rewrite (Ndouble_plus_one_div2 a0) in H.
  rewrite (Neqb_correct a0) in H. discriminate H.
  intro H0. rewrite Neqb_comm. assumption.
Qed.

Lemma Nbit0_neq :
 forall a a',
   Nbit0 a = false -> Nbit0 a' = true -> Neqb a a' = false.
Proof.
  intros. elim (sumbool_of_bool (Neqb a a')). intro H1.
  rewrite (Neqb_complete _ _ H1) in H.
  rewrite H in H0. discriminate H0.
  trivial.
Qed.

Lemma Ndiv2_eq :
 forall a a', Neqb a a' = true -> Neqb (Ndiv2 a) (Ndiv2 a') = true.
Proof.
  intros. cut (a = a'). intros. rewrite H0. apply Neqb_correct.
  apply Neqb_complete. exact H.
Qed.

Lemma Ndiv2_neq :
 forall a a',
   Neqb (Ndiv2 a) (Ndiv2 a') = false -> Neqb a a' = false.
Proof.
  intros. elim (sumbool_of_bool (Neqb a a')). intro H0.
  rewrite (Neqb_complete _ _ H0) in H.
  rewrite (Neqb_correct (Ndiv2 a')) in H. discriminate H.
  trivial.
Qed.

Lemma Ndiv2_bit_eq :
 forall a a',
   Nbit0 a = Nbit0 a' -> Ndiv2 a = Ndiv2 a' -> a = a'.
Proof.
  intros. apply Nbit_faithful. unfold eqf in |- *. destruct n.
  rewrite Nbit0_correct. rewrite Nbit0_correct. assumption.
  rewrite <- Ndiv2_correct. rewrite <- Ndiv2_correct.
  rewrite H0. reflexivity.
Qed.

Lemma Ndiv2_bit_neq :
 forall a a',
   Neqb a a' = false ->
   Nbit0 a = Nbit0 a' -> Neqb (Ndiv2 a) (Ndiv2 a') = false.
Proof.
  intros. elim (sumbool_of_bool (Neqb (Ndiv2 a) (Ndiv2 a'))). intro H1.
  rewrite (Ndiv2_bit_eq _ _ H0 (Neqb_complete _ _ H1)) in H.
  rewrite (Neqb_correct a') in H. discriminate H.
  trivial.
Qed.

Lemma Nneq_elim :
 forall a a',
   Neqb a a' = false ->
   Nbit0 a = negb (Nbit0 a') \/
   Neqb (Ndiv2 a) (Ndiv2 a') = false.
Proof.
  intros. cut (Nbit0 a = Nbit0 a' \/ Nbit0 a = negb (Nbit0 a')).
  intros. elim H0. intro. right. apply Ndiv2_bit_neq. assumption.
  assumption.
  intro. left. assumption.
  case (Nbit0 a); case (Nbit0 a'); auto.
Qed.

Lemma Ndouble_or_double_plus_un :
 forall a,
   {a0 : N | a = Ndouble a0} + {a1 : N | a = Ndouble_plus_one a1}.
Proof.
  intro. elim (sumbool_of_bool (Nbit0 a)). intro H. right. split with (Ndiv2 a).
  rewrite (Ndiv2_double_plus_one a H). reflexivity.
  intro H. left. split with (Ndiv2 a). rewrite (Ndiv2_double a H). reflexivity.
Qed.

(** A boolean order on [N] *)

Definition Nleb (a b:N) := leb (nat_of_N a) (nat_of_N b).

Lemma Nleb_Nle : forall a b, Nleb a b = true <-> Nle a b.
Proof.
 intros; unfold Nle; rewrite nat_of_Ncompare.
 unfold Nleb; apply leb_compare.
Qed.

Lemma Nleb_refl : forall a, Nleb a a = true.
Proof.
  intro. unfold Nleb in |- *. apply leb_correct. apply le_n.
Qed.

Lemma Nleb_antisym :
 forall a b, Nleb a b = true -> Nleb b a = true -> a = b.
Proof.
  unfold Nleb in |- *. intros. rewrite <- (N_of_nat_of_N a). rewrite <- (N_of_nat_of_N b).
  rewrite (le_antisym _ _ (leb_complete _ _ H) (leb_complete _ _ H0)). reflexivity.
Qed.

Lemma Nleb_trans :
 forall a b c, Nleb a b = true -> Nleb b c = true -> Nleb a c = true.
Proof.
  unfold Nleb in |- *. intros. apply leb_correct. apply le_trans with (m := nat_of_N b).
  apply leb_complete. assumption.
  apply leb_complete. assumption.
Qed.

Lemma Nleb_ltb_trans :
 forall a b c,
   Nleb a b = true -> Nleb c b = false -> Nleb c a = false.
Proof.
  unfold Nleb in |- *. intros. apply leb_correct_conv. apply le_lt_trans with (m := nat_of_N b).
  apply leb_complete. assumption.
  apply leb_complete_conv. assumption.
Qed.

Lemma Nltb_leb_trans :
 forall a b c,
   Nleb b a = false -> Nleb b c = true -> Nleb c a = false.
Proof.
  unfold Nleb in |- *. intros. apply leb_correct_conv. apply lt_le_trans with (m := nat_of_N b).
  apply leb_complete_conv. assumption.
  apply leb_complete. assumption.
Qed.

Lemma Nltb_trans :
 forall a b c,
   Nleb b a = false -> Nleb c b = false -> Nleb c a = false.
Proof.
  unfold Nleb in |- *. intros. apply leb_correct_conv. apply lt_trans with (m := nat_of_N b).
  apply leb_complete_conv. assumption.
  apply leb_complete_conv. assumption.
Qed.

Lemma Nltb_leb_weak : forall a b:N, Nleb b a = false -> Nleb a b = true.
Proof.
  unfold Nleb in |- *. intros. apply leb_correct. apply lt_le_weak.
  apply leb_complete_conv. assumption.
Qed.

Lemma Nleb_double_mono :
 forall a b,
   Nleb a b = true -> Nleb (Ndouble a) (Ndouble b) = true.
Proof.
  unfold Nleb in |- *. intros. rewrite nat_of_Ndouble. rewrite nat_of_Ndouble. apply leb_correct.
  simpl in |- *. apply plus_le_compat. apply leb_complete. assumption.
  apply plus_le_compat. apply leb_complete. assumption.
  apply le_n.
Qed.

Lemma Nleb_double_plus_one_mono :
 forall a b,
   Nleb a b = true ->
   Nleb (Ndouble_plus_one a) (Ndouble_plus_one b) = true.
Proof.
  unfold Nleb in |- *. intros. rewrite nat_of_Ndouble_plus_one. rewrite nat_of_Ndouble_plus_one.
  apply leb_correct. apply le_n_S. simpl in |- *. apply plus_le_compat. apply leb_complete.
  assumption.
  apply plus_le_compat. apply leb_complete. assumption.
  apply le_n.
Qed.

Lemma Nleb_double_mono_conv :
 forall a b,
   Nleb (Ndouble a) (Ndouble b) = true -> Nleb a b = true.
Proof.
  unfold Nleb in |- *. intros a b. rewrite nat_of_Ndouble. rewrite nat_of_Ndouble. intro.
  apply leb_correct. apply (mult_S_le_reg_l 1). apply leb_complete. assumption.
Qed.

Lemma Nleb_double_plus_one_mono_conv :
 forall a b,
   Nleb (Ndouble_plus_one a) (Ndouble_plus_one b) = true ->
   Nleb a b = true.
Proof.
  unfold Nleb in |- *. intros a b. rewrite nat_of_Ndouble_plus_one. rewrite nat_of_Ndouble_plus_one.
  intro. apply leb_correct. apply (mult_S_le_reg_l 1). apply le_S_n. apply leb_complete.
  assumption.
Qed.

Lemma Nltb_double_mono :
 forall a b,
   Nleb a b = false -> Nleb (Ndouble a) (Ndouble b) = false.
Proof.
  intros. elim (sumbool_of_bool (Nleb (Ndouble a) (Ndouble b))). intro H0.
  rewrite (Nleb_double_mono_conv _ _ H0) in H. discriminate H.
  trivial.
Qed.

Lemma Nltb_double_plus_one_mono :
 forall a b,
   Nleb a b = false ->
   Nleb (Ndouble_plus_one a) (Ndouble_plus_one b) = false.
Proof.
  intros. elim (sumbool_of_bool (Nleb (Ndouble_plus_one a) (Ndouble_plus_one b))). intro H0.
  rewrite (Nleb_double_plus_one_mono_conv _ _ H0) in H. discriminate H.
  trivial.
Qed.

Lemma Nltb_double_mono_conv :
 forall a b,
   Nleb (Ndouble a) (Ndouble b) = false -> Nleb a b = false.
Proof.
  intros. elim (sumbool_of_bool (Nleb a b)). intro H0. rewrite (Nleb_double_mono _ _ H0) in H.
  discriminate H.
  trivial.
Qed.

Lemma Nltb_double_plus_one_mono_conv :
 forall a b,
   Nleb (Ndouble_plus_one a) (Ndouble_plus_one b) = false ->
   Nleb a b = false.
Proof.
  intros. elim (sumbool_of_bool (Nleb a b)). intro H0.
  rewrite (Nleb_double_plus_one_mono _ _ H0) in H. discriminate H.
  trivial.
Qed.

(* Nleb and Ncompare *)

(* NB: No need to prove that Nleb a b = true <-> Ncompare a b <> Gt,
   this statement is in fact Nleb_Nle! *)

Lemma Nltb_Ncompare : forall a b,
 Nleb a b = false <-> Ncompare a b = Gt.
Proof.
 intros.
 assert (IFF : forall x:bool, x = false <-> ~ x = true)
   by (destruct x; intuition).
 rewrite IFF, Nleb_Nle; unfold Nle.
 destruct (Ncompare a b); split; intro H; auto;
  elim H; discriminate.
Qed.

Lemma Ncompare_Gt_Nltb : forall a b,
 Ncompare a b = Gt -> Nleb a b = false.
Proof.
 intros; apply <- Nltb_Ncompare; auto.
Qed.

Lemma Ncompare_Lt_Nltb : forall a b,
 Ncompare a b = Lt -> Nleb b a = false.
Proof.
 intros a b H.
 rewrite Nltb_Ncompare, <- Ncompare_antisym, H; auto.
Qed.

(* An alternate [min] function over [N] *)

Definition Nmin' (a b:N) := if Nleb a b then a else b.

Lemma Nmin_Nmin' : forall a b, Nmin a b = Nmin' a b.
Proof.
 unfold Nmin, Nmin', Nleb; intros.
 rewrite nat_of_Ncompare.
 generalize (leb_compare (nat_of_N a) (nat_of_N b));
 destruct (nat_compare (nat_of_N a) (nat_of_N b));
 destruct (leb (nat_of_N a) (nat_of_N b)); intuition.
 lapply H1; intros; discriminate.
 lapply H1; intros; discriminate.
Qed.

Lemma Nmin_choice : forall a b, {Nmin a b = a} + {Nmin a b = b}.
Proof.
  unfold Nmin in *; intros; destruct (Ncompare a b); auto.
Qed.

Lemma Nmin_le_1 : forall a b, Nleb (Nmin a b) a = true.
Proof.
  intros; rewrite Nmin_Nmin'.
  unfold Nmin'; elim (sumbool_of_bool (Nleb a b)). intro H. rewrite H.
  apply Nleb_refl.
  intro H. rewrite H. apply Nltb_leb_weak. assumption.
Qed.

Lemma Nmin_le_2 : forall a b, Nleb (Nmin a b) b = true.
Proof.
  intros; rewrite Nmin_Nmin'.
  unfold Nmin'; elim (sumbool_of_bool (Nleb a b)). intro H. rewrite H. assumption.
  intro H. rewrite H. apply Nleb_refl.
Qed.

Lemma Nmin_le_3 :
 forall a b c, Nleb a (Nmin b c) = true -> Nleb a b = true.
Proof.
  intros; rewrite Nmin_Nmin' in *.
  unfold Nmin' in *; elim (sumbool_of_bool (Nleb b c)). intro H0. rewrite H0 in H.
  assumption.
  intro H0. rewrite H0 in H. apply Nltb_leb_weak. apply Nleb_ltb_trans with (b := c); assumption.
Qed.

Lemma Nmin_le_4 :
 forall a b c, Nleb a (Nmin b c) = true -> Nleb a c = true.
Proof.
  intros; rewrite Nmin_Nmin' in *.
  unfold Nmin' in *; elim (sumbool_of_bool (Nleb b c)). intro H0. rewrite H0 in H.
  apply Nleb_trans with (b := b); assumption.
  intro H0. rewrite H0 in H. assumption.
Qed.

Lemma Nmin_le_5 :
 forall a b c,
   Nleb a b = true -> Nleb a c = true -> Nleb a (Nmin b c) = true.
Proof.
  intros. elim (Nmin_choice b c). intro H1. rewrite H1. assumption.
  intro H1. rewrite H1. assumption.
Qed.

Lemma Nmin_lt_3 :
 forall a b c, Nleb (Nmin b c) a = false -> Nleb b a = false.
Proof.
  intros; rewrite Nmin_Nmin' in *.
  unfold Nmin' in *. intros. elim (sumbool_of_bool (Nleb b c)). intro H0. rewrite H0 in H.
  assumption.
  intro H0. rewrite H0 in H. apply Nltb_trans with (b := c); assumption.
Qed.

Lemma Nmin_lt_4 :
 forall a b c, Nleb (Nmin b c) a = false -> Nleb c a = false.
Proof.
  intros; rewrite Nmin_Nmin' in *.
  unfold Nmin' in *. elim (sumbool_of_bool (Nleb b c)). intro H0. rewrite H0 in H.
  apply Nltb_leb_trans with (b := b); assumption.
  intro H0. rewrite H0 in H. assumption.
Qed.

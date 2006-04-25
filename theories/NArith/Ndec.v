(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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

Fixpoint Peqb (p1 p2:positive) {struct p2} : bool :=
  match p1, p2 with
  | xH, xH => true
  | xO p'1, xO p'2 => Peqb p'1 p'2
  | xI p'1, xI p'2 => Peqb p'1 p'2
  | _, _ => false
  end.

Lemma Peqb_correct : forall p, Peqb p p = true.
Proof.
induction p; auto.
Qed.

Lemma Peqb_Pcompare : forall p p', Peqb p p' = true -> Pcompare p p' Eq = Eq.
Proof.
 induction p; destruct p'; simpl; intros; try discriminate; auto.
Qed.

Lemma Pcompare_Peqb : forall p p', Pcompare p p' Eq = Eq -> Peqb p p' = true.
Proof. 
intros; rewrite <- (Pcompare_Eq_eq _ _ H).
apply Peqb_correct.
Qed.

Definition Neqb (a a':N) :=
  match a, a' with
  | N0, N0 => true
  | Npos p, Npos p' => Peqb p p'
  | _, _ => false
  end.

Lemma Neqb_correct : forall n, Neqb n n = true.
Proof.
  destruct n; trivial.
  simpl; apply Peqb_correct.
Qed.

Lemma Neqb_Ncompare : forall n n', Neqb n n' = true -> Ncompare n n' = Eq.
Proof.
 destruct n; destruct n'; simpl; intros; try discriminate; auto; apply Peqb_Pcompare; auto.
Qed.

Lemma Ncompare_Neqb : forall n n', Ncompare n n' = Eq -> Neqb n n' = true.
Proof. 
intros; rewrite <- (Ncompare_Eq_eq _ _ H).
apply Neqb_correct.
Qed.

Lemma Neqb_complete : forall a a', Neqb a a' = true -> a = a'.
Proof.
  intros.
  apply Ncompare_Eq_eq.
  apply Neqb_Ncompare; auto.
Qed.

Lemma Neqb_comm : forall a a', Neqb a a' = Neqb a' a.
Proof.
  intros; apply bool_1; split; intros.
  rewrite (Neqb_complete _ _ H); apply Neqb_correct.
  rewrite (Neqb_complete _ _ H); apply Neqb_correct.
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
  rewrite (Neqb_complete a a' H0) in H. rewrite (Nxor_nilpotent a') in H. discriminate H.
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
  intros. elim (sumbool_of_bool (Neqb a a')). intro H1. rewrite (Neqb_complete _ _ H1) in H.
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
  rewrite (Neqb_complete _ _ H0) in H. rewrite (Neqb_correct (Ndiv2 a')) in H. discriminate H.
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

Definition Nle (a b:N) := leb (nat_of_N a) (nat_of_N b).

Lemma Nle_Ncompare : forall a b, Nle a b = true <-> Ncompare a b <> Gt.
Proof.
 intros; rewrite nat_of_Ncompare.
 unfold Nle; apply leb_compare.
Qed.

Lemma Nle_refl : forall a, Nle a a = true.
Proof.
  intro. unfold Nle in |- *. apply leb_correct. apply le_n.
Qed.

Lemma Nle_antisym :
 forall a b, Nle a b = true -> Nle b a = true -> a = b.
Proof.
  unfold Nle in |- *. intros. rewrite <- (N_of_nat_of_N a). rewrite <- (N_of_nat_of_N b).
  rewrite (le_antisym _ _ (leb_complete _ _ H) (leb_complete _ _ H0)). reflexivity.
Qed.

Lemma Nle_trans :
 forall a b c, Nle a b = true -> Nle b c = true -> Nle a c = true.
Proof.
  unfold Nle in |- *. intros. apply leb_correct. apply le_trans with (m := nat_of_N b).
  apply leb_complete. assumption.
  apply leb_complete. assumption.
Qed.

Lemma Nle_lt_trans :
 forall a b c,
   Nle a b = true -> Nle c b = false -> Nle c a = false.
Proof.
  unfold Nle in |- *. intros. apply leb_correct_conv. apply le_lt_trans with (m := nat_of_N b).
  apply leb_complete. assumption.
  apply leb_complete_conv. assumption.
Qed.

Lemma Nlt_le_trans :
 forall a b c,
   Nle b a = false -> Nle b c = true -> Nle c a = false.
Proof.
  unfold Nle in |- *. intros. apply leb_correct_conv. apply lt_le_trans with (m := nat_of_N b).
  apply leb_complete_conv. assumption.
  apply leb_complete. assumption.
Qed.

Lemma Nlt_trans :
 forall a b c,
   Nle b a = false -> Nle c b = false -> Nle c a = false.
Proof.
  unfold Nle in |- *. intros. apply leb_correct_conv. apply lt_trans with (m := nat_of_N b).
  apply leb_complete_conv. assumption.
  apply leb_complete_conv. assumption.
Qed.

Lemma Nlt_le_weak : forall a b:N, Nle b a = false -> Nle a b = true.
Proof.
  unfold Nle in |- *. intros. apply leb_correct. apply lt_le_weak.
  apply leb_complete_conv. assumption.
Qed.

Lemma Nle_double_mono :
 forall a b,
   Nle a b = true -> Nle (Ndouble a) (Ndouble b) = true.
Proof.
  unfold Nle in |- *. intros. rewrite nat_of_Ndouble. rewrite nat_of_Ndouble. apply leb_correct.
  simpl in |- *. apply plus_le_compat. apply leb_complete. assumption.
  apply plus_le_compat. apply leb_complete. assumption.
  apply le_n.
Qed.

Lemma Nle_double_plus_one_mono :
 forall a b,
   Nle a b = true ->
   Nle (Ndouble_plus_one a) (Ndouble_plus_one b) = true.
Proof.
  unfold Nle in |- *. intros. rewrite nat_of_Ndouble_plus_one. rewrite nat_of_Ndouble_plus_one.
  apply leb_correct. apply le_n_S. simpl in |- *. apply plus_le_compat. apply leb_complete.
  assumption.
  apply plus_le_compat. apply leb_complete. assumption.
  apply le_n.
Qed.

Lemma Nle_double_mono_conv :
 forall a b,
   Nle (Ndouble a) (Ndouble b) = true -> Nle a b = true.
Proof.
  unfold Nle in |- *. intros a b. rewrite nat_of_Ndouble. rewrite nat_of_Ndouble. intro.
  apply leb_correct. apply (mult_S_le_reg_l 1). apply leb_complete. assumption.
Qed.

Lemma Nle_double_plus_one_mono_conv :
 forall a b,
   Nle (Ndouble_plus_one a) (Ndouble_plus_one b) = true ->
   Nle a b = true.
Proof.
  unfold Nle in |- *. intros a b. rewrite nat_of_Ndouble_plus_one. rewrite nat_of_Ndouble_plus_one.
  intro. apply leb_correct. apply (mult_S_le_reg_l 1). apply le_S_n. apply leb_complete.
  assumption.
Qed.

Lemma Nlt_double_mono :
 forall a b,
   Nle a b = false -> Nle (Ndouble a) (Ndouble b) = false.
Proof.
  intros. elim (sumbool_of_bool (Nle (Ndouble a) (Ndouble b))). intro H0.
  rewrite (Nle_double_mono_conv _ _ H0) in H. discriminate H.
  trivial.
Qed.

Lemma Nlt_double_plus_one_mono :
 forall a b,
   Nle a b = false ->
   Nle (Ndouble_plus_one a) (Ndouble_plus_one b) = false.
Proof.
  intros. elim (sumbool_of_bool (Nle (Ndouble_plus_one a) (Ndouble_plus_one b))). intro H0.
  rewrite (Nle_double_plus_one_mono_conv _ _ H0) in H. discriminate H.
  trivial.
Qed.

Lemma Nlt_double_mono_conv :
 forall a b,
   Nle (Ndouble a) (Ndouble b) = false -> Nle a b = false.
Proof.
  intros. elim (sumbool_of_bool (Nle a b)). intro H0. rewrite (Nle_double_mono _ _ H0) in H.
  discriminate H.
  trivial.
Qed.

Lemma Nlt_double_plus_one_mono_conv :
 forall a b,
   Nle (Ndouble_plus_one a) (Ndouble_plus_one b) = false ->
   Nle a b = false.
Proof.
  intros. elim (sumbool_of_bool (Nle a b)). intro H0.
  rewrite (Nle_double_plus_one_mono _ _ H0) in H. discriminate H.
  trivial.
Qed.

(* A [min] function over [N] *)

Definition Nmin (a b:N) := if Nle a b then a else b.

Lemma Nmin_choice : forall a b, {Nmin a b = a} + {Nmin a b = b}.
Proof.
  unfold Nmin in |- *. intros. elim (sumbool_of_bool (Nle a b)). intro H. left. rewrite H.
  reflexivity.
  intro H. right. rewrite H. reflexivity.
Qed.

Lemma Nmin_le_1 : forall a b, Nle (Nmin a b) a = true.
Proof.
  unfold Nmin in |- *. intros. elim (sumbool_of_bool (Nle a b)). intro H. rewrite H.
  apply Nle_refl.
  intro H. rewrite H. apply Nlt_le_weak. assumption.
Qed.

Lemma Nmin_le_2 : forall a b, Nle (Nmin a b) b = true.
Proof.
  unfold Nmin in |- *. intros. elim (sumbool_of_bool (Nle a b)). intro H. rewrite H. assumption.
  intro H. rewrite H. apply Nle_refl.
Qed.

Lemma Nmin_le_3 :
 forall a b c, Nle a (Nmin b c) = true -> Nle a b = true.
Proof.
  unfold Nmin in |- *. intros. elim (sumbool_of_bool (Nle b c)). intro H0. rewrite H0 in H.
  assumption.
  intro H0. rewrite H0 in H. apply Nlt_le_weak. apply Nle_lt_trans with (b := c); assumption.
Qed.

Lemma Nmin_le_4 :
 forall a b c, Nle a (Nmin b c) = true -> Nle a c = true.
Proof.
  unfold Nmin in |- *. intros. elim (sumbool_of_bool (Nle b c)). intro H0. rewrite H0 in H.
  apply Nle_trans with (b := b); assumption.
  intro H0. rewrite H0 in H. assumption.
Qed.

Lemma Nmin_le_5 :
 forall a b c,
   Nle a b = true -> Nle a c = true -> Nle a (Nmin b c) = true.
Proof.
  intros. elim (Nmin_choice b c). intro H1. rewrite H1. assumption.
  intro H1. rewrite H1. assumption.
Qed.

Lemma Nmin_lt_3 :
 forall a b c, Nle (Nmin b c) a = false -> Nle b a = false.
Proof.
  unfold Nmin in |- *. intros. elim (sumbool_of_bool (Nle b c)). intro H0. rewrite H0 in H.
  assumption.
  intro H0. rewrite H0 in H. apply Nlt_trans with (b := c); assumption.
Qed.

Lemma Nmin_lt_4 :
 forall a b c, Nle (Nmin b c) a = false -> Nle c a = false.
Proof.
  unfold Nmin in |- *. intros. elim (sumbool_of_bool (Nle b c)). intro H0. rewrite H0 in H.
  apply Nlt_le_trans with (b := b); assumption.
  intro H0. rewrite H0 in H. assumption.
Qed.

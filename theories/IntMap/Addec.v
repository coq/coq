(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

(** Equality on adresses *)

Require Import Bool.
Require Import Sumbool.
Require Import ZArith.
Require Import Addr.

Fixpoint ad_eq_1 (p1 p2:positive) {struct p2} : bool :=
  match p1, p2 with
  | xH, xH => true
  | xO p'1, xO p'2 => ad_eq_1 p'1 p'2
  | xI p'1, xI p'2 => ad_eq_1 p'1 p'2
  | _, _ => false
  end.

Definition ad_eq (a a':ad) :=
  match a, a' with
  | ad_z, ad_z => true
  | ad_x p, ad_x p' => ad_eq_1 p p'
  | _, _ => false
  end.

Lemma ad_eq_correct : forall a:ad, ad_eq a a = true.
Proof.
  destruct a; trivial.
  induction p; trivial.
Qed.

Lemma ad_eq_complete : forall a a':ad, ad_eq a a' = true -> a = a'.
Proof.
  destruct a. destruct a'; trivial. destruct p.
  discriminate 1.
  discriminate 1.
  discriminate 1.
  destruct a'. intros. discriminate H.
  unfold ad_eq in |- *. intros. cut (p = p0). intros. rewrite H0. reflexivity.
  generalize dependent p0.
  induction p as [p IHp| p IHp| ]. destruct p0; intro H.
  rewrite (IHp p0). reflexivity.
  exact H.
  discriminate H.
  discriminate H.
  destruct p0; intro H. discriminate H.
  rewrite (IHp p0 H). reflexivity.
  discriminate H.
  destruct p0 as [p| p| ]; intro H. discriminate H.
  discriminate H.
  trivial.
Qed.

Lemma ad_eq_comm : forall a a':ad, ad_eq a a' = ad_eq a' a.
Proof.
  intros. cut (forall b b':bool, ad_eq a a' = b -> ad_eq a' a = b' -> b = b').
  intros. apply H. reflexivity.
  reflexivity.
  destruct b. intros. cut (a = a').
  intro. rewrite H1 in H0. rewrite (ad_eq_correct a') in H0. exact H0.
  apply ad_eq_complete. exact H.
  destruct b'. intros. cut (a' = a).
  intro. rewrite H1 in H. rewrite H1 in H0. rewrite <- H. exact H0.
  apply ad_eq_complete. exact H0.
  trivial.
Qed.

Lemma ad_xor_eq_true :
 forall a a':ad, ad_xor a a' = ad_z -> ad_eq a a' = true.
Proof.
  intros. rewrite (ad_xor_eq a a' H). apply ad_eq_correct.
Qed.

Lemma ad_xor_eq_false :
 forall (a a':ad) (p:positive), ad_xor a a' = ad_x p -> ad_eq a a' = false.
Proof.
  intros. elim (sumbool_of_bool (ad_eq a a')). intro H0.
  rewrite (ad_eq_complete a a' H0) in H. rewrite (ad_xor_nilpotent a') in H. discriminate H.
  trivial.
Qed.

Lemma ad_bit_0_1_not_double :
 forall a:ad,
   ad_bit_0 a = true -> forall a0:ad, ad_eq (ad_double a0) a = false.
Proof.
  intros. elim (sumbool_of_bool (ad_eq (ad_double a0) a)). intro H0.
  rewrite <- (ad_eq_complete _ _ H0) in H. rewrite (ad_double_bit_0 a0) in H. discriminate H.
  trivial.
Qed.

Lemma ad_not_div_2_not_double :
 forall a a0:ad,
   ad_eq (ad_div_2 a) a0 = false -> ad_eq a (ad_double a0) = false.
Proof.
  intros. elim (sumbool_of_bool (ad_eq (ad_double a0) a)). intro H0.
  rewrite <- (ad_eq_complete _ _ H0) in H. rewrite (ad_double_div_2 a0) in H.
  rewrite (ad_eq_correct a0) in H. discriminate H.
  intro. rewrite ad_eq_comm. assumption.
Qed.

Lemma ad_bit_0_0_not_double_plus_un :
 forall a:ad,
   ad_bit_0 a = false -> forall a0:ad, ad_eq (ad_double_plus_un a0) a = false.
Proof.
  intros. elim (sumbool_of_bool (ad_eq (ad_double_plus_un a0) a)). intro H0.
  rewrite <- (ad_eq_complete _ _ H0) in H. rewrite (ad_double_plus_un_bit_0 a0) in H.
  discriminate H.
  trivial.
Qed.

Lemma ad_not_div_2_not_double_plus_un :
 forall a a0:ad,
   ad_eq (ad_div_2 a) a0 = false -> ad_eq (ad_double_plus_un a0) a = false.
Proof.
  intros. elim (sumbool_of_bool (ad_eq a (ad_double_plus_un a0))). intro H0.
  rewrite (ad_eq_complete _ _ H0) in H. rewrite (ad_double_plus_un_div_2 a0) in H.
  rewrite (ad_eq_correct a0) in H. discriminate H.
  intro H0. rewrite ad_eq_comm. assumption.
Qed.

Lemma ad_bit_0_neq :
 forall a a':ad,
   ad_bit_0 a = false -> ad_bit_0 a' = true -> ad_eq a a' = false.
Proof.
  intros. elim (sumbool_of_bool (ad_eq a a')). intro H1. rewrite (ad_eq_complete _ _ H1) in H.
  rewrite H in H0. discriminate H0.
  trivial.
Qed.

Lemma ad_div_eq :
 forall a a':ad, ad_eq a a' = true -> ad_eq (ad_div_2 a) (ad_div_2 a') = true.
Proof.
  intros. cut (a = a'). intros. rewrite H0. apply ad_eq_correct.
  apply ad_eq_complete. exact H.
Qed.

Lemma ad_div_neq :
 forall a a':ad,
   ad_eq (ad_div_2 a) (ad_div_2 a') = false -> ad_eq a a' = false.
Proof.
  intros. elim (sumbool_of_bool (ad_eq a a')). intro H0.
  rewrite (ad_eq_complete _ _ H0) in H. rewrite (ad_eq_correct (ad_div_2 a')) in H. discriminate H.
  trivial.
Qed.

Lemma ad_div_bit_eq :
 forall a a':ad,
   ad_bit_0 a = ad_bit_0 a' -> ad_div_2 a = ad_div_2 a' -> a = a'.
Proof.
  intros. apply ad_faithful. unfold eqf in |- *. destruct n.
  rewrite ad_bit_0_correct. rewrite ad_bit_0_correct. assumption.
  rewrite <- ad_div_2_correct. rewrite <- ad_div_2_correct.
  rewrite H0. reflexivity.
Qed.

Lemma ad_div_bit_neq :
 forall a a':ad,
   ad_eq a a' = false ->
   ad_bit_0 a = ad_bit_0 a' -> ad_eq (ad_div_2 a) (ad_div_2 a') = false.
Proof.
  intros. elim (sumbool_of_bool (ad_eq (ad_div_2 a) (ad_div_2 a'))). intro H1.
  rewrite (ad_div_bit_eq _ _ H0 (ad_eq_complete _ _ H1)) in H.
  rewrite (ad_eq_correct a') in H. discriminate H.
  trivial.
Qed.

Lemma ad_neq :
 forall a a':ad,
   ad_eq a a' = false ->
   ad_bit_0 a = negb (ad_bit_0 a') \/
   ad_eq (ad_div_2 a) (ad_div_2 a') = false.
Proof.
  intros. cut (ad_bit_0 a = ad_bit_0 a' \/ ad_bit_0 a = negb (ad_bit_0 a')).
  intros. elim H0. intro. right. apply ad_div_bit_neq. assumption.
  assumption.
  intro. left. assumption.
  case (ad_bit_0 a); case (ad_bit_0 a'); auto.
Qed.

Lemma ad_double_or_double_plus_un :
 forall a:ad,
   {a0 : ad | a = ad_double a0} + {a1 : ad | a = ad_double_plus_un a1}.
Proof.
  intro. elim (sumbool_of_bool (ad_bit_0 a)). intro H. right. split with (ad_div_2 a).
  rewrite (ad_div_2_double_plus_un a H). reflexivity.
  intro H. left. split with (ad_div_2 a). rewrite (ad_div_2_double a H). reflexivity.
Qed.
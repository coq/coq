(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Arith_base.
Require Import Compare_dec.
Require Import Sumbool.
Require Import Div2.
Require Import BinPos.
Require Import BinNat.
Require Import Pnat.

(** Translation from [N] to [nat] and back. *)

Definition nat_of_N (a:N) :=
  match a with
  | N0 => 0%nat
  | Npos p => nat_of_P p
  end.

Definition N_of_nat (n:nat) :=
  match n with
  | O => N0
  | S n' => Npos (P_of_succ_nat n')
  end.

Lemma N_of_nat_of_N : forall a:N, N_of_nat (nat_of_N a) = a.
Proof.
  destruct a as [| p]. reflexivity.
  simpl in |- *. elim (ZL4 p). intros n H. rewrite H. simpl in |- *. 
  rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ in H.
  rewrite nat_of_P_inj with (1 := H). reflexivity.
Qed.

Lemma nat_of_N_of_nat : forall n:nat, nat_of_N (N_of_nat n) = n.
Proof.
  induction n. trivial.
  intros. simpl in |- *. apply nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.

(** Interaction of this translation and usual operations. *)

Lemma nat_of_Ndouble : forall a, nat_of_N (Ndouble a) = 2*(nat_of_N a).
Proof.
  destruct a; simpl nat_of_N; auto.
  apply nat_of_P_xO.
Qed.

Lemma N_of_double : forall n, N_of_nat (2*n) = Ndouble (N_of_nat n).
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  rewrite <- nat_of_Ndouble.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Ndouble_plus_one : 
  forall a, nat_of_N (Ndouble_plus_one a) = S (2*(nat_of_N a)).
Proof.
  destruct a; simpl nat_of_N; auto.
  apply nat_of_P_xI.
Qed.

Lemma N_of_double_plus_one : 
  forall n, N_of_nat (S (2*n)) = Ndouble_plus_one (N_of_nat n).
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  rewrite <- nat_of_Ndouble_plus_one.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Nsucc : forall a, nat_of_N (Nsucc a) = S (nat_of_N a).
Proof.
  destruct a; simpl.
  apply nat_of_P_xH.
  apply nat_of_P_succ_morphism.
Qed.

Lemma N_of_S : forall n, N_of_nat (S n) = Nsucc (N_of_nat n).
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  rewrite <- nat_of_Nsucc.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Nplus : 
  forall a a', nat_of_N (Nplus a a') = (nat_of_N a)+(nat_of_N a').
Proof.
  destruct a; destruct a'; simpl; auto.
  apply nat_of_P_plus_morphism.
Qed.

Lemma N_of_plus : 
  forall n n', N_of_nat (n+n') = Nplus (N_of_nat n) (N_of_nat n').
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  pattern n' at 1; rewrite <- (nat_of_N_of_nat n').
  rewrite <- nat_of_Nplus.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Nmult : 
  forall a a', nat_of_N (Nmult a a') = (nat_of_N a)*(nat_of_N a').
Proof.
  destruct a; destruct a'; simpl; auto.
  apply nat_of_P_mult_morphism.
Qed.

Lemma N_of_mult : 
  forall n n', N_of_nat (n*n') = Nmult (N_of_nat n) (N_of_nat n').
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  pattern n' at 1; rewrite <- (nat_of_N_of_nat n').
  rewrite <- nat_of_Nmult.
  apply N_of_nat_of_N.
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

Lemma N_of_div2 : 
  forall n, N_of_nat (div2 n) = Ndiv2 (N_of_nat n).
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  rewrite <- nat_of_Ndiv2.
  apply N_of_nat_of_N.
Qed.

Lemma nat_of_Ncompare : 
 forall a a', Ncompare a a' = nat_compare (nat_of_N a) (nat_of_N a').
Proof.
  destruct a; destruct a'; simpl.
  compute; auto.
  generalize (lt_O_nat_of_P p).
  unfold nat_compare.
  destruct (lt_eq_lt_dec 0 (nat_of_P p)) as [[H|H]|H]; auto.
  rewrite <- H; inversion 1.
  intros; generalize (lt_trans _ _ _ H0 H); inversion 1.
  generalize (lt_O_nat_of_P p).
  unfold nat_compare.
  destruct (lt_eq_lt_dec (nat_of_P p) 0) as [[H|H]|H]; auto.
  intros; generalize (lt_trans _ _ _ H0 H); inversion 1.
  rewrite H; inversion 1.
  unfold nat_compare.
  destruct (lt_eq_lt_dec (nat_of_P p) (nat_of_P p0)) as [[H|H]|H]; auto.
  apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
  rewrite (nat_of_P_inj _ _ H); apply Pcompare_refl.
  apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
Qed.

Lemma N_of_nat_compare : 
 forall n n', nat_compare n n' = Ncompare (N_of_nat n) (N_of_nat n').
Proof.
  intros.
  pattern n at 1; rewrite <- (nat_of_N_of_nat n).
  pattern n' at 1; rewrite <- (nat_of_N_of_nat n').
  symmetry; apply nat_of_Ncompare.
Qed.

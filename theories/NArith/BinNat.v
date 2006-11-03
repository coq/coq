(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import BinPos.
Unset Boxed Definitions.

(**********************************************************************)
(** Binary natural numbers *)

Inductive N : Set :=
  | N0 : N
  | Npos : positive -> N.

(** Declare binding key for scope positive_scope *)

Delimit Scope N_scope with N.

(** Automatically open scope positive_scope for the constructors of N *)

Bind Scope N_scope with N.
Arguments Scope Npos [positive_scope].

Open Local Scope N_scope.

Definition Ndiscr : forall n:N, { p:positive | n = Npos p } + { n = N0 }.
Proof.
 destruct n; auto.
 left; exists p; auto.
Defined.

(** Operation x -> 2*x+1 *)

Definition Ndouble_plus_one x :=
  match x with
  | N0 => Npos 1
  | Npos p => Npos (xI p)
  end.

(** Operation x -> 2*x *)

Definition Ndouble n := 
  match n with
  | N0 => N0
  | Npos p => Npos (xO p)
  end.

(** Successor *)

Definition Nsucc n :=
  match n with
  | N0 => Npos 1
  | Npos p => Npos (Psucc p)
  end.

(** Addition *)

Definition Nplus n m :=
  match n, m with
  | N0, _ => m
  | _, N0 => n
  | Npos p, Npos q => Npos (p + q)
  end.

Infix "+" := Nplus : N_scope.

(** Multiplication *)

Definition Nmult n m :=
  match n, m with
  | N0, _ => N0
  | _, N0 => N0
  | Npos p, Npos q => Npos (p * q)
  end.

Infix "*" := Nmult : N_scope.

(** Order *)

Definition Ncompare n m :=
  match n, m with
  | N0, N0 => Eq
  | N0, Npos m' => Lt
  | Npos n', N0 => Gt
  | Npos n', Npos m' => (n' ?= m')%positive Eq
  end.

Infix "?=" := Ncompare (at level 70, no associativity) : N_scope.

(** convenient induction principles *)

Lemma N_ind_double :
 forall (a:N) (P:N -> Prop),
   P N0 ->
   (forall a, P a -> P (Ndouble a)) ->
   (forall a, P a -> P (Ndouble_plus_one a)) -> P a.
Proof.
  intros; elim a. trivial.
  simple induction p. intros. 
  apply (H1 (Npos p0)); trivial.
  intros; apply (H0 (Npos p0)); trivial.
  intros; apply (H1 N0); assumption.
Qed.

Lemma N_rec_double :
 forall (a:N) (P:N -> Set),
   P N0 ->
   (forall a, P a -> P (Ndouble a)) ->
   (forall a, P a -> P (Ndouble_plus_one a)) -> P a.
Proof.
  intros; elim a. trivial.
  simple induction p. intros. 
  apply (H1 (Npos p0)); trivial.
  intros; apply (H0 (Npos p0)); trivial.
  intros; apply (H1 N0); assumption.
Qed.

(** Peano induction on binary natural numbers *)

Theorem Nind :
 forall P:N -> Prop,
   P N0 -> (forall n:N, P n -> P (Nsucc n)) -> forall n:N, P n.
Proof.
destruct n.
  assumption.
  apply Pind with (P := fun p => P (Npos p)).
exact (H0 N0 H).
intro p'; exact (H0 (Npos p')).
Qed.

(** Properties of addition *)

Theorem Nplus_0_l : forall n:N, N0 + n = n.
Proof.
reflexivity.
Qed.

Theorem Nplus_0_r : forall n:N, n + N0 = n.
Proof.
destruct n; reflexivity.
Qed.

Theorem Nplus_comm : forall n m:N, n + m = m + n.
Proof.
intros.
destruct n; destruct m; simpl in |- *; try reflexivity.
rewrite Pplus_comm; reflexivity.
Qed.

Theorem Nplus_assoc : forall n m p:N, n + (m + p) = n + m + p.
Proof.
intros.
destruct n; try reflexivity.
destruct m; try reflexivity.
destruct p; try reflexivity.
simpl in |- *; rewrite Pplus_assoc; reflexivity.
Qed.

Theorem Nplus_succ : forall n m:N, Nsucc n + m = Nsucc (n + m).
Proof.
destruct n; destruct m.
  simpl in |- *; reflexivity.
  unfold Nsucc, Nplus in |- *; rewrite <- Pplus_one_succ_l; reflexivity.
  simpl in |- *; reflexivity.
  simpl in |- *; rewrite Pplus_succ_permute_l; reflexivity.
Qed.

Theorem Nsucc_inj : forall n m:N, Nsucc n = Nsucc m -> n = m.
Proof.
destruct n; destruct m; simpl in |- *; intro H; reflexivity || injection H;
 clear H; intro H.
  symmetry  in H; contradiction Psucc_not_one with p.
  contradiction Psucc_not_one with p.
  rewrite Psucc_inj with (1 := H); reflexivity.
Qed.

Theorem Nplus_reg_l : forall n m p:N, n + m = n + p -> m = p.
Proof.
intro n; pattern n in |- *; apply Nind; clear n; simpl in |- *.
  trivial.
  intros n IHn m p H0; do 2 rewrite Nplus_succ in H0.
  apply IHn; apply Nsucc_inj; assumption.
Qed.

(** Properties of multiplication *)

Theorem Nmult_1_l : forall n:N, Npos 1 * n = n.
Proof.
destruct n; reflexivity.
Qed.

Theorem Nmult_1_r : forall n:N, n * Npos 1%positive = n.
Proof.
destruct n; simpl in |- *; try reflexivity.
rewrite Pmult_1_r; reflexivity.
Qed.

Theorem Nmult_comm : forall n m:N, n * m = m * n.
Proof.
intros.
destruct n; destruct m; simpl in |- *; try reflexivity.
rewrite Pmult_comm; reflexivity.
Qed.

Theorem Nmult_assoc : forall n m p:N, n * (m * p) = n * m * p.
Proof.
intros.
destruct n; try reflexivity.
destruct m; try reflexivity.
destruct p; try reflexivity.
simpl in |- *; rewrite Pmult_assoc; reflexivity.
Qed.

Theorem Nmult_plus_distr_r : forall n m p:N, (n + m) * p = n * p + m * p.
Proof.
intros.
destruct n; try reflexivity.
destruct m; destruct p; try reflexivity.
simpl in |- *; rewrite Pmult_plus_distr_r; reflexivity.
Qed.

Theorem Nmult_reg_r : forall n m p:N, p <> N0 -> n * p = m * p -> n = m.
Proof.
destruct p; intros Hp H.
contradiction Hp; reflexivity.
destruct n; destruct m; reflexivity || (try discriminate H).
injection H; clear H; intro H; rewrite Pmult_reg_r with (1 := H); reflexivity.
Qed. 

Theorem Nmult_0_l : forall n:N, N0 * n = N0.
Proof.
reflexivity.
Qed.

(** Properties of comparison *)

Theorem Ncompare_Eq_eq : forall n m:N, (n ?= m) = Eq -> n = m.
Proof.
destruct n as [| n]; destruct m as [| m]; simpl in |- *; intro H;
 reflexivity || (try discriminate H).
  rewrite (Pcompare_Eq_eq n m H); reflexivity.
Qed.

Lemma Ncompare_refl : forall n, (n ?= n) = Eq.
Proof.
destruct n; simpl; auto.
apply Pcompare_refl.
Qed.

Lemma Ncompare_antisym : forall n m, CompOpp (n ?= m) = (m ?= n).
Proof.
destruct n; destruct m; simpl; auto.
exact (Pcompare_antisym p p0 Eq).
Qed.

(** Dividing by 2 *)

Definition Ndiv2 (n:N) :=
  match n with
  | N0 => N0
  | Npos 1 => N0
  | Npos (xO p) => Npos p
  | Npos (xI p) => Npos p
  end.

Lemma Ndouble_div2 : forall n:N, Ndiv2 (Ndouble n) = n.
Proof.
  destruct n; trivial.
Qed.

Lemma Ndouble_plus_one_div2 :
 forall n:N, Ndiv2 (Ndouble_plus_one n) = n.
Proof.
  destruct n; trivial.
Qed.

Lemma Ndouble_inj : forall n m, Ndouble n = Ndouble m -> n = m.
Proof.
  intros. rewrite <- (Ndouble_div2 n). rewrite H. apply Ndouble_div2.
Qed.

Lemma Ndouble_plus_one_inj :
 forall n m, Ndouble_plus_one n = Ndouble_plus_one m -> n = m.
Proof.
  intros. rewrite <- (Ndouble_plus_one_div2 n). rewrite H. apply Ndouble_plus_one_div2.
Qed.

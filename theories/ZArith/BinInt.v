(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export BinNums BinPos Pnat.
Require Import BinNat Plus Mult.

(***********************************************************)
(** * Binary Integers *)
(***********************************************************)

(** Initial author: Pierre Crégut, CNET, Lannion, France *)

(** The type [Z] and its constructors [Z0] and [Zpos] and [Zneg]
    are now defined in [BinNums.v] *)

Local Open Scope Z_scope.

(*************************************)
(** * Basic operations *)

(** ** Subtraction of positive into Z *)

Definition Zdouble_plus_one (x:Z) :=
  match x with
    | Z0 => Zpos 1
    | Zpos p => Zpos p~1
    | Zneg p => Zneg (Pdouble_minus_one p)
  end.

Definition Zdouble_minus_one (x:Z) :=
  match x with
    | Z0 => Zneg 1
    | Zneg p => Zneg p~1
    | Zpos p => Zpos (Pdouble_minus_one p)
  end.

Definition Zdouble (x:Z) :=
  match x with
    | Z0 => Z0
    | Zpos p => Zpos p~0
    | Zneg p => Zneg p~0
  end.

Fixpoint ZPminus (x y:positive) {struct y} : Z :=
  match x, y with
    | p~1, q~1 => Zdouble (ZPminus p q)
    | p~1, q~0 => Zdouble_plus_one (ZPminus p q)
    | p~1, 1 => Zpos p~0
    | p~0, q~1 => Zdouble_minus_one (ZPminus p q)
    | p~0, q~0 => Zdouble (ZPminus p q)
    | p~0, 1 => Zpos (Pdouble_minus_one p)
    | 1, q~1 => Zneg q~0
    | 1, q~0 => Zneg (Pdouble_minus_one q)
    | 1, 1 => Z0
  end%positive.

(** ** Addition on integers *)

Definition Zplus (x y:Z) :=
  match x, y with
    | Z0, y => y
    | Zpos x', Z0 => Zpos x'
    | Zneg x', Z0 => Zneg x'
    | Zpos x', Zpos y' => Zpos (x' + y')
    | Zpos x', Zneg y' =>
      match (x' ?= y')%positive with
	| Eq => Z0
	| Lt => Zneg (y' - x')
	| Gt => Zpos (x' - y')
      end
    | Zneg x', Zpos y' =>
      match (x' ?= y')%positive with
	| Eq => Z0
	| Lt => Zpos (y' - x')
	| Gt => Zneg (x' - y')
      end
    | Zneg x', Zneg y' => Zneg (x' + y')
  end.

Infix "+" := Zplus : Z_scope.

(** ** Opposite *)

Definition Zopp (x:Z) :=
  match x with
    | Z0 => Z0
    | Zpos x => Zneg x
    | Zneg x => Zpos x
  end.

Notation "- x" := (Zopp x) : Z_scope.

(** ** Successor on integers *)

Definition Zsucc (x:Z) := (x + Zpos 1)%Z.

(** ** Predecessor on integers *)

Definition Zpred (x:Z) := (x + Zneg 1)%Z.

(** ** Subtraction on integers *)

Definition Zminus (m n:Z) := (m + - n)%Z.

Infix "-" := Zminus : Z_scope.

(** ** Multiplication on integers *)

Definition Zmult (x y:Z) :=
  match x, y with
    | Z0, _ => Z0
    | _, Z0 => Z0
    | Zpos x', Zpos y' => Zpos (x' * y')
    | Zpos x', Zneg y' => Zneg (x' * y')
    | Zneg x', Zpos y' => Zneg (x' * y')
    | Zneg x', Zneg y' => Zpos (x' * y')
  end.

Infix "*" := Zmult : Z_scope.

(** ** Comparison of integers *)

Definition Zcompare (x y:Z) :=
  match x, y with
    | Z0, Z0 => Eq
    | Z0, Zpos y' => Lt
    | Z0, Zneg y' => Gt
    | Zpos x', Z0 => Gt
    | Zpos x', Zpos y' => (x' ?= y')%positive
    | Zpos x', Zneg y' => Gt
    | Zneg x', Z0 => Lt
    | Zneg x', Zpos y' => Lt
    | Zneg x', Zneg y' => CompOpp ((x' ?= y')%positive)
  end.

Infix "?=" := Zcompare (at level 70, no associativity) : Z_scope.

Ltac elim_compare com1 com2 :=
  case (Dcompare (com1 ?= com2)%Z);
    [ idtac | let x := fresh "H" in
      (intro x; case x; clear x) ].

(** ** Sign function *)

Definition Zsgn (z:Z) : Z :=
  match z with
    | Z0 => Z0
    | Zpos p => Zpos 1
    | Zneg p => Zneg 1
  end.

(** ** Direct, easier to handle variants of successor and addition *)

Definition Zsucc' (x:Z) :=
  match x with
    | Z0 => Zpos 1
    | Zpos x' => Zpos (Psucc x')
    | Zneg x' => ZPminus 1 x'
  end.

Definition Zpred' (x:Z) :=
  match x with
    | Z0 => Zneg 1
    | Zpos x' => ZPminus x' 1
    | Zneg x' => Zneg (Psucc x')
  end.

Definition Zplus' (x y:Z) :=
  match x, y with
    | Z0, y => y
    | x, Z0 => x
    | Zpos x', Zpos y' => Zpos (x' + y')
    | Zpos x', Zneg y' => ZPminus x' y'
    | Zneg x', Zpos y' => ZPminus y' x'
    | Zneg x', Zneg y' => Zneg (x' + y')
  end.

(**********************************************************************)
(** ** Inductive specification of Z *)

Theorem Zind :
  forall P:Z -> Prop,
    P Z0 ->
    (forall x:Z, P x -> P (Zsucc' x)) ->
    (forall x:Z, P x -> P (Zpred' x)) -> forall n:Z, P n.
Proof.
  intros P H0 Hs Hp z; destruct z.
  assumption.
  apply Pind with (P := fun p => P (Zpos p)).
    change (P (Zsucc' Z0)); apply Hs; apply H0.
    intro n; exact (Hs (Zpos n)).
  apply Pind with (P := fun p => P (Zneg p)).
    change (P (Zpred' Z0)); apply Hp; apply H0.
    intro n; exact (Hp (Zneg n)).
Qed.

(**********************************************************************)
(** * Misc properties about binary integer operations *)

(**********************************************************************)
(** ** Properties of opposite on binary integer numbers *)

Theorem Zopp_0 : Zopp Z0 = Z0.
Proof.
  reflexivity.
Qed.

Theorem Zopp_neg : forall p:positive, - Zneg p = Zpos p.
Proof.
  reflexivity.
Qed.

(** [opp] is involutive *)

Theorem Zopp_involutive : forall n:Z, - - n = n.
Proof.
  intro x; destruct x; reflexivity.
Qed.

(** Injectivity of the opposite *)

Theorem Zopp_inj : forall n m:Z, - n = - m -> n = m.
Proof.
  intros x y; case x; case y; simpl; intros;
    [ trivial
      | discriminate H
      | discriminate H
      | discriminate H
      | simplify_eq H; intro E; rewrite E; trivial
      | discriminate H
      | discriminate H
      | discriminate H
      | simplify_eq H; intro E; rewrite E; trivial ].
Qed.

(**********************************************************************)
(** ** Other properties of binary integer numbers *)

Lemma ZL0 : 2%nat = (1 + 1)%nat.
Proof.
  reflexivity.
Qed.

(**********************************************************************)
(** * Properties of the addition on integers *)

(** ** Zero is left neutral for addition *)

Theorem Zplus_0_l : forall n:Z, Z0 + n = n.
Proof.
  intro x; destruct x; reflexivity.
Qed.

(** ** Zero is right neutral for addition *)

Theorem Zplus_0_r : forall n:Z, n + Z0 = n.
Proof.
  intro x; destruct x; reflexivity.
Qed.

(** ** Addition is commutative *)

Theorem Zplus_comm : forall n m:Z, n + m = m + n.
Proof.
  induction n as [|p|p]; intros [|q|q]; simpl; try reflexivity.
  rewrite Pplus_comm; reflexivity.
  rewrite Pos.compare_antisym. now case Pcompare_spec.
  rewrite Pos.compare_antisym. now case Pcompare_spec.
  rewrite Pplus_comm; reflexivity.
Qed.

(** ** Opposite distributes over addition *)

Theorem Zopp_plus_distr : forall n m:Z, - (n + m) = - n + - m.
Proof.
  intro x; destruct x as [| p| p]; intro y; destruct y as [| q| q];
    simpl; reflexivity || destruct ((p ?= q)%positive);
      reflexivity.
Qed.

Theorem Zopp_succ : forall n:Z, Zopp (Zsucc n) = Zpred (Zopp n).
Proof.
intro; unfold Zsucc; now rewrite Zopp_plus_distr.
Qed.

(** ** Opposite is inverse for addition *)

Theorem Zplus_opp_r : forall n:Z, n + - n = Z0.
Proof.
  intro x; destruct x as [| p| p]; simpl;
    [ reflexivity
      | rewrite (Pcompare_refl p); reflexivity
      | rewrite (Pcompare_refl p); reflexivity ].
Qed.

Theorem Zplus_opp_l : forall n:Z, - n + n = Z0.
Proof.
  intro; rewrite Zplus_comm; apply Zplus_opp_r.
Qed.

Hint Local Resolve Zplus_0_l Zplus_0_r.

(** ** Addition is associative *)

Lemma weak_assoc :
  forall (p q:positive) (n:Z), Zpos p + (Zpos q + n) = Zpos p + Zpos q + n.
Proof.
 intros x y [|z|z]; simpl; trivial.
 now rewrite Pplus_assoc.
 case (Pcompare_spec y z); intros E0.
 (* y = z *)
 subst.
 assert (H := Plt_plus_r z x). rewrite Pplus_comm in H. apply ZC2 in H.
 now rewrite H, Pplus_minus_eq.
 (* y < z *)
 assert (Hz : (z = (z-y)+y)%positive) by (now rewrite Pos.sub_add).
 pattern z at 4. rewrite Hz, Pplus_compare_mono_r.
 case Pcompare_spec; intros E1; trivial; f_equal.
 symmetry. rewrite Pplus_comm. apply Pminus_plus_distr.
 rewrite Hz, Pplus_comm. now apply Pplus_lt_mono_r.
 apply Pminus_minus_distr; trivial.
 (* z < y *)
 assert (LT : (z < x + y)%positive).
  rewrite Pplus_comm. apply Plt_trans with y; trivial using Plt_plus_r.
 apply ZC2 in LT. rewrite LT. f_equal.
 now apply Pplus_minus_assoc.
Qed.

Theorem Zplus_assoc : forall n m p:Z, n + (m + p) = n + m + p.
Proof.
 intros [|x|x] [|y|y] [|z|z]; trivial.
 apply weak_assoc.
 apply weak_assoc.
 now rewrite !Zplus_0_r.
 rewrite 2 (Zplus_comm _ (Zpos z)), 2 weak_assoc.
  f_equal; apply Zplus_comm.
 apply Zopp_inj. rewrite !Zopp_plus_distr, !Zopp_neg.
  rewrite 2 (Zplus_comm (-Zpos x)), 2 (Zplus_comm _ (Zpos z)).
  now rewrite weak_assoc.
 now rewrite !Zplus_0_r.
 rewrite 2 (Zplus_comm (Zneg x)), 2 (Zplus_comm _ (Zpos z)).
  now rewrite weak_assoc.
 apply Zopp_inj. rewrite !Zopp_plus_distr, !Zopp_neg.
 rewrite 2 (Zplus_comm _ (Zpos z)), 2 weak_assoc.
  f_equal; apply Zplus_comm.
 apply Zopp_inj. rewrite !Zopp_plus_distr, !Zopp_neg.
  apply weak_assoc.
 apply Zopp_inj. rewrite !Zopp_plus_distr, !Zopp_neg.
  apply weak_assoc.
Qed.

Lemma Zplus_assoc_reverse : forall n m p:Z, n + m + p = n + (m + p).
Proof.
  intros; symmetry ; apply Zplus_assoc.
Qed.

(** ** Associativity mixed with commutativity *)

Theorem Zplus_permute : forall n m p:Z, n + (m + p) = m + (n + p).
Proof.
  intros n m p; rewrite Zplus_comm; rewrite <- Zplus_assoc;
    rewrite (Zplus_comm p n); trivial with arith.
Qed.

(** ** Addition simplifies *)

Theorem Zplus_reg_l : forall n m p:Z, n + m = n + p -> m = p.
  intros n m p H; cut (- n + (n + m) = - n + (n + p));
    [ do 2 rewrite Zplus_assoc; rewrite (Zplus_comm (- n) n);
      rewrite Zplus_opp_r; simpl; trivial with arith
      | rewrite H; trivial with arith ].
Qed.

(** ** Addition and successor permutes *)

Lemma Zplus_succ_l : forall n m:Z, Zsucc n + m = Zsucc (n + m).
Proof.
  intros x y; unfold Zsucc; rewrite (Zplus_comm (x + y));
    rewrite Zplus_assoc; rewrite (Zplus_comm (Zpos 1));
      trivial with arith.
Qed.

Lemma Zplus_succ_r_reverse : forall n m:Z, Zsucc (n + m) = n + Zsucc m.
Proof.
  intros n m; unfold Zsucc; rewrite Zplus_assoc; trivial with arith.
Qed.

Notation Zplus_succ_r := Zplus_succ_r_reverse (only parsing).

Lemma Zplus_succ_comm : forall n m:Z, Zsucc n + m = n + Zsucc m.
Proof.
  unfold Zsucc; intros n m; rewrite <- Zplus_assoc;
    rewrite (Zplus_comm (Zpos 1)); trivial with arith.
Qed.

(** ** Misc properties, usually redundant or non natural *)

Lemma Zplus_0_r_reverse : forall n:Z, n = n + Z0.
Proof.
  symmetry ; apply Zplus_0_r.
Qed.

Lemma Zplus_0_simpl_l : forall n m:Z, n + Z0 = m -> n = m.
Proof.
  intros n m; rewrite Zplus_0_r; intro; assumption.
Qed.

Lemma Zplus_0_simpl_l_reverse : forall n m:Z, n = m + Z0 -> n = m.
Proof.
  intros n m; rewrite Zplus_0_r; intro; assumption.
Qed.

Lemma Zplus_eq_compat : forall n m p q:Z, n = m -> p = q -> n + p = m + q.
Proof.
  intros; rewrite H; rewrite H0; reflexivity.
Qed.

Lemma Zplus_opp_expand : forall n m p:Z, n + - m = n + - p + (p + - m).
Proof.
  intros x y z.
  rewrite <- (Zplus_assoc x).
  rewrite (Zplus_assoc (- z)).
  rewrite Zplus_opp_l.
  reflexivity.
Qed.

(************************************************************************)
(** * Properties of successor and predecessor on binary integer numbers *)

Theorem Zsucc_discr : forall n:Z, n <> Zsucc n.
Proof.
  intros n; cut (Z0 <> Zpos 1);
    [ unfold not; intros H1 H2; apply H1; apply (Zplus_reg_l n);
      rewrite Zplus_0_r; exact H2
      | discriminate ].
Qed.

Theorem Zpos_succ_morphism :
  forall p:positive, Zpos (Psucc p) = Zsucc (Zpos p).
Proof.
  intro; rewrite Pplus_one_succ_r; unfold Zsucc; simpl;
    trivial with arith.
Qed.

(** successor and predecessor are inverse functions *)

Theorem Zsucc_pred : forall n:Z, n = Zsucc (Zpred n).
Proof.
  intros n; unfold Zsucc, Zpred; rewrite <- Zplus_assoc; simpl;
    rewrite Zplus_0_r; trivial with arith.
Qed.

Hint Immediate Zsucc_pred: zarith.

Theorem Zpred_succ : forall n:Z, n = Zpred (Zsucc n).
Proof.
  intros m; unfold Zpred, Zsucc; rewrite <- Zplus_assoc; simpl;
    rewrite Zplus_comm; auto with arith.
Qed.

Theorem Zsucc_inj : forall n m:Z, Zsucc n = Zsucc m -> n = m.
Proof.
  intros n m H.
  change (Zneg 1 + Zpos 1 + n = Zneg 1 + Zpos 1 + m);
    do 2 rewrite <- Zplus_assoc; do 2 rewrite (Zplus_comm (Zpos 1));
      unfold Zsucc in H; rewrite H; trivial with arith.
Qed.

(*************************************************************************)
(** **  Properties of the direct definition of successor and predecessor *)

Theorem Zsucc_succ' : forall n:Z, Zsucc n = Zsucc' n.
Proof.
destruct n as [| p | p]; simpl.
reflexivity.
now rewrite Pplus_one_succ_r.
now destruct p as [q | q |].
Qed.

Theorem Zpred_pred' : forall n:Z, Zpred n = Zpred' n.
Proof.
destruct n as [| p | p]; simpl.
reflexivity.
now destruct p as [q | q |].
now rewrite Pplus_one_succ_r.
Qed.

Theorem Zsucc'_inj : forall n m:Z, Zsucc' n = Zsucc' m -> n = m.
Proof.
intros n m; do 2 rewrite <- Zsucc_succ'; now apply Zsucc_inj.
Qed.

Theorem Zsucc'_pred' : forall n:Z, Zsucc' (Zpred' n) = n.
Proof.
intro; rewrite <- Zsucc_succ'; rewrite <- Zpred_pred';
symmetry; apply Zsucc_pred.
Qed.

Theorem Zpred'_succ' : forall n:Z, Zpred' (Zsucc' n) = n.
Proof.
intro; apply Zsucc'_inj; now rewrite Zsucc'_pred'.
Qed.

Theorem Zpred'_inj : forall n m:Z, Zpred' n = Zpred' m -> n = m.
Proof.
intros n m H.
rewrite <- (Zsucc'_pred' n); rewrite <- (Zsucc'_pred' m); now rewrite H.
Qed.

Theorem Zsucc'_discr : forall n:Z, n <> Zsucc' n.
Proof.
  intro x; destruct x; simpl.
  discriminate.
  injection; apply Psucc_discr.
  destruct p; simpl.
    discriminate.
    intro H; symmetry  in H; injection H; apply double_moins_un_xO_discr.
    discriminate.
Qed.

(** Misc properties, usually redundant or non natural *)

Lemma Zsucc_eq_compat : forall n m:Z, n = m -> Zsucc n = Zsucc m.
Proof.
  intros n m H; rewrite H; reflexivity.
Qed.

Lemma Zsucc_inj_contrapositive : forall n m:Z, n <> m -> Zsucc n <> Zsucc m.
Proof.
  unfold not; intros n m H1 H2; apply H1; apply Zsucc_inj; assumption.
Qed.

(**********************************************************************)
(** * Properties of subtraction on binary integer numbers *)

(** ** [minus] and [Z0] *)

Lemma Zminus_0_r : forall n:Z, n - Z0 = n.
Proof.
  intro; unfold Zminus; simpl; rewrite Zplus_0_r;
    trivial with arith.
Qed.

Lemma Zminus_0_l_reverse : forall n:Z, n = n - Z0.
Proof.
  intro; symmetry ; apply Zminus_0_r.
Qed.

Lemma Zminus_diag : forall n:Z, n - n = Z0.
Proof.
  intro; unfold Zminus; rewrite Zplus_opp_r; trivial with arith.
Qed.

Lemma Zminus_diag_reverse : forall n:Z, Z0 = n - n.
Proof.
  intro; symmetry ; apply Zminus_diag.
Qed.


(** ** Relating [minus] with [plus] and [Zsucc] *)

Lemma Zminus_plus_distr : forall n m p:Z, n - (m + p) = n - m - p.
Proof.
intros; unfold Zminus; rewrite Zopp_plus_distr; apply Zplus_assoc.
Qed.

Lemma Zminus_succ_l : forall n m:Z, Zsucc (n - m) = Zsucc n - m.
Proof.
  intros n m; unfold Zminus, Zsucc; rewrite (Zplus_comm n (- m));
    rewrite <- Zplus_assoc; apply Zplus_comm.
Qed.

Lemma Zminus_succ_r : forall n m:Z, n - (Zsucc m) = Zpred (n - m).
Proof.
intros; unfold Zsucc; now rewrite Zminus_plus_distr.
Qed.

Lemma Zplus_minus_eq : forall n m p:Z, n = m + p -> p = n - m.
Proof.
  intros n m p H; unfold Zminus; apply (Zplus_reg_l m);
    rewrite (Zplus_comm m (n + - m)); rewrite <- Zplus_assoc;
      rewrite Zplus_opp_l; rewrite Zplus_0_r; rewrite H;
	trivial with arith.
Qed.

Lemma Zminus_plus : forall n m:Z, n + m - n = m.
Proof.
  intros n m; unfold Zminus; rewrite (Zplus_comm n m);
    rewrite <- Zplus_assoc; rewrite Zplus_opp_r; apply Zplus_0_r.
Qed.

Lemma Zplus_minus : forall n m:Z, n + (m - n) = m.
Proof.
  unfold Zminus; intros n m; rewrite Zplus_permute; rewrite Zplus_opp_r;
    apply Zplus_0_r.
Qed.

Lemma Zminus_plus_simpl_l : forall n m p:Z, p + n - (p + m) = n - m.
Proof.
  intros n m p; unfold Zminus; rewrite Zopp_plus_distr;
    rewrite Zplus_assoc; rewrite (Zplus_comm p); rewrite <- (Zplus_assoc n p);
      rewrite Zplus_opp_r; rewrite Zplus_0_r; trivial with arith.
Qed.

Lemma Zminus_plus_simpl_l_reverse : forall n m p:Z, n - m = p + n - (p + m).
Proof.
  intros; symmetry ; apply Zminus_plus_simpl_l.
Qed.

Lemma Zminus_plus_simpl_r : forall n m p:Z, n + p - (m + p) = n - m.
Proof.
  intros x y n.
  unfold Zminus.
  rewrite Zopp_plus_distr.
  rewrite (Zplus_comm (- y) (- n)).
  rewrite Zplus_assoc.
  rewrite <- (Zplus_assoc x n (- n)).
  rewrite (Zplus_opp_r n).
  rewrite <- Zplus_0_r_reverse.
  reflexivity.
Qed.

Lemma Zpos_minus_morphism : forall a b:positive, Pos.compare a b = Lt ->
  Zpos (b-a) = Zpos b - Zpos a.
Proof.
  intros.
  simpl.
  rewrite Pos.compare_antisym.
  rewrite H; simpl; auto.
Qed.

(** ** Misc redundant properties *)

Lemma Zeq_minus : forall n m:Z, n = m -> n - m = Z0.
Proof.
  intros x y H; rewrite H; symmetry ; apply Zminus_diag_reverse.
Qed.

Lemma Zminus_eq : forall n m:Z, n - m = Z0 -> n = m.
Proof.
  intros x y H; rewrite <- (Zplus_minus y x); rewrite H; apply Zplus_0_r.
Qed.


(**********************************************************************)
(** * Properties of multiplication on binary integer numbers *)

Theorem Zpos_mult_morphism :
  forall p q:positive, Zpos (p*q) = Zpos p * Zpos q.
Proof.
  auto.
Qed.

(** ** One is neutral for multiplication *)

Theorem Zmult_1_l : forall n:Z, Zpos 1 * n = n.
Proof.
  intro x; destruct x; reflexivity.
Qed.

Theorem Zmult_1_r : forall n:Z, n * Zpos 1 = n.
Proof.
  intro x; destruct x; simpl; try rewrite Pmult_1_r; reflexivity.
Qed.

(** ** Zero property of multiplication *)

Theorem Zmult_0_l : forall n:Z, Z0 * n = Z0.
Proof.
  intro x; destruct x; reflexivity.
Qed.

Theorem Zmult_0_r : forall n:Z, n * Z0 = Z0.
Proof.
  intro x; destruct x; reflexivity.
Qed.

Hint Local Resolve Zmult_0_l Zmult_0_r.

Lemma Zmult_0_r_reverse : forall n:Z, Z0 = n * Z0.
Proof.
  intro x; destruct x; reflexivity.
Qed.

(** ** Commutativity of multiplication *)

Theorem Zmult_comm : forall n m:Z, n * m = m * n.
Proof.
  intros x y; destruct x as [| p| p]; destruct y as [| q| q]; simpl;
    try rewrite (Pmult_comm p q); reflexivity.
Qed.

(** ** Associativity of multiplication *)

Theorem Zmult_assoc : forall n m p:Z, n * (m * p) = n * m * p.
Proof.
  intros x y z; destruct x; destruct y; destruct z; simpl;
    try rewrite Pmult_assoc; reflexivity.
Qed.

Lemma Zmult_assoc_reverse : forall n m p:Z, n * m * p = n * (m * p).
Proof.
  intros n m p; rewrite Zmult_assoc; trivial with arith.
Qed.

(** ** Associativity mixed with commutativity *)

Theorem Zmult_permute : forall n m p:Z, n * (m * p) = m * (n * p).
Proof.
  intros x y z; rewrite (Zmult_assoc y x z); rewrite (Zmult_comm y x).
  apply Zmult_assoc.
Qed.

(** ** Z is integral *)

Theorem Zmult_integral_l : forall n m:Z, n <> Z0 -> m * n = Z0 -> m = Z0.
Proof.
  intros x y; destruct x as [| p| p].
  intro H; absurd (Z0 = Z0); trivial.
  intros _ H; destruct y as [| q| q]; reflexivity || discriminate.
  intros _ H; destruct y as [| q| q]; reflexivity || discriminate.
Qed.


Theorem Zmult_integral : forall n m:Z, n * m = Z0 -> n = Z0 \/ m = Z0.
Proof.
  intros x y; destruct x; destruct y; auto; simpl; intro H;
    discriminate H.
Qed.


Lemma Zmult_1_inversion_l :
  forall n m:Z, n * m = Zpos 1 -> n = Zpos 1 \/ n = Zneg 1.
Proof.
  intros x y; destruct x as [| p| p]; intro; [ discriminate | left | right ];
    (destruct y as [| q| q]; try discriminate; simpl in H; injection H; clear H;
      intro H; rewrite Pmult_1_inversion_l with (1 := H);
	reflexivity).
Qed.

(** ** Multiplication and Doubling *)

Lemma Zdouble_mult : forall z, Zdouble z = (Zpos 2) * z.
Proof.
  reflexivity.
Qed.

Lemma Zdouble_plus_one_mult : forall z,
  Zdouble_plus_one z = (Zpos 2) * z + (Zpos 1).
Proof.
  destruct z; simpl; auto with zarith.
Qed.

(** ** Multiplication and Opposite *)

Theorem Zopp_mult_distr_l : forall n m:Z, - (n * m) = - n * m.
Proof.
  intros x y; destruct x; destruct y; reflexivity.
Qed.

Theorem Zopp_mult_distr_r : forall n m:Z, - (n * m) = n * - m.
Proof.
  intros x y; rewrite (Zmult_comm x y); rewrite Zopp_mult_distr_l;
    apply Zmult_comm.
Qed.

Lemma Zopp_mult_distr_l_reverse : forall n m:Z, - n * m = - (n * m).
Proof.
  intros x y; symmetry ; apply Zopp_mult_distr_l.
Qed.

Theorem Zmult_opp_comm : forall n m:Z, - n * m = n * - m.
Proof.
  intros x y; rewrite Zopp_mult_distr_l_reverse; rewrite Zopp_mult_distr_r;
    trivial with arith.
Qed.

Theorem Zmult_opp_opp : forall n m:Z, - n * - m = n * m.
Proof.
  intros x y; destruct x; destruct y; reflexivity.
Qed.

Theorem Zopp_eq_mult_neg_1 : forall n:Z, - n = n * Zneg 1.
Proof.
  intro x; induction x; intros; rewrite Zmult_comm; auto with arith.
Qed.

(** ** Distributivity of multiplication over addition *)

Lemma weak_Zmult_plus_distr_r :
  forall (p:positive) (n m:Z), Zpos p * (n + m) = Zpos p * n + Zpos p * m.
Proof.
 intros x [ |y|y] [ |z|z]; simpl; trivial; f_equal;
  apply Pmult_plus_distr_l || rewrite Pmult_compare_mono_l;
  case_eq ((y ?= z)%positive); intros H; trivial;
   rewrite Pmult_minus_distr_l; trivial; now apply ZC1.
Qed.

Theorem Zmult_plus_distr_r : forall n m p:Z, n * (m + p) = n * m + n * p.
Proof.
 intros [|x|x] y z. trivial.
 apply weak_Zmult_plus_distr_r.
 apply Zopp_inj; rewrite Zopp_plus_distr, !Zopp_mult_distr_l, !Zopp_neg.
 apply weak_Zmult_plus_distr_r.
Qed.

Theorem Zmult_plus_distr_l : forall n m p:Z, (n + m) * p = n * p + m * p.
Proof.
  intros n m p; rewrite Zmult_comm; rewrite Zmult_plus_distr_r;
    do 2 rewrite (Zmult_comm p); trivial with arith.
Qed.

(** ** Distributivity of multiplication over subtraction *)

Lemma Zmult_minus_distr_r : forall n m p:Z, (n - m) * p = n * p - m * p.
Proof.
  intros x y z; unfold Zminus.
  rewrite <- Zopp_mult_distr_l_reverse.
  apply Zmult_plus_distr_l.
Qed.


Lemma Zmult_minus_distr_l : forall n m p:Z, p * (n - m) = p * n - p * m.
Proof.
  intros x y z; rewrite (Zmult_comm z (x - y)).
  rewrite (Zmult_comm z x).
  rewrite (Zmult_comm z y).
  apply Zmult_minus_distr_r.
Qed.

(** ** Simplification of multiplication for non-zero integers *)

Lemma Zmult_reg_l : forall n m p:Z, p <> Z0 -> p * n = p * m -> n = m.
Proof.
  intros x y z H H0.
  generalize (Zeq_minus _ _ H0).
  intro.
  apply Zminus_eq.
  rewrite <- Zmult_minus_distr_l in H1.
  clear H0; destruct (Zmult_integral _ _ H1).
  contradiction.
  trivial.
Qed.

Lemma Zmult_reg_r : forall n m p:Z, p <> Z0 -> n * p = m * p -> n = m.
Proof.
  intros x y z Hz.
  rewrite (Zmult_comm x z).
  rewrite (Zmult_comm y z).
  intro; apply Zmult_reg_l with z; assumption.
Qed.

(** ** Addition and multiplication by 2 *)

Lemma Zplus_diag_eq_mult_2 : forall n:Z, n + n = n * Zpos 2.
Proof.
  intros x; pattern x at 1 2; rewrite <- (Zmult_1_r x);
    rewrite <- Zmult_plus_distr_r; reflexivity.
Qed.

(** ** Multiplication and successor *)

Lemma Zmult_succ_r : forall n m:Z, n * Zsucc m = n * m + n.
Proof.
  intros n m; unfold Zsucc; rewrite Zmult_plus_distr_r;
    rewrite (Zmult_comm n (Zpos 1)); rewrite Zmult_1_l;
      trivial with arith.
Qed.

Lemma Zmult_succ_r_reverse : forall n m:Z, n * m + n = n * Zsucc m.
Proof.
  intros; symmetry ; apply Zmult_succ_r.
Qed.

Lemma Zmult_succ_l : forall n m:Z, Zsucc n * m = n * m + m.
Proof.
  intros n m; unfold Zsucc; rewrite Zmult_plus_distr_l;
    rewrite Zmult_1_l; trivial with arith.
Qed.

Lemma Zmult_succ_l_reverse : forall n m:Z, n * m + m = Zsucc n * m.
Proof.
  intros; symmetry; apply Zmult_succ_l.
Qed.



(** ** Misc redundant properties *)

Lemma Z_eq_mult : forall n m:Z, m = Z0 -> m * n = Z0.
Proof.
  intros x y H; rewrite H; auto with arith.
Qed.



(**********************************************************************)
(** * Relating binary positive numbers and binary integers *)

Lemma Zpos_eq : forall p q:positive, p = q -> Zpos p = Zpos q.
Proof.
  intros; f_equal; auto.
Qed.

Lemma Zpos_eq_rev : forall p q:positive, Zpos p = Zpos q -> p = q.
Proof.
  inversion 1; auto.
Qed.

Lemma Zpos_eq_iff : forall p q:positive, p = q <-> Zpos p = Zpos q.
Proof.
  split; [apply Zpos_eq|apply Zpos_eq_rev].
Qed.

Lemma Zpos_xI : forall p:positive, Zpos p~1 = Zpos 2 * Zpos p + Zpos 1.
Proof.
  intro; apply refl_equal.
Qed.

Lemma Zpos_xO : forall p:positive, Zpos p~0 = Zpos 2 * Zpos p.
Proof.
  intro; apply refl_equal.
Qed.

Lemma Zneg_xI : forall p:positive, Zneg p~1 = Zpos 2 * Zneg p - Zpos 1.
Proof.
  intro; apply refl_equal.
Qed.

Lemma Zneg_xO : forall p:positive, Zneg p~0 = Zpos 2 * Zneg p.
Proof.
  reflexivity.
Qed.

Lemma Zpos_plus_distr : forall p q:positive, Zpos (p + q) = Zpos p + Zpos q.
Proof.
  intros p p'; destruct p;
    [ destruct p' as [p0| p0| ]
      | destruct p' as [p0| p0| ]
      | destruct p' as [p| p| ] ]; reflexivity.
Qed.

Lemma Zneg_plus_distr : forall p q:positive, Zneg (p + q) = Zneg p + Zneg q.
Proof.
  intros p p'; destruct p;
    [ destruct p' as [p0| p0| ]
      | destruct p' as [p0| p0| ]
      | destruct p' as [p| p| ] ]; reflexivity.
Qed.

(**********************************************************************)
(** * Order relations *)

Definition Zlt (x y:Z) := (x ?= y) = Lt.
Definition Zgt (x y:Z) := (x ?= y) = Gt.
Definition Zle (x y:Z) := (x ?= y) <> Gt.
Definition Zge (x y:Z) := (x ?= y) <> Lt.
Definition Zne (x y:Z) := x <> y.

Infix "<=" := Zle : Z_scope.
Infix "<" := Zlt : Z_scope.
Infix ">=" := Zge : Z_scope.
Infix ">" := Zgt : Z_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : Z_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Z_scope.
Notation "x < y < z" := (x < y /\ y < z) : Z_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Z_scope.

Lemma Zpos_lt : forall p q, Zlt (Zpos p) (Zpos q) <-> Plt p q.
Proof.
 intros. apply iff_refl.
Qed.

Lemma Zpos_le : forall p q, Zle (Zpos p) (Zpos q) <-> Ple p q.
Proof.
 intros. apply iff_refl.
Qed.

(**********************************************************************)
(** * Minimum and maximum *)

Definition Zmax (n m:Z) :=
  match n ?= m with
    | Eq | Gt => n
    | Lt => m
  end.

Definition Zmin (n m:Z) :=
  match n ?= m with
    | Eq | Lt => n
    | Gt => m
  end.

(**********************************************************************)
(** * Absolute value on integers *)

Definition Zabs_nat (x:Z) : nat :=
  match x with
    | Z0 => 0%nat
    | Zpos p => nat_of_P p
    | Zneg p => nat_of_P p
  end.

Definition Zabs (z:Z) : Z :=
  match z with
    | Z0 => Z0
    | Zpos p => Zpos p
    | Zneg p => Zpos p
  end.

(**********************************************************************)
(** * From [nat] to [Z] *)

Definition Z_of_nat (x:nat) :=
  match x with
    | O => Z0
    | S y => Zpos (P_of_succ_nat y)
  end.

Definition Zabs_N (z:Z) :=
  match z with
    | Z0 => 0%N
    | Zpos p => Npos p
    | Zneg p => Npos p
  end.

Definition Z_of_N (x:N) :=
  match x with
    | N0 => Z0
    | Npos p => Zpos p
  end.

(** Compatibility Notations *)

Notation Z := Z (only parsing).
Notation Z_rect := Z_rect (only parsing).
Notation Z_rec := Z_rec (only parsing).
Notation Z_ind := Z_ind (only parsing).
Notation Z0 := Z0 (only parsing).
Notation Zpos := Zpos (only parsing).
Notation Zneg := Zneg (only parsing).

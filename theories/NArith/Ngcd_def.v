(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos BinNat.

Local Open Scope N_scope.

(** * Divisibility *)

Definition Ndivide p q := exists r, p*r = q.
Notation "( p | q )" := (Ndivide p q) (at level 0) : N_scope.

(** * Definition of a Pgcd function for binary natural numbers *)

Definition Ngcd (a b : N) :=
 match a, b with
  | 0, _ => b
  | _, 0 => a
  | Npos p, Npos q => Npos (Pos.gcd p q)
 end.

(** * Generalized Gcd, also computing rests of a and b after
    division by gcd. *)

Definition Nggcd (a b : N) :=
 match a, b with
  | 0, _ => (b,(0,1))
  | _, 0 => (a,(1,0))
  | Npos p, Npos q =>
     let '(g,(aa,bb)) := Pos.ggcd p q in
     (Npos g, (Npos aa, Npos bb))
 end.

(** The first component of Nggcd is Ngcd *)

Lemma Nggcd_gcd : forall  a b, fst (Nggcd a b) = Ngcd a b.
Proof.
 intros [ |p] [ |q]; simpl; auto.
 generalize (Pos.ggcd_gcd p q). destruct Pos.ggcd as (g,(aa,bb)); simpl; congruence.
Qed.

(** The other components of Nggcd are indeed the correct factors. *)

Lemma Nggcd_correct_divisors : forall a b,
  let '(g,(aa,bb)) := Nggcd a b in
  a=g*aa /\ b=g*bb.
Proof.
 intros [ |p] [ |q]; simpl; auto.
 now rewrite Pmult_1_r.
 now rewrite Pmult_1_r.
 generalize (Pos.ggcd_correct_divisors p q).
 destruct Pos.ggcd as (g,(aa,bb)); simpl. destruct 1; split; congruence.
Qed.

(** We can use this fact to prove a part of the gcd correctness *)

Lemma Ngcd_divide_l : forall a b, (Ngcd a b | a).
Proof.
 intros a b. rewrite <- Nggcd_gcd. generalize (Nggcd_correct_divisors a b).
 destruct Nggcd as (g,(aa,bb)); simpl. intros (H,_). exists aa; auto.
Qed.

Lemma Ngcd_divide_r : forall a b, (Ngcd a b | b).
Proof.
 intros a b. rewrite <- Nggcd_gcd. generalize (Nggcd_correct_divisors a b).
 destruct Nggcd as (g,(aa,bb)); simpl. intros (_,H). exists bb; auto.
Qed.

(** We now prove directly that gcd is the greatest amongst common divisors *)

Lemma Ngcd_greatest : forall a b c, (c|a) -> (c|b) -> (c|Ngcd a b).
Proof.
 intros [ |p] [ |q]; simpl; auto.
 intros [ |r]. intros (s,H). discriminate.
 intros ([ |s],Hs) ([ |t],Ht); try discriminate; simpl in *.
 destruct (Pos.gcd_greatest p q r) as (u,H).
 exists s. now inversion Hs.
 exists t. now inversion Ht.
 exists (Npos u). simpl; now f_equal.
Qed.

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos BinInt.

Open Local Scope Z_scope.

(** * Definition of a gcd function for relative numbers *)

Definition Zgcd (a b : Z) : Z :=
  match a,b with
    | Z0, _ => Zabs b
    | _, Z0 => Zabs a
    | Zpos a, Zpos b => Zpos (Pos.gcd a b)
    | Zpos a, Zneg b => Zpos (Pos.gcd a b)
    | Zneg a, Zpos b => Zpos (Pos.gcd a b)
    | Zneg a, Zneg b => Zpos (Pos.gcd a b)
  end.

(** * Generalized Gcd, also computing division of a and b by gcd. *)

Definition Zggcd (a b : Z) : Z*(Z*Z) :=
  match a,b with
    | Z0, _ => (Zabs b,(Z0, Zsgn b))
    | _, Z0 => (Zabs a,(Zsgn a, Z0))
    | Zpos a, Zpos b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (Zpos g, (Zpos aa, Zpos bb))
    | Zpos a, Zneg b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (Zpos g, (Zpos aa, Zneg bb))
    | Zneg a, Zpos b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (Zpos g, (Zneg aa, Zpos bb))
    | Zneg a, Zneg b =>
       let '(g,(aa,bb)) := Pos.ggcd a b in (Zpos g, (Zneg aa, Zneg bb))
  end.

(** The first component of Zggcd is Zgcd *)

Lemma Zggcd_gcd : forall a b, fst (Zggcd a b) = Zgcd a b.
Proof.
 intros [ |p|p] [ |q|q]; simpl; auto;
  generalize (Pos.ggcd_gcd p q); destruct Pos.ggcd as (g,(aa,bb)); simpl; congruence.
Qed.

(** The other components of Zggcd are indeed the correct factors. *)

Lemma Zggcd_correct_divisors : forall a b,
  let '(g,(aa,bb)) := Zggcd a b in
  a = g*aa /\ b = g*bb.
Proof.
 intros [ |p|p] [ |q|q]; simpl; rewrite ?Pmult_1_r; auto;
  generalize (Pos.ggcd_correct_divisors p q);
  destruct Pos.ggcd as (g,(aa,bb)); simpl; destruct 1; subst; auto.
Qed.

(** Divisibility. We use here a simple "exists", while the historical
    Znumtheory.Zdivide is a specialized inductive type. *)

Definition Zdivide' x y := exists z, x*z = y.

Local Notation "( x | y )" := (Zdivide' x y) (at level 0).

Lemma Zgcd_divide_l : forall a b, (Zgcd a b | a).
Proof.
 intros a b. rewrite <- Zggcd_gcd. generalize (Zggcd_correct_divisors a b).
 destruct Zggcd as (g,(aa,bb)); simpl. intros (H,_). exists aa; auto.
Qed.

Lemma Zgcd_divide_r : forall a b, (Zgcd a b | b).
Proof.
 intros a b. rewrite <- Zggcd_gcd. generalize (Zggcd_correct_divisors a b).
 destruct Zggcd as (g,(aa,bb)); simpl. intros (_,H). exists bb; auto.
Qed.

Lemma Zdivide'_0_l : forall x, (0|x) -> x = 0.
Proof.
 intros x (y,H). auto.
Qed.

Lemma Zdivide'_Zpos_Zneg_r : forall x y, (x|Zpos y) <-> (x|Zneg y).
Proof.
 intros x y; split; intros (z,H); exists (-z);
  now rewrite <- Zopp_mult_distr_r, H.
Qed.

Lemma Zdivide'_Zpos_Zneg_l : forall x y, (Zpos x|y) <-> (Zneg x|y).
Proof.
 intros x y; split; intros (z,H); exists (-z);
  now rewrite <- Zmult_opp_comm.
Qed.

Lemma Zdivide'_Pdivide : forall p q, (Zpos p|Zpos q) <-> (p|q)%positive.
Proof.
 intros p q. split.
 intros ([ |r|r],H); simpl in *; discriminate H || injection H. exists r; auto.
 intros (r,H). exists (Zpos r); simpl; f_equal; auto.
Qed.

Lemma Zgcd_greatest : forall a b c, (c|a) -> (c|b) -> (c|Zgcd a b).
Proof.
 assert (D : forall p q c, (c|Zpos p) -> (c|Zpos q) -> (c|Zpos (Pos.gcd p q))).
  intros p q [|r|r] H H'.
  apply Zdivide'_0_l in H. discriminate.
  apply Zdivide'_Pdivide, Pos.gcd_greatest; now apply Zdivide'_Pdivide.
  apply Zdivide'_Zpos_Zneg_l, Zdivide'_Pdivide, Pos.gcd_greatest;
   now apply Zdivide'_Pdivide, Zdivide'_Zpos_Zneg_l.
 intros [ |p|p] [ |q|q]; simpl; auto; intros; try apply D; trivial;
  now apply Zdivide'_Zpos_Zneg_r.
Qed.

Lemma Zgcd_nonneg : forall a b, 0 <= Zgcd a b.
Proof.
 intros [ |p|p] [ |q|q]; discriminate.
Qed.

(*
(** Zggcd produces coefficients that are relatively prime *)

Lemma Zggcd_greatest : forall a b,
 let (aa,bb) := snd (Zggcd a b) in
 forall z, (z|aa) -> (z|bb) -> z=1 \/ z=-1.
Proof.
 intros [ |p|p] [ |q|q]; simpl.
*)


(** Zggcd and opp : an auxiliary result used in QArith *)

Theorem Zggcd_opp: forall x y,
  Zggcd (-x) y = let '(g,(aa,bb)) := Zggcd x y in
                 (g,(-aa,bb)).
Proof.
intros [|x|x] [|y|y]; unfold Zggcd, Zopp; auto;
 destruct (Pos.ggcd x y) as (g,(aa,bb)); auto.
Qed.

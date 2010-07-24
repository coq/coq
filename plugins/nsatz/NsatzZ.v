(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Reals ZArith.
Require Export NsatzR.

Open Scope Z_scope.

Lemma nsatzZhypR: forall x y:Z, x=y -> IZR x = IZR y.
Proof IZR_eq. (* or f_equal ... *)

Lemma nsatzZconclR: forall x y:Z, IZR x = IZR y -> x = y.
Proof eq_IZR.

Lemma nsatzZhypnotR: forall x y:Z, x<>y -> IZR x <> IZR y.
Proof IZR_neq.

Lemma nsatzZconclnotR: forall x y:Z, IZR x <> IZR y -> x <> y.
Proof.
intros x y H. contradict H. f_equal. assumption.
Qed.

Ltac nsatzZtoR1 :=
 repeat
  (match goal with
   | H:(@eq Z ?x ?y) |- _ =>
       generalize (@nsatzZhypR _ _ H); clear H; intro H
   | |- (@eq Z ?x ?y) => apply nsatzZconclR
   | H:not (@eq Z ?x ?y) |- _ =>
       generalize (@nsatzZhypnotR _ _ H); clear H; intro H
   | |- not (@eq Z ?x ?y) => apply nsatzZconclnotR
   end).

Lemma nsatzZR1: forall x y:Z, IZR(x+y) = (IZR x + IZR y)%R.
Proof plus_IZR.

Lemma nsatzZR2: forall x y:Z, IZR(x*y) = (IZR x * IZR y)%R.
Proof mult_IZR.

Lemma nsatzZR3: forall x y:Z, IZR(x-y) = (IZR x - IZR y)%R.
Proof.
intros; symmetry. apply Z_R_minus.
Qed.

Lemma nsatzZR4: forall (x:Z) p, IZR(x ^ Zpos p) = (IZR x ^ nat_of_P p)%R.
Proof.
intros. rewrite pow_IZR.
do 2 f_equal.
apply Zpos_eq_Z_of_nat_o_nat_of_P.
Qed.

Ltac nsatzZtoR2:=
  repeat
   (rewrite nsatzZR1 in * ||
    rewrite nsatzZR2 in * ||
    rewrite nsatzZR3 in * ||
    rewrite nsatzZR4 in *).

Ltac nsatzZ_begin :=
 intros;
 nsatzZtoR1;
 nsatzZtoR2;
 simpl in *.
 (*cbv beta iota zeta delta [nat_of_P Pmult_nat plus mult] in *.*)

Ltac nsatzZ :=
 nsatzZ_begin; (*idtac "nsatzZ_begin;";*)
 nsatzR.

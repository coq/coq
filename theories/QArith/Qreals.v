(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Rbase.
Require Export QArith_base.

(** Injection of rational numbers into real numbers. *)

Definition Q2R (x : Q) : R := (IZR (Qnum x) * / IZR (QDen x))%R.

Lemma IZR_nz : forall p : positive, IZR (Zpos p) <> 0%R.
Proof.
intros.
now apply not_O_IZR.
Qed.

Hint Resolve IZR_nz Rmult_integral_contrapositive.

Lemma eqR_Qeq : forall x y : Q, Q2R x = Q2R y -> x==y.
Proof.
unfold Qeq, Q2R; intros (x1, x2) (y1, y2); unfold Qnum, Qden;
 intros.
apply eq_IZR.
do 2 rewrite mult_IZR.
set (X1 := IZR x1) in *; assert (X2nz := IZR_nz x2);
 set (X2 := IZR (Zpos x2)) in *.
set (Y1 := IZR y1) in *; assert (Y2nz := IZR_nz y2);
 set (Y2 := IZR (Zpos y2)) in *.
assert ((X2 * X1 * / X2)%R = (X2 * (Y1 * / Y2))%R).
rewrite <- H; field; auto.
rewrite Rinv_r_simpl_m in H0; auto; rewrite H0; field; auto.
Qed.

Lemma Qeq_eqR : forall x y : Q, x==y -> Q2R x = Q2R y.
Proof.
unfold Qeq, Q2R; intros (x1, x2) (y1, y2); unfold Qnum, Qden;
 intros.
set (X1 := IZR x1) in *; assert (X2nz := IZR_nz x2);
 set (X2 := IZR (Zpos x2)) in *.
set (Y1 := IZR y1) in *; assert (Y2nz := IZR_nz y2);
 set (Y2 := IZR (Zpos y2)) in *.
assert ((X1 * Y2)%R = (Y1 * X2)%R).
 unfold X1, X2, Y1, Y2; do 2 rewrite <- mult_IZR.
 apply IZR_eq; auto.
clear H.
field_simplify_eq; auto.
rewrite H0; ring.
Qed.

Lemma Rle_Qle : forall x y : Q, (Q2R x <= Q2R y)%R -> x<=y.
Proof.
unfold Qle, Q2R; intros (x1, x2) (y1, y2); unfold Qnum, Qden;
 intros.
apply le_IZR.
do 2 rewrite mult_IZR.
set (X1 := IZR x1) in *; assert (X2nz := IZR_nz x2);
 set (X2 := IZR (Zpos x2)) in *.
set (Y1 := IZR y1) in *; assert (Y2nz := IZR_nz y2);
 set (Y2 := IZR (Zpos y2)) in *.
replace (X1 * Y2)%R with (X1 * / X2 * (X2 * Y2))%R; try (field; auto).
replace (Y1 * X2)%R with (Y1 * / Y2 * (X2 * Y2))%R; try (field; auto).
apply Rmult_le_compat_r; auto.
apply Rmult_le_pos.
now apply IZR_le.
now apply IZR_le.
Qed.

Lemma Qle_Rle : forall x y : Q, x<=y -> (Q2R x <= Q2R y)%R.
Proof.
unfold Qle, Q2R; intros (x1, x2) (y1, y2); unfold Qnum, Qden;
 intros.
set (X1 := IZR x1) in *; assert (X2nz := IZR_nz x2);
 set (X2 := IZR (Zpos x2)) in *.
set (Y1 := IZR y1) in *; assert (Y2nz := IZR_nz y2);
 set (Y2 := IZR (Zpos y2)) in *.
assert (X1 * Y2 <= Y1 * X2)%R.
 unfold X1, X2, Y1, Y2; do 2 rewrite <- mult_IZR.
 apply IZR_le; auto.
clear H.
replace (X1 * / X2)%R with (X1 * Y2 * (/ X2 * / Y2))%R; try (field; auto).
replace (Y1 * / Y2)%R with (Y1 * X2 * (/ X2 * / Y2))%R; try (field; auto).
apply Rmult_le_compat_r; auto.
apply Rmult_le_pos; apply Rlt_le; apply Rinv_0_lt_compat.
now apply IZR_lt.
now apply IZR_lt.
Qed.

Lemma Rlt_Qlt : forall x y : Q, (Q2R x < Q2R y)%R -> x<y.
Proof.
unfold Qlt, Q2R; intros (x1, x2) (y1, y2); unfold Qnum, Qden;
 intros.
apply lt_IZR.
do 2 rewrite mult_IZR.
set (X1 := IZR x1) in *; assert (X2nz := IZR_nz x2);
 set (X2 := IZR (Zpos x2)) in *.
set (Y1 := IZR y1) in *; assert (Y2nz := IZR_nz y2);
 set (Y2 := IZR (Zpos y2)) in *.
replace (X1 * Y2)%R with (X1 * / X2 * (X2 * Y2))%R; try (field; auto).
replace (Y1 * X2)%R with (Y1 * / Y2 * (X2 * Y2))%R; try (field; auto).
apply Rmult_lt_compat_r; auto.
apply Rmult_lt_0_compat.
now apply IZR_lt.
now apply IZR_lt.
Qed.

Lemma Qlt_Rlt : forall x y : Q, x<y -> (Q2R x < Q2R y)%R.
Proof.
unfold Qlt, Q2R; intros (x1, x2) (y1, y2); unfold Qnum, Qden;
 intros.
set (X1 := IZR x1) in *; assert (X2nz := IZR_nz x2);
 set (X2 := IZR (Zpos x2)) in *.
set (Y1 := IZR y1) in *; assert (Y2nz := IZR_nz y2);
 set (Y2 := IZR (Zpos y2)) in *.
assert (X1 * Y2 < Y1 * X2)%R.
 unfold X1, X2, Y1, Y2; do 2 rewrite <- mult_IZR.
 apply IZR_lt; auto.
clear H.
replace (X1 * / X2)%R with (X1 * Y2 * (/ X2 * / Y2))%R; try (field; auto).
replace (Y1 * / Y2)%R with (Y1 * X2 * (/ X2 * / Y2))%R; try (field; auto).
apply Rmult_lt_compat_r; auto.
apply Rmult_lt_0_compat; apply Rinv_0_lt_compat.
now apply IZR_lt.
now apply IZR_lt.
Qed.

Lemma Q2R_plus : forall x y : Q, Q2R (x+y) = (Q2R x + Q2R y)%R.
Proof.
unfold Qplus, Qeq, Q2R; intros (x1, x2) (y1, y2);
 unfold Qden, Qnum.
simpl_mult.
rewrite plus_IZR.
do 3 rewrite mult_IZR.
field; auto.
Qed.

Lemma Q2R_mult : forall x y : Q, Q2R (x*y) = (Q2R x * Q2R y)%R.
Proof.
unfold Qmult, Qeq, Q2R; intros (x1, x2) (y1, y2);
 unfold Qden, Qnum.
simpl_mult.
do 2 rewrite mult_IZR.
field; auto.
Qed.

Lemma Q2R_opp : forall x : Q, Q2R (- x) = (- Q2R x)%R.
Proof.
unfold Qopp, Qeq, Q2R; intros (x1, x2); unfold Qden, Qnum.
rewrite Ropp_Ropp_IZR.
field; auto.
Qed.

Lemma Q2R_minus : forall x y : Q, Q2R (x-y) = (Q2R x - Q2R y)%R.
Proof.
unfold Qminus; intros; rewrite Q2R_plus; rewrite Q2R_opp; auto.
Qed.

Lemma Q2R_inv : forall x : Q, ~ x==0 -> Q2R (/x) = (/ Q2R x)%R.
Proof.
unfold Qinv, Q2R, Qeq; intros (x1, x2). case x1; unfold Qnum, Qden.
simpl; intros; elim H; trivial.
intros; field; auto. 
intros;
  change (IZR (Zneg x2)) with (- IZR (Zpos x2))%R;
  change (IZR (Zneg p)) with (- IZR (Zpos p))%R;
  simpl; field; (*auto 8 with real.*)
  repeat split; auto; auto with real.
Qed.

Lemma Q2R_div :
 forall x y : Q, ~ y==0 -> Q2R (x/y) = (Q2R x / Q2R y)%R.
Proof.
unfold Qdiv, Rdiv.
intros; rewrite Q2R_mult.
rewrite Q2R_inv; auto.
Qed.

Hint Rewrite Q2R_plus Q2R_mult Q2R_opp Q2R_minus Q2R_inv Q2R_div : q2r_simpl.

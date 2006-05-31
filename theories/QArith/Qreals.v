(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export Rbase.
Require Export QArith_base.

(** * A field tactic for rational numbers. *)

(** Since field cannot operate on setoid datatypes (yet?), 
  we translate Q goals into reals before applying field. *)

Lemma IZR_nz : forall p : positive, IZR (Zpos p) <> 0%R.
intros; apply not_O_IZR; auto with qarith.
Qed.

Hint Immediate IZR_nz.
Hint Resolve Rmult_integral_contrapositive.

Definition Q2R (x : Q) : R := (IZR (Qnum x) * / IZR (QDen x))%R.

Lemma eqR_Qeq : forall x y : Q, Q2R x = Q2R y -> x==y.
Proof.
unfold Qeq, Q2R in |- *; intros (x1, x2) (y1, y2); unfold Qnum, Qden in |- *;
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
unfold Qeq, Q2R in |- *; intros (x1, x2) (y1, y2); unfold Qnum, Qden in |- *;
 intros.
set (X1 := IZR x1) in *; assert (X2nz := IZR_nz x2);
 set (X2 := IZR (Zpos x2)) in *.
set (Y1 := IZR y1) in *; assert (Y2nz := IZR_nz y2);
 set (Y2 := IZR (Zpos y2)) in *.
assert ((X1 * Y2)%R = (Y1 * X2)%R).
 unfold X1, X2, Y1, Y2 in |- *; do 2 rewrite <- mult_IZR.
 apply IZR_eq; auto.
clear H.
field; auto.
rewrite <- H0; field; auto.
Qed.

Lemma Rle_Qle : forall x y : Q, (Q2R x <= Q2R y)%R -> x<=y.
Proof.
unfold Qle, Q2R in |- *; intros (x1, x2) (y1, y2); unfold Qnum, Qden in |- *;
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
unfold X2 in |- *; replace 0%R with (IZR 0); auto; apply IZR_le;
 auto with zarith.
unfold Y2 in |- *; replace 0%R with (IZR 0); auto; apply IZR_le;
 auto with zarith.
Qed.

Lemma Qle_Rle : forall x y : Q, x<=y -> (Q2R x <= Q2R y)%R.
Proof.
unfold Qle, Q2R in |- *; intros (x1, x2) (y1, y2); unfold Qnum, Qden in |- *;
 intros.
set (X1 := IZR x1) in *; assert (X2nz := IZR_nz x2);
 set (X2 := IZR (Zpos x2)) in *.
set (Y1 := IZR y1) in *; assert (Y2nz := IZR_nz y2);
 set (Y2 := IZR (Zpos y2)) in *.
assert (X1 * Y2 <= Y1 * X2)%R.
 unfold X1, X2, Y1, Y2 in |- *; do 2 rewrite <- mult_IZR.
 apply IZR_le; auto.
clear H.
replace (X1 * / X2)%R with (X1 * Y2 * (/ X2 * / Y2))%R; try (field; auto).
replace (Y1 * / Y2)%R with (Y1 * X2 * (/ X2 * / Y2))%R; try (field; auto).
apply Rmult_le_compat_r; auto.
apply Rmult_le_pos; apply Rlt_le; apply Rinv_0_lt_compat.
unfold X2 in |- *; replace 0%R with (IZR 0); auto; apply IZR_lt; red in |- *;
 auto with zarith.
unfold Y2 in |- *; replace 0%R with (IZR 0); auto; apply IZR_lt; red in |- *;
 auto with zarith.
Qed.

Lemma Rlt_Qlt : forall x y : Q, (Q2R x < Q2R y)%R -> x<y.
Proof.
unfold Qlt, Q2R in |- *; intros (x1, x2) (y1, y2); unfold Qnum, Qden in |- *;
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
unfold X2 in |- *; replace 0%R with (IZR 0); auto; apply IZR_lt; red in |- *;
 auto with zarith.
unfold Y2 in |- *; replace 0%R with (IZR 0); auto; apply IZR_lt; red in |- *;
 auto with zarith.
Qed.

Lemma Qlt_Rlt : forall x y : Q, x<y -> (Q2R x < Q2R y)%R.
Proof.
unfold Qlt, Q2R in |- *; intros (x1, x2) (y1, y2); unfold Qnum, Qden in |- *;
 intros.
set (X1 := IZR x1) in *; assert (X2nz := IZR_nz x2);
 set (X2 := IZR (Zpos x2)) in *.
set (Y1 := IZR y1) in *; assert (Y2nz := IZR_nz y2);
 set (Y2 := IZR (Zpos y2)) in *.
assert (X1 * Y2 < Y1 * X2)%R.
 unfold X1, X2, Y1, Y2 in |- *; do 2 rewrite <- mult_IZR.
 apply IZR_lt; auto.
clear H.
replace (X1 * / X2)%R with (X1 * Y2 * (/ X2 * / Y2))%R; try (field; auto).
replace (Y1 * / Y2)%R with (Y1 * X2 * (/ X2 * / Y2))%R; try (field; auto).
apply Rmult_lt_compat_r; auto.
apply Rmult_lt_0_compat; apply Rinv_0_lt_compat.
unfold X2 in |- *; replace 0%R with (IZR 0); auto; apply IZR_lt; red in |- *;
 auto with zarith.
unfold Y2 in |- *; replace 0%R with (IZR 0); auto; apply IZR_lt; red in |- *;
 auto with zarith.
Qed.

Lemma Q2R_plus : forall x y : Q, Q2R (x+y) = (Q2R x + Q2R y)%R.
Proof.
unfold Qplus, Qeq, Q2R in |- *; intros (x1, x2) (y1, y2);
 unfold Qden, Qnum in |- *.
simpl_mult.
rewrite plus_IZR.
do 3 rewrite mult_IZR.
field; auto.
Qed.

Lemma Q2R_mult : forall x y : Q, Q2R (x*y) = (Q2R x * Q2R y)%R.
Proof.
unfold Qmult, Qeq, Q2R in |- *; intros (x1, x2) (y1, y2);
 unfold Qden, Qnum in |- *.
simpl_mult.
do 2 rewrite mult_IZR.
field; auto.
Qed.

Lemma Q2R_opp : forall x : Q, Q2R (- x) = (- Q2R x)%R.
Proof.
unfold Qopp, Qeq, Q2R in |- *; intros (x1, x2); unfold Qden, Qnum in |- *.
rewrite Ropp_Ropp_IZR.
field; auto.
Qed.

Lemma Q2R_minus : forall x y : Q, Q2R (x-y) = (Q2R x - Q2R y)%R.
unfold Qminus in |- *; intros; rewrite Q2R_plus; rewrite Q2R_opp; auto.
Qed.

Lemma Q2R_inv : forall x : Q, ~ x==0#1 -> Q2R (/x) = (/ Q2R x)%R.
Proof.
unfold Qinv, Q2R, Qeq in |- *; intros (x1, x2); unfold Qden, Qnum in |- *.
case x1.
simpl in |- *; intros; elim H; trivial.
intros; field; auto.
apply Rmult_integral_contrapositive; split; auto.
apply Rmult_integral_contrapositive; split; auto.
apply Rinv_neq_0_compat; auto.
intros; field; auto.
do 2 rewrite <- mult_IZR.
simpl in |- *; rewrite Pmult_comm; auto.
apply Rmult_integral_contrapositive; split; auto.
apply Rmult_integral_contrapositive; split; auto.
apply not_O_IZR; auto with qarith.
apply Rinv_neq_0_compat; auto.
Qed.

Lemma Q2R_div :
 forall x y : Q, ~ y==0#1 -> Q2R (x/y) = (Q2R x / Q2R y)%R.
Proof.
unfold Qdiv, Rdiv in |- *.
intros; rewrite Q2R_mult.
rewrite Q2R_inv; auto.
Qed.

Hint Rewrite Q2R_plus Q2R_mult Q2R_opp Q2R_minus Q2R_inv Q2R_div : q2r_simpl.

Ltac QField := apply eqR_Qeq; autorewrite with q2r_simpl; try field; auto.

(** Examples of use: *)

Goal forall x y z : Q, (x+y)*z == (x*z)+(y*z).
intros; QField.
Abort.

Goal forall x y : Q, ~ y==0#1 -> (x/y)*y == x.
intros; QField.
intro; apply H; apply eqR_Qeq.
rewrite H0; unfold Q2R in |- *; simpl in |- *; field; auto with real.
Abort.
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Export Rbase.
Comments "Lemmas used by the tactic Fourier".

Open Scope R_scope.
 
Lemma Rfourier_lt:
 (x1, y1, a : R) (Rlt x1 y1) -> (Rlt R0 a) ->  (Rlt (Rmult a x1) (Rmult a y1)).
Intros; Apply Rlt_monotony; Assumption.
Qed.
 
Lemma Rfourier_le:
 (x1, y1, a : R) (Rle x1 y1) -> (Rlt R0 a) ->  (Rle (Rmult a x1) (Rmult a y1)).
Red.
Intros.
Case H; Auto with real.
Qed.
 
Lemma Rfourier_lt_lt:
 (x1, y1, x2, y2, a : R)
 (Rlt x1 y1) ->
 (Rlt x2 y2) ->
 (Rlt R0 a) ->  (Rlt (Rplus x1 (Rmult a x2)) (Rplus y1 (Rmult a y2))).
Intros x1 y1 x2 y2 a H H0 H1; Try Assumption.
Apply Rplus_lt.
Try Exact H.
Apply Rfourier_lt.
Try Exact H0.
Try Exact H1.
Qed.
 
Lemma Rfourier_lt_le:
 (x1, y1, x2, y2, a : R)
 (Rlt x1 y1) ->
 (Rle x2 y2) ->
 (Rlt R0 a) ->  (Rlt (Rplus x1 (Rmult a x2)) (Rplus y1 (Rmult a y2))).
Intros x1 y1 x2 y2 a H H0 H1; Try Assumption.
Case H0; Intros.
Apply Rplus_lt.
Try Exact H.
Apply Rfourier_lt; Auto with real.
Rewrite H2.
Rewrite (Rplus_sym y1 (Rmult a y2)).
Rewrite (Rplus_sym x1 (Rmult a y2)).
Apply Rlt_compatibility.
Try Exact H.
Qed.
 
Lemma Rfourier_le_lt:
 (x1, y1, x2, y2, a : R)
 (Rle x1 y1) ->
 (Rlt x2 y2) ->
 (Rlt R0 a) ->  (Rlt (Rplus x1 (Rmult a x2)) (Rplus y1 (Rmult a y2))).
Intros x1 y1 x2 y2 a H H0 H1; Try Assumption.
Case H; Intros.
Apply Rfourier_lt_le; Auto with real.
Rewrite H2.
Apply Rlt_compatibility.
Apply Rfourier_lt; Auto with real.
Qed.
 
Lemma Rfourier_le_le:
 (x1, y1, x2, y2, a : R)
 (Rle x1 y1) ->
 (Rle x2 y2) ->
 (Rlt R0 a) ->  (Rle (Rplus x1 (Rmult a x2)) (Rplus y1 (Rmult a y2))).
Intros x1 y1 x2 y2 a H H0 H1; Try Assumption.
Case H0; Intros.
Red.
Left; Try Assumption.
Apply Rfourier_le_lt; Auto with real.
Rewrite H2.
Case H; Intros.
Red.
Left; Try Assumption.
Rewrite (Rplus_sym x1 (Rmult a y2)).
Rewrite (Rplus_sym y1 (Rmult a y2)).
Apply Rlt_compatibility.
Try Exact H3.
Rewrite H3.
Red.
Right; Try Assumption.
Auto with real.
Qed.
 
Lemma Rlt_zero_pos_plus1: (x : R) (Rlt R0 x) ->  (Rlt R0 (Rplus R1 x)).
Intros x H; Try Assumption.
Rewrite Rplus_sym.
Apply Rlt_r_plus_R1.
Red; Auto with real.
Qed.
 
Lemma Rlt_mult_inv_pos:
 (x, y : R) (Rlt R0 x) -> (Rlt R0 y) ->  (Rlt R0 (Rmult x (Rinv y))).
Intros x y H H0; Try Assumption.
Replace R0 with (Rmult x R0).
Apply Rlt_monotony; Auto with real.
Ring.
Qed.
 
Lemma Rlt_zero_1: (Rlt R0 R1).
Exact Rlt_R0_R1.
Qed.
 
Lemma Rle_zero_pos_plus1: (x : R) (Rle R0 x) ->  (Rle R0 (Rplus R1 x)).
Intros x H; Try Assumption.
Case H; Intros.
Red.
Left; Try Assumption.
Apply Rlt_zero_pos_plus1; Auto with real.
Rewrite <- H0.
Replace (Rplus R1 R0) with R1.
Red; Left.
Exact Rlt_zero_1.
Ring.
Qed.
 
Lemma Rle_mult_inv_pos:
 (x, y : R) (Rle R0 x) -> (Rlt R0 y) ->  (Rle R0 (Rmult x (Rinv y))).
Intros x y H H0; Try Assumption.
Case H; Intros.
Red; Left.
Apply Rlt_mult_inv_pos; Auto with real.
Rewrite <- H1.
Red; Right; Ring.
Qed.
 
Lemma Rle_zero_1: (Rle R0 R1).
Red; Left.
Exact Rlt_zero_1.
Qed.
 
Lemma Rle_not_lt:
 (n, d : R) (Rle R0 (Rmult n (Rinv d))) ->  ~ (Rlt R0 (Rmult (Ropp n) (Rinv d))).
Intros n d H; Red; Intros H0; Try Exact H0.
Generalize (Rle_not R0 (Rmult n (Rinv d))).
Intros H1; Elim H1; Try Assumption.
Replace (Rmult n (Rinv d)) with (Ropp (Ropp (Rmult n (Rinv d)))).
Replace R0 with (Ropp (Ropp R0)).
Replace (Ropp (Rmult n (Rinv d))) with (Rmult (Ropp n) (Rinv d)).
Replace (Ropp R0) with R0.
Red.
Apply Rgt_Ropp.
Red.
Exact H0.
Ring.
Ring.
Ring.
Ring.
Qed.
 
Lemma Rnot_lt0: (x : R)  ~ (Rlt R0 (Rmult R0 x)).
Intros x; Try Assumption.
Replace (Rmult R0 x) with R0.
Apply Rlt_antirefl.
Ring.
Qed.
 
Lemma Rlt_not_le:
 (n, d : R) (Rlt R0 (Rmult n (Rinv d))) ->  ~ (Rle R0 (Rmult (Ropp n) (Rinv d))).
Intros n d H; Try Assumption.
Apply Rle_not.
Replace R0 with (Ropp R0).
Replace (Rmult (Ropp n) (Rinv d)) with (Ropp (Rmult n (Rinv d))).
Apply Rlt_Ropp.
Try Exact H.
Ring.
Ring.
Qed.
 
Lemma Rnot_lt_lt: (x, y : R) ~ (Rlt R0 (Rminus y x)) ->  ~ (Rlt x y).
Unfold not; Intros.
Apply H.
Apply Rlt_anti_compatibility with x.
Replace (Rplus x R0) with x.
Replace (Rplus x (Rminus y x)) with y.
Try Exact H0.
Ring.
Ring.
Qed.
 
Lemma Rnot_le_le: (x, y : R) ~ (Rle R0 (Rminus y x)) ->  ~ (Rle x y).
Unfold not; Intros.
Apply H.
Case H0; Intros.
Left.
Apply Rlt_anti_compatibility with x.
Replace (Rplus x R0) with x.
Replace (Rplus x (Rminus y x)) with y.
Try Exact H1.
Ring.
Ring.
Right.
Rewrite H1; Ring.
Qed.
 
Lemma Rfourier_gt_to_lt: (x, y : R) (Rgt y x) ->  (Rlt x y).
Unfold Rgt; Intros; Assumption.
Qed.
 
Lemma Rfourier_ge_to_le: (x, y : R) (Rge y x) ->  (Rle x y).
Intros x y; Exact (Rge_le y x).
Qed.
 
Lemma Rfourier_eqLR_to_le: (x, y : R) x == y ->  (Rle x y).
Exact eq_Rle.
Qed.
 
Lemma Rfourier_eqRL_to_le: (x, y : R) y == x ->  (Rle x y).
Exact eq_Rle_sym.
Qed.
 
Lemma Rfourier_not_ge_lt: (x, y : R) ((Rge x y) ->  False) ->  (Rlt x y).
Exact not_Rge.
Qed.
 
Lemma Rfourier_not_gt_le: (x, y : R) ((Rgt x y) ->  False) ->  (Rle x y).
Exact Rgt_not_le.
Qed.
 
Lemma Rfourier_not_le_gt: (x, y : R) ((Rle x y) ->  False) ->  (Rgt x y).
Exact not_Rle.
Qed.
 
Lemma Rfourier_not_lt_ge: (x, y : R) ((Rlt x y) ->  False) ->  (Rge x y).
Exact Rlt_not_ge.
Qed.

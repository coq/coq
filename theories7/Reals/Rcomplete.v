(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Rbase.
Require Rfunctions.
Require Rseries.
Require SeqProp.
Require Max.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

(****************************************************)
(*              R is complete :                     *)
(*        Each sequence which satisfies             *)
(*       the Cauchy's criterion converges           *)
(*                                                  *)
(*    Proof with adjacent sequences (Vn and Wn)     *)
(****************************************************)

Theorem R_complete : (Un:nat->R) (Cauchy_crit Un) -> (sigTT R [l:R](Un_cv Un l)).
Intros.
Pose Vn := (sequence_minorant Un (cauchy_min Un H)).
Pose Wn := (sequence_majorant Un (cauchy_maj Un H)).
Assert H0 := (maj_cv Un H).
Fold Wn in H0.
Assert H1 := (min_cv Un H).
Fold Vn in H1.
Elim H0; Intros.
Elim H1; Intros.
Cut x==x0.
Intros.
Apply existTT with x.
Rewrite <- H2 in p0.
Unfold Un_cv.
Intros.
Unfold Un_cv in p; Unfold Un_cv in p0.
Cut ``0<eps/3``.
Intro.
Elim (p ``eps/3`` H4); Intros.
Elim (p0 ``eps/3`` H4); Intros.
Exists (max x1 x2).
Intros.
Unfold R_dist.
Apply Rle_lt_trans with ``(Rabsolu ((Un n)-(Vn n)))+(Rabsolu ((Vn n)-x))``.
Replace ``(Un n)-x`` with ``((Un n)-(Vn n))+((Vn n)-x)``; [Apply Rabsolu_triang | Ring].
Apply Rle_lt_trans with ``(Rabsolu ((Wn n)-(Vn n)))+(Rabsolu ((Vn n)-x))``.
Do 2 Rewrite <- (Rplus_sym ``(Rabsolu ((Vn n)-x))``).
Apply Rle_compatibility.
Repeat Rewrite Rabsolu_right.
Unfold Rminus; Do 2 Rewrite <- (Rplus_sym ``-(Vn n)``); Apply Rle_compatibility.
Assert H8 := (Vn_Un_Wn_order Un (cauchy_maj Un H) (cauchy_min Un H)).
Fold Vn Wn in H8.
Elim (H8 n); Intros.
Assumption.
Apply Rle_sym1.
Unfold Rminus; Apply Rle_anti_compatibility with (Vn n).
Rewrite Rplus_Or.
Replace ``(Vn n)+((Wn n)+ -(Vn n))`` with (Wn n); [Idtac | Ring].
Assert H8 := (Vn_Un_Wn_order Un (cauchy_maj Un H) (cauchy_min Un H)).
Fold Vn Wn in H8.
Elim (H8 n); Intros.
Apply Rle_trans with (Un n); Assumption.
Apply Rle_sym1.
Unfold Rminus; Apply Rle_anti_compatibility with (Vn n).
Rewrite Rplus_Or.
Replace ``(Vn n)+((Un n)+ -(Vn n))`` with (Un n); [Idtac | Ring].
Assert H8 := (Vn_Un_Wn_order Un (cauchy_maj Un H) (cauchy_min Un H)).
Fold Vn Wn in H8.
Elim (H8 n); Intros.
Assumption.
Apply Rle_lt_trans with ``(Rabsolu ((Wn n)-x))+(Rabsolu (x-(Vn n)))+(Rabsolu ((Vn n)-x))``.
Do 2 Rewrite <- (Rplus_sym ``(Rabsolu ((Vn n)-x))``).
Apply Rle_compatibility.
Replace ``(Wn n)-(Vn n)`` with ``((Wn n)-x)+(x-(Vn n))``; [Apply Rabsolu_triang | Ring].
Apply Rlt_le_trans with ``eps/3+eps/3+eps/3``.
Repeat Apply Rplus_lt.
Unfold R_dist in H5.
Apply H5.
Unfold ge; Apply le_trans with (max x1 x2).
Apply le_max_l.
Assumption.
Rewrite <- Rabsolu_Ropp.
Replace ``-(x-(Vn n))`` with ``(Vn n)-x``; [Idtac | Ring].
Unfold R_dist in H6.
Apply H6.
Unfold ge; Apply le_trans with (max x1 x2).
Apply le_max_r.
Assumption.
Unfold R_dist in H6.
Apply H6.
Unfold ge; Apply le_trans with (max x1 x2).
Apply le_max_r.
Assumption.
Right.
Pattern 4 eps; Replace ``eps`` with ``3*eps/3``.
Ring.
Unfold Rdiv; Rewrite <- Rmult_assoc; Apply Rinv_r_simpl_m; DiscrR.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Apply cond_eq.
Intros.
Cut ``0<eps/5``.
Intro.
Unfold Un_cv in p; Unfold Un_cv in p0.
Unfold R_dist in p; Unfold R_dist in p0.
Elim (p ``eps/5`` H3); Intros N1 H4.
Elim (p0 ``eps/5`` H3); Intros N2 H5.
Unfold Cauchy_crit in H.
Unfold R_dist in H.
Elim (H ``eps/5`` H3); Intros N3 H6.
Pose N := (max (max N1 N2) N3).
Apply Rle_lt_trans with ``(Rabsolu (x-(Wn N)))+(Rabsolu ((Wn N)-x0))``.
Replace ``x-x0`` with ``(x-(Wn N))+((Wn N)-x0)``; [Apply Rabsolu_triang | Ring].
Apply Rle_lt_trans with ``(Rabsolu (x-(Wn N)))+(Rabsolu ((Wn N)-(Vn N)))+(Rabsolu (((Vn N)-x0)))``.
Rewrite Rplus_assoc.
Apply Rle_compatibility.
Replace ``(Wn N)-x0`` with ``((Wn N)-(Vn N))+((Vn N)-x0)``; [Apply Rabsolu_triang | Ring].
Replace ``eps`` with ``eps/5+3*eps/5+eps/5``.
Repeat Apply Rplus_lt.
Rewrite <- Rabsolu_Ropp.
Replace ``-(x-(Wn N))`` with ``(Wn N)-x``; [Apply H4 | Ring].
Unfold ge N.
Apply le_trans with (max N1 N2); Apply le_max_l.
Unfold Wn Vn.
Unfold sequence_majorant sequence_minorant.
Assert H7 := (approx_maj [k:nat](Un (plus N k)) (maj_ss Un N (cauchy_maj Un H))).
Assert H8 := (approx_min [k:nat](Un (plus N k)) (min_ss Un N (cauchy_min Un H))).
Cut (Wn N)==(majorant ([k:nat](Un (plus N k))) (maj_ss Un N (cauchy_maj Un H))).
Cut (Vn N)==(minorant ([k:nat](Un (plus N k))) (min_ss Un N (cauchy_min Un H))).
Intros.
Rewrite <- H9; Rewrite <- H10.
Rewrite <- H9 in H8.
Rewrite <- H10 in H7.
Elim (H7 ``eps/5`` H3); Intros k2 H11.
Elim (H8 ``eps/5`` H3); Intros k1 H12.
Apply Rle_lt_trans with ``(Rabsolu ((Wn N)-(Un (plus N k2))))+(Rabsolu ((Un (plus N k2))-(Vn N)))``.
Replace ``(Wn N)-(Vn N)`` with ``((Wn N)-(Un (plus N k2)))+((Un (plus N k2))-(Vn N))``; [Apply Rabsolu_triang | Ring].
Apply Rle_lt_trans with ``(Rabsolu ((Wn N)-(Un (plus N k2))))+(Rabsolu ((Un (plus N k2))-(Un (plus N k1))))+(Rabsolu ((Un (plus N k1))-(Vn N)))``.
Rewrite Rplus_assoc.
Apply Rle_compatibility.
Replace ``(Un (plus N k2))-(Vn N)`` with ``((Un (plus N k2))-(Un (plus N k1)))+((Un (plus N k1))-(Vn N))``; [Apply Rabsolu_triang | Ring].
Replace ``3*eps/5`` with ``eps/5+eps/5+eps/5``; [Repeat Apply Rplus_lt | Ring].
Assumption.
Apply H6.
Unfold ge.
Apply le_trans with N.
Unfold N; Apply le_max_r.
Apply le_plus_l.
Unfold ge.
Apply le_trans with N.
Unfold N; Apply le_max_r.
Apply le_plus_l.
Rewrite <- Rabsolu_Ropp.
Replace ``-((Un (plus N k1))-(Vn N))`` with ``(Vn N)-(Un (plus N k1))``; [Assumption | Ring].
Reflexivity.
Reflexivity.
Apply H5.
Unfold ge; Apply le_trans with (max N1 N2).
Apply le_max_r.
Unfold N; Apply le_max_l.
Pattern 4 eps; Replace ``eps`` with ``5*eps/5``.
Ring.
Unfold Rdiv; Rewrite <- Rmult_assoc; Apply Rinv_r_simpl_m.
DiscrR.
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv.
Sup0; Try Apply lt_O_Sn.
Qed.

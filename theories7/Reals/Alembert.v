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
Require PartSum.
Require Max.

Open Local Scope R_scope.

(***************************************************)
(* Various versions of the criterion of D'Alembert *)
(***************************************************)

Lemma Alembert_C1 : (An:nat->R) ((n:nat)``0<(An n)``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) R0) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros An H H0.
Cut (sigTT R [l:R](is_lub (EUn [N:nat](sum_f_R0 An N)) l)) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intro; Apply X.
Apply complet.
Unfold Un_cv in H0; Unfold bound; Cut ``0</2``; [Intro | Apply Rlt_Rinv; Sup0].
Elim (H0 ``/2`` H1); Intros.
Exists ``(sum_f_R0 An x)+2*(An (S x))``.
Unfold is_upper_bound; Intros; Unfold EUn in H3; Elim H3; Intros.
Rewrite H4; Assert H5 := (lt_eq_lt_dec x1 x).
Elim H5; Intros.
Elim a; Intro.
Replace (sum_f_R0 An x) with (Rplus (sum_f_R0 An x1) (sum_f_R0 [i:nat](An (plus (S x1) i)) (minus x (S x1)))).
Pattern 1 (sum_f_R0 An x1); Rewrite <- Rplus_Or; Rewrite Rplus_assoc; Apply Rle_compatibility.
Left; Apply gt0_plus_gt0_is_gt0.
Apply tech1; Intros; Apply H.
Apply Rmult_lt_pos; [Sup0 | Apply H].
Symmetry; Apply tech2; Assumption.
Rewrite b; Pattern 1 (sum_f_R0 An x); Rewrite <- Rplus_Or; Apply Rle_compatibility.
Left; Apply Rmult_lt_pos; [Sup0 | Apply H].
Replace (sum_f_R0 An x1) with (Rplus (sum_f_R0 An x) (sum_f_R0 [i:nat](An (plus (S x) i)) (minus x1 (S x)))).
Apply Rle_compatibility.
Cut (Rle (sum_f_R0 [i:nat](An (plus (S x) i)) (minus x1 (S x))) (Rmult (An (S x)) (sum_f_R0 [i:nat](pow ``/2`` i) (minus x1 (S x))))).
Intro; Apply Rle_trans with (Rmult (An (S x)) (sum_f_R0 [i:nat](pow ``/2`` i) (minus x1 (S x)))).
Assumption.
Rewrite <- (Rmult_sym (An (S x))); Apply Rle_monotony.
Left; Apply H.
Rewrite tech3.
Replace ``1-/2`` with ``/2``.
Unfold Rdiv; Rewrite Rinv_Rinv.
Pattern 3 ``2``; Rewrite <- Rmult_1r; Rewrite <- (Rmult_sym ``2``); Apply Rle_monotony.
Left; Sup0.
Left; Apply Rlt_anti_compatibility with ``(pow (/2) (S (minus x1 (S x))))``.
Replace ``(pow (/2) (S (minus x1 (S x))))+(1-(pow (/2) (S (minus x1 (S x)))))`` with R1; [Idtac | Ring].
Rewrite <- (Rplus_sym ``1``); Pattern 1 R1; Rewrite <- Rplus_Or; Apply Rlt_compatibility.
Apply pow_lt; Apply Rlt_Rinv; Sup0.
DiscrR.
Apply r_Rmult_mult with ``2``.
Rewrite Rminus_distr; Rewrite <- Rinv_r_sym.
Ring.
DiscrR.
DiscrR.
Pattern 3 R1; Replace R1 with ``/1``; [Apply tech7; DiscrR | Apply Rinv_R1].
Replace (An (S x)) with (An (plus (S x) O)).
Apply (tech6 [i:nat](An (plus (S x) i)) ``/2``).
Left; Apply Rlt_Rinv; Sup0.
Intro; Cut (n:nat)(ge n x)->``(An (S n))</2*(An n)``.
Intro; Replace (plus (S x) (S i)) with (S (plus (S x) i)).
Apply H6; Unfold ge; Apply tech8.
Apply INR_eq; Rewrite S_INR; Do 2 Rewrite plus_INR; Do 2 Rewrite S_INR; Ring.
Intros; Unfold R_dist in H2; Apply Rlt_monotony_contra with ``/(An n)``.
Apply Rlt_Rinv; Apply H.
Do 2 Rewrite (Rmult_sym ``/(An n)``); Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Replace ``(An (S n))*/(An n)`` with ``(Rabsolu ((Rabsolu ((An (S n))/(An n)))-0))``.
Apply H2; Assumption.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu; Rewrite Rabsolu_right.
Unfold Rdiv; Reflexivity.
Left; Unfold Rdiv; Change ``0<(An (S n))*/(An n)``; Apply Rmult_lt_pos; [Apply H | Apply Rlt_Rinv; Apply H].
Red; Intro; Assert H8 := (H n); Rewrite H7 in H8; Elim (Rlt_antirefl ? H8).
Replace (plus (S x) O) with (S x); [Reflexivity | Ring].
Symmetry; Apply tech2; Assumption.
Exists (sum_f_R0 An O); Unfold EUn; Exists O; Reflexivity.
Intro; Elim X; Intros.
Apply Specif.existT with x; Apply tech10; [Unfold Un_growing; Intro; Rewrite tech5; Pattern 1 (sum_f_R0 An n); Rewrite <- Rplus_Or; Apply Rle_compatibility; Left; Apply H | Apply p].
Qed.

Lemma Alembert_C2 : (An:nat->R) ((n:nat)``(An n)<>0``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) R0) -> (SigT R  [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros.
Pose Vn := [i:nat]``(2*(Rabsolu (An i))+(An i))/2``.
Pose Wn := [i:nat]``(2*(Rabsolu (An i))-(An i))/2``.
Cut (n:nat)``0<(Vn n)``.
Intro; Cut (n:nat)``0<(Wn n)``.
Intro; Cut (Un_cv [n:nat](Rabsolu ``(Vn (S n))/(Vn n)``) ``0``).
Intro; Cut (Un_cv [n:nat](Rabsolu ``(Wn (S n))/(Wn n)``) ``0``).
Intro; Assert H5 := (Alembert_C1 Vn H1 H3).
Assert H6 := (Alembert_C1 Wn H2 H4).
Elim H5; Intros.
Elim H6; Intros.
Apply Specif.existT with ``x-x0``; Unfold Un_cv; Unfold Un_cv in p; Unfold Un_cv in p0; Intros; Cut ``0<eps/2``.
Intro; Elim (p ``eps/2`` H8); Clear p; Intros.
Elim (p0 ``eps/2`` H8); Clear p0; Intros.
Pose N := (max x1 x2).
Exists N; Intros; Replace (sum_f_R0 An n) with (Rminus (sum_f_R0 Vn n) (sum_f_R0 Wn n)).
Unfold R_dist; Replace (Rminus (Rminus (sum_f_R0 Vn n) (sum_f_R0 Wn n)) (Rminus x x0)) with (Rplus (Rminus (sum_f_R0 Vn n) x) (Ropp (Rminus (sum_f_R0 Wn n) x0))); [Idtac | Ring]; Apply Rle_lt_trans with (Rplus (Rabsolu (Rminus (sum_f_R0 Vn n) x)) (Rabsolu (Ropp (Rminus (sum_f_R0 Wn n) x0)))).
Apply Rabsolu_triang.
Rewrite Rabsolu_Ropp; Apply Rlt_le_trans with ``eps/2+eps/2``.
Apply Rplus_lt.
Unfold R_dist in H9; Apply H9; Unfold ge; Apply le_trans with N; [Unfold N; Apply le_max_l | Assumption].
Unfold R_dist in H10; Apply H10; Unfold ge; Apply le_trans with N; [Unfold N; Apply le_max_r | Assumption].
Right; Symmetry; Apply double_var.
Symmetry; Apply tech11; Intro; Unfold Vn Wn; Unfold Rdiv; Do 2 Rewrite <- (Rmult_sym ``/2``); Apply r_Rmult_mult with ``2``.
Rewrite Rminus_distr; Repeat Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Ring.
DiscrR.
DiscrR.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Cut (n:nat)``/2*(Rabsolu (An n))<=(Wn n)<=(3*/2)*(Rabsolu (An n))``.
Intro; Cut (n:nat)``/(Wn n)<=2*/(Rabsolu (An n))``.
Intro; Cut (n:nat)``(Wn (S n))/(Wn n)<=3*(Rabsolu (An (S n))/(An n))``.
Intro; Unfold Un_cv; Intros; Unfold Un_cv in H0; Cut ``0<eps/3``.
Intro; Elim (H0 ``eps/3`` H8); Intros.
Exists x; Intros.
Assert H11 := (H9 n H10).
Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu; Unfold R_dist in H11; Unfold Rminus in H11; Rewrite Ropp_O in H11; Rewrite Rplus_Or in H11; Rewrite Rabsolu_Rabsolu in H11; Rewrite Rabsolu_right.
Apply Rle_lt_trans with ``3*(Rabsolu ((An (S n))/(An n)))``.
Apply H6.
Apply Rlt_monotony_contra with ``/3``.
Apply Rlt_Rinv; Sup0.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym; [Idtac | DiscrR]; Rewrite Rmult_1l; Rewrite <- (Rmult_sym eps); Unfold Rdiv in H11; Exact H11.
Left; Change ``0<(Wn (S n))/(Wn n)``; Unfold Rdiv; Apply Rmult_lt_pos.
Apply H2.
Apply Rlt_Rinv; Apply H2.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Intro; Unfold Rdiv; Rewrite Rabsolu_mult; Rewrite <- Rmult_assoc; Replace ``3`` with ``2*(3*/2)``; [Idtac | Rewrite <- Rmult_assoc; Apply Rinv_r_simpl_m; DiscrR]; Apply Rle_trans with ``(Wn (S n))*2*/(Rabsolu (An n))``.
Rewrite Rmult_assoc; Apply Rle_monotony.
Left; Apply H2.
Apply H5.
Rewrite Rabsolu_Rinv.
Replace ``(Wn (S n))*2*/(Rabsolu (An n))`` with ``(2*/(Rabsolu (An n)))*(Wn (S n))``; [Idtac | Ring]; Replace ``2*(3*/2)*(Rabsolu (An (S n)))*/(Rabsolu (An n))`` with ``(2*/(Rabsolu (An n)))*((3*/2)*(Rabsolu (An (S n))))``; [Idtac | Ring]; Apply Rle_monotony.
Left; Apply Rmult_lt_pos.
Sup0.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Apply H.
Elim (H4 (S n)); Intros; Assumption.
Apply H.
Intro; Apply Rle_monotony_contra with (Wn n).
Apply H2.
Rewrite <- Rinv_r_sym.
Apply Rle_monotony_contra with (Rabsolu (An n)).
Apply Rabsolu_pos_lt; Apply H.
Rewrite Rmult_1r; Replace ``(Rabsolu (An n))*((Wn n)*(2*/(Rabsolu (An n))))`` with ``2*(Wn n)*((Rabsolu (An n))*/(Rabsolu (An n)))``; [Idtac | Ring]; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Apply Rle_monotony_contra with ``/2``.
Apply Rlt_Rinv; Sup0.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Elim (H4 n); Intros; Assumption.
DiscrR.
Apply Rabsolu_no_R0; Apply H.
Red; Intro; Assert H6 := (H2 n); Rewrite H5 in H6; Elim (Rlt_antirefl ? H6).
Intro; Split.
Unfold Wn; Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Apply Rle_monotony.
Left; Apply Rlt_Rinv; Sup0.
Pattern 1 (Rabsolu (An n)); Rewrite <- Rplus_Or; Rewrite double; Unfold Rminus; Rewrite Rplus_assoc; Apply Rle_compatibility.
Apply Rle_anti_compatibility with (An n).
Rewrite Rplus_Or; Rewrite (Rplus_sym (An n)); Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Apply Rle_Rabsolu.
Unfold Wn; Unfold Rdiv; Repeat Rewrite <- (Rmult_sym ``/2``); Repeat Rewrite Rmult_assoc; Apply Rle_monotony.
Left; Apply Rlt_Rinv; Sup0.
Unfold Rminus; Rewrite double; Replace ``3*(Rabsolu (An n))`` with ``(Rabsolu (An n))+(Rabsolu (An n))+(Rabsolu (An n))``; [Idtac | Ring]; Repeat Rewrite Rplus_assoc; Repeat Apply Rle_compatibility.
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu.
Cut (n:nat)``/2*(Rabsolu (An n))<=(Vn n)<=(3*/2)*(Rabsolu (An n))``.
Intro; Cut (n:nat)``/(Vn n)<=2*/(Rabsolu (An n))``.
Intro; Cut (n:nat)``(Vn (S n))/(Vn n)<=3*(Rabsolu (An (S n))/(An n))``.
Intro; Unfold Un_cv; Intros; Unfold Un_cv in H1; Cut ``0<eps/3``.
Intro; Elim (H0 ``eps/3`` H7); Intros.
Exists x; Intros.
Assert H10 := (H8 n H9).
Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu; Unfold R_dist in H10; Unfold Rminus in H10; Rewrite Ropp_O in H10; Rewrite Rplus_Or in H10; Rewrite Rabsolu_Rabsolu in H10; Rewrite Rabsolu_right.
Apply Rle_lt_trans with ``3*(Rabsolu ((An (S n))/(An n)))``.
Apply H5.
Apply Rlt_monotony_contra with ``/3``.
Apply Rlt_Rinv; Sup0.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym; [Idtac | DiscrR]; Rewrite Rmult_1l; Rewrite <- (Rmult_sym eps); Unfold Rdiv in H10; Exact H10.
Left; Change ``0<(Vn (S n))/(Vn n)``; Unfold Rdiv; Apply Rmult_lt_pos.
Apply H1.
Apply Rlt_Rinv; Apply H1.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Intro; Unfold Rdiv; Rewrite Rabsolu_mult; Rewrite <- Rmult_assoc; Replace ``3`` with ``2*(3*/2)``; [Idtac | Rewrite <- Rmult_assoc; Apply Rinv_r_simpl_m; DiscrR]; Apply Rle_trans with ``(Vn (S n))*2*/(Rabsolu (An n))``.
Rewrite Rmult_assoc; Apply Rle_monotony.
Left; Apply H1.
Apply H4.
Rewrite Rabsolu_Rinv.
Replace ``(Vn (S n))*2*/(Rabsolu (An n))`` with ``(2*/(Rabsolu (An n)))*(Vn (S n))``; [Idtac | Ring]; Replace ``2*(3*/2)*(Rabsolu (An (S n)))*/(Rabsolu (An n))`` with ``(2*/(Rabsolu (An n)))*((3*/2)*(Rabsolu (An (S n))))``; [Idtac | Ring]; Apply Rle_monotony.
Left; Apply Rmult_lt_pos.
Sup0.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Apply H.
Elim (H3 (S n)); Intros; Assumption.
Apply H.
Intro; Apply Rle_monotony_contra with (Vn n).
Apply H1.
Rewrite <- Rinv_r_sym.
Apply Rle_monotony_contra with (Rabsolu (An n)).
Apply Rabsolu_pos_lt; Apply H.
Rewrite Rmult_1r; Replace ``(Rabsolu (An n))*((Vn n)*(2*/(Rabsolu (An n))))`` with ``2*(Vn n)*((Rabsolu (An n))*/(Rabsolu (An n)))``; [Idtac | Ring]; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Apply Rle_monotony_contra with ``/2``.
Apply Rlt_Rinv; Sup0.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Elim (H3 n); Intros; Assumption.
DiscrR.
Apply Rabsolu_no_R0; Apply H.
Red; Intro; Assert H5 := (H1 n); Rewrite H4 in H5; Elim (Rlt_antirefl ? H5).
Intro; Split.
Unfold Vn; Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Apply Rle_monotony.
Left; Apply Rlt_Rinv; Sup0.
Pattern 1 (Rabsolu (An n)); Rewrite <- Rplus_Or; Rewrite double; Rewrite Rplus_assoc; Apply Rle_compatibility.
Apply Rle_anti_compatibility with ``-(An n)``; Rewrite Rplus_Or; Rewrite <- (Rplus_sym (An n)); Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu.
Unfold Vn; Unfold Rdiv; Repeat Rewrite <- (Rmult_sym ``/2``); Repeat Rewrite Rmult_assoc; Apply Rle_monotony.
Left; Apply Rlt_Rinv; Sup0.
Unfold Rminus; Rewrite double; Replace ``3*(Rabsolu (An n))`` with ``(Rabsolu (An n))+(Rabsolu (An n))+(Rabsolu (An n))``; [Idtac | Ring]; Repeat Rewrite Rplus_assoc; Repeat Apply Rle_compatibility; Apply Rle_Rabsolu.
Intro; Unfold Wn; Unfold Rdiv; Rewrite <- (Rmult_Or ``/2``); Rewrite <- (Rmult_sym ``/2``); Apply Rlt_monotony.
Apply Rlt_Rinv; Sup0.
Apply Rlt_anti_compatibility with (An n); Rewrite Rplus_Or; Unfold Rminus; Rewrite (Rplus_sym (An n)); Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Apply Rle_lt_trans with (Rabsolu (An n)).
Apply Rle_Rabsolu.
Rewrite double; Pattern 1 (Rabsolu (An n)); Rewrite <- Rplus_Or; Apply Rlt_compatibility; Apply Rabsolu_pos_lt; Apply H.
Intro; Unfold Vn; Unfold Rdiv; Rewrite <- (Rmult_Or ``/2``); Rewrite <- (Rmult_sym ``/2``); Apply Rlt_monotony.
Apply Rlt_Rinv; Sup0.
Apply Rlt_anti_compatibility with ``-(An n)``; Rewrite Rplus_Or; Unfold Rminus; Rewrite (Rplus_sym ``-(An n)``); Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or; Apply Rle_lt_trans with (Rabsolu (An n)).
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu.
Rewrite double; Pattern 1 (Rabsolu (An n)); Rewrite <- Rplus_Or; Apply Rlt_compatibility; Apply Rabsolu_pos_lt; Apply H.
Qed.

Lemma AlembertC3_step1 : (An:nat->R;x:R) ``x<>0`` -> ((n:nat)``(An n)<>0``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) ``0``) -> (SigT R [l:R](Pser An x l)).
Intros; Pose Bn := [i:nat]``(An i)*(pow x i)``.
Cut (n:nat)``(Bn n)<>0``.
Intro; Cut (Un_cv [n:nat](Rabsolu ``(Bn (S n))/(Bn n)``) ``0``).
Intro; Assert H4 := (Alembert_C2 Bn H2 H3).
Elim H4; Intros.
Apply Specif.existT with x0; Unfold Bn in p; Apply tech12; Assumption.
Unfold Un_cv; Intros; Unfold Un_cv in H1; Cut ``0<eps/(Rabsolu x)``.
Intro; Elim (H1 ``eps/(Rabsolu x)`` H4); Intros.
Exists x0; Intros; Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu; Unfold Bn; Replace ``((An (S n))*(pow x (S n)))/((An n)*(pow x n))`` with ``(An (S n))/(An n)*x``.
Rewrite Rabsolu_mult; Apply Rlt_monotony_contra with ``/(Rabsolu x)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption.
Rewrite <- (Rmult_sym (Rabsolu x)); Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Rewrite <- (Rmult_sym eps); Unfold Rdiv in H5; Replace ``(Rabsolu ((An (S n))/(An n)))`` with ``(R_dist (Rabsolu ((An (S n))*/(An n))) 0)``.
Apply H5; Assumption.
Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu; Unfold Rdiv; Reflexivity.
Apply Rabsolu_no_R0; Assumption.
Replace (S n) with (plus n (1)); [Idtac | Ring]; Rewrite pow_add; Unfold Rdiv; Rewrite Rinv_Rmult.
Replace ``(An (plus n (S O)))*((pow x n)*(pow x (S O)))*(/(An n)*/(pow x n))`` with ``(An (plus n (S O)))*(pow x (S O))*/(An n)*((pow x n)*/(pow x n))``; [Idtac | Ring]; Rewrite <- Rinv_r_sym.
Simpl; Ring.
Apply pow_nonzero; Assumption.
Apply H0.
Apply pow_nonzero; Assumption.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption].
Intro; Unfold Bn; Apply prod_neq_R0; [Apply H0 | Apply pow_nonzero; Assumption].
Qed.

Lemma AlembertC3_step2 : (An:nat->R;x:R) ``x==0`` -> (SigT R [l:R](Pser An x l)).
Intros; Apply Specif.existT with (An O).
Unfold Pser; Unfold infinit_sum; Intros; Exists O; Intros; Replace (sum_f_R0 [n0:nat]``(An n0)*(pow x n0)`` n) with (An O).
Unfold R_dist; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Induction n.
Simpl; Ring.
Rewrite tech5; Rewrite Hrecn; [Rewrite H; Simpl; Ring | Unfold ge; Apply le_O_n].
Qed.

(* An useful criterion of convergence for power series *)
Theorem Alembert_C3 : (An:nat->R;x:R) ((n:nat)``(An n)<>0``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) ``0``) -> (SigT R [l:R](Pser An x l)).
Intros; Case (total_order_T x R0); Intro.
Elim s; Intro.
Cut ``x<>0``.
Intro; Apply AlembertC3_step1; Assumption.
Red; Intro; Rewrite H1 in a; Elim (Rlt_antirefl ? a).
Apply AlembertC3_step2; Assumption.
Cut ``x<>0``.
Intro; Apply AlembertC3_step1; Assumption.
Red; Intro; Rewrite H1 in r; Elim (Rlt_antirefl ? r).
Qed.

Lemma Alembert_C4 : (An:nat->R;k:R) ``0<=k<1`` -> ((n:nat)``0<(An n)``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) k) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros An k Hyp H H0.
Cut (sigTT R [l:R](is_lub (EUn [N:nat](sum_f_R0 An N)) l)) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intro; Apply X.
Apply complet.
Assert H1 := (tech13 ? ? Hyp H0).
Elim H1; Intros.
Elim H2; Intros.
Elim H4; Intros.
Unfold bound; Exists ``(sum_f_R0 An x0)+/(1-x)*(An (S x0))``.
Unfold is_upper_bound; Intros; Unfold EUn in H6.
Elim H6; Intros.
Rewrite H7.
Assert H8 := (lt_eq_lt_dec x2 x0).
Elim H8; Intros.
Elim a; Intro.
Replace (sum_f_R0 An x0) with (Rplus (sum_f_R0 An x2) (sum_f_R0 [i:nat](An (plus (S x2) i)) (minus x0 (S x2)))).
Pattern 1 (sum_f_R0 An x2); Rewrite <- Rplus_Or.
Rewrite Rplus_assoc; Apply Rle_compatibility.
Left; Apply gt0_plus_gt0_is_gt0.
Apply tech1.
Intros; Apply H.
Apply Rmult_lt_pos.
Apply Rlt_Rinv; Apply Rlt_anti_compatibility with x; Rewrite Rplus_Or; Replace ``x+(1-x)`` with R1; [Elim H3; Intros; Assumption | Ring].
Apply H.
Symmetry; Apply tech2; Assumption.
Rewrite b; Pattern 1 (sum_f_R0 An x0); Rewrite <- Rplus_Or; Apply Rle_compatibility.
Left; Apply Rmult_lt_pos.
Apply Rlt_Rinv; Apply Rlt_anti_compatibility with x; Rewrite Rplus_Or; Replace ``x+(1-x)`` with R1; [Elim H3; Intros; Assumption | Ring].
Apply H.
Replace (sum_f_R0 An x2) with (Rplus (sum_f_R0 An x0) (sum_f_R0 [i:nat](An (plus (S x0) i)) (minus x2 (S x0)))).
Apply Rle_compatibility.
Cut (Rle (sum_f_R0 [i:nat](An (plus (S x0) i)) (minus x2 (S x0))) (Rmult (An (S x0)) (sum_f_R0 [i:nat](pow x i) (minus x2 (S x0))))).
Intro; Apply Rle_trans with (Rmult (An (S x0)) (sum_f_R0 [i:nat](pow x i) (minus x2 (S x0)))).
Assumption.
Rewrite <- (Rmult_sym (An (S x0))); Apply Rle_monotony.
Left; Apply H.
Rewrite tech3.
Unfold Rdiv; Apply Rle_monotony_contra with ``1-x``.
Apply Rlt_anti_compatibility with x; Rewrite Rplus_Or.
Replace ``x+(1-x)`` with R1; [Elim H3; Intros; Assumption | Ring].
Do 2 Rewrite (Rmult_sym ``1-x``).
Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Apply Rle_anti_compatibility with ``(pow x (S (minus x2 (S x0))))``.
Replace ``(pow x (S (minus x2 (S x0))))+(1-(pow x (S (minus x2 (S x0)))))`` with R1; [Idtac | Ring].
Rewrite <- (Rplus_sym R1); Pattern 1 R1; Rewrite <- Rplus_Or; Apply Rle_compatibility.
Left; Apply pow_lt.
Apply Rle_lt_trans with k.
Elim Hyp; Intros; Assumption.
Elim H3; Intros; Assumption.
Apply Rminus_eq_contra.
Red; Intro.
Elim H3; Intros.
Rewrite H10 in H12; Elim (Rlt_antirefl ? H12).
Red; Intro.
Elim H3; Intros.
Rewrite H10 in H12; Elim (Rlt_antirefl ? H12).
Replace (An (S x0)) with (An (plus (S x0) O)).
Apply (tech6 [i:nat](An (plus (S x0) i)) x).
Left; Apply Rle_lt_trans with k.
Elim Hyp; Intros; Assumption.
Elim H3; Intros; Assumption.
Intro.
Cut (n:nat)(ge n x0)->``(An (S n))<x*(An n)``.
Intro.
Replace (plus (S x0) (S i)) with (S (plus (S x0) i)).
Apply H9.
Unfold ge.
Apply tech8.
  Apply INR_eq; Rewrite S_INR; Do 2 Rewrite plus_INR; Do 2 Rewrite S_INR; Ring.
Intros.
Apply Rlt_monotony_contra with ``/(An n)``.
Apply Rlt_Rinv; Apply H.
Do 2 Rewrite (Rmult_sym ``/(An n)``).
Rewrite Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r.
Replace ``(An (S n))*/(An n)`` with ``(Rabsolu ((An (S n))/(An n)))``.
Apply H5; Assumption.
Rewrite Rabsolu_right.
Unfold Rdiv; Reflexivity.
Left; Unfold Rdiv; Change ``0<(An (S n))*/(An n)``; Apply Rmult_lt_pos.
Apply H.
Apply Rlt_Rinv; Apply H.
Red; Intro.
Assert H11 := (H n).
Rewrite H10 in H11; Elim (Rlt_antirefl ? H11).
Replace (plus (S x0) O) with (S x0); [Reflexivity | Ring].
Symmetry; Apply tech2; Assumption.
Exists (sum_f_R0 An O); Unfold EUn; Exists O; Reflexivity.
Intro; Elim X; Intros.
Apply Specif.existT with x; Apply tech10; [Unfold Un_growing; Intro; Rewrite tech5; Pattern 1 (sum_f_R0 An n); Rewrite <- Rplus_Or; Apply Rle_compatibility; Left; Apply H | Apply p].
Qed.

Lemma Alembert_C5 : (An:nat->R;k:R) ``0<=k<1`` -> ((n:nat)``(An n)<>0``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) k) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros.
Cut (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intro Hyp0; Apply Hyp0.
Apply cv_cauchy_2.
Apply cauchy_abs.
Apply cv_cauchy_1.
Cut (SigT R [l:R](Un_cv [N:nat](sum_f_R0 [i:nat](Rabsolu (An i)) N) l)) -> (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 [i:nat](Rabsolu (An i)) N) l)).
Intro Hyp; Apply Hyp.
Apply (Alembert_C4 [i:nat](Rabsolu (An i)) k).
Assumption.
Intro; Apply Rabsolu_pos_lt; Apply H0.
Unfold Un_cv.
Unfold Un_cv in H1.
Unfold Rdiv.
Intros.
Elim (H1 eps H2); Intros.
Exists x; Intros.
Rewrite <- Rabsolu_Rinv.
Rewrite <- Rabsolu_mult.
Rewrite Rabsolu_Rabsolu.
Unfold Rdiv in H3; Apply H3; Assumption.
Apply H0.
Intro.
Elim X; Intros.
Apply existTT with x.
Assumption.
Intro.
Elim X; Intros.
Apply Specif.existT with x.
Assumption.
Qed.

(* Convergence of power series in D(O,1/k) *)
(*     k=0 is described in Alembert_C3     *)
Lemma Alembert_C6 : (An:nat->R;x,k:R) ``0<k`` -> ((n:nat)``(An n)<>0``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) k) -> ``(Rabsolu x)</k`` -> (SigT R [l:R](Pser An x l)).
Intros.
Cut (SigT R [l:R](Un_cv [N:nat](sum_f_R0 [i:nat]``(An i)*(pow x i)`` N) l)).
Intro.
Elim X; Intros.
Apply Specif.existT with x0.
Apply tech12; Assumption.
Case (total_order_T x R0); Intro.
Elim s; Intro.
EApply Alembert_C5 with ``k*(Rabsolu x)``.
Split.
Unfold Rdiv; Apply Rmult_le_pos.
Left; Assumption.
Left; Apply Rabsolu_pos_lt.
Red; Intro; Rewrite H3 in a; Elim (Rlt_antirefl ? a).
Apply Rlt_monotony_contra with ``/k``.
Apply Rlt_Rinv; Assumption.
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite Rmult_1r; Assumption.
Red; Intro; Rewrite H3 in H; Elim (Rlt_antirefl ? H).
Intro; Apply prod_neq_R0.
Apply H0.
Apply pow_nonzero.
Red; Intro; Rewrite H3 in a; Elim (Rlt_antirefl ? a).
Unfold Un_cv; Unfold Un_cv in H1.
Intros.
Cut ``0<eps/(Rabsolu x)``.
Intro.
Elim (H1 ``eps/(Rabsolu x)`` H4); Intros.
Exists x0.
Intros.
Replace ``((An (S n))*(pow x (S n)))/((An n)*(pow x n))`` with ``(An (S n))/(An n)*x``.
Unfold R_dist.
Rewrite Rabsolu_mult.
Replace ``(Rabsolu ((An (S n))/(An n)))*(Rabsolu x)-k*(Rabsolu x)`` with ``(Rabsolu x)*((Rabsolu ((An (S n))/(An n)))-k)``; [Idtac | Ring].
Rewrite Rabsolu_mult.
Rewrite Rabsolu_Rabsolu.
Apply Rlt_monotony_contra with ``/(Rabsolu x)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Red; Intro; Rewrite H7 in a; Elim (Rlt_antirefl ? a).
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite <- (Rmult_sym eps).
Unfold R_dist in H5.
Unfold Rdiv; Unfold Rdiv in H5; Apply H5; Assumption.
Apply Rabsolu_no_R0.
Red; Intro; Rewrite H7 in a; Elim (Rlt_antirefl ? a).
Unfold Rdiv; Replace (S n) with (plus n (1)); [Idtac | Ring].
Rewrite pow_add.
Simpl.
Rewrite Rmult_1r.
Rewrite Rinv_Rmult.
Replace ``(An (plus n (S O)))*((pow x n)*x)*(/(An n)*/(pow x n))`` with ``(An (plus n (S O)))*/(An n)*x*((pow x n)*/(pow x n))``; [Idtac | Ring].
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Reflexivity.
Apply pow_nonzero.
Red; Intro; Rewrite H7 in a; Elim (Rlt_antirefl ? a).
Apply H0.
Apply pow_nonzero.
Red; Intro; Rewrite H7 in a; Elim (Rlt_antirefl ? a).
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Red; Intro H7; Rewrite H7 in a; Elim (Rlt_antirefl ? a).
Apply Specif.existT with (An O).
Unfold Un_cv.
Intros.
Exists O.
Intros.
Unfold R_dist.
Replace (sum_f_R0 [i:nat]``(An i)*(pow x i)`` n) with (An O).
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Induction n.
Simpl; Ring.
Rewrite tech5.
Rewrite <- Hrecn.
Rewrite b; Simpl; Ring.
Unfold ge; Apply le_O_n.
EApply Alembert_C5 with ``k*(Rabsolu x)``.
Split.
Unfold Rdiv; Apply Rmult_le_pos.
Left; Assumption.
Left; Apply Rabsolu_pos_lt.
Red; Intro; Rewrite H3 in r; Elim (Rlt_antirefl ? r).
Apply Rlt_monotony_contra with ``/k``.
Apply Rlt_Rinv; Assumption.
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite Rmult_1r; Assumption.
Red; Intro; Rewrite H3 in H; Elim (Rlt_antirefl ? H).
Intro; Apply prod_neq_R0.
Apply H0.
Apply pow_nonzero.
Red; Intro; Rewrite H3 in r; Elim (Rlt_antirefl ? r).
Unfold Un_cv; Unfold Un_cv in H1.
Intros.
Cut ``0<eps/(Rabsolu x)``.
Intro.
Elim (H1 ``eps/(Rabsolu x)`` H4); Intros.
Exists x0.
Intros.
Replace ``((An (S n))*(pow x (S n)))/((An n)*(pow x n))`` with ``(An (S n))/(An n)*x``.
Unfold R_dist.
Rewrite Rabsolu_mult.
Replace ``(Rabsolu ((An (S n))/(An n)))*(Rabsolu x)-k*(Rabsolu x)`` with ``(Rabsolu x)*((Rabsolu ((An (S n))/(An n)))-k)``; [Idtac | Ring].
Rewrite Rabsolu_mult.
Rewrite Rabsolu_Rabsolu.
Apply Rlt_monotony_contra with ``/(Rabsolu x)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Red; Intro; Rewrite H7 in r; Elim (Rlt_antirefl ? r).
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite <- (Rmult_sym eps).
Unfold R_dist in H5.
Unfold Rdiv; Unfold Rdiv in H5; Apply H5; Assumption.
Apply Rabsolu_no_R0.
Red; Intro; Rewrite H7 in r; Elim (Rlt_antirefl ? r).
Unfold Rdiv; Replace (S n) with (plus n (1)); [Idtac | Ring].
Rewrite pow_add.
Simpl.
Rewrite Rmult_1r.
Rewrite Rinv_Rmult.
Replace ``(An (plus n (S O)))*((pow x n)*x)*(/(An n)*/(pow x n))`` with ``(An (plus n (S O)))*/(An n)*x*((pow x n)*/(pow x n))``; [Idtac | Ring].
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Reflexivity.
Apply pow_nonzero.
Red; Intro; Rewrite H7 in r; Elim (Rlt_antirefl ? r).
Apply H0.
Apply pow_nonzero.
Red; Intro; Rewrite H7 in r; Elim (Rlt_antirefl ? r).
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt.
Red; Intro H7; Rewrite H7 in r; Elim (Rlt_antirefl ? r).
Qed.

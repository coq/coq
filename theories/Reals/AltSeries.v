(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
 
(*i $Id$ i*)

Require Even.
Require Div2.
Require Max.
Require DiscrR.
Require Rseries.
Require Alembert.
Require Rcomplet.
Require Binome.

(* Tout entier s'ecrit sous la forme 2p ou 2p+1 *)
Lemma even_odd_cor : (n:nat) (EX p : nat | n=(mult (2) p)\/n=(S (mult (2) p))).
Intro.
Assert H := (even_or_odd n).
Exists (div2 n).
Assert H0 := (even_odd_double n).
Elim H0; Intros.
Elim H1; Intros H3 _.
Elim H2; Intros H4 _.
Replace (mult (2) (div2 n)) with (Div2.double (div2 n)).
Elim H; Intro.
Left.
Apply H3; Assumption.
Right.
Apply H4; Assumption.
Unfold Div2.double; Ring.
Qed.

(**********)
Definition tg_alt [Un:nat->R] : nat->R := [i:nat]``(pow (-1) i)*(Un i)``.
Definition positivity_sui [Un:nat->R] : Prop := (n:nat)``0<=(Un n)``.

(**********)
Lemma pow_1_even : (n:nat) ``(pow (-1) (mult (S (S O)) n))==1``.
Intro; Induction n.
Reflexivity.
Replace (mult (2) (S n)) with (plus (2) (mult (2) n)).
Rewrite pow_add; Rewrite Hrecn; Simpl; Ring.
Replace (S n) with (plus n (1)); [Ring | Ring].
Qed.

(**********)
Lemma pow_1_odd : (n:nat) ``(pow (-1) (S (mult (S (S O)) n)))==-1``.
Intro; Replace (S (mult (2) n)) with (plus (mult (2) n) (1)); [Idtac | Ring].
Rewrite pow_add; Rewrite pow_1_even; Simpl; Ring.
Qed.

(* Croissance des sommes partielles impaires *)
Lemma CV_ALT_step1 : (Un:nat->R) (Un_decreasing Un) -> (Un_growing [N:nat](sum_f_R0 (tg_alt Un) (S (mult (2) N)))).
Intros; Unfold Un_growing; Intro.
Cut (mult (S (S O)) (S n)) = (S (S (mult (2) n))).
Intro; Rewrite H0.
Do 4 Rewrite tech5; Repeat Rewrite Rplus_assoc; Apply Rle_compatibility.
Pattern 1 (tg_alt Un (S (mult (S (S O)) n))); Rewrite <- Rplus_Or.
Apply Rle_compatibility.
Unfold tg_alt; Rewrite <- H0; Rewrite pow_1_odd; Rewrite pow_1_even; Rewrite Rmult_1l.
Apply Rle_anti_compatibility with ``(Un (S (mult (S (S O)) (S n))))``.
Rewrite Rplus_Or; Replace ``(Un (S (mult (S (S O)) (S n))))+((Un (mult (S (S O)) (S n)))+ -1*(Un (S (mult (S (S O)) (S n)))))`` with ``(Un (mult (S (S O)) (S n)))``; [Idtac | Ring].
Apply H.
Cut (n:nat) (S n)=(plus n (1)); [Intro | Intro; Ring].
Rewrite (H0 n); Rewrite (H0 (S (mult (2) n))); Rewrite (H0 (mult (2) n)); Ring.
Qed.

(* D�croissance des sommes partielles paires *)
Lemma CV_ALT_step1_bis : (Un:nat->R) (Un_decreasing Un) -> (Un_decreasing [N:nat](sum_f_R0 (tg_alt Un) (mult (2) N))).
Intros; Unfold Un_decreasing; Intro.
Cut (mult (S (S O)) (S n)) = (S (S (mult (2) n))).
Intro; Rewrite H0; Do 2 Rewrite tech5; Repeat Rewrite Rplus_assoc.
Pattern 2 (sum_f_R0 (tg_alt Un) (mult (S (S O)) n)); Rewrite <- Rplus_Or.
Apply Rle_compatibility.
Unfold tg_alt; Rewrite <- H0; Rewrite pow_1_odd; Rewrite pow_1_even; Rewrite Rmult_1l.
Apply Rle_anti_compatibility with ``(Un (S (mult (S (S O)) n)))``.
Rewrite Rplus_Or; Replace ``(Un (S (mult (S (S O)) n)))+( -1*(Un (S (mult (S (S O)) n)))+(Un (mult (S (S O)) (S n))))`` with ``(Un (mult (S (S O)) (S n)))``; [Idtac | Ring].
Rewrite H0; Apply H.
Cut (n:nat) (S n)=(plus n (1)); [Intro | Intro; Ring].
Rewrite (H0 n); Rewrite (H0 (S (mult (2) n))); Rewrite (H0 (mult (2) n)); Ring.
Qed.

(**********)
Lemma CV_ALT_step2 : (Un:nat->R;N:nat) (Un_decreasing Un) -> (positivity_sui Un) -> (Rle (sum_f_R0 [i:nat](tg_alt Un (S i)) (S (mult (2) N))) R0). 
Intros; Induction N.
Simpl; Unfold tg_alt; Simpl; Rewrite Rmult_1r.
Replace ``-1* -1*(Un (S (S O)))`` with (Un (S (S O))); [Idtac | Ring].
Apply Rle_anti_compatibility with ``(Un (S O))``; Rewrite Rplus_Or.
Replace ``(Un (S O))+ (-1*(Un (S O))+(Un (S (S O))))`` with (Un (S (S O))); [Apply H | Ring].
Cut (S (mult (2) (S N))) = (S (S (S (mult (2) N)))).
Intro; Rewrite H1; Do 2 Rewrite tech5.
Apply Rle_trans with (sum_f_R0 [i:nat](tg_alt Un (S i)) (S (mult (S (S O)) N))).
Pattern 2 (sum_f_R0 [i:nat](tg_alt Un (S i)) (S (mult (S (S O)) N))); Rewrite <- Rplus_Or.
Rewrite Rplus_assoc; Apply Rle_compatibility.
Unfold tg_alt; Rewrite <- H1.
Rewrite pow_1_odd.
Cut (S (S (mult (2) (S N)))) = (mult (2) (S (S N))).
Intro; Rewrite H2; Rewrite pow_1_even; Rewrite Rmult_1l; Rewrite <- H2.
Apply Rle_anti_compatibility with ``(Un (S (mult (S (S O)) (S N))))``.
Rewrite Rplus_Or; Replace ``(Un (S (mult (S (S O)) (S N))))+( -1*(Un (S (mult (S (S O)) (S N))))+(Un (S (S (mult (S (S O)) (S N))))))`` with ``(Un (S (S (mult (S (S O)) (S N)))))``; [Idtac | Ring].
Apply H.
Apply INR_eq; Rewrite mult_INR; Repeat Rewrite S_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply HrecN.
Apply INR_eq; Repeat Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Qed.

(* A more general inequality *)
Lemma CV_ALT_step3 : (Un:nat->R;N:nat) (Un_decreasing Un) -> (positivity_sui Un) -> (Rle (sum_f_R0 [i:nat](tg_alt Un (S i)) N) R0). 
Intros; Induction N.
Simpl; Unfold tg_alt; Simpl; Rewrite Rmult_1r.
Apply Rle_anti_compatibility with (Un (S O)).
Rewrite Rplus_Or; Replace ``(Un (S O))+ -1*(Un (S O))`` with R0; [Apply H0 | Ring].
Assert H1 := (even_odd_cor N).
Elim H1; Intros.
Elim H2; Intro.
Rewrite H3; Apply CV_ALT_step2; Assumption.
Rewrite H3; Rewrite tech5.
Apply Rle_trans with (sum_f_R0 [i:nat](tg_alt Un (S i)) (S (mult (S (S O)) x))).
Pattern 2 (sum_f_R0 [i:nat](tg_alt Un (S i)) (S (mult (S (S O)) x))); Rewrite <- Rplus_Or.
Apply Rle_compatibility.
Unfold tg_alt; Simpl.
Replace (plus x (plus x O)) with (mult (2) x); [Idtac | Ring].
Rewrite pow_1_even.
Replace `` -1*( -1*( -1*1))*(Un (S (S (S (mult (S (S O)) x)))))`` with ``-(Un (S (S (S (mult (S (S O)) x)))))``; [Idtac | Ring].
Apply Rle_anti_compatibility with (Un (S (S (S (mult (S (S O)) x))))).
Rewrite Rplus_Or; Rewrite Rplus_Ropp_r.
Apply H0.
Apply CV_ALT_step2; Assumption.
Qed.

(**********)
Lemma CV_ALT_step4 : (Un:nat->R) (Un_decreasing Un) -> (positivity_sui Un) -> (majoree [N:nat](sum_f_R0 (tg_alt Un) (S (mult (2) N)))).
Intros; Unfold majoree; Unfold bound.
Exists ``(Un O)``.
Unfold is_upper_bound; Intros; Elim H1; Intros.
Rewrite H2; Rewrite decomp_sum.
Replace (tg_alt Un O) with ``(Un O)``.
Pattern 2 ``(Un O)``; Rewrite <- Rplus_Or.
Apply Rle_compatibility.
Apply CV_ALT_step3; Assumption.
Unfold tg_alt; Simpl; Ring.
Apply lt_O_Sn.
Qed.

(**********)
Lemma pow_1_abs : (n:nat) ``(Rabsolu (pow (-1) n))==1``.
Intro; Induction n.
Simpl; Apply Rabsolu_R1.
Replace (S n) with (plus n (1)); [Rewrite pow_add | Ring].
Rewrite Rabsolu_mult.
Rewrite Hrecn; Rewrite Rmult_1l; Simpl; Rewrite Rmult_1r; Rewrite Rabsolu_Ropp; Apply Rabsolu_R1.
Qed.

(* 2m <= 2n => m<=n *)
Lemma le_double : (m,n:nat) (le (mult (2) m) (mult (2) n)) -> (le m n).
Intros; Apply INR_le.
Assert H1 := (le_INR ? ? H).
Do 2 Rewrite mult_INR in H1.
Apply Rle_monotony_contra with ``(INR (S (S O)))``.
Replace (INR (S (S O))) with ``2``; [Apply Rgt_2_0 | Reflexivity].
Assumption.
Qed.

(* Ceci donne quasiment le r�sultat sur la convergence des s�ries altern�es *)
Lemma CV_ALT : (Un:nat->R) (Un_decreasing Un) -> (positivity_sui Un) -> (Un_cv Un R0) -> (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 (tg_alt Un) N) l)).
Intros.
Assert H2 := (CV_ALT_step1 ? H).
Assert H3 := (CV_ALT_step4 ? H H0).
Assert X := (growing_cv ? H2 H3).
Elim X; Intros.
Apply existTT with x.
Unfold Un_cv; Unfold R_dist; Unfold Un_cv in H1; Unfold R_dist in H1; Unfold Un_cv in p; Unfold R_dist in p.
Intros; Cut ``0<eps/2``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]].
Elim (H1 ``eps/2`` H5); Intros N2 H6.
Elim (p ``eps/2`` H5); Intros N1 H7.
Pose N := (max (S (mult (2) N1)) N2).
Exists N; Intros.
Assert H9 := (even_odd_cor n).
Elim H9; Intros P H10.
Cut (le N1 P).
Intro; Elim H10; Intro.
Replace ``(sum_f_R0 (tg_alt Un) n)-x`` with ``((sum_f_R0 (tg_alt Un) (S n))-x)+(-(tg_alt Un (S n)))``.
Apply Rle_lt_trans with ``(Rabsolu ((sum_f_R0 (tg_alt Un) (S n))-x))+(Rabsolu (-(tg_alt Un (S n))))``.
Apply Rabsolu_triang.
Rewrite (double_var eps); Apply Rplus_lt.
Rewrite H12; Apply H7; Assumption.
Rewrite Rabsolu_Ropp; Unfold tg_alt; Rewrite Rabsolu_mult; Rewrite pow_1_abs; Rewrite Rmult_1l; Unfold Rminus in H6; Rewrite Ropp_O in H6; Rewrite <- (Rplus_Or (Un (S n))); Apply H6.
Unfold ge; Apply le_trans with n.
Apply le_trans with N; [Unfold N; Apply le_max_r | Assumption].
Apply le_n_Sn.
Rewrite tech5; Ring.
Rewrite H12; Apply Rlt_trans with ``eps/2``.
Apply H7; Assumption.
Unfold Rdiv; Apply Rlt_monotony_contra with ``2``.
Apply Rgt_2_0.
Rewrite (Rmult_sym ``2``); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Rewrite Rmult_1r | DiscrR].
Rewrite Rlimit.double.
Pattern 1 eps; Rewrite <- (Rplus_Or eps); Apply Rlt_compatibility; Assumption.
Elim H10; Intro; Apply le_double.
Rewrite <- H11; Apply le_trans with N.
Unfold N; Apply le_trans with (S (mult (2) N1)); [Apply le_n_Sn | Apply le_max_l].
Assumption.
Apply lt_n_Sm_le.
Rewrite <- H11.
Apply lt_le_trans with N.
Unfold N; Apply lt_le_trans with (S (mult (2) N1)).
Apply lt_n_Sn.
Apply le_max_l.
Assumption.
Qed.

(**********)
Lemma growing_ineq : (Un:nat->R;l:R) (Un_growing Un) -> (Un_cv Un l) -> ((n:nat)``(Un n)<=l``). 
Intros; Case (total_order_T (Un n) l); Intro.
Elim s; Intro.
Left; Assumption.
Right; Assumption.
Cut ``0<(Un n)-l``.
Intro; Unfold Un_cv in H0; Unfold R_dist in H0.
Elim (H0 ``(Un n)-l`` H1); Intros N1 H2.
Pose N := (max n N1).
Cut ``(Un n)-l<=(Un N)-l``.
Intro; Cut ``(Un N)-l<(Un n)-l``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H3 H4)).
Apply Rle_lt_trans with ``(Rabsolu ((Un N)-l))``.
Apply Rle_Rabsolu.
Apply H2.
Unfold ge N; Apply le_max_r.
Unfold Rminus; Do 2 Rewrite <- (Rplus_sym ``-l``); Apply Rle_compatibility.
Apply tech9.
Assumption.
Unfold N; Apply le_max_l.
Apply Rlt_anti_compatibility with l.
Rewrite Rplus_Or.
Replace ``l+((Un n)-l)`` with (Un n); [Assumption | Ring].
Qed.

(* Un->l => (-Un) -> (-l) *)
Lemma CV_opp : (An:nat->R;l:R) (Un_cv An l) -> (Un_cv (opp_sui An) ``-l``).
Intros An l.
Unfold Un_cv; Unfold R_dist; Intros.
Elim (H eps H0); Intros.
Exists x; Intros.
Unfold opp_sui; Replace ``-(An n)- (-l)`` with ``-((An n)-l)``; [Rewrite Rabsolu_Ropp | Ring].
Apply H1; Assumption.
Qed.

(**********)
Lemma decreasing_ineq : (Un:nat->R;l:R) (Un_decreasing Un) -> (Un_cv Un l) -> ((n:nat)``l<=(Un n)``).
Intros.
Assert H1 := (decreasing_growing ? H).
Assert H2 := (CV_opp ? ? H0).
Assert H3 := (growing_ineq ? ? H1 H2).
Apply Ropp_Rle.
Unfold opp_sui in H3; Apply H3.
Qed.

(************************************************)
(* Th�or�me de convergence des s�ries altern�es *)
(*                                              *)
(* Applications: PI, cos, sin...                *)
(************************************************)
Theorem Series_Alternees : (Un:nat->R) (Un_decreasing Un) -> (Un_cv Un R0) -> (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 (tg_alt Un) N) l)).
Intros; Apply CV_ALT.
Assumption.
Unfold positivity_sui; Apply decreasing_ineq; Assumption.
Assumption.
Qed.

(* Encadrement de la limite par les sommes partielles *)
Theorem sommes_partielles_ineq : (Un:nat->R;l:R;N:nat) (Un_decreasing Un) -> (Un_cv Un R0) -> (Un_cv [N:nat](sum_f_R0 (tg_alt Un) N) l) -> ``(sum_f_R0 (tg_alt Un) (S (mult (S (S O)) N)))<=l<=(sum_f_R0 (tg_alt Un) (mult (S (S O)) N))``.
Intros.
Cut (Un_cv [N:nat](sum_f_R0 (tg_alt Un) (mult (2) N)) l).
Cut (Un_cv [N:nat](sum_f_R0 (tg_alt Un) (S (mult (2) N))) l).
Intros; Split.
Apply (growing_ineq [N:nat](sum_f_R0 (tg_alt Un) (S (mult (2) N)))).
Apply CV_ALT_step1; Assumption.
Assumption.
Apply (decreasing_ineq [N:nat](sum_f_R0 (tg_alt Un) (mult (2) N))).
Apply CV_ALT_step1_bis; Assumption.
Assumption.
Unfold Un_cv; Unfold R_dist; Unfold Un_cv in H1; Unfold R_dist in H1; Intros. 
Elim (H1 eps H2); Intros.
Exists x; Intros.
Apply H3.
Unfold ge; Apply le_trans with (mult (2) n).
Apply le_trans with n.
Assumption.
Assert H5 := (mult_O_le n (2)).
Elim H5; Intro. 
Cut ~(O)=(2); [Intro; Elim H7; Symmetry; Assumption | Discriminate].
Assumption.
Apply le_n_Sn.
Unfold Un_cv; Unfold R_dist; Unfold Un_cv in H1; Unfold R_dist in H1; Intros. 
Elim (H1 eps H2); Intros.
Exists x; Intros.
Apply H3.
Unfold ge; Apply le_trans with n.
Assumption.
Assert H5 := (mult_O_le n (2)).
Elim H5; Intro. 
Cut ~(O)=(2); [Intro; Elim H7; Symmetry; Assumption | Discriminate].
Assumption.
Qed.

(************************************)
(* Application : construction de PI *)
(************************************)

Definition PI_tg := [n:nat]``/(INR (plus (mult (S (S O)) n) (S O)))``.

Lemma PI_tg_pos : (n:nat)``0<=(PI_tg n)``.
Intro; Unfold PI_tg; Left; Apply Rlt_Rinv; Apply lt_INR_0; Replace (plus (mult (2) n) (1)) with (S (mult (2) n)); [Apply lt_O_Sn | Ring].
Qed.

Lemma PI_tg_decreasing : (Un_decreasing PI_tg).
Unfold PI_tg Un_decreasing; Intro.
Apply Rle_monotony_contra with ``(INR (plus (mult (S (S O)) n) (S O)))``.
Apply lt_INR_0.
Replace (plus (mult (2) n) (1)) with (S (mult (2) n)); [Apply lt_O_Sn | Ring].
Rewrite <- Rinv_r_sym.
Apply Rle_monotony_contra with ``(INR (plus (mult (S (S O)) (S n)) (S O)))``.
Apply lt_INR_0.
Replace (plus (mult (2) (S n)) (1)) with (S (mult (2) (S n))); [Apply lt_O_Sn | Ring].
Rewrite (Rmult_sym ``(INR (plus (mult (S (S O)) (S n)) (S O)))``); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Do 2 Rewrite Rmult_1r; Apply le_INR.
Replace (plus (mult (2) (S n)) (1)) with (S (S (plus (mult (2) n) (1)))).
Apply le_trans with (S (plus (mult (2) n) (1))); Apply le_n_Sn.
Apply INR_eq; Do 2  Rewrite S_INR; Do 2 Rewrite plus_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply not_O_INR; Discriminate.
Apply not_O_INR; Replace (plus (mult (2) n) (1)) with (S (mult (2) n)); [Discriminate | Ring].
Qed.

Lemma PI_tg_cv : (Un_cv PI_tg R0).
Unfold Un_cv; Unfold R_dist; Intros.
Cut ``0<2*eps``; [Intro | Apply Rmult_lt_pos; [Apply Rgt_2_0 | Assumption]].
Assert H1 := (archimed ``/(2*eps)``).
Cut (Zle `0` ``(up (/(2*eps)))``).
Intro; Assert H3 := (IZN ``(up (/(2*eps)))`` H2).
Elim H3; Intros N H4.
Cut (lt O N).
Intro; Exists N; Intros.
Cut (lt O n).
Intro; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_right.
Unfold PI_tg; Apply Rlt_trans with ``/(INR (mult (S (S O)) n))``.
Apply Rlt_monotony_contra with ``(INR (mult (S (S O)) n))``.
Apply lt_INR_0.
Replace (mult (2) n) with (plus n n); [Idtac | Ring].
Apply lt_le_trans with n.
Assumption.
Apply le_plus_l.
Rewrite <- Rinv_r_sym.
Apply Rlt_monotony_contra with ``(INR (plus (mult (S (S O)) n) (S O)))``.
Apply lt_INR_0.
Replace (plus (mult (2) n) (1)) with (S (mult (2) n)); [Apply lt_O_Sn | Ring].
Rewrite (Rmult_sym ``(INR (plus (mult (S (S O)) n) (S O)))``).
Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Do 2 Rewrite Rmult_1r; Apply lt_INR.
Replace (plus (mult (2) n) (1)) with (S (mult (2) n)); [Apply lt_n_Sn | Ring].
Apply not_O_INR; Replace (plus (mult (2) n) (1)) with (S (mult (2) n)); [Discriminate | Ring].
Replace n with (S (pred n)).
Apply not_O_INR; Discriminate.
Symmetry; Apply S_pred with O.
Assumption.
Apply Rle_lt_trans with ``/(INR (mult (S (S O)) N))``.
Apply Rle_monotony_contra with ``(INR (mult (S (S O)) N))``.
Rewrite mult_INR; Apply Rmult_lt_pos; [Apply Rgt_2_0 | Apply lt_INR_0; Assumption].
Rewrite <- Rinv_r_sym.
Apply Rle_monotony_contra with ``(INR (mult (S (S O)) n))``.
Rewrite mult_INR; Apply Rmult_lt_pos; [Apply Rgt_2_0 | Apply lt_INR_0; Assumption].
Rewrite (Rmult_sym (INR (mult (S (S O)) n))); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Do 2 Rewrite Rmult_1r; Apply le_INR.
Apply mult_le; Assumption.
Replace n with (S (pred n)).
Apply not_O_INR; Discriminate.
Symmetry; Apply S_pred with O.
Assumption.
Replace N with (S (pred N)).
Apply not_O_INR; Discriminate.
Symmetry; Apply S_pred with O.
Assumption.
Rewrite mult_INR.
Rewrite Rinv_Rmult.
Replace (INR (S (S O))) with ``2``; [Idtac | Reflexivity].
Apply Rlt_monotony_contra with ``2``.
Apply Rgt_2_0.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Idtac | DiscrR].
Rewrite Rmult_1l; Apply Rlt_monotony_contra with (INR N).
Apply lt_INR_0; Assumption.
Rewrite <- Rinv_r_sym.
Apply Rlt_monotony_contra with ``/(2*eps)``.
Apply Rlt_Rinv; Assumption.
Rewrite Rmult_1r; Replace ``/(2*eps)*((INR N)*(2*eps))`` with ``(INR N)*((2*eps)*/(2*eps))``; [Idtac | Ring].
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Replace (INR N) with (IZR (INZ N)).
Rewrite <- H4.
Elim H1; Intros; Assumption.
Symmetry; Apply INR_IZR_INZ.
Apply prod_neq_R0; [DiscrR | Red; Intro; Rewrite H8 in H; Elim (Rlt_antirefl ? H)].
Apply not_O_INR.
Red; Intro; Rewrite H8 in H5; Elim (lt_n_n ? H5).
Replace (INR (S (S O))) with ``2``; [DiscrR | Reflexivity].
Apply not_O_INR.
Red; Intro; Rewrite H8 in H5; Elim (lt_n_n ? H5).
Apply Rle_sym1; Apply PI_tg_pos.
Apply lt_le_trans with N; Assumption.
Elim H1; Intros H5 _.
Assert H6 := (lt_eq_lt_dec O N).
Elim H6; Intro.
Elim a; Intro.
Assumption.
Rewrite <- b in H4.
Rewrite H4 in H5.
Simpl in H5.
Cut ``0</(2*eps)``; [Intro | Apply Rlt_Rinv; Assumption].
Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H7 H5)).
Elim (lt_n_O ? b).
Apply le_IZR.
Simpl.
Left; Apply Rlt_trans with ``/(2*eps)``.
Apply Rlt_Rinv; Assumption.
Elim H1; Intros; Assumption.
Qed.

Lemma exist_PI : (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 (tg_alt PI_tg) N) l)).
Apply Series_Alternees.
Apply PI_tg_decreasing.
Apply PI_tg_cv.
Qed.

(* Now, PI is defined *)
Definition PI : R := (Rmult ``4`` (Cases exist_PI of (existTT a b) => a end)).

(* We can get an approximation of PI with the following inequality *)
Lemma PI_ineq : (N:nat) ``(sum_f_R0 (tg_alt PI_tg) (S (mult (S (S O)) N)))<=PI/4<=(sum_f_R0 (tg_alt PI_tg) (mult (S (S O)) N))``.
Intro; Apply sommes_partielles_ineq.
Apply PI_tg_decreasing.
Apply PI_tg_cv.
Unfold PI; Case exist_PI; Intro.
Replace ``(4*x)/4`` with x.
Trivial.
Unfold Rdiv; Rewrite (Rmult_sym ``4``); Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1r; Reflexivity | DiscrR].
Qed.

Lemma PI_RGT_0 : ``0<PI``.
Assert H := (PI_ineq O).
Apply Rlt_monotony_contra with ``/4``.
Apply Rlt_Rinv; Sup0.
Rewrite Rmult_Or; Rewrite Rmult_sym.
Elim H; Clear H; Intros H _.
Unfold Rdiv in H; Apply Rlt_le_trans with ``(sum_f_R0 (tg_alt PI_tg) (S (mult (S (S O)) O)))``.
Simpl; Unfold tg_alt; Simpl; Rewrite Rmult_1l; Rewrite Rmult_1r; Apply Rlt_anti_compatibility with ``(PI_tg (S O))``.
Rewrite Rplus_Or; Replace ``(PI_tg (S O))+((PI_tg O)+ -1*(PI_tg (S O)))`` with ``(PI_tg O)``; [Unfold PI_tg | Ring].
Simpl; Apply Rinv_lt.
Rewrite Rmult_1l; Replace ``2+1`` with ``3``; [Apply Rgt_3_0 | Ring].
Rewrite Rplus_sym; Pattern 1 R1; Rewrite <- Rplus_Or; Apply Rlt_compatibility; Apply Rgt_2_0.
Assumption.
Qed.

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Rfunctions.
Require SeqSeries.
Require Ranalysis.
Require Rbase.
Require RiemannInt_SF.
Require Classical_Prop.
Require Classical_Pred_Type.
Require Max.
V7only [Import R_scope.]. Open Local Scope R_scope.

Implicit Arguments On.

(********************************************)
(*            Riemann's Integral            *)
(********************************************)

Definition Riemann_integrable [f:R->R;a,b:R] : Type := (eps:posreal) (SigT ? [phi:(StepFun a b)](SigT ? [psi:(StepFun a b)]((t:R)``(Rmin a b)<=t<=(Rmax a b)``->``(Rabsolu ((f t)-(phi t)))<=(psi t)``)/\``(Rabsolu (RiemannInt_SF psi))<eps``)).

Definition phi_sequence [un:nat->posreal;f:R->R;a,b:R;pr:(Riemann_integrable f a b)] := [n:nat](projT1 ? ? (pr (un n))).

Lemma phi_sequence_prop : (un:nat->posreal;f:R->R;a,b:R;pr:(Riemann_integrable f a b);N:nat) (SigT ? [psi:(StepFun a b)]((t:R)``(Rmin a b)<=t<=(Rmax a b)``->``(Rabsolu ((f t)-[(phi_sequence un pr N t)]))<=(psi t)``)/\``(Rabsolu (RiemannInt_SF psi))<(un N)``).
Intros; Apply (projT2 ? ? (pr (un N))).
Qed.

Lemma RiemannInt_P1 : (f:R->R;a,b:R) (Riemann_integrable f a b) -> (Riemann_integrable f b a).
Unfold Riemann_integrable; Intros; Elim (X eps); Clear X; Intros; Elim p; Clear p; Intros; Apply Specif.existT with (mkStepFun (StepFun_P6 (pre x))); Apply Specif.existT with (mkStepFun (StepFun_P6 (pre x0))); Elim p; Clear p; Intros; Split.
Intros; Apply (H t); Elim H1; Clear H1; Intros; Split; [Apply Rle_trans with (Rmin b a); Try Assumption; Right; Unfold Rmin | Apply Rle_trans with (Rmax b a); Try Assumption; Right; Unfold Rmax]; (Case (total_order_Rle a b); Case (total_order_Rle b a); Intros; Try Reflexivity Orelse Apply Rle_antisym; [Assumption | Assumption | Auto with real | Auto with real]).
Generalize H0; Unfold RiemannInt_SF; Case (total_order_Rle a b); Case (total_order_Rle b a); Intros; (Replace (Int_SF (subdivision_val (mkStepFun (StepFun_P6 (pre x0)))) (subdivision (mkStepFun (StepFun_P6 (pre x0))))) with (Int_SF (subdivision_val x0) (subdivision x0)); [Idtac | Apply StepFun_P17 with (fe x0) a b; [Apply StepFun_P1 | Apply StepFun_P2; Apply (StepFun_P1 (mkStepFun (StepFun_P6 (pre x0))))]]).
Apply H1.
Rewrite Rabsolu_Ropp; Apply H1.
Rewrite Rabsolu_Ropp in H1; Apply H1.
Apply H1.
Qed.

Lemma RiemannInt_P2 : (f:R->R;a,b:R;un:nat->posreal;vn,wn:nat->(StepFun a b)) (Un_cv un R0) -> ``a<=b`` -> ((n:nat)((t:R)``(Rmin a b)<=t<=(Rmax a b)``->``(Rabsolu ((f t)-(vn n t)))<=(wn n t)``)/\``(Rabsolu (RiemannInt_SF (wn n)))<(un n)``) -> (sigTT ? [l:R](Un_cv [N:nat](RiemannInt_SF (vn N)) l)).
Intros; Apply R_complete; Unfold Un_cv in H; Unfold Cauchy_crit; Intros; Assert H3 : ``0<eps/2``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Elim (H ? H3); Intros N0 H4; Exists N0; Intros; Unfold R_dist; Unfold R_dist in H4; Elim (H1 n); Elim (H1 m); Intros; Replace ``(RiemannInt_SF (vn n))-(RiemannInt_SF (vn m))`` with ``(RiemannInt_SF (vn n))+(-1)*(RiemannInt_SF (vn m))``; [Idtac | Ring]; Rewrite <- StepFun_P30; Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 ``-1`` (vn n) (vn m)))))).
Apply StepFun_P34; Assumption.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P28 R1 (wn n) (wn m)))).
Apply StepFun_P37; Try Assumption.
Intros; Simpl; Apply Rle_trans with ``(Rabsolu ((vn n x)-(f x)))+(Rabsolu ((f x)-(vn m x)))``.
Replace ``(vn n x)+-1*(vn m x)`` with ``((vn n x)-(f x))+((f x)-(vn m x))``; [Apply Rabsolu_triang | Ring].
Assert H12 : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Assert H13 : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Rewrite <- H12 in H11; Pattern 2 b in H11; Rewrite <- H13 in H11; Rewrite Rmult_1l; Apply Rplus_le.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H9.
Elim H11; Intros; Split; Left; Assumption.
Apply H7.
Elim H11; Intros; Split; Left; Assumption.
Rewrite StepFun_P30; Rewrite Rmult_1l; Apply Rlt_trans with ``(un n)+(un m)``.
Apply Rle_lt_trans with ``(Rabsolu (RiemannInt_SF (wn n)))+(Rabsolu (RiemannInt_SF (wn m)))``.
Apply Rplus_le; Apply Rle_Rabsolu.
Apply Rplus_lt; Assumption.
Apply Rle_lt_trans with ``(Rabsolu (un n))+(Rabsolu (un m))``.
Apply Rplus_le; Apply Rle_Rabsolu.
Replace (pos (un n)) with ``(un n)-0``; [Idtac | Ring]; Replace (pos (un m)) with ``(un m)-0``; [Idtac | Ring]; Rewrite (double_var eps); Apply Rplus_lt; Apply H4; Assumption.
Qed.

Lemma RiemannInt_P3 : (f:R->R;a,b:R;un:nat->posreal;vn,wn:nat->(StepFun a b)) (Un_cv un R0) -> ((n:nat)((t:R)``(Rmin a b)<=t<=(Rmax a b)``->``(Rabsolu ((f t)-(vn n t)))<=(wn n t)``)/\``(Rabsolu (RiemannInt_SF (wn n)))<(un n)``)->(sigTT R ([l:R](Un_cv ([N:nat](RiemannInt_SF (vn N))) l))).
Intros; Case (total_order_Rle a b); Intro.
Apply RiemannInt_P2 with f un wn; Assumption.
Assert H1 : ``b<=a``; Auto with real.
Pose vn' := [n:nat](mkStepFun (StepFun_P6 (pre (vn n)))); Pose wn' := [n:nat](mkStepFun (StepFun_P6 (pre (wn n)))); Assert H2 : (n:nat)((t:R)``(Rmin b a)<=t<=(Rmax b a)``->``(Rabsolu ((f t)-(vn' n t)))<=(wn' n t)``)/\``(Rabsolu (RiemannInt_SF (wn' n)))<(un n)``.
Intro; Elim (H0 n0); Intros; Split.
Intros; Apply (H2 t); Elim H4; Clear H4; Intros; Split; [Apply Rle_trans with (Rmin b a); Try Assumption; Right; Unfold Rmin | Apply Rle_trans with (Rmax b a); Try Assumption; Right; Unfold Rmax]; (Case (total_order_Rle a b); Case (total_order_Rle b a); Intros; Try Reflexivity Orelse Apply Rle_antisym; [Assumption | Assumption | Auto with real | Auto with real]).
Generalize H3; Unfold RiemannInt_SF; Case (total_order_Rle a b); Case (total_order_Rle b a); Unfold wn'; Intros; (Replace (Int_SF (subdivision_val (mkStepFun (StepFun_P6 (pre (wn n0))))) (subdivision (mkStepFun (StepFun_P6 (pre (wn n0)))))) with (Int_SF (subdivision_val (wn n0)) (subdivision (wn n0))); [Idtac | Apply StepFun_P17 with (fe (wn n0)) a b; [Apply StepFun_P1 | Apply StepFun_P2; Apply (StepFun_P1 (mkStepFun (StepFun_P6 (pre (wn n0)))))]]).
Apply H4.
Rewrite Rabsolu_Ropp; Apply H4.
Rewrite Rabsolu_Ropp in H4; Apply H4.
Apply H4.
Assert H3 := (RiemannInt_P2 H H1 H2); Elim H3; Intros; Apply existTT with ``-x``; Unfold Un_cv; Unfold Un_cv in p; Intros; Elim (p ? H4); Intros; Exists x0; Intros; Generalize (H5 ? H6); Unfold R_dist RiemannInt_SF; Case (total_order_Rle b a); Case (total_order_Rle a b); Intros.
Elim n; Assumption.
Unfold vn' in H7; Replace (Int_SF (subdivision_val (vn n0)) (subdivision (vn n0))) with (Int_SF (subdivision_val (mkStepFun (StepFun_P6 (pre (vn n0))))) (subdivision (mkStepFun (StepFun_P6 (pre (vn n0)))))); [Unfold Rminus; Rewrite Ropp_Ropp; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr1; Rewrite Ropp_Ropp; Apply H7 | Symmetry; Apply StepFun_P17 with (fe (vn n0)) a b; [Apply StepFun_P1 | Apply StepFun_P2; Apply (StepFun_P1 (mkStepFun (StepFun_P6 (pre (vn n0)))))]].
Elim n1; Assumption.
Elim n2; Assumption.
Qed.

Lemma RiemannInt_exists : (f:R->R;a,b:R;pr:(Riemann_integrable f a b);un:nat->posreal) (Un_cv un R0) -> (sigTT ? [l:R](Un_cv [N:nat](RiemannInt_SF (phi_sequence un pr N)) l)).
Intros f; Intros; Apply RiemannInt_P3 with f un [n:nat](projT1 ? ? (phi_sequence_prop un pr n)); [Apply H | Intro; Apply (projT2 ? ? (phi_sequence_prop un pr n))].
Qed.

Lemma RiemannInt_P4 : (f:R->R;a,b,l:R;pr1,pr2:(Riemann_integrable f a b);un,vn:nat->posreal) (Un_cv un R0) -> (Un_cv vn R0) -> (Un_cv [N:nat](RiemannInt_SF (phi_sequence un pr1 N)) l) -> (Un_cv [N:nat](RiemannInt_SF (phi_sequence vn pr2 N)) l).
Unfold Un_cv; Unfold R_dist; Intros f; Intros; Assert H3 : ``0<eps/3``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Elim (H ? H3); Clear H; Intros N0 H; Elim (H0 ? H3); Clear H0; Intros N1 H0; Elim (H1 ? H3); Clear H1; Intros N2 H1; Pose N := (max (max N0 N1) N2); Exists N; Intros; Apply Rle_lt_trans with ``(Rabsolu ((RiemannInt_SF [(phi_sequence vn pr2 n)])-(RiemannInt_SF [(phi_sequence un pr1 n)])))+(Rabsolu ((RiemannInt_SF [(phi_sequence un pr1 n)])-l))``.
Replace ``(RiemannInt_SF [(phi_sequence vn pr2 n)])-l`` with ``((RiemannInt_SF [(phi_sequence vn pr2 n)])-(RiemannInt_SF [(phi_sequence un pr1 n)]))+((RiemannInt_SF [(phi_sequence un pr1 n)])-l)``; [Apply Rabsolu_triang | Ring].
Replace ``eps`` with ``2*eps/3+eps/3``.
Apply Rplus_lt.
Elim (phi_sequence_prop vn pr2 n); Intros psi_vn H5; Elim (phi_sequence_prop un pr1 n); Intros psi_un H6; Replace ``(RiemannInt_SF [(phi_sequence vn pr2 n)])-(RiemannInt_SF [(phi_sequence un pr1 n)])`` with ``(RiemannInt_SF [(phi_sequence vn pr2 n)])+(-1)*(RiemannInt_SF [(phi_sequence un pr1 n)])``; [Idtac | Ring]; Rewrite <- StepFun_P30.
Case (total_order_Rle a b); Intro.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 ``-1`` (phi_sequence vn pr2 n) (phi_sequence un pr1 n)))))).
Apply StepFun_P34; Assumption.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P28 R1 psi_un psi_vn))).
Apply StepFun_P37; Try Assumption; Intros; Simpl; Rewrite Rmult_1l; Apply Rle_trans with ``(Rabsolu ([(phi_sequence vn pr2 n x)]-(f x)))+(Rabsolu ((f x)-[(phi_sequence un pr1 n x)]))``.
Replace ``[(phi_sequence vn pr2 n x)]+-1*[(phi_sequence un pr1 n x)]`` with ``([(phi_sequence vn pr2 n x)]-(f x))+((f x)-[(phi_sequence un pr1 n x)])``; [Apply Rabsolu_triang | Ring].
Assert H10 : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Assert H11 : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Rewrite (Rplus_sym (psi_un x)); Apply Rplus_le.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Elim H5; Intros; Apply H8.
Rewrite H10; Rewrite H11; Elim H7; Intros; Split; Left; Assumption.
Elim H6; Intros; Apply H8.
Rewrite H10; Rewrite H11; Elim H7; Intros; Split; Left; Assumption.
Rewrite StepFun_P30; Rewrite Rmult_1l; Rewrite double; Apply Rplus_lt.
Apply Rlt_trans with (pos (un n)).
Elim H6; Intros; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF psi_un)).
Apply Rle_Rabsolu.
Assumption.
Replace (pos (un n)) with (Rabsolu ``(un n)-0``); [Apply H; Unfold ge; Apply le_trans with N; Try Assumption; Unfold N; Apply le_trans with (max N0 N1); Apply le_max_l | Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right; Apply Rle_sym1; Left; Apply (cond_pos (un n))].
Apply Rlt_trans with (pos (vn n)).
Elim H5; Intros; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF psi_vn)).
Apply Rle_Rabsolu; Assumption.
Assumption.
Replace (pos (vn n)) with (Rabsolu ``(vn n)-0``); [Apply H0; Unfold ge; Apply le_trans with N; Try Assumption; Unfold N; Apply le_trans with (max N0 N1); [Apply le_max_r | Apply le_max_l] | Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right; Apply Rle_sym1; Left; Apply (cond_pos (vn n))].
Rewrite StepFun_P39; Rewrite Rabsolu_Ropp; Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P6 (pre (mkStepFun (StepFun_P28 ``-1`` (phi_sequence vn pr2 n) (phi_sequence un pr1 n))))))))).
Apply StepFun_P34; Try Auto with real.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P6 (pre (mkStepFun (StepFun_P28 R1 psi_vn psi_un)))))).
Apply StepFun_P37.
Auto with real.
Intros; Simpl; Rewrite Rmult_1l; Apply Rle_trans with ``(Rabsolu ([(phi_sequence vn pr2 n x)]-(f x)))+(Rabsolu ((f x)-[(phi_sequence un pr1 n x)]))``.
Replace ``[(phi_sequence vn pr2 n x)]+-1*[(phi_sequence un pr1 n x)]`` with ``([(phi_sequence vn pr2 n x)]-(f x))+((f x)-[(phi_sequence un pr1 n x)])``; [Apply Rabsolu_triang | Ring].
Assert H10 : (Rmin a b)==b.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Elim n0; Assumption | Reflexivity].
Assert H11 : (Rmax a b)==a.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Elim n0; Assumption | Reflexivity].
Apply Rplus_le.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Elim H5; Intros; Apply H8.
Rewrite H10; Rewrite H11; Elim H7; Intros; Split; Left; Assumption.
Elim H6; Intros; Apply H8.
Rewrite H10; Rewrite H11; Elim H7; Intros; Split; Left; Assumption.
Rewrite <- (Ropp_Ropp (RiemannInt_SF (mkStepFun (StepFun_P6 (pre (mkStepFun (StepFun_P28 R1 psi_vn psi_un))))))); Rewrite <- StepFun_P39; Rewrite StepFun_P30; Rewrite Rmult_1l; Rewrite double; Rewrite Ropp_distr1; Apply Rplus_lt.
Apply Rlt_trans with (pos (vn n)).
Elim H5; Intros; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF psi_vn)).
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu.
Assumption.
Replace (pos (vn n)) with (Rabsolu ``(vn n)-0``); [Apply H0; Unfold ge; Apply le_trans with N; Try Assumption; Unfold N; Apply le_trans with (max N0 N1); [Apply le_max_r | Apply le_max_l] | Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right; Apply Rle_sym1; Left; Apply (cond_pos (vn n))].
Apply Rlt_trans with (pos (un n)).
Elim H6; Intros; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF psi_un)).
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu; Assumption.
Assumption.
Replace (pos (un n)) with (Rabsolu ``(un n)-0``); [Apply H; Unfold ge; Apply le_trans with N; Try Assumption; Unfold N; Apply le_trans with (max N0 N1); Apply le_max_l | Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right; Apply Rle_sym1; Left; Apply (cond_pos (un n))].
Apply H1; Unfold ge; Apply le_trans with N; Try Assumption; Unfold N; Apply le_max_r.
Apply r_Rmult_mult with ``3``; [Unfold Rdiv; Rewrite Rmult_Rplus_distr; Do 2 Rewrite (Rmult_sym ``3``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Ring | DiscrR] | DiscrR].
Qed.

Lemma RinvN_pos : (n:nat) ``0</((INR n)+1)``.
Intro; Apply Rlt_Rinv; Apply ge0_plus_gt0_is_gt0; [Apply pos_INR | Apply Rlt_R0_R1].
Qed.

Definition RinvN : nat->posreal := [N:nat](mkposreal ? (RinvN_pos N)).
 
Lemma RinvN_cv : (Un_cv RinvN R0).
Unfold Un_cv; Intros; Assert H0 := (archimed ``/eps``); Elim H0; Clear H0; Intros; Assert H2 : `0<=(up (Rinv eps))`.
Apply le_IZR; Left; Apply Rlt_trans with ``/eps``; [Apply Rlt_Rinv; Assumption | Assumption].
Elim (IZN ? H2); Intros; Exists x; Intros; Unfold R_dist; Simpl; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Assert H5 : ``0<(INR n)+1``.
Apply ge0_plus_gt0_is_gt0; [Apply pos_INR | Apply Rlt_R0_R1].
Rewrite Rabsolu_right; [Idtac | Left; Change ``0</((INR n)+1)``; Apply Rlt_Rinv; Assumption]; Apply Rle_lt_trans with ``/((INR x)+1)``.
Apply Rle_Rinv.
Apply ge0_plus_gt0_is_gt0; [Apply pos_INR | Apply Rlt_R0_R1].
Assumption.
Do 2 Rewrite <- (Rplus_sym R1); Apply Rle_compatibility; Apply le_INR; Apply H4.
Rewrite <- (Rinv_Rinv eps).
Apply Rinv_lt.
Apply Rmult_lt_pos.
Apply Rlt_Rinv; Assumption.
Apply ge0_plus_gt0_is_gt0; [Apply pos_INR | Apply Rlt_R0_R1].
Apply Rlt_trans with (INR x); [Rewrite INR_IZR_INZ; Rewrite <- H3; Apply H0 | Pattern 1 (INR x); Rewrite <- Rplus_Or; Apply Rlt_compatibility; Apply Rlt_R0_R1].
Red; Intro; Rewrite H6 in H; Elim (Rlt_antirefl ? H).
Qed.

(**********) 
Definition RiemannInt [f:R->R;a,b:R;pr:(Riemann_integrable f a b)] : R := Cases
(RiemannInt_exists pr 5!RinvN RinvN_cv) of (existTT a' b') => a' end.

Lemma RiemannInt_P5 : (f:R->R;a,b:R;pr1:(Riemann_integrable f a b);pr2:(Riemann_integrable f a b)) (RiemannInt pr1)==(RiemannInt pr2).
Intros; Unfold RiemannInt; Case (RiemannInt_exists pr1 5!RinvN RinvN_cv); Case (RiemannInt_exists pr2 5!RinvN RinvN_cv); Intros; EApply UL_sequence; [Apply u0 | Apply RiemannInt_P4 with pr2 RinvN; Apply RinvN_cv Orelse Assumption].
Qed.

(**************************************)
(* C°([a,b]) is included in L1([a,b]) *)
(**************************************)

Lemma maxN : (a,b:R;del:posreal) ``a<b`` -> (sigTT ? [n:nat]``a+(INR n)*del<b``/\``b<=a+(INR (S n))*del``).
Intros; Pose I := [n:nat]``a+(INR n)*del < b``; Assert H0 : (EX n:nat | (I n)).
Exists O; Unfold I; Rewrite Rmult_Ol; Rewrite Rplus_Or; Assumption.
Cut (Nbound I).
Intro; Assert H2 := (Nzorn H0 H1); Elim H2; Intros; Exists x; Elim p; Intros; Split.
Apply H3.
Case (total_order_T ``a+(INR (S x))*del`` b); Intro.
Elim s; Intro.
Assert H5 := (H4 (S x) a0); Elim (le_Sn_n ? H5).
Right; Symmetry; Assumption.
Left; Apply r.
Assert H1 : ``0<=(b-a)/del``.
Unfold Rdiv; Apply Rmult_le_pos; [Apply Rle_sym2; Apply Rge_minus; Apply Rle_sym1; Left; Apply H | Left; Apply Rlt_Rinv; Apply (cond_pos del)].
Elim (archimed ``(b-a)/del``); Intros; Assert H4 : `0<=(up (Rdiv (Rminus b a) del))`.
Apply le_IZR; Simpl; Left; Apply Rle_lt_trans with ``(b-a)/del``; Assumption.
Assert H5 := (IZN ? H4); Elim H5; Clear H5; Intros N H5; Unfold Nbound; Exists N; Intros; Unfold I in H6; Apply INR_le; Rewrite H5 in H2; Rewrite <- INR_IZR_INZ in H2; Left; Apply Rle_lt_trans with ``(b-a)/del``; Try Assumption; Apply Rle_monotony_contra with (pos del); [Apply (cond_pos del) | Unfold Rdiv; Rewrite <- (Rmult_sym ``/del``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Rewrite Rmult_sym; Apply Rle_anti_compatibility with a; Replace ``a+(b-a)`` with b; [Left; Assumption | Ring] | Assert H7 := (cond_pos del); Red; Intro; Rewrite H8 in H7; Elim (Rlt_antirefl ? H7)]].
Qed.

Fixpoint SubEquiN [N:nat] : R->R->posreal->Rlist :=
[x:R][y:R][del:posreal] Cases N of
| O => (cons y nil)
| (S p) => (cons x (SubEquiN p ``x+del`` y del))
end.

Definition max_N [a,b:R;del:posreal;h:``a<b``] : nat := Cases (maxN del h) of (existTT N H0) => N end.

Definition SubEqui [a,b:R;del:posreal;h:``a<b``] :Rlist := (SubEquiN (S (max_N del h)) a b del).

Lemma Heine_cor1 : (f:R->R;a,b:R) ``a<b`` -> ((x:R)``a<=x<=b``->(continuity_pt f x)) -> (eps:posreal) (sigTT ? [delta:posreal]``delta<=b-a``/\(x,y:R)``a<=x<=b``->``a<=y<=b``->``(Rabsolu (x-y)) < delta``->``(Rabsolu ((f x)-(f y))) < eps``).
Intro f; Intros; Pose E := [l:R]``0<l<=b-a``/\(x,y:R)``a <= x <= b``->``a <= y <= b``->``(Rabsolu (x-y)) < l``->``(Rabsolu ((f x)-(f y))) < eps``; Assert H1 : (bound E).
Unfold bound; Exists ``b-a``; Unfold is_upper_bound; Intros; Unfold E in H1; Elim H1; Clear H1; Intros H1 _; Elim H1; Intros; Assumption.
Assert H2 : (EXT x:R | (E x)).
Assert H2 := (Heine f [x:R]``a<=x<=b`` (compact_P3 a b) H0 eps); Elim H2; Intros; Exists (Rmin x ``b-a``); Unfold E; Split; [Split; [Unfold Rmin; Case (total_order_Rle x ``b-a``); Intro; [Apply (cond_pos x) | Apply Rlt_Rminus; Assumption] | Apply Rmin_r] | Intros; Apply H3; Try Assumption; Apply Rlt_le_trans with (Rmin x ``b-a``); [Assumption | Apply Rmin_l]].
Assert H3 := (complet E H1 H2); Elim H3; Intros; Cut ``0<x<=b-a``.
Intro; Elim H4; Clear H4; Intros; Apply existTT with (mkposreal ? H4); Split.
Apply H5.
Unfold is_lub in p; Elim p; Intros; Unfold is_upper_bound in H6; Pose D := ``(Rabsolu (x0-y))``; Elim (classic (EXT y:R | ``D<y``/\(E y))); Intro.
Elim H11; Intros; Elim H12; Clear H12; Intros; Unfold E in H13; Elim H13; Intros; Apply H15; Assumption.
Assert H12 := (not_ex_all_not ? [y:R]``D < y``/\(E y) H11); Assert H13 : (is_upper_bound E D).
Unfold is_upper_bound; Intros; Assert H14 := (H12 x1); Elim (not_and_or ``D<x1`` (E x1) H14); Intro.
Case (total_order_Rle x1 D); Intro.
Assumption.
Elim H15; Auto with real.
Elim H15; Assumption.
Assert H14 := (H7 ? H13); Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H14 H10)).
Unfold is_lub in p; Unfold is_upper_bound in p; Elim p; Clear p; Intros; Split.
Elim H2; Intros; Assert H7 := (H4 ? H6); Unfold E in H6; Elim H6; Clear H6; Intros H6 _; Elim H6; Intros; Apply Rlt_le_trans with x0; Assumption.
Apply H5; Intros; Unfold E in H6; Elim H6; Clear H6; Intros H6 _; Elim H6; Intros; Assumption.
Qed.

Lemma Heine_cor2 : (f:(R->R); a,b:R) ((x:R)``a <= x <= b``->(continuity_pt f x))->(eps:posreal)(sigTT posreal [delta:posreal]((x,y:R)``a <= x <= b``->``a <= y <= b``->``(Rabsolu (x-y)) < delta``->``(Rabsolu ((f x)-(f y))) < eps``)).
Intro f; Intros; Case (total_order_T a b); Intro.
Elim s; Intro.
Assert H0 := (Heine_cor1 a0 H eps); Elim H0; Intros; Apply existTT with x; Elim p; Intros; Apply H2; Assumption.
Apply existTT with (mkposreal ? Rlt_R0_R1); Intros; Assert H3 : x==y; [Elim H0; Elim H1; Intros; Rewrite b0 in H3; Rewrite b0 in H5; Apply Rle_antisym; Apply Rle_trans with b; Assumption | Rewrite H3; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply (cond_pos eps)].
Apply existTT with (mkposreal ? Rlt_R0_R1); Intros; Elim H0; Intros; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? (Rle_trans ? ? ? H3 H4) r)).
Qed.

Lemma SubEqui_P1 : (a,b:R;del:posreal;h:``a<b``) (pos_Rl (SubEqui del h) O)==a.
Intros; Unfold SubEqui; Case (maxN del h); Intros; Reflexivity.
Qed.

Lemma SubEqui_P2 : (a,b:R;del:posreal;h:``a<b``) (pos_Rl (SubEqui del h) (pred (Rlength (SubEqui del h))))==b.
Intros; Unfold SubEqui; Case (maxN del h); Intros; Clear a0; Cut (x:nat)(a:R)(del:posreal)(pos_Rl (SubEquiN (S x) a b del) (pred (Rlength (SubEquiN (S x) a b del)))) == b; [Intro; Apply H | Induction x0; [Intros; Reflexivity | Intros; Change (pos_Rl (SubEquiN (S n) ``a0+del0`` b del0) (pred (Rlength (SubEquiN (S n) ``a0+del0`` b del0))))==b; Apply H]].
Qed.

Lemma SubEqui_P3 : (N:nat;a,b:R;del:posreal) (Rlength (SubEquiN N a b del))=(S N).
Induction N; Intros; [Reflexivity | Simpl; Rewrite H; Reflexivity].
Qed.

Lemma SubEqui_P4 : (N:nat;a,b:R;del:posreal;i:nat) (lt i (S N)) -> (pos_Rl (SubEquiN (S N) a b del) i)==``a+(INR i)*del``.
Induction N; [Intros; Inversion H; [Simpl; Ring | Elim (le_Sn_O ? H1)] | Intros; Induction i; [Simpl; Ring | Change (pos_Rl (SubEquiN (S n) ``a+del`` b del) i)==``a+(INR (S i))*del``; Rewrite H; [Rewrite S_INR; Ring | Apply lt_S_n; Apply H0]]].
Qed.

Lemma SubEqui_P5 : (a,b:R;del:posreal;h:``a<b``) (Rlength (SubEqui del h))=(S (S (max_N del h))).
Intros; Unfold SubEqui; Apply SubEqui_P3.
Qed.

Lemma SubEqui_P6 : (a,b:R;del:posreal;h:``a<b``;i:nat) (lt i (S (max_N del h))) -> (pos_Rl (SubEqui del h) i)==``a+(INR i)*del``.
Intros; Unfold SubEqui; Apply SubEqui_P4; Assumption.
Qed.

Lemma SubEqui_P7 : (a,b:R;del:posreal;h:``a<b``) (ordered_Rlist (SubEqui del h)).
Intros; Unfold ordered_Rlist; Intros; Rewrite SubEqui_P5 in H; Simpl in H; Inversion H.
Rewrite (SubEqui_P6 3!del 4!h 5!(max_N del h)).
Replace (S (max_N del h)) with (pred (Rlength (SubEqui del h))).
Rewrite SubEqui_P2; Unfold max_N; Case (maxN del h); Intros; Left; Elim a0; Intros; Assumption.
Rewrite SubEqui_P5; Reflexivity.
Apply lt_n_Sn.
Repeat Rewrite SubEqui_P6.
3:Assumption.
2:Apply le_lt_n_Sm; Assumption.
Apply Rle_compatibility; Rewrite S_INR; Rewrite Rmult_Rplus_distrl; Pattern 1 ``(INR i)*del``; Rewrite <- Rplus_Or; Apply Rle_compatibility; Rewrite Rmult_1l; Left; Apply (cond_pos del).
Qed.

Lemma SubEqui_P8 : (a,b:R;del:posreal;h:``a<b``;i:nat) (lt i (Rlength (SubEqui del h))) -> ``a<=(pos_Rl (SubEqui del h) i)<=b``.
Intros; Split.
Pattern 1 a; Rewrite <- (SubEqui_P1 del h); Apply RList_P5.
Apply SubEqui_P7.
Elim (RList_P3 (SubEqui del h) (pos_Rl (SubEqui del h) i)); Intros; Apply H1; Exists i; Split; [Reflexivity | Assumption].
Pattern 2 b; Rewrite <- (SubEqui_P2 del h); Apply RList_P7; [Apply SubEqui_P7 | Elim (RList_P3 (SubEqui del h) (pos_Rl (SubEqui del h) i)); Intros; Apply H1; Exists i; Split; [Reflexivity | Assumption]].
Qed.

Lemma SubEqui_P9 : (a,b:R;del:posreal;f:R->R;h:``a<b``) (sigTT ? [g:(StepFun a b)](g b)==(f b)/\(i:nat)(lt i (pred (Rlength (SubEqui del h))))->(constant_D_eq g (co_interval (pos_Rl (SubEqui del h) i) (pos_Rl (SubEqui del h) (S i))) (f (pos_Rl (SubEqui del h) i)))).
Intros; Apply StepFun_P38; [Apply SubEqui_P7 | Apply SubEqui_P1 | Apply SubEqui_P2].
Qed.

Lemma  RiemannInt_P6 : (f:R->R;a,b:R) ``a<b`` -> ((x:R)``a<=x<=b``->(continuity_pt f x)) -> (Riemann_integrable f a b).
Intros; Unfold Riemann_integrable; Intro; Assert H1 : ``0<eps/(2*(b-a))``.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos eps) | Apply Rlt_Rinv; Apply Rmult_lt_pos; [Sup0 | Apply Rlt_Rminus; Assumption]].
Assert H2 : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Left; Assumption].
Assert H3 : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Left; Assumption].
Elim (Heine_cor2 H0 (mkposreal ? H1)); Intros del H4; Elim (SubEqui_P9 del f H); Intros phi [H5 H6]; Split with phi; Split with (mkStepFun (StepFun_P4 a b ``eps/(2*(b-a))``)); Split.
2:Rewrite StepFun_P18; Unfold Rdiv; Rewrite Rinv_Rmult.
2:Do 2 Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
2:Rewrite Rmult_1r; Rewrite Rabsolu_right.
2:Apply Rlt_monotony_contra with ``2``.
2:Sup0.
2:Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
2:Rewrite Rmult_1l; Pattern 1 (pos eps); Rewrite <- Rplus_Or; Rewrite double; Apply Rlt_compatibility; Apply (cond_pos eps).
2:DiscrR.
2:Apply Rle_sym1; Left; Apply Rmult_lt_pos.
2:Apply (cond_pos eps).
2:Apply Rlt_Rinv; Sup0.
2:Apply Rminus_eq_contra; Red; Intro; Clear H6; Rewrite H7 in H; Elim (Rlt_antirefl ? H).
2:DiscrR.
2:Apply Rminus_eq_contra; Red; Intro; Clear H6; Rewrite H7 in H; Elim (Rlt_antirefl ? H).
Intros; Rewrite H2 in H7; Rewrite H3 in H7; Simpl; Unfold fct_cte; Cut (t:R)``a<=t<=b``->t==b\/(EX i:nat | (lt i (pred (Rlength (SubEqui del H))))/\(co_interval (pos_Rl (SubEqui del H) i) (pos_Rl (SubEqui del H) (S i)) t)).
Intro; Elim (H8 ? H7); Intro.
Rewrite H9; Rewrite H5; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Left; Assumption.
Elim H9; Clear H9; Intros I [H9 H10]; Assert H11 := (H6 I H9 t H10); Rewrite H11; Left; Apply H4.
Assumption.
Apply SubEqui_P8; Apply lt_trans with (pred (Rlength (SubEqui del H))).
Assumption.
Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H12 in H9; Elim (lt_n_O ? H9).
Unfold co_interval in H10; Elim H10; Clear H10; Intros; Rewrite Rabsolu_right.
Rewrite SubEqui_P5 in H9; Simpl in H9; Inversion H9.
Apply Rlt_anti_compatibility with (pos_Rl (SubEqui del H) (max_N del H)).
Replace ``(pos_Rl (SubEqui del H) (max_N del H))+(t-(pos_Rl (SubEqui del H) (max_N del H)))`` with t; [Idtac | Ring]; Apply Rlt_le_trans with b.
Rewrite H14 in H12; Assert H13 : (S (max_N del H))=(pred (Rlength (SubEqui del H))).
Rewrite SubEqui_P5; Reflexivity.
Rewrite H13 in H12; Rewrite SubEqui_P2 in H12; Apply H12.
Rewrite SubEqui_P6.
2:Apply lt_n_Sn.
Unfold max_N; Case (maxN del H); Intros; Elim a0; Clear a0; Intros _ H13; Replace ``a+(INR x)*del+del`` with ``a+(INR (S x))*del``; [Assumption | Rewrite S_INR; Ring].
Apply Rlt_anti_compatibility with (pos_Rl (SubEqui del H) I); Replace ``(pos_Rl (SubEqui del H) I)+(t-(pos_Rl (SubEqui del H) I))`` with t; [Idtac | Ring]; Replace ``(pos_Rl (SubEqui del H) I)+del`` with (pos_Rl (SubEqui del H) (S I)).
Assumption.
Repeat Rewrite SubEqui_P6.
Rewrite S_INR; Ring.
Assumption.
Apply le_lt_n_Sm; Assumption.
Apply Rge_minus; Apply Rle_sym1; Assumption.
Intros; Clear H0 H1 H4 phi H5 H6 t H7; Case (Req_EM t0 b); Intro.
Left; Assumption.
Right; Pose I := [j:nat]``a+(INR j)*del<=t0``; Assert H1 : (EX n:nat | (I n)).
Exists O; Unfold I; Rewrite Rmult_Ol; Rewrite Rplus_Or; Elim H8; Intros; Assumption.
Assert H4 : (Nbound I).
Unfold Nbound; Exists (S (max_N del H)); Intros; Unfold max_N; Case (maxN del H); Intros; Elim a0; Clear a0; Intros _ H5; Apply INR_le; Apply Rle_monotony_contra with (pos del).
Apply (cond_pos del).
Apply Rle_anti_compatibility with a; Do 2 Rewrite (Rmult_sym del); Apply Rle_trans with t0; Unfold I in H4; Try Assumption; Apply Rle_trans with b; Try Assumption; Elim H8; Intros; Assumption.
Elim (Nzorn H1 H4); Intros N [H5 H6]; Assert H7 : (lt N (S (max_N del H))).
Unfold max_N; Case (maxN del H); Intros; Apply INR_lt; Apply Rlt_monotony_contra with (pos del).
Apply (cond_pos del).
Apply Rlt_anti_compatibility with a; Do 2 Rewrite (Rmult_sym del); Apply Rle_lt_trans with t0; Unfold I in H5; Try Assumption; Elim a0; Intros; Apply Rlt_le_trans with b; Try Assumption; Elim H8; Intros.
Elim H11; Intro.
Assumption.
Elim H0; Assumption.
Exists N; Split.
Rewrite SubEqui_P5; Simpl; Assumption.
Unfold co_interval; Split.
Rewrite SubEqui_P6.
Apply H5.
Assumption.
Inversion H7.
Replace (S (max_N del H)) with (pred (Rlength (SubEqui del H))).
Rewrite (SubEqui_P2 del H); Elim H8; Intros.
Elim H11; Intro.
Assumption.
Elim H0; Assumption.
Rewrite SubEqui_P5; Reflexivity.
Rewrite SubEqui_P6.
Case (total_order_Rle ``a+(INR (S N))*del`` t0); Intro.
Assert H11 := (H6 (S N) r); Elim (le_Sn_n ? H11).
Auto with real.
Apply le_lt_n_Sm; Assumption.
Qed.

Lemma RiemannInt_P7 : (f:R->R;a:R) (Riemann_integrable f a a).
Unfold Riemann_integrable; Intro f; Intros; Split with (mkStepFun (StepFun_P4 a a (f a))); Split with (mkStepFun (StepFun_P4 a a R0)); Split.
Intros; Simpl; Unfold fct_cte; Replace t with a.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Right; Reflexivity.
Generalize H; Unfold Rmin Rmax; Case (total_order_Rle a a); Intros; Elim H0; Intros; Apply Rle_antisym; Assumption.
Rewrite StepFun_P18; Rewrite Rmult_Ol; Rewrite Rabsolu_R0; Apply (cond_pos eps).
Qed.

Lemma continuity_implies_RiemannInt : (f:R->R;a,b:R) ``a<=b`` -> ((x:R)``a<=x<=b``->(continuity_pt f x)) -> (Riemann_integrable f a b).
Intros; Case (total_order_T a b); Intro; [Elim s; Intro; [Apply RiemannInt_P6; Assumption | Rewrite b0; Apply RiemannInt_P7] | Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H r))].
Qed.

Lemma RiemannInt_P8 : (f:R->R;a,b:R;pr1:(Riemann_integrable f a b);pr2:(Riemann_integrable f b a)) ``(RiemannInt pr1)==-(RiemannInt pr2)``.
Intro f; Intros; EApply UL_sequence.
Unfold RiemannInt; Case (RiemannInt_exists pr1 5!RinvN RinvN_cv); Intros; Apply u.
Unfold RiemannInt; Case (RiemannInt_exists pr2 5!RinvN RinvN_cv); Intros; Cut (EXT psi1:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((f t)-([(phi_sequence RinvN pr1 n)] t)))<= (psi1 n t)``)/\``(Rabsolu (RiemannInt_SF (psi1 n))) < (RinvN n)``).
Cut (EXT psi2:nat->(StepFun b a) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((f t)-([(phi_sequence RinvN pr2 n)] t)))<= (psi2 n t)``)/\``(Rabsolu (RiemannInt_SF (psi2 n))) < (RinvN n)``).
Intros; Elim H; Clear H; Intros psi2 H; Elim H0; Clear H0; Intros psi1 H0; Assert H1 := RinvN_cv; Unfold Un_cv; Intros; Assert H3 : ``0<eps/3``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Unfold Un_cv in H1; Elim (H1 ? H3); Clear H1; Intros N0 H1; Unfold R_dist in H1; Simpl in H1; Assert H4 : (n:nat)(ge n N0)->``(RinvN n)<eps/3``.
Intros; Assert H5 := (H1 ? H4); Replace (pos (RinvN n)) with ``(Rabsolu (/((INR n)+1)-0))``; [Assumption | Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right; Left; Apply (cond_pos (RinvN n))].
Clear H1; Unfold Un_cv in u; Elim (u ? H3); Clear u; Intros N1 H1; Exists (max N0 N1); Intros; Unfold R_dist; Apply Rle_lt_trans with ``(Rabsolu ((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+(RiemannInt_SF [(phi_sequence RinvN pr2 n)])))+(Rabsolu ((RiemannInt_SF [(phi_sequence RinvN pr2 n)])-x))``.
Rewrite <- (Rabsolu_Ropp ``(RiemannInt_SF [(phi_sequence RinvN pr2 n)])-x``); Replace ``(RiemannInt_SF [(phi_sequence RinvN pr1 n)])- -x`` with ``((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))+ -((RiemannInt_SF [(phi_sequence RinvN pr2 n)])-x)``; [Apply Rabsolu_triang | Ring].
Replace eps with ``2*eps/3+eps/3``.
Apply Rplus_lt.
Rewrite (StepFun_P39 (phi_sequence RinvN pr2 n)); Replace ``(RiemannInt_SF [(phi_sequence RinvN pr1 n)])+ -(RiemannInt_SF (mkStepFun (StepFun_P6 (pre [(phi_sequence RinvN pr2 n)]))))`` with ``(RiemannInt_SF [(phi_sequence RinvN pr1 n)])+(-1)*(RiemannInt_SF (mkStepFun (StepFun_P6 (pre [(phi_sequence RinvN pr2 n)]))))``; [Idtac | Ring]; Rewrite <- StepFun_P30.
Case (total_order_Rle a b); Intro.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 ``-1`` (phi_sequence RinvN pr1 n) (mkStepFun (StepFun_P6 (pre (phi_sequence RinvN pr2 n))))))))).
Apply StepFun_P34; Assumption.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P28 ``1`` (psi1 n) (mkStepFun (StepFun_P6 (pre (psi2 n))))))).
Apply StepFun_P37; Try Assumption.
Intros; Simpl; Rewrite Rmult_1l; Apply Rle_trans with ``(Rabsolu (([(phi_sequence RinvN pr1 n)] x0)-(f x0)))+(Rabsolu ((f x0)-([(phi_sequence RinvN pr2 n)] x0)))``.
Replace ``([(phi_sequence RinvN pr1 n)] x0)+ -1*([(phi_sequence RinvN pr2 n)] x0)`` with ``(([(phi_sequence RinvN pr1 n)] x0)-(f x0))+((f x0)-([(phi_sequence RinvN pr2 n)] x0))``; [Apply Rabsolu_triang | Ring].
Assert H7 : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Assert H8 : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Apply Rplus_le.
Elim (H0 n); Intros; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H9; Rewrite H7; Rewrite H8.
Elim H6; Intros; Split; Left; Assumption.
Elim (H n); Intros; Apply H9; Rewrite H7; Rewrite H8.
Elim H6; Intros; Split; Left; Assumption.
Rewrite StepFun_P30; Rewrite Rmult_1l; Rewrite double; Apply Rplus_lt.
Elim (H0 n); Intros; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi1 n))); [Apply Rle_Rabsolu | Apply Rlt_trans with (pos (RinvN n)); [Assumption | Apply H4; Unfold ge; Apply le_trans with (max N0 N1); [Apply le_max_l | Assumption]]].
Elim (H n); Intros; Rewrite <- (Ropp_Ropp (RiemannInt_SF (mkStepFun (StepFun_P6 (pre (psi2 n)))))); Rewrite <- StepFun_P39; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi2 n))); [Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu | Apply Rlt_trans with (pos (RinvN n)); [Assumption | Apply H4; Unfold ge; Apply le_trans with (max N0 N1); [Apply le_max_l | Assumption]]].
Assert Hyp : ``b<=a``.
Auto with real.
Rewrite StepFun_P39; Rewrite Rabsolu_Ropp; Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P6 (StepFun_P28 ``-1`` (phi_sequence RinvN pr1 n) (mkStepFun (StepFun_P6 (pre (phi_sequence RinvN pr2 n)))))))))).
Apply StepFun_P34; Assumption.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P28 ``1`` (mkStepFun (StepFun_P6 (pre (psi1 n)))) (psi2 n)))).
Apply StepFun_P37; Try Assumption.
Intros; Simpl; Rewrite Rmult_1l; Apply Rle_trans with ``(Rabsolu (([(phi_sequence RinvN pr1 n)] x0)-(f x0)))+(Rabsolu ((f x0)-([(phi_sequence RinvN pr2 n)] x0)))``.
Replace ``([(phi_sequence RinvN pr1 n)] x0)+ -1*([(phi_sequence RinvN pr2 n)] x0)`` with ``(([(phi_sequence RinvN pr1 n)] x0)-(f x0))+((f x0)-([(phi_sequence RinvN pr2 n)] x0))``; [Apply Rabsolu_triang | Ring].
Assert H7 : (Rmin a b)==b.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Elim n0; Assumption | Reflexivity].
Assert H8 : (Rmax a b)==a.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Elim n0; Assumption | Reflexivity].
Apply Rplus_le.
Elim (H0 n); Intros; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H9; Rewrite H7; Rewrite H8.
Elim H6; Intros; Split; Left; Assumption.
Elim (H n); Intros; Apply H9; Rewrite H7; Rewrite H8; Elim H6; Intros; Split; Left; Assumption.
Rewrite StepFun_P30; Rewrite Rmult_1l; Rewrite double; Apply Rplus_lt.
Elim (H0 n); Intros; Rewrite <- (Ropp_Ropp (RiemannInt_SF (mkStepFun (StepFun_P6 (pre (psi1 n)))))); Rewrite <- StepFun_P39; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi1 n))); [Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu | Apply Rlt_trans with (pos (RinvN n)); [Assumption | Apply H4; Unfold ge; Apply le_trans with (max N0 N1); [Apply le_max_l | Assumption]]].
Elim (H n); Intros; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi2 n))); [Apply Rle_Rabsolu | Apply Rlt_trans with (pos (RinvN n)); [Assumption | Apply H4; Unfold ge; Apply le_trans with (max N0 N1); [Apply le_max_l | Assumption]]].
Unfold R_dist in H1; Apply H1; Unfold ge; Apply le_trans with (max N0 N1); [Apply le_max_r | Assumption].
Apply r_Rmult_mult with ``3``; [Unfold Rdiv; Rewrite Rmult_Rplus_distr; Do 2 Rewrite (Rmult_sym ``3``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Ring | DiscrR] | DiscrR].
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr2 n)); Intro; Rewrite Rmin_sym; Rewrite RmaxSym; Apply (projT2 ? ? (phi_sequence_prop RinvN pr2 n)).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr1 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr1 n)).
Qed.

Lemma RiemannInt_P9 : (f:R->R;a:R;pr:(Riemann_integrable f a a)) ``(RiemannInt pr)==0``.
Intros; Assert H := (RiemannInt_P8 pr pr); Apply r_Rmult_mult with ``2``; [Rewrite Rmult_Or; Rewrite double; Pattern 2 (RiemannInt pr); Rewrite H; Apply Rplus_Ropp_r | DiscrR].
Qed.

Lemma Req_EM_T :(r1,r2:R) (sumboolT (r1==r2) ``r1<>r2``).
Intros; Elim (total_order_T r1 r2);Intros; [Elim a;Intro; [Right; Red; Intro; Rewrite H in a0; Elim (Rlt_antirefl ``r2`` a0) | Left;Assumption] | Right; Red; Intro; Rewrite H in b; Elim (Rlt_antirefl ``r2`` b)].
Qed.

(* L1([a,b]) is a vectorial space *)
Lemma RiemannInt_P10 : (f,g:R->R;a,b,l:R) (Riemann_integrable f a b) -> (Riemann_integrable g a b) -> (Riemann_integrable [x:R]``(f x)+l*(g x)`` a b).
Unfold Riemann_integrable; Intros f g; Intros; Case (Req_EM_T l R0); Intro.
Elim (X eps); Intros; Split with x; Elim p; Intros; Split with x0; Elim p0; Intros; Split; Try Assumption; Rewrite e; Intros; Rewrite Rmult_Ol; Rewrite Rplus_Or; Apply H; Assumption.
Assert H : ``0<eps/2``.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos eps) | Apply Rlt_Rinv; Sup0].
Assert H0 : ``0<eps/(2*(Rabsolu l))``.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos eps) | Apply Rlt_Rinv; Apply Rmult_lt_pos; [Sup0 | Apply Rabsolu_pos_lt; Assumption]].
Elim (X (mkposreal ? H)); Intros; Elim (X0 (mkposreal ? H0)); Intros; Split with (mkStepFun (StepFun_P28 l x x0)); Elim p0; Elim p; Intros; Split with (mkStepFun (StepFun_P28 (Rabsolu l) x1 x2)); Elim p1; Elim p2; Clear p1 p2 p0 p X X0; Intros; Split.
Intros; Simpl; Apply Rle_trans with ``(Rabsolu ((f t)-(x t)))+(Rabsolu (l*((g t)-(x0 t))))``.
Replace ``(f t)+l*(g t)-((x t)+l*(x0 t))`` with ``((f t)-(x t))+ l*((g t)-(x0 t))``; [Apply Rabsolu_triang | Ring].
Apply Rplus_le; [Apply H3; Assumption | Rewrite Rabsolu_mult; Apply Rle_monotony; [Apply Rabsolu_pos | Apply H1; Assumption]].
Rewrite StepFun_P30; Apply Rle_lt_trans with ``(Rabsolu (RiemannInt_SF x1))+(Rabsolu ((Rabsolu l)*(RiemannInt_SF x2)))``.
Apply Rabsolu_triang.
Rewrite (double_var eps); Apply Rplus_lt.
Apply H4.
Rewrite Rabsolu_mult; Rewrite Rabsolu_Rabsolu; Apply Rlt_monotony_contra with ``/(Rabsolu l)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym; [Rewrite Rmult_1l; Replace ``/(Rabsolu l)*eps/2`` with ``eps/(2*(Rabsolu l))``; [Apply H2 | Unfold Rdiv; Rewrite Rinv_Rmult; [Ring | DiscrR | Apply Rabsolu_no_R0; Assumption]] | Apply Rabsolu_no_R0; Assumption].
Qed.

Lemma RiemannInt_P11 : (f:R->R;a,b,l:R;un:nat->posreal;phi1,phi2,psi1,psi2:nat->(StepFun a b)) (Un_cv un R0) -> ((n:nat)((t:R)``(Rmin a b)<=t<=(Rmax a b)``->``(Rabsolu ((f t)-(phi1 n t)))<=(psi1 n t)``)/\``(Rabsolu (RiemannInt_SF (psi1 n)))<(un n)``) -> ((n:nat)((t:R)``(Rmin a b)<=t<=(Rmax a b)``->``(Rabsolu ((f t)-(phi2 n t)))<=(psi2 n t)``)/\``(Rabsolu (RiemannInt_SF (psi2 n)))<(un n)``) -> (Un_cv [N:nat](RiemannInt_SF (phi1 N)) l) -> (Un_cv [N:nat](RiemannInt_SF (phi2 N)) l).
Unfold Un_cv; Intro f; Intros; Intros.
Case (total_order_Rle a b); Intro Hyp.
Assert H4 : ``0<eps/3``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Elim (H ? H4); Clear H; Intros N0 H.
Elim (H2 ? H4); Clear H2; Intros N1 H2.
Pose N := (max N0 N1); Exists N; Intros; Unfold R_dist.
Apply Rle_lt_trans with ``(Rabsolu ((RiemannInt_SF (phi2 n))-(RiemannInt_SF (phi1 n))))+(Rabsolu ((RiemannInt_SF (phi1 n))-l))``.
Replace ``(RiemannInt_SF (phi2 n))-l`` with ``((RiemannInt_SF (phi2 n))-(RiemannInt_SF (phi1 n)))+((RiemannInt_SF (phi1 n))-l)``; [Apply Rabsolu_triang | Ring].
Replace ``eps`` with ``2*eps/3+eps/3``.
Apply Rplus_lt.
Replace ``(RiemannInt_SF (phi2 n))-(RiemannInt_SF (phi1 n))`` with ``(RiemannInt_SF (phi2 n))+(-1)*(RiemannInt_SF (phi1 n))``; [Idtac | Ring].
Rewrite <- StepFun_P30.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 ``-1`` (phi2 n) (phi1 n)))))).
Apply StepFun_P34; Assumption.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P28 R1 (psi1 n) (psi2 n)))).
Apply StepFun_P37; Try Assumption; Intros; Simpl; Rewrite Rmult_1l.
Apply Rle_trans with ``(Rabsolu ((phi2 n x)-(f x)))+(Rabsolu ((f x)-(phi1 n x)))``.
Replace ``(phi2 n x)+-1*(phi1 n x)`` with ``((phi2 n x)-(f x))+((f x)-(phi1 n x))``; [Apply Rabsolu_triang | Ring].
Rewrite (Rplus_sym (psi1 n x)); Apply Rplus_le.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Elim (H1 n); Intros; Apply H7.
Assert H10 : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Assert H11 : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Rewrite H10; Rewrite H11; Elim H6; Intros; Split; Left; Assumption.
Elim (H0 n); Intros; Apply H7; Assert H10 : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Assert H11 : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Rewrite H10; Rewrite H11; Elim H6; Intros; Split; Left; Assumption.
Rewrite StepFun_P30; Rewrite Rmult_1l; Rewrite double; Apply Rplus_lt.
Apply Rlt_trans with (pos (un n)).
Elim (H0 n); Intros; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi1 n))).
Apply Rle_Rabsolu.
Assumption.
Replace (pos (un n)) with (R_dist (un n) R0).
Apply H; Unfold ge; Apply le_trans with N; Try Assumption.
Unfold N; Apply le_max_l.
Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right.
Apply Rle_sym1; Left; Apply (cond_pos (un n)).
Apply Rlt_trans with (pos (un n)).
Elim (H1 n); Intros; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi2 n))).
Apply Rle_Rabsolu; Assumption.
Assumption.
Replace (pos (un n)) with (R_dist (un n) R0).
Apply H; Unfold ge; Apply le_trans with N; Try Assumption; Unfold N; Apply le_max_l.
Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right; Apply Rle_sym1; Left; Apply (cond_pos (un n)).
Unfold R_dist in H2; Apply H2; Unfold ge; Apply le_trans with N; Try Assumption; Unfold N; Apply le_max_r.
Apply r_Rmult_mult with ``3``; [Unfold Rdiv; Rewrite Rmult_Rplus_distr; Do 2 Rewrite (Rmult_sym ``3``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Ring | DiscrR] | DiscrR].
Assert H4 : ``0<eps/3``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Elim (H ? H4); Clear H; Intros N0 H.
Elim (H2 ? H4); Clear H2; Intros N1 H2.
Pose N := (max N0 N1); Exists N; Intros; Unfold R_dist.
Apply Rle_lt_trans with ``(Rabsolu ((RiemannInt_SF (phi2 n))-(RiemannInt_SF (phi1 n))))+(Rabsolu ((RiemannInt_SF (phi1 n))-l))``.
Replace ``(RiemannInt_SF (phi2 n))-l`` with ``((RiemannInt_SF (phi2 n))-(RiemannInt_SF (phi1 n)))+((RiemannInt_SF (phi1 n))-l)``; [Apply Rabsolu_triang | Ring].
Assert Hyp_b : ``b<=a``.
Auto with real.
Replace ``eps`` with ``2*eps/3+eps/3``.
Apply Rplus_lt.
Replace ``(RiemannInt_SF (phi2 n))-(RiemannInt_SF (phi1 n))`` with ``(RiemannInt_SF (phi2 n))+(-1)*(RiemannInt_SF (phi1 n))``; [Idtac | Ring].
Rewrite <- StepFun_P30.
Rewrite StepFun_P39.
Rewrite Rabsolu_Ropp.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P6 (pre (mkStepFun (StepFun_P28 ``-1`` (phi2 n) (phi1 n))))))))).
Apply StepFun_P34; Try Assumption.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P6 (pre (mkStepFun (StepFun_P28 R1 (psi1 n) (psi2 n))))))).
Apply StepFun_P37; Try Assumption.
Intros; Simpl; Rewrite Rmult_1l.
Apply Rle_trans with ``(Rabsolu ((phi2 n x)-(f x)))+(Rabsolu ((f x)-(phi1 n x)))``.
Replace ``(phi2 n x)+-1*(phi1 n x)`` with ``((phi2 n x)-(f x))+((f x)-(phi1 n x))``; [Apply Rabsolu_triang | Ring].
Rewrite (Rplus_sym (psi1 n x)); Apply Rplus_le.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Elim (H1 n); Intros; Apply H7.
Assert H10 : (Rmin a b)==b.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Elim Hyp; Assumption | Reflexivity].
Assert H11 : (Rmax a b)==a.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Elim Hyp; Assumption | Reflexivity].
Rewrite H10; Rewrite H11; Elim H6; Intros; Split; Left; Assumption.
Elim (H0 n); Intros; Apply H7; Assert H10 : (Rmin a b)==b.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Elim Hyp; Assumption | Reflexivity].
Assert H11 : (Rmax a b)==a.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Elim Hyp; Assumption | Reflexivity].
Rewrite H10; Rewrite H11; Elim H6; Intros; Split; Left; Assumption.
Rewrite <- (Ropp_Ropp (RiemannInt_SF
     (mkStepFun
     (StepFun_P6 (pre (mkStepFun (StepFun_P28 R1 (psi1 n) (psi2 n)))))))).
Rewrite <- StepFun_P39.
Rewrite StepFun_P30.
Rewrite Rmult_1l; Rewrite double.
Rewrite Ropp_distr1; Apply Rplus_lt.
Apply Rlt_trans with (pos (un n)).
Elim (H0 n); Intros; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi1 n))).
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu.
Assumption.
Replace (pos (un n)) with (R_dist (un n) R0).
Apply H; Unfold ge; Apply le_trans with N; Try Assumption.
Unfold N; Apply le_max_l.
Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right.
Apply Rle_sym1; Left; Apply (cond_pos (un n)).
Apply Rlt_trans with (pos (un n)).
Elim (H1 n); Intros; Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi2 n))).
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu; Assumption.
Assumption.
Replace (pos (un n)) with (R_dist (un n) R0).
Apply H; Unfold ge; Apply le_trans with N; Try Assumption; Unfold N; Apply le_max_l.
Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right; Apply Rle_sym1; Left; Apply (cond_pos (un n)).
Unfold R_dist in H2; Apply H2; Unfold ge; Apply le_trans with N; Try Assumption; Unfold N; Apply le_max_r.
Apply r_Rmult_mult with ``3``; [Unfold Rdiv; Rewrite Rmult_Rplus_distr; Do 2 Rewrite (Rmult_sym ``3``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Ring | DiscrR] | DiscrR].
Qed.

Lemma RiemannInt_P12 : (f,g:R->R;a,b,l:R;pr1:(Riemann_integrable f a b);pr2:(Riemann_integrable g a b);pr3:(Riemann_integrable [x:R]``(f x)+l*(g x)`` a b)) ``a<=b`` -> ``(RiemannInt pr3)==(RiemannInt pr1)+l*(RiemannInt pr2)``.
Intro f; Intros; Case (Req_EM l R0); Intro.
Pattern 2 l; Rewrite H0; Rewrite Rmult_Ol; Rewrite Rplus_Or; Unfold RiemannInt; Case (RiemannInt_exists pr3 5!RinvN RinvN_cv); Case (RiemannInt_exists pr1 5!RinvN RinvN_cv); Intros; EApply UL_sequence; [Apply u0 | Pose psi1 := [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr1 n)); Pose psi2 := [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr3 n)); Apply RiemannInt_P11 with f RinvN (phi_sequence RinvN pr1) psi1 psi2; [Apply RinvN_cv | Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr1 n)) | Intro; Assert H1 : ((t:R) ``(Rmin a b) <= t``/\``t <= (Rmax a b)`` -> (Rle (Rabsolu (Rminus ``(f t)+l*(g t)`` (phi_sequence RinvN pr3 n t))) (psi2 n t))) /\ ``(Rabsolu (RiemannInt_SF (psi2 n))) < (RinvN n)``; [Apply (projT2 ? ? (phi_sequence_prop RinvN pr3 n)) | Elim H1; Intros; Split; Try Assumption; Intros; Replace (f t) with ``(f t)+l*(g t)``; [Apply H2; Assumption | Rewrite H0; Ring]] | Assumption]].
EApply UL_sequence.
Unfold RiemannInt; Case (RiemannInt_exists pr3 5!RinvN RinvN_cv); Intros; Apply u.
Unfold Un_cv; Intros; Unfold RiemannInt; Case (RiemannInt_exists pr1 5!RinvN RinvN_cv); Case (RiemannInt_exists pr2 5!RinvN RinvN_cv); Unfold Un_cv; Intros; Assert H2 : ``0<eps/5``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Elim (u0 ? H2); Clear u0; Intros N0 H3; Assert H4 := RinvN_cv; Unfold Un_cv in H4; Elim (H4 ? H2); Clear H4 H2; Intros N1 H4; Assert H5 : ``0<eps/(5*(Rabsolu l))``. 
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rmult_lt_pos; [Sup0 | Apply Rabsolu_pos_lt; Assumption]].
Elim (u ? H5); Clear u; Intros N2 H6; Assert H7 := RinvN_cv; Unfold Un_cv in H7; Elim (H7 ? H5); Clear H7 H5; Intros N3 H5; Unfold R_dist in H3 H4 H5 H6; Pose N := (max (max N0 N1) (max N2 N3)).
Assert H7 : (n:nat) (ge n N1)->``(RinvN n)< eps/5``.
Intros; Replace (pos (RinvN n)) with ``(Rabsolu ((RinvN n)-0))``; [Unfold RinvN; Apply H4; Assumption | Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right; Left; Apply (cond_pos (RinvN n))].
Clear H4; Assert H4 := H7; Clear H7; Assert H7 : (n:nat) (ge n N3)->``(RinvN n)< eps/(5*(Rabsolu l))``.
Intros; Replace (pos (RinvN n)) with ``(Rabsolu ((RinvN n)-0))``; [Unfold RinvN; Apply H5; Assumption | Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right; Left; Apply (cond_pos (RinvN n))].
Clear H5; Assert H5 := H7; Clear H7; Exists N; Intros; Unfold R_dist.
Apply Rle_lt_trans with ``(Rabsolu ((RiemannInt_SF [(phi_sequence RinvN pr3 n)])-((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+l*(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))))+(Rabsolu ((RiemannInt_SF [(phi_sequence RinvN pr1 n)])-x0))+(Rabsolu l)*(Rabsolu ((RiemannInt_SF [(phi_sequence RinvN pr2 n)])-x))``.
Apply Rle_trans with ``(Rabsolu ((RiemannInt_SF [(phi_sequence RinvN pr3 n)])-((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+l*(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))))+(Rabsolu (((RiemannInt_SF [(phi_sequence RinvN pr1 n)])-x0)+l*((RiemannInt_SF [(phi_sequence RinvN pr2 n)])-x)))``.
Replace ``(RiemannInt_SF [(phi_sequence RinvN pr3 n)])-(x0+l*x)`` with ``(((RiemannInt_SF [(phi_sequence RinvN pr3 n)])-((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+l*(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))))+(((RiemannInt_SF [(phi_sequence RinvN pr1 n)])-x0)+l*((RiemannInt_SF [(phi_sequence RinvN pr2 n)])-x))``; [Apply Rabsolu_triang | Ring].
Rewrite Rplus_assoc; Apply Rle_compatibility; Rewrite <- Rabsolu_mult; Replace ``(RiemannInt_SF [(phi_sequence RinvN pr1 n)])-x0+l*((RiemannInt_SF [(phi_sequence RinvN pr2 n)])-x)`` with ``((RiemannInt_SF [(phi_sequence RinvN pr1 n)])-x0)+(l*((RiemannInt_SF [(phi_sequence RinvN pr2 n)])-x))``; [Apply Rabsolu_triang | Ring].
Replace eps with ``3*eps/5+eps/5+eps/5``.
Repeat Apply Rplus_lt.
Assert H7 : (EXT psi1:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((f t)-([(phi_sequence RinvN pr1 n)] t)))<= (psi1 n t)``)/\``(Rabsolu (RiemannInt_SF (psi1 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr1 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr1 n0)).
Assert H8 : (EXT psi2:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((g t)-([(phi_sequence RinvN pr2 n)] t)))<= (psi2 n t)``)/\``(Rabsolu (RiemannInt_SF (psi2 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr2 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr2 n0)).
Assert H9 : (EXT psi3:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu (((f t)+l*(g t))-([(phi_sequence RinvN pr3 n)] t)))<= (psi3 n t)``)/\``(Rabsolu (RiemannInt_SF (psi3 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr3 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr3 n0)).
Elim H7; Clear H7; Intros psi1 H7; Elim H8; Clear H8; Intros psi2 H8; Elim H9; Clear H9; Intros psi3 H9; Replace ``(RiemannInt_SF [(phi_sequence RinvN pr3 n)])-((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+l*(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))`` with ``(RiemannInt_SF [(phi_sequence RinvN pr3 n)])+(-1)*((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+l*(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))``; [Idtac | Ring]; Do 2 Rewrite <- StepFun_P30; Assert H10 : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Assert H11 : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Rewrite H10 in H7; Rewrite H10 in H8; Rewrite H10 in H9; Rewrite H11 in H7; Rewrite H11 in H8; Rewrite H11 in H9; Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 ``-1`` (phi_sequence RinvN pr3 n) (mkStepFun (StepFun_P28 l (phi_sequence RinvN pr1 n) (phi_sequence RinvN pr2 n)))))))).
Apply StepFun_P34; Assumption.
Apply Rle_lt_trans with (RiemannInt_SF (mkStepFun (StepFun_P28 R1 (psi3 n) (mkStepFun (StepFun_P28 (Rabsolu l) (psi1 n) (psi2 n)))))).
Apply StepFun_P37; Try Assumption.
Intros; Simpl; Rewrite Rmult_1l.
Apply Rle_trans with ``(Rabsolu (([(phi_sequence RinvN pr3 n)] x1)-((f x1)+l*(g x1))))+(Rabsolu (((f x1)+l*(g x1))+ -1*(([(phi_sequence RinvN pr1 n)] x1)+l*([(phi_sequence RinvN pr2 n)] x1))))``.
Replace ``([(phi_sequence RinvN pr3 n)] x1)+ -1*(([(phi_sequence RinvN pr1 n)] x1)+l*([(phi_sequence RinvN pr2 n)] x1))`` with ``(([(phi_sequence RinvN pr3 n)] x1)-((f x1)+l*(g x1)))+(((f x1)+l*(g x1))+ -1*(([(phi_sequence RinvN pr1 n)] x1)+l*([(phi_sequence RinvN pr2 n)] x1)))``; [Apply Rabsolu_triang | Ring].
Rewrite Rplus_assoc; Apply Rplus_le.
Elim (H9 n); Intros; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H13.
Elim H12; Intros; Split; Left; Assumption. 
Apply Rle_trans with ``(Rabsolu ((f x1)-([(phi_sequence RinvN pr1 n)] x1)))+(Rabsolu l)*(Rabsolu ((g x1)-([(phi_sequence RinvN pr2 n)] x1)))``.
Rewrite <- Rabsolu_mult; Replace ``((f x1)+(l*(g x1)+ -1*(([(phi_sequence RinvN pr1 n)] x1)+l*([(phi_sequence RinvN pr2 n)] x1))))`` with ``((f x1)-([(phi_sequence RinvN pr1 n)] x1))+l*((g x1)-([(phi_sequence RinvN pr2 n)] x1))``; [Apply Rabsolu_triang | Ring].
Apply Rplus_le.
Elim (H7 n); Intros; Apply H13.
Elim H12; Intros; Split; Left; Assumption.
Apply Rle_monotony; [Apply Rabsolu_pos | Elim (H8 n); Intros; Apply H13; Elim H12; Intros; Split; Left; Assumption].
Do 2 Rewrite StepFun_P30; Rewrite Rmult_1l; Replace ``3*eps/5`` with ``eps/5+(eps/5+eps/5)``; [Repeat Apply Rplus_lt | Ring].
Apply Rlt_trans with (pos (RinvN n)); [Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi3 n))); [Apply Rle_Rabsolu | Elim (H9 n); Intros; Assumption] | Apply H4; Unfold ge; Apply le_trans with N; [Apply le_trans with (max N0 N1); [Apply le_max_r | Unfold N; Apply le_max_l] | Assumption]].
Apply Rlt_trans with (pos (RinvN n)); [Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi1 n))); [Apply Rle_Rabsolu | Elim (H7 n); Intros; Assumption] | Apply H4; Unfold ge; Apply le_trans with N; [Apply le_trans with (max N0 N1); [Apply le_max_r | Unfold N; Apply le_max_l] | Assumption]].
Apply Rlt_monotony_contra with ``/(Rabsolu l)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Replace ``/(Rabsolu l)*eps/5`` with ``eps/(5*(Rabsolu l))``.
Apply Rlt_trans with (pos (RinvN n)); [Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi2 n))); [Apply Rle_Rabsolu | Elim (H8 n); Intros; Assumption] | Apply H5; Unfold ge; Apply le_trans with N; [Apply le_trans with (max N2 N3); [Apply le_max_r | Unfold N; Apply le_max_r] | Assumption]].
Unfold Rdiv; Rewrite Rinv_Rmult; [Ring | DiscrR | Apply Rabsolu_no_R0; Assumption].
Apply Rabsolu_no_R0; Assumption.
Apply H3; Unfold ge; Apply le_trans with (max N0 N1); [Apply le_max_l | Apply le_trans with N; [Unfold N; Apply le_max_l | Assumption]].
Apply Rlt_monotony_contra with ``/(Rabsolu l)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption.
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Replace ``/(Rabsolu l)*eps/5`` with ``eps/(5*(Rabsolu l))``.
Apply H6; Unfold ge; Apply le_trans with (max N2 N3); [Apply le_max_l | Apply le_trans with N; [Unfold N; Apply le_max_r | Assumption]].
Unfold Rdiv; Rewrite Rinv_Rmult; [Ring | DiscrR | Apply Rabsolu_no_R0; Assumption].
Apply Rabsolu_no_R0; Assumption.
Apply r_Rmult_mult with ``5``; [Unfold Rdiv; Do 2 Rewrite Rmult_Rplus_distr; Do 3 Rewrite (Rmult_sym ``5``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Ring | DiscrR] | DiscrR]. 
Qed.

Lemma RiemannInt_P13 : (f,g:R->R;a,b,l:R;pr1:(Riemann_integrable f a b);pr2:(Riemann_integrable g a b);pr3:(Riemann_integrable [x:R]``(f x)+l*(g x)`` a b)) ``(RiemannInt pr3)==(RiemannInt pr1)+l*(RiemannInt pr2)``.
Intros; Case (total_order_Rle a b); Intro; [Apply RiemannInt_P12; Assumption | Assert H : ``b<=a``; [Auto with real | Replace (RiemannInt pr3) with (Ropp (RiemannInt (RiemannInt_P1 pr3))); [Idtac | Symmetry; Apply RiemannInt_P8]; Replace (RiemannInt pr2) with (Ropp (RiemannInt (RiemannInt_P1 pr2))); [Idtac | Symmetry; Apply RiemannInt_P8]; Replace (RiemannInt pr1) with (Ropp (RiemannInt (RiemannInt_P1 pr1))); [Idtac | Symmetry; Apply RiemannInt_P8]; Rewrite (RiemannInt_P12 (RiemannInt_P1 pr1) (RiemannInt_P1 pr2) (RiemannInt_P1 pr3) H); Ring]].
Qed.

Lemma RiemannInt_P14 : (a,b,c:R) (Riemann_integrable (fct_cte c) a b).
Unfold Riemann_integrable; Intros; Split with (mkStepFun (StepFun_P4 a b c)); Split with (mkStepFun (StepFun_P4 a b R0)); Split; [Intros; Simpl; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Unfold fct_cte; Right; Reflexivity | Rewrite StepFun_P18; Rewrite Rmult_Ol; Rewrite Rabsolu_R0; Apply (cond_pos eps)].
Qed.

Lemma RiemannInt_P15 : (a,b,c:R;pr:(Riemann_integrable (fct_cte c) a b)) ``(RiemannInt pr)==c*(b-a)``.
Intros; Unfold RiemannInt; Case (RiemannInt_exists 1!(fct_cte c) 2!a 3!b pr 5!RinvN RinvN_cv); Intros; EApply UL_sequence.
Apply u.
Pose phi1 := [N:nat](phi_sequence RinvN 2!(fct_cte c) 3!a 4!b pr N); Change (Un_cv [N:nat](RiemannInt_SF (phi1 N)) ``c*(b-a)``); Pose f := (fct_cte c); Assert H1 : (EXT psi1:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((f t)-([(phi_sequence RinvN pr n)] t)))<= (psi1 n t)``)/\``(Rabsolu (RiemannInt_SF (psi1 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr n)).
Elim H1; Clear H1; Intros psi1 H1; Pose phi2 := [n:nat](mkStepFun (StepFun_P4 a b c)); Pose psi2 := [n:nat](mkStepFun (StepFun_P4 a b R0)); Apply RiemannInt_P11 with f RinvN phi2 psi2 psi1; Try Assumption.
Apply RinvN_cv.
Intro; Split.
Intros; Unfold f; Simpl; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Unfold fct_cte; Right; Reflexivity.
Unfold psi2; Rewrite StepFun_P18; Rewrite Rmult_Ol; Rewrite Rabsolu_R0; Apply (cond_pos (RinvN n)).
Unfold Un_cv; Intros; Split with O; Intros; Unfold R_dist; Unfold phi2; Rewrite StepFun_P18; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply H.
Qed.

Lemma RiemannInt_P16 : (f:R->R;a,b:R) (Riemann_integrable f a b) -> (Riemann_integrable [x:R](Rabsolu (f x)) a b).
Unfold Riemann_integrable; Intro f; Intros; Elim (X eps); Clear X; Intros phi [psi [H H0]]; Split with (mkStepFun (StepFun_P32 phi)); Split with psi; Split; Try Assumption; Intros; Simpl; Apply Rle_trans with ``(Rabsolu ((f t)-(phi t)))``; [Apply Rabsolu_triang_inv2 | Apply H; Assumption].
Qed.

Lemma Rle_cv_lim : (Un,Vn:nat->R;l1,l2:R) ((n:nat)``(Un n)<=(Vn n)``) -> (Un_cv Un l1) -> (Un_cv Vn l2) -> ``l1<=l2``.
Intros; Case (total_order_Rle l1 l2); Intro.
Assumption.
Assert H2 : ``l2<l1``.
Auto with real.
Clear n; Assert H3 : ``0<(l1-l2)/2``.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply Rlt_Rminus; Assumption | Apply Rlt_Rinv; Sup0].
Elim (H1 ? H3); Elim (H0 ? H3); Clear H0 H1; Unfold R_dist; Intros; Pose N := (max x x0); Cut ``(Vn N)<(Un N)``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? (H N) H4)).
Apply Rlt_trans with ``(l1+l2)/2``.
Apply Rlt_anti_compatibility with ``-l2``; Replace ``-l2+(l1+l2)/2`` with ``(l1-l2)/2``.
Rewrite Rplus_sym; Apply Rle_lt_trans with ``(Rabsolu ((Vn N)-l2))``.
Apply Rle_Rabsolu.
Apply H1; Unfold ge; Unfold N; Apply le_max_r.
Apply r_Rmult_mult with ``2``; [Unfold Rdiv; Do 2 Rewrite -> (Rmult_sym ``2``); Rewrite (Rmult_Rplus_distrl ``-l2`` ``(l1+l2)*/2`` ``2``); Repeat Rewrite -> Rmult_assoc; Rewrite <- Rinv_l_sym; [ Ring | DiscrR ] | DiscrR].
Apply Ropp_Rlt; Apply Rlt_anti_compatibility with l1; Replace ``l1+ -((l1+l2)/2)`` with ``(l1-l2)/2``.
Apply Rle_lt_trans with ``(Rabsolu ((Un N)-l1))``.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply Rle_Rabsolu.
Apply H0; Unfold ge; Unfold N; Apply le_max_l.
Apply r_Rmult_mult with ``2``; [Unfold Rdiv; Do 2 Rewrite -> (Rmult_sym ``2``); Rewrite (Rmult_Rplus_distrl ``l1`` ``-((l1+l2)*/2)`` ``2``); Rewrite <- Ropp_mul1; Repeat Rewrite -> Rmult_assoc; Rewrite <- Rinv_l_sym; [ Ring | DiscrR ] | DiscrR].
Qed.

Lemma RiemannInt_P17 : (f:R->R;a,b:R;pr1:(Riemann_integrable f a b);pr2:(Riemann_integrable [x:R](Rabsolu (f x)) a b)) ``a<=b`` -> ``(Rabsolu (RiemannInt pr1))<=(RiemannInt pr2)``.
Intro f; Intros; Unfold RiemannInt; Case (RiemannInt_exists 1!f 2!a 3!b pr1 5!RinvN RinvN_cv); Case (RiemannInt_exists 1!([x0:R](Rabsolu (f x0))) 2!a 3!b pr2 5!RinvN RinvN_cv); Intros; Pose phi1 := (phi_sequence RinvN pr1); Pose phi2 := [N:nat](mkStepFun (StepFun_P32 (phi1 N))); Apply Rle_cv_lim with [N:nat](Rabsolu (RiemannInt_SF (phi1 N))) [N:nat](RiemannInt_SF (phi2 N)).
Intro; Unfold phi2; Apply StepFun_P34; Assumption.
Fold phi1 in u0; Apply (continuity_seq Rabsolu [N:nat](RiemannInt_SF (phi1 N)) x0); Try Assumption.
Apply continuity_Rabsolu.
Pose phi3 := (phi_sequence RinvN pr2); Assert H0 : (EXT psi3:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((Rabsolu (f t))-((phi3 n) t)))<= (psi3 n t)``)/\``(Rabsolu (RiemannInt_SF (psi3 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr2 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr2 n)). 
Assert H1 : (EXT psi2:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((Rabsolu (f t))-((phi2 n) t)))<= (psi2 n t)``)/\``(Rabsolu (RiemannInt_SF (psi2 n))) < (RinvN n)``).
Assert H1 : (EXT psi2:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((f t)-((phi1 n) t)))<= (psi2 n t)``)/\``(Rabsolu (RiemannInt_SF (psi2 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr1 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr1 n)).
Elim H1; Clear H1; Intros psi2 H1; Split with psi2; Intros; Elim (H1 n); Clear H1; Intros; Split; Try Assumption.
Intros; Unfold phi2; Simpl; Apply Rle_trans with ``(Rabsolu ((f t)-((phi1 n) t)))``.
Apply Rabsolu_triang_inv2.
Apply H1; Assumption.
Elim H0; Clear H0; Intros psi3 H0; Elim H1; Clear H1; Intros psi2 H1; Apply RiemannInt_P11 with [x:R](Rabsolu (f x)) RinvN phi3 psi3 psi2; Try Assumption; Apply RinvN_cv.
Qed.

Lemma RiemannInt_P18 : (f,g:R->R;a,b:R;pr1:(Riemann_integrable f a b);pr2:(Riemann_integrable g a b)) ``a<=b`` -> ((x:R)``a<x<b``->``(f x)==(g x)``) -> ``(RiemannInt pr1)==(RiemannInt pr2)``.
Intro f; Intros; Unfold RiemannInt; Case (RiemannInt_exists 1!f 2!a 3!b pr1 5!RinvN RinvN_cv); Case (RiemannInt_exists 1!g 2!a 3!b pr2 5!RinvN RinvN_cv); Intros; EApply UL_sequence.
Apply u0.
Pose phi1 := [N:nat](phi_sequence RinvN 2!f 3!a 4!b pr1 N); Change (Un_cv [N:nat](RiemannInt_SF (phi1 N)) x); Assert H1 : (EXT psi1:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((f t)-((phi1 n) t)))<= (psi1 n t)``)/\``(Rabsolu (RiemannInt_SF (psi1 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr1 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr1 n)). 
Elim H1; Clear H1; Intros psi1 H1; Pose phi2 := [N:nat](phi_sequence RinvN 2!g 3!a 4!b pr2 N).
Pose phi2_aux := [N:nat][x:R](Cases (Req_EM_T x a) of
    | (leftT _) => (f a)
    | (rightT _) => (Cases (Req_EM_T x b) of
	| (leftT _) => (f b)
	| (rightT _) => (phi2 N x) end) end).
Cut (N:nat)(IsStepFun (phi2_aux N) a b).
Intro; Pose phi2_m := [N:nat](mkStepFun (X N)).
Assert H2 : (EXT psi2:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((g t)-((phi2 n) t)))<= (psi2 n t)``)/\``(Rabsolu (RiemannInt_SF (psi2 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr2 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr2 n)). 
Elim H2; Clear H2; Intros psi2 H2; Apply RiemannInt_P11 with f RinvN phi2_m psi2 psi1; Try Assumption. 
Apply RinvN_cv.
Intro; Elim (H2 n); Intros; Split; Try Assumption.
Intros; Unfold phi2_m; Simpl; Unfold phi2_aux; Case (Req_EM_T t a); Case (Req_EM_T t b); Intros.
Rewrite e0; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply Rle_trans with ``(Rabsolu ((g t)-((phi2 n) t)))``.
Apply Rabsolu_pos.
Pattern 3 a; Rewrite <- e0; Apply H3; Assumption.
Rewrite e; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply Rle_trans with ``(Rabsolu ((g t)-((phi2 n) t)))``.
Apply Rabsolu_pos.
Pattern 3 a; Rewrite <- e; Apply H3; Assumption.
Rewrite e; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply Rle_trans with ``(Rabsolu ((g t)-((phi2 n) t)))``.
Apply Rabsolu_pos.
Pattern 3 b; Rewrite <- e; Apply H3; Assumption.
Replace (f t) with (g t).
Apply H3; Assumption.
Symmetry; Apply H0; Elim H5; Clear H5; Intros.
Assert H7 : (Rmin a b)==a.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n2; Assumption].
Assert H8 : (Rmax a b)==b.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n2; Assumption].
Rewrite H7 in H5; Rewrite H8 in H6; Split.
Elim H5; Intro; [Assumption | Elim n1; Symmetry; Assumption].
Elim H6; Intro; [Assumption | Elim n0; Assumption].
Cut (N:nat)(RiemannInt_SF (phi2_m N))==(RiemannInt_SF (phi2 N)).
Intro; Unfold Un_cv; Intros; Elim (u ? H4); Intros; Exists x1; Intros; Rewrite (H3 n); Apply H5; Assumption.
Intro; Apply Rle_antisym.
Apply StepFun_P37; Try Assumption.
Intros; Unfold phi2_m; Simpl; Unfold phi2_aux; Case (Req_EM_T x1 a); Case (Req_EM_T x1 b); Intros.
Elim H3; Intros; Rewrite e0 in H4; Elim (Rlt_antirefl ? H4).
Elim H3; Intros; Rewrite e in H4; Elim (Rlt_antirefl ? H4).
Elim H3; Intros; Rewrite e in H5; Elim (Rlt_antirefl ? H5).
Right; Reflexivity.
Apply StepFun_P37; Try Assumption.
Intros; Unfold phi2_m; Simpl; Unfold phi2_aux; Case (Req_EM_T x1 a); Case (Req_EM_T x1 b); Intros.
Elim H3; Intros; Rewrite e0 in H4; Elim (Rlt_antirefl ? H4).
Elim H3; Intros; Rewrite e in H4; Elim (Rlt_antirefl ? H4).
Elim H3; Intros; Rewrite e in H5; Elim (Rlt_antirefl ? H5).
Right; Reflexivity.
Intro; Assert H2 := (pre (phi2 N)); Unfold IsStepFun in H2; Unfold is_subdivision in H2; Elim H2; Clear H2; Intros l [lf H2]; Split with l; Split with lf; Unfold adapted_couple in H2; Decompose [and] H2; Clear H2; Unfold adapted_couple; Repeat Split; Try Assumption.
Intros; Assert H9 := (H8 i H2); Unfold constant_D_eq open_interval in H9; Unfold constant_D_eq open_interval; Intros; Rewrite <- (H9 x1 H7); Assert H10 : ``a<=(pos_Rl l i)``.
Replace a with (Rmin a b).
Rewrite <- H5; Elim (RList_P6 l); Intros; Apply H10.
Assumption.
Apply le_O_n.
Apply lt_trans with (pred (Rlength l)); [Assumption | Apply lt_pred_n_n].
Apply neq_O_lt; Intro; Rewrite <- H12 in H6; Discriminate.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Assert H11 : ``(pos_Rl l (S i))<=b``.
Replace b with (Rmax a b).
Rewrite <- H4; Elim (RList_P6 l); Intros; Apply H11.
Assumption.
Apply lt_le_S; Assumption.
Apply lt_pred_n_n; Apply neq_O_lt; Intro; Rewrite <- H13 in H6; Discriminate.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Elim H7; Clear H7; Intros; Unfold phi2_aux; Case (Req_EM_T x1 a); Case (Req_EM_T x1 b); Intros.
Rewrite e in H12; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H11 H12)).
Rewrite e in H7; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H10 H7)).
Rewrite e in H12; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H11 H12)).
Reflexivity.
Qed.

Lemma RiemannInt_P19 : (f,g:R->R;a,b:R;pr1:(Riemann_integrable f a b);pr2:(Riemann_integrable g a b)) ``a<=b`` -> ((x:R)``a<x<b``->``(f x)<=(g x)``) -> ``(RiemannInt pr1)<=(RiemannInt pr2)``.
Intro f; Intros; Apply Rle_anti_compatibility with ``-(RiemannInt pr1)``; Rewrite Rplus_Ropp_l; Rewrite Rplus_sym; Apply Rle_trans with (Rabsolu (RiemannInt (RiemannInt_P10 ``-1`` pr2 pr1))).
Apply Rabsolu_pos.
Replace ``(RiemannInt pr2)+ -(RiemannInt pr1)`` with (RiemannInt (RiemannInt_P16 (RiemannInt_P10 ``-1`` pr2 pr1))).
Apply (RiemannInt_P17 (RiemannInt_P10 ``-1`` pr2 pr1) (RiemannInt_P16 (RiemannInt_P10 ``-1`` pr2 pr1))); Assumption.
Replace ``(RiemannInt pr2)+-(RiemannInt pr1)`` with (RiemannInt (RiemannInt_P10 ``-1`` pr2 pr1)).
Apply RiemannInt_P18; Try Assumption.
Intros; Apply Rabsolu_right.
Apply Rle_sym1; Apply Rle_anti_compatibility with (f x); Rewrite Rplus_Or; Replace ``(f x)+((g x)+ -1*(f x))`` with (g x); [Apply H0; Assumption | Ring].
Rewrite (RiemannInt_P12 pr2 pr1 (RiemannInt_P10 ``-1`` pr2 pr1)); [Ring | Assumption].
Qed.

Lemma FTC_P1 : (f:R->R;a,b:R) ``a<=b`` -> ((x:R)``a<=x<=b``->(continuity_pt f x)) -> ((x:R)``a<=x``->``x<=b``->(Riemann_integrable f a x)).
Intros; Apply continuity_implies_RiemannInt; [Assumption | Intros; Apply H0; Elim H3; Intros; Split; Assumption Orelse Apply Rle_trans with x; Assumption].
Qed.
V7only [Notation FTC_P2 := Rle_refl.].

Definition primitive [f:R->R;a,b:R;h:``a<=b``;pr:((x:R)``a<=x``->``x<=b``->(Riemann_integrable f a x))] : R->R := [x:R] Cases (total_order_Rle a x) of
   | (leftT r) => Cases (total_order_Rle x b) of
          | (leftT r0) => (RiemannInt (pr x r r0))
          | (rightT _) => ``(f b)*(x-b)+(RiemannInt (pr b h (FTC_P2 b)))`` end
   | (rightT _) => ``(f a)*(x-a)`` end.

Lemma RiemannInt_P20 : (f:R->R;a,b:R;h:``a<=b``;pr:((x:R)``a<=x``->``x<=b``->(Riemann_integrable f a x));pr0:(Riemann_integrable f a b)) ``(RiemannInt pr0)==(primitive h pr b)-(primitive h pr a)``.
Intros; Replace (primitive h pr a) with R0.
Replace (RiemannInt pr0) with (primitive h pr b).
Ring.
Unfold primitive; Case (total_order_Rle a b); Case (total_order_Rle b b); Intros; [Apply RiemannInt_P5 | Elim n; Right; Reflexivity | Elim n; Assumption | Elim n0; Assumption].
Symmetry; Unfold primitive; Case (total_order_Rle a a); Case (total_order_Rle a b); Intros; [Apply RiemannInt_P9 | Elim n; Assumption | Elim n; Right; Reflexivity | Elim n0; Right; Reflexivity].
Qed.

Lemma RiemannInt_P21 : (f:R->R;a,b,c:R) ``a<=b``-> ``b<=c`` -> (Riemann_integrable f a b) -> (Riemann_integrable f b c) -> (Riemann_integrable f a c).
Unfold Riemann_integrable; Intros f a b c Hyp1 Hyp2 X X0 eps.
Assert H : ``0<eps/2``.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos eps) | Apply Rlt_Rinv; Sup0].
Elim (X (mkposreal ? H)); Clear X; Intros phi1 [psi1 H1]; Elim (X0 (mkposreal ? H)); Clear X0; Intros phi2 [psi2 H2].
Pose phi3 := [x:R] Cases (total_order_Rle a x) of
  | (leftT _) => Cases (total_order_Rle x b) of
    | (leftT _) => (phi1 x)
    | (rightT _) => (phi2 x) end
  | (rightT _) => R0 end.
Pose psi3 := [x:R] Cases (total_order_Rle a x) of
  | (leftT _) => Cases (total_order_Rle x b) of
    | (leftT _) => (psi1 x)
    | (rightT _) => (psi2 x) end
  | (rightT _) => R0 end.
Cut (IsStepFun phi3 a c).
Intro; Cut (IsStepFun psi3 a b).
Intro; Cut (IsStepFun psi3 b c).
Intro; Cut (IsStepFun psi3 a c).
Intro; Split with (mkStepFun X); Split with (mkStepFun X2); Simpl; Split.
Intros; Unfold phi3 psi3; Case (total_order_Rle t b); Case (total_order_Rle a t); Intros.
Elim H1; Intros; Apply H3.
Replace (Rmin a b) with a.
Replace (Rmax a b) with b.
Split; Assumption.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Elim n; Replace a with (Rmin a c).
Elim H0; Intros; Assumption.
Unfold Rmin; Case (total_order_Rle a c); Intro; [Reflexivity | Elim n0; Apply Rle_trans with b; Assumption].
Elim H2; Intros; Apply H3.
Replace (Rmax b c) with (Rmax a c).
Elim H0; Intros; Split; Try Assumption.
Replace (Rmin b c) with b.
Auto with real.
Unfold Rmin; Case (total_order_Rle b c); Intro; [Reflexivity | Elim n0; Assumption].
Unfold Rmax; Case (total_order_Rle a c); Case (total_order_Rle b c); Intros; Try (Elim n0; Assumption Orelse Elim n0; Apply Rle_trans with b; Assumption).
Reflexivity.
Elim n; Replace a with (Rmin a c).
Elim H0; Intros; Assumption.
Unfold Rmin; Case (total_order_Rle a c); Intro; [Reflexivity | Elim n1; Apply Rle_trans with b; Assumption].
Rewrite <- (StepFun_P43 X0 X1 X2).
Apply Rle_lt_trans with ``(Rabsolu (RiemannInt_SF (mkStepFun X0)))+(Rabsolu (RiemannInt_SF (mkStepFun X1)))``.
Apply Rabsolu_triang.
Rewrite (double_var eps); Replace (RiemannInt_SF (mkStepFun X0)) with (RiemannInt_SF psi1).
Replace (RiemannInt_SF (mkStepFun X1)) with (RiemannInt_SF psi2).
Apply Rplus_lt.
Elim H1; Intros; Assumption.
Elim H2; Intros; Assumption.
Apply Rle_antisym.
Apply StepFun_P37; Try Assumption.
Simpl; Intros; Unfold psi3; Elim H0; Clear H0; Intros; Case (total_order_Rle a x); Case (total_order_Rle x b); Intros; [Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H0)) | Right; Reflexivity | Elim n; Apply Rle_trans with b; [Assumption | Left; Assumption] | Elim n0; Apply Rle_trans with b; [Assumption | Left; Assumption]].
Apply StepFun_P37; Try Assumption.
Simpl; Intros; Unfold psi3; Elim H0; Clear H0; Intros; Case (total_order_Rle a x); Case (total_order_Rle x b); Intros; [Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H0)) | Right; Reflexivity | Elim n; Apply Rle_trans with b; [Assumption | Left; Assumption] | Elim n0; Apply Rle_trans with b; [Assumption | Left; Assumption]].
Apply Rle_antisym.
Apply StepFun_P37; Try Assumption.
Simpl; Intros; Unfold psi3; Elim H0; Clear H0; Intros; Case (total_order_Rle a x); Case (total_order_Rle x b); Intros; [Right; Reflexivity | Elim n; Left; Assumption | Elim n; Left; Assumption | Elim n0; Left; Assumption].
Apply StepFun_P37; Try Assumption.
Simpl; Intros; Unfold psi3; Elim H0; Clear H0; Intros; Case (total_order_Rle a x); Case (total_order_Rle x b); Intros; [Right; Reflexivity | Elim n; Left; Assumption | Elim n; Left; Assumption | Elim n0; Left; Assumption].
Apply StepFun_P46 with b; Assumption.
Assert H3 := (pre psi2); Unfold IsStepFun in H3; Unfold is_subdivision in H3; Elim H3; Clear H3; Intros l1 [lf1 H3]; Split with l1; Split with lf1; Unfold adapted_couple in H3; Decompose [and] H3; Clear H3; Unfold adapted_couple; Repeat Split; Try Assumption.
Intros; Assert H9 := (H8 i H3); Unfold constant_D_eq open_interval; Unfold constant_D_eq open_interval in H9; Intros; Rewrite <- (H9 x H7); Unfold psi3; Assert H10 : ``b<x``.
Apply Rle_lt_trans with (pos_Rl l1 i).
Replace b with (Rmin b c).
Rewrite <- H5; Elim (RList_P6 l1); Intros; Apply H10; Try Assumption.
Apply le_O_n.
Apply lt_trans with (pred (Rlength l1)); Try Assumption; Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H12 in H6; Discriminate. 
Unfold Rmin; Case (total_order_Rle b c); Intro; [Reflexivity | Elim n; Assumption].
Elim H7; Intros; Assumption.
Case (total_order_Rle a x); Case (total_order_Rle x b); Intros; [Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H10)) | Reflexivity | Elim n; Apply Rle_trans with b; [Assumption | Left; Assumption] | Elim n0; Apply Rle_trans with b; [Assumption | Left; Assumption]].
Assert H3 := (pre psi1); Unfold IsStepFun in H3; Unfold is_subdivision in H3; Elim H3; Clear H3; Intros l1 [lf1 H3]; Split with l1; Split with lf1; Unfold adapted_couple in H3; Decompose [and] H3; Clear H3; Unfold adapted_couple; Repeat Split; Try Assumption.
Intros; Assert H9 := (H8 i H3); Unfold constant_D_eq open_interval; Unfold constant_D_eq open_interval in H9; Intros; Rewrite <- (H9 x H7); Unfold psi3; Assert H10 : ``x<=b``.
Apply Rle_trans with (pos_Rl l1 (S i)).
Elim H7; Intros; Left; Assumption.
Replace b with (Rmax a b).
Rewrite <- H4; Elim (RList_P6 l1); Intros; Apply H10; Try Assumption.
Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H12 in H6; Discriminate. 
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Assert H11 : ``a<=x``.
Apply Rle_trans with (pos_Rl l1 i).
Replace a with (Rmin a b).
Rewrite <- H5; Elim (RList_P6 l1); Intros; Apply H11; Try Assumption.
Apply le_O_n.
Apply lt_trans with (pred (Rlength l1)); Try Assumption; Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H13 in H6; Discriminate. 
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Left; Elim H7; Intros; Assumption.
Case (total_order_Rle a x); Case (total_order_Rle x b); Intros; Reflexivity Orelse Elim n; Assumption.
Apply StepFun_P46 with b.
Assert H3 := (pre phi1); Unfold IsStepFun in H3; Unfold is_subdivision in H3; Elim H3; Clear H3; Intros l1 [lf1 H3]; Split with l1; Split with lf1; Unfold adapted_couple in H3; Decompose [and] H3; Clear H3; Unfold adapted_couple; Repeat Split; Try Assumption.
Intros; Assert H9 := (H8 i H3); Unfold constant_D_eq open_interval; Unfold constant_D_eq open_interval in H9; Intros; Rewrite <- (H9 x H7); Unfold psi3; Assert H10 : ``x<=b``.
Apply Rle_trans with (pos_Rl l1 (S i)).
Elim H7; Intros; Left; Assumption.
Replace b with (Rmax a b).
Rewrite <- H4; Elim (RList_P6 l1); Intros; Apply H10; Try Assumption.
Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H12 in H6; Discriminate. 
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Assert H11 : ``a<=x``.
Apply Rle_trans with (pos_Rl l1 i).
Replace a with (Rmin a b).
Rewrite <- H5; Elim (RList_P6 l1); Intros; Apply H11; Try Assumption.
Apply le_O_n.
Apply lt_trans with (pred (Rlength l1)); Try Assumption; Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H13 in H6; Discriminate. 
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Assumption].
Left; Elim H7; Intros; Assumption.
Unfold phi3; Case (total_order_Rle a x); Case (total_order_Rle x b); Intros; Reflexivity Orelse Elim n; Assumption.
Assert H3 := (pre phi2); Unfold IsStepFun in H3; Unfold is_subdivision in H3; Elim H3; Clear H3; Intros l1 [lf1 H3]; Split with l1; Split with lf1; Unfold adapted_couple in H3; Decompose [and] H3; Clear H3; Unfold adapted_couple; Repeat Split; Try Assumption.
Intros; Assert H9 := (H8 i H3); Unfold constant_D_eq open_interval; Unfold constant_D_eq open_interval in H9; Intros; Rewrite <- (H9 x H7); Unfold psi3; Assert H10 : ``b<x``.
Apply Rle_lt_trans with (pos_Rl l1 i).
Replace b with (Rmin b c).
Rewrite <- H5; Elim (RList_P6 l1); Intros; Apply H10; Try Assumption.
Apply le_O_n.
Apply lt_trans with (pred (Rlength l1)); Try Assumption; Apply lt_pred_n_n; Apply neq_O_lt; Red; Intro; Rewrite <- H12 in H6; Discriminate. 
Unfold Rmin; Case (total_order_Rle b c); Intro; [Reflexivity | Elim n; Assumption].
Elim H7; Intros; Assumption.
Unfold phi3; Case (total_order_Rle a x); Case (total_order_Rle x b); Intros; [Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H10)) | Reflexivity | Elim n; Apply Rle_trans with b; [Assumption | Left; Assumption] | Elim n0; Apply Rle_trans with b; [Assumption | Left; Assumption]].
Qed.

Lemma RiemannInt_P22 : (f:R->R;a,b,c:R) (Riemann_integrable f a b) -> ``a<=c<=b`` -> (Riemann_integrable f a c).
Unfold Riemann_integrable; Intros; Elim (X eps); Clear X; Intros phi [psi H0]; Elim H; Elim H0; Clear H H0; Intros; Assert H3 : (IsStepFun phi a c).
Apply StepFun_P44 with b.
Apply (pre phi).
Split; Assumption.
Assert H4 : (IsStepFun psi a c).
Apply StepFun_P44 with b.
Apply (pre psi).
Split; Assumption.
Split with (mkStepFun H3); Split with (mkStepFun H4); Split.
Simpl; Intros; Apply H.
Replace (Rmin a b) with (Rmin a c).
Elim H5; Intros; Split; Try Assumption.
Apply Rle_trans with (Rmax a c); Try Assumption.
Replace (Rmax a b) with b.
Replace (Rmax a c) with c.
Assumption.
Unfold Rmax; Case (total_order_Rle a c); Intro; [Reflexivity | Elim n; Assumption].
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption].
Unfold Rmin; Case (total_order_Rle a c); Case (total_order_Rle a b); Intros; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption | Elim n; Assumption | Elim n0; Assumption].
Rewrite Rabsolu_right.
Assert H5 : (IsStepFun psi c b).
Apply StepFun_P46 with a.
Apply StepFun_P6; Assumption.
Apply (pre psi).
Replace (RiemannInt_SF (mkStepFun H4)) with ``(RiemannInt_SF psi)-(RiemannInt_SF (mkStepFun H5))``.
Apply Rle_lt_trans with (RiemannInt_SF psi).
Unfold Rminus; Pattern 2 (RiemannInt_SF psi); Rewrite <- Rplus_Or; Apply Rle_compatibility; Rewrite <- Ropp_O; Apply Rge_Ropp; Apply Rle_sym1; Replace R0 with (RiemannInt_SF (mkStepFun (StepFun_P4 c b R0))).
Apply StepFun_P37; Try Assumption.
Intros; Simpl; Unfold fct_cte; Apply Rle_trans with ``(Rabsolu ((f x)-(phi x)))``.
Apply Rabsolu_pos.
Apply H.
Replace (Rmin a b) with a.
Replace (Rmax a b) with b.
Elim H6; Intros; Split; Left.
Apply Rle_lt_trans with c; Assumption.
Assumption.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption].
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption].
Rewrite StepFun_P18; Ring.
Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF psi)).
Apply Rle_Rabsolu.
Assumption.
Assert H6 : (IsStepFun psi a b).
Apply (pre psi).
Replace (RiemannInt_SF psi) with (RiemannInt_SF (mkStepFun H6)).
Rewrite <- (StepFun_P43 H4 H5 H6); Ring.
Unfold RiemannInt_SF; Case (total_order_Rle a b); Intro.
EApply StepFun_P17.
Apply StepFun_P1.
Simpl; Apply StepFun_P1.
Apply eq_Ropp; EApply StepFun_P17.
Apply StepFun_P1.
Simpl; Apply StepFun_P1.
Apply Rle_sym1; Replace R0 with (RiemannInt_SF (mkStepFun (StepFun_P4 a c R0))).
Apply StepFun_P37; Try Assumption.
Intros; Simpl; Unfold fct_cte; Apply Rle_trans with ``(Rabsolu ((f x)-(phi x)))``.
Apply Rabsolu_pos.
Apply H.
Replace (Rmin a b) with a.
Replace (Rmax a b) with b.
Elim H5; Intros; Split; Left.
Assumption.
Apply Rlt_le_trans with c; Assumption.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption].
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption].
Rewrite StepFun_P18; Ring.
Qed.

Lemma RiemannInt_P23 : (f:R->R;a,b,c:R) (Riemann_integrable f a b) -> ``a<=c<=b`` -> (Riemann_integrable f c b).
Unfold Riemann_integrable; Intros; Elim (X eps); Clear X; Intros phi [psi H0]; Elim H; Elim H0; Clear H H0; Intros; Assert H3 : (IsStepFun phi c b).
Apply StepFun_P45 with a.
Apply (pre phi).
Split; Assumption.
Assert H4 : (IsStepFun psi c b).
Apply StepFun_P45 with a.
Apply (pre psi).
Split; Assumption.
Split with (mkStepFun H3); Split with (mkStepFun H4); Split.
Simpl; Intros; Apply H.
Replace (Rmax a b) with (Rmax c b).
Elim H5; Intros; Split; Try Assumption.
Apply Rle_trans with (Rmin c b); Try Assumption.
Replace (Rmin a b) with a.
Replace (Rmin c b) with c.
Assumption.
Unfold Rmin; Case (total_order_Rle c b); Intro; [Reflexivity | Elim n; Assumption].
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption].
Unfold Rmax; Case (total_order_Rle c b); Case (total_order_Rle a b); Intros; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption | Elim n; Assumption | Elim n0; Assumption].
Rewrite Rabsolu_right.
Assert H5 : (IsStepFun psi a c).
Apply StepFun_P46 with b.
Apply (pre psi).
Apply StepFun_P6; Assumption.
Replace (RiemannInt_SF (mkStepFun H4)) with ``(RiemannInt_SF psi)-(RiemannInt_SF (mkStepFun H5))``.
Apply Rle_lt_trans with (RiemannInt_SF psi).
Unfold Rminus; Pattern 2 (RiemannInt_SF psi); Rewrite <- Rplus_Or; Apply Rle_compatibility; Rewrite <- Ropp_O; Apply Rge_Ropp; Apply Rle_sym1; Replace R0 with (RiemannInt_SF (mkStepFun (StepFun_P4 a c R0))).
Apply StepFun_P37; Try Assumption.
Intros; Simpl; Unfold fct_cte; Apply Rle_trans with ``(Rabsolu ((f x)-(phi x)))``.
Apply Rabsolu_pos.
Apply H.
Replace (Rmin a b) with a.
Replace (Rmax a b) with b.
Elim H6; Intros; Split; Left.
Assumption.
Apply Rlt_le_trans with c; Assumption.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption].
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption].
Rewrite StepFun_P18; Ring.
Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF psi)).
Apply Rle_Rabsolu.
Assumption.
Assert H6 : (IsStepFun psi a b).
Apply (pre psi).
Replace (RiemannInt_SF psi) with (RiemannInt_SF (mkStepFun H6)).
Rewrite <- (StepFun_P43 H5 H4 H6); Ring.
Unfold RiemannInt_SF; Case (total_order_Rle a b); Intro.
EApply StepFun_P17.
Apply StepFun_P1.
Simpl; Apply StepFun_P1.
Apply eq_Ropp; EApply StepFun_P17.
Apply StepFun_P1.
Simpl; Apply StepFun_P1.
Apply Rle_sym1; Replace R0 with (RiemannInt_SF (mkStepFun (StepFun_P4 c b R0))).
Apply StepFun_P37; Try Assumption.
Intros; Simpl; Unfold fct_cte; Apply Rle_trans with ``(Rabsolu ((f x)-(phi x)))``.
Apply Rabsolu_pos.
Apply H.
Replace (Rmin a b) with a.
Replace (Rmax a b) with b.
Elim H5; Intros; Split; Left.
Apply Rle_lt_trans with c; Assumption.
Assumption.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption].
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n; Apply Rle_trans with c; Assumption].
Rewrite StepFun_P18; Ring.
Qed.

Lemma RiemannInt_P24 : (f:R->R;a,b,c:R) (Riemann_integrable f a b) -> (Riemann_integrable f b c) -> (Riemann_integrable f a c).
Intros; Case (total_order_Rle a b); Case (total_order_Rle b c); Intros.
Apply RiemannInt_P21 with b; Assumption.
Case (total_order_Rle a c); Intro.
Apply RiemannInt_P22 with b; Try Assumption.
Split; [Assumption | Auto with real].
Apply RiemannInt_P1; Apply RiemannInt_P22 with b.
Apply RiemannInt_P1; Assumption.
Split; Auto with real.
Case (total_order_Rle a c); Intro.
Apply RiemannInt_P23 with b; Try Assumption.
Split; Auto with real.
Apply RiemannInt_P1; Apply RiemannInt_P23 with b.
Apply RiemannInt_P1; Assumption.
Split; [Assumption | Auto with real].
Apply RiemannInt_P1; Apply RiemannInt_P21 with b; Auto with real Orelse Apply RiemannInt_P1; Assumption.
Qed.

Lemma RiemannInt_P25 : (f:R->R;a,b,c:R;pr1:(Riemann_integrable f a b);pr2:(Riemann_integrable f b c);pr3:(Riemann_integrable f a c)) ``a<=b``->``b<=c``->``(RiemannInt pr1)+(RiemannInt pr2)==(RiemannInt pr3)``.
Intros f a b c pr1 pr2 pr3 Hyp1 Hyp2; Unfold RiemannInt; Case (RiemannInt_exists 1!f 2!a 3!b pr1 5!RinvN RinvN_cv); Case (RiemannInt_exists 1!f 2!b 3!c pr2 5!RinvN RinvN_cv); Case (RiemannInt_exists 1!f 2!a 3!c pr3 5!RinvN RinvN_cv); Intros; Symmetry; EApply UL_sequence.
Apply u.
Unfold Un_cv; Intros; Assert H0 : ``0<eps/3``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Elim (u1 ? H0); Clear u1; Intros N1 H1; Elim (u0 ? H0); Clear u0; Intros N2 H2; Cut (Un_cv [n:nat]``(RiemannInt_SF [(phi_sequence RinvN pr3 n)])-((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))`` R0).
Intro; Elim (H3 ? H0); Clear H3; Intros N3 H3; Pose N0 := (max (max N1 N2) N3); Exists N0; Intros; Unfold R_dist; Apply Rle_lt_trans with ``(Rabsolu ((RiemannInt_SF [(phi_sequence RinvN pr3 n)])-((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))))+(Rabsolu (((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))-(x1+x0)))``.
Replace ``(RiemannInt_SF [(phi_sequence RinvN pr3 n)])-(x1+x0)`` with ``((RiemannInt_SF [(phi_sequence RinvN pr3 n)])-((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+(RiemannInt_SF [(phi_sequence RinvN pr2 n)])))+(((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))-(x1+x0))``; [Apply Rabsolu_triang | Ring].
Replace eps with ``eps/3+eps/3+eps/3``.
Rewrite Rplus_assoc; Apply Rplus_lt.
Unfold R_dist in H3; Cut (ge n N3).
Intro; Assert H6 := (H3 ? H5); Unfold Rminus in H6; Rewrite Ropp_O in H6; Rewrite Rplus_Or in H6; Apply H6.
Unfold ge; Apply le_trans with N0; [Unfold N0; Apply le_max_r | Assumption].
Apply Rle_lt_trans with ``(Rabsolu ((RiemannInt_SF [(phi_sequence RinvN pr1 n)])-x1))+(Rabsolu ((RiemannInt_SF [(phi_sequence RinvN pr2 n)])-x0))``.
Replace ``((RiemannInt_SF [(phi_sequence RinvN pr1 n)])+(RiemannInt_SF [(phi_sequence RinvN pr2 n)]))-(x1+x0)`` with ``((RiemannInt_SF [(phi_sequence RinvN pr1 n)])-x1)+((RiemannInt_SF [(phi_sequence RinvN pr2 n)])-x0)``; [Apply Rabsolu_triang | Ring].
Apply Rplus_lt.
Unfold R_dist in H1; Apply H1.
Unfold ge; Apply le_trans with N0; [Apply le_trans with (max N1 N2); [Apply le_max_l | Unfold N0; Apply le_max_l] | Assumption].
Unfold R_dist in H2; Apply H2.
Unfold ge; Apply le_trans with N0; [Apply le_trans with (max N1 N2); [Apply le_max_r | Unfold N0; Apply le_max_l] | Assumption].
Apply r_Rmult_mult with ``3``; [Unfold Rdiv; Repeat Rewrite Rmult_Rplus_distr; Do 2 Rewrite (Rmult_sym ``3``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Ring | DiscrR] | DiscrR].
Clear x u x0 x1 eps H H0 N1 H1 N2 H2; Assert H1 : (EXT psi1:nat->(StepFun a b) | (n:nat) ((t:R)``(Rmin a b) <= t``/\``t <= (Rmax a b)``->``(Rabsolu ((f t)-([(phi_sequence RinvN pr1 n)] t)))<= (psi1 n t)``)/\``(Rabsolu (RiemannInt_SF (psi1 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr1 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr1 n)). 
Assert H2 : (EXT psi2:nat->(StepFun b c) | (n:nat) ((t:R)``(Rmin b c) <= t``/\``t <= (Rmax b c)``->``(Rabsolu ((f t)-([(phi_sequence RinvN pr2 n)] t)))<= (psi2 n t)``)/\``(Rabsolu (RiemannInt_SF (psi2 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr2 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr2 n)). 
Assert H3 : (EXT psi3:nat->(StepFun a c) | (n:nat) ((t:R)``(Rmin a c) <= t``/\``t <= (Rmax a c)``->``(Rabsolu ((f t)-([(phi_sequence RinvN pr3 n)] t)))<= (psi3 n t)``)/\``(Rabsolu (RiemannInt_SF (psi3 n))) < (RinvN n)``).
Split with [n:nat](projT1 ? ? (phi_sequence_prop RinvN pr3 n)); Intro; Apply (projT2 ? ? (phi_sequence_prop RinvN pr3 n)). 
Elim H1; Clear H1; Intros psi1 H1; Elim H2; Clear H2; Intros psi2 H2; Elim H3; Clear H3; Intros psi3 H3; Assert H := RinvN_cv; Unfold Un_cv; Intros; Assert H4 : ``0<eps/3``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Elim (H ? H4); Clear H; Intros N0 H; Assert H5 : (n:nat)(ge n N0)->``(RinvN n)<eps/3``.
Intros; Replace (pos (RinvN n)) with ``(R_dist (mkposreal (/((INR n)+1)) (RinvN_pos n)) 0)``.
Apply H; Assumption.
Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply Rabsolu_right; Apply Rle_sym1; Left; Apply (cond_pos (RinvN n)).
Exists N0; Intros; Elim (H1 n); Elim (H2 n); Elim (H3 n); Clear H1 H2 H3; Intros; Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Pose phi1 := (phi_sequence RinvN pr1 n); Fold phi1 in H8; Pose phi2 := (phi_sequence RinvN pr2 n); Fold phi2 in H3; Pose phi3 := (phi_sequence RinvN pr3 n); Fold phi2 in H1; Assert H10 : (IsStepFun phi3 a b).
Apply StepFun_P44 with c.
Apply (pre phi3).
Split; Assumption.
Assert H11 : (IsStepFun (psi3 n) a b).
Apply StepFun_P44 with c.
Apply (pre (psi3 n)).
Split; Assumption.
Assert H12 : (IsStepFun phi3 b c).
Apply StepFun_P45 with a.
Apply (pre phi3).
Split; Assumption.
Assert H13 : (IsStepFun (psi3 n) b c).
Apply StepFun_P45 with a.
Apply (pre (psi3 n)).
Split; Assumption.
Replace (RiemannInt_SF phi3) with ``(RiemannInt_SF (mkStepFun H10))+(RiemannInt_SF (mkStepFun H12))``.
Apply Rle_lt_trans with ``(Rabsolu ((RiemannInt_SF (mkStepFun H10))-(RiemannInt_SF phi1)))+(Rabsolu ((RiemannInt_SF (mkStepFun H12))-(RiemannInt_SF phi2)))``.
Replace ``(RiemannInt_SF (mkStepFun H10))+(RiemannInt_SF (mkStepFun H12))+ -((RiemannInt_SF phi1)+(RiemannInt_SF phi2))`` with ``((RiemannInt_SF (mkStepFun H10))-(RiemannInt_SF phi1))+((RiemannInt_SF (mkStepFun H12))-(RiemannInt_SF phi2))``; [Apply Rabsolu_triang | Ring].
Replace ``(RiemannInt_SF (mkStepFun H10))-(RiemannInt_SF phi1)`` with (RiemannInt_SF (mkStepFun (StepFun_P28 ``-1`` (mkStepFun H10) phi1))).
Replace ``(RiemannInt_SF (mkStepFun H12))-(RiemannInt_SF phi2)`` with (RiemannInt_SF (mkStepFun (StepFun_P28 ``-1`` (mkStepFun H12) phi2))).
Apply Rle_lt_trans with ``(RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (mkStepFun H10) phi1)))))+(RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (mkStepFun H12) phi2)))))``.
Apply Rle_trans with ``(Rabsolu (RiemannInt_SF (mkStepFun (StepFun_P28 (-1) (mkStepFun H10) phi1))))+(RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (mkStepFun H12) phi2)))))``.
Apply Rle_compatibility.
Apply StepFun_P34; Try Assumption.
Do 2 Rewrite <- (Rplus_sym (RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 ``-1`` (mkStepFun H12) phi2)))))); Apply Rle_compatibility; Apply StepFun_P34; Try Assumption.
Apply Rle_lt_trans with ``(RiemannInt_SF (mkStepFun (StepFun_P28 R1 (mkStepFun H11) (psi1 n))))+(RiemannInt_SF (mkStepFun (StepFun_P28 R1 (mkStepFun H13) (psi2 n))))``.
Apply Rle_trans with ``(RiemannInt_SF (mkStepFun (StepFun_P32 (mkStepFun (StepFun_P28 (-1) (mkStepFun H10) phi1)))))+(RiemannInt_SF (mkStepFun (StepFun_P28 R1 (mkStepFun H13) (psi2 n))))``.
Apply Rle_compatibility; Apply StepFun_P37; Try Assumption.
Intros; Simpl; Rewrite Rmult_1l; Apply Rle_trans with ``(Rabsolu ((f x)-(phi3 x)))+(Rabsolu ((f x)-(phi2 x)))``.
Rewrite <- (Rabsolu_Ropp ``(f x)-(phi3 x)``); Rewrite Ropp_distr2; Replace ``(phi3 x)+ -1*(phi2 x)`` with ``((phi3 x)-(f x))+((f x)-(phi2 x))``; [Apply Rabsolu_triang | Ring].
Apply Rplus_le.
Fold phi3 in H1; Apply H1.
Elim H14; Intros; Split.
Replace (Rmin a c) with a.
Apply Rle_trans with b; Try Assumption.
Left; Assumption.
Unfold Rmin; Case (total_order_Rle a c); Intro; [Reflexivity | Elim n0; Apply Rle_trans with b; Assumption].
Replace (Rmax a c) with c.
Left; Assumption.
Unfold Rmax; Case (total_order_Rle a c); Intro; [Reflexivity | Elim n0; Apply Rle_trans with b; Assumption].
Apply H3.
Elim H14; Intros; Split.
Replace (Rmin b c) with b.
Left; Assumption.
Unfold Rmin; Case (total_order_Rle b c); Intro; [Reflexivity | Elim n0; Assumption].
Replace (Rmax b c) with c.
Left; Assumption.
Unfold Rmax; Case (total_order_Rle b c); Intro; [Reflexivity | Elim n0; Assumption].
Do 2 Rewrite <- (Rplus_sym ``(RiemannInt_SF (mkStepFun (StepFun_P28 R1 (mkStepFun H13) (psi2 n))))``); Apply Rle_compatibility; Apply StepFun_P37; Try Assumption.
Intros; Simpl; Rewrite Rmult_1l; Apply Rle_trans with ``(Rabsolu ((f x)-(phi3 x)))+(Rabsolu ((f x)-(phi1 x)))``.
Rewrite <- (Rabsolu_Ropp ``(f x)-(phi3 x)``); Rewrite Ropp_distr2; Replace ``(phi3 x)+ -1*(phi1 x)`` with ``((phi3 x)-(f x))+((f x)-(phi1 x))``; [Apply Rabsolu_triang | Ring].
Apply Rplus_le.
Apply H1.
Elim H14; Intros; Split.
Replace (Rmin a c) with a.
Left; Assumption.
Unfold Rmin; Case (total_order_Rle a c); Intro; [Reflexivity | Elim n0; Apply Rle_trans with b; Assumption].
Replace (Rmax a c) with c.
Apply Rle_trans with b.
Left; Assumption.
Assumption.
Unfold Rmax; Case (total_order_Rle a c); Intro; [Reflexivity | Elim n0; Apply Rle_trans with b; Assumption].
Apply H8.
Elim H14; Intros; Split.
Replace (Rmin a b) with a.
Left; Assumption.
Unfold Rmin; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Replace (Rmax a b) with b.
Left; Assumption.
Unfold Rmax; Case (total_order_Rle a b); Intro; [Reflexivity | Elim n0; Assumption].
Do 2 Rewrite StepFun_P30.
Do 2 Rewrite Rmult_1l; Replace ``(RiemannInt_SF (mkStepFun H11))+(RiemannInt_SF (psi1 n))+((RiemannInt_SF (mkStepFun H13))+(RiemannInt_SF (psi2 n)))`` with ``(RiemannInt_SF (psi3 n))+(RiemannInt_SF (psi1 n))+(RiemannInt_SF (psi2 n))``.
Replace eps with ``eps/3+eps/3+eps/3``.
Repeat Rewrite Rplus_assoc; Repeat Apply Rplus_lt.
Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi3 n))).
Apply Rle_Rabsolu.
Apply Rlt_trans with (pos (RinvN n)).
Assumption.
Apply H5; Assumption.
Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi1 n))).
Apply Rle_Rabsolu.
Apply Rlt_trans with (pos (RinvN n)).
Assumption.
Apply H5; Assumption.
Apply Rle_lt_trans with (Rabsolu (RiemannInt_SF (psi2 n))).
Apply Rle_Rabsolu.
Apply Rlt_trans with (pos (RinvN n)).
Assumption.
Apply H5; Assumption.
Apply r_Rmult_mult with ``3``; [Unfold Rdiv; Repeat Rewrite Rmult_Rplus_distr; Do 2 Rewrite (Rmult_sym ``3``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Ring | DiscrR] | DiscrR].
Replace (RiemannInt_SF (psi3 n)) with (RiemannInt_SF (mkStepFun (pre (psi3 n)))).
Rewrite <- (StepFun_P43 H11 H13 (pre (psi3 n))); Ring.
Reflexivity.
Rewrite StepFun_P30; Ring.
Rewrite StepFun_P30; Ring.
Apply (StepFun_P43 H10 H12 (pre phi3)).
Qed.

Lemma RiemannInt_P26 : (f:R->R;a,b,c:R;pr1:(Riemann_integrable f a b);pr2:(Riemann_integrable f b c);pr3:(Riemann_integrable f a c)) ``(RiemannInt pr1)+(RiemannInt pr2)==(RiemannInt pr3)``.
Intros; Case (total_order_Rle a b); Case (total_order_Rle b c); Intros.
Apply RiemannInt_P25; Assumption.
Case (total_order_Rle a c); Intro.
Assert H : ``c<=b``.
Auto with real.
Rewrite <- (RiemannInt_P25 pr3 (RiemannInt_P1 pr2) pr1 r0 H); Rewrite (RiemannInt_P8 pr2 (RiemannInt_P1 pr2)); Ring.
Assert H : ``c<=a``.
Auto with real.
Rewrite (RiemannInt_P8 pr2 (RiemannInt_P1 pr2)); Rewrite <- (RiemannInt_P25 (RiemannInt_P1 pr3) pr1 (RiemannInt_P1 pr2) H r); Rewrite (RiemannInt_P8 pr3 (RiemannInt_P1 pr3)); Ring.
Assert H : ``b<=a``.
Auto with real.
Case (total_order_Rle a c); Intro.
Rewrite <- (RiemannInt_P25 (RiemannInt_P1 pr1) pr3 pr2 H r0); Rewrite (RiemannInt_P8 pr1 (RiemannInt_P1 pr1)); Ring.
Assert H0 : ``c<=a``.
Auto with real.
Rewrite (RiemannInt_P8 pr1 (RiemannInt_P1 pr1)); Rewrite <- (RiemannInt_P25 pr2 (RiemannInt_P1 pr3) (RiemannInt_P1 pr1) r  H0); Rewrite (RiemannInt_P8 pr3 (RiemannInt_P1 pr3)); Ring.
Rewrite (RiemannInt_P8 pr1 (RiemannInt_P1 pr1)); Rewrite (RiemannInt_P8 pr2 (RiemannInt_P1 pr2)); Rewrite (RiemannInt_P8 pr3 (RiemannInt_P1 pr3)); Rewrite <- (RiemannInt_P25 (RiemannInt_P1 pr2) (RiemannInt_P1 pr1) (RiemannInt_P1 pr3)); [Ring | Auto with real | Auto with real].
Qed.

Lemma RiemannInt_P27 : (f:R->R;a,b,x:R;h:``a<=b``;C0:((x:R)``a<=x<=b``->(continuity_pt f x))) ``a<x<b`` -> (derivable_pt_lim (primitive h (FTC_P1 h C0)) x (f x)).
Intro f; Intros; Elim H; Clear H; Intros; Assert H1 : (continuity_pt f x).
Apply C0; Split; Left; Assumption.
Unfold derivable_pt_lim; Intros; Assert Hyp : ``0<eps/2``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Elim (H1 ? Hyp); Unfold dist D_x no_cond; Simpl; Unfold R_dist; Intros; Pose del := (Rmin x0 (Rmin ``b-x`` ``x-a``)); Assert H4 : ``0<del``.
Unfold del; Unfold Rmin; Case (total_order_Rle ``b-x`` ``x-a``); Intro.
Case (total_order_Rle x0 ``b-x``); Intro; [Elim H3; Intros; Assumption | Apply Rlt_Rminus; Assumption].
Case (total_order_Rle x0 ``x-a``); Intro; [Elim H3; Intros; Assumption | Apply Rlt_Rminus; Assumption].
Split with (mkposreal ? H4); Intros; Assert H7 : (Riemann_integrable f x ``x+h0``).
Case (total_order_Rle x ``x+h0``); Intro.
Apply continuity_implies_RiemannInt; Try Assumption.
Intros; Apply C0; Elim H7; Intros; Split.
Apply Rle_trans with x; [Left; Assumption | Assumption].
Apply Rle_trans with ``x+h0``.
Assumption.
Left; Apply Rlt_le_trans with ``x+del``.
Apply Rlt_compatibility; Apply Rle_lt_trans with (Rabsolu h0); [Apply Rle_Rabsolu | Apply H6].
Unfold del; Apply Rle_trans with ``x+(Rmin (b-x) (x-a))``.
Apply Rle_compatibility; Apply Rmin_r.
Pattern 2 b; Replace b with ``x+(b-x)``; [Apply Rle_compatibility; Apply Rmin_l | Ring].
Apply RiemannInt_P1; Apply continuity_implies_RiemannInt; Auto with real.
Intros; Apply C0; Elim H7; Intros; Split.
Apply Rle_trans with ``x+h0``.
Left; Apply Rle_lt_trans with ``x-del``.
Unfold del; Apply Rle_trans with ``x-(Rmin (b-x) (x-a))``.
Pattern 1 a; Replace a with ``x+(a-x)``; [Idtac | Ring].
Unfold Rminus; Apply Rle_compatibility; Apply Ropp_Rle.
Rewrite Ropp_Ropp; Rewrite Ropp_distr1; Rewrite Ropp_Ropp; Rewrite (Rplus_sym x); Apply Rmin_r.
Unfold Rminus; Apply Rle_compatibility; Apply Ropp_Rle.
Do 2 Rewrite Ropp_Ropp; Apply Rmin_r.
Unfold Rminus; Apply Rlt_compatibility; Apply Ropp_Rlt.
Rewrite Ropp_Ropp; Apply Rle_lt_trans with (Rabsolu h0); [Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu | Apply H6].
Assumption.
Apply Rle_trans with x; [Assumption | Left; Assumption].
Replace ``(primitive h (FTC_P1 h C0) (x+h0))-(primitive h (FTC_P1 h C0) x)`` with (RiemannInt H7).
Replace (f x) with ``(RiemannInt (RiemannInt_P14 x (x+h0) (f x)))/h0``.
Replace ``(RiemannInt H7)/h0-(RiemannInt (RiemannInt_P14 x (x+h0) (f x)))/h0`` with ``((RiemannInt H7)-(RiemannInt (RiemannInt_P14 x (x+h0) (f x))))/h0``.
Replace ``(RiemannInt H7)-(RiemannInt (RiemannInt_P14 x (x+h0) (f x)))`` with (RiemannInt (RiemannInt_P10 ``-1`` H7 (RiemannInt_P14 x ``x+h0`` (f x)))).
Unfold Rdiv; Rewrite Rabsolu_mult; Case (total_order_Rle x ``x+h0``); Intro.
Apply Rle_lt_trans with ``(RiemannInt (RiemannInt_P16 (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x+h0) (f x)))))*(Rabsolu (/h0))``.
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu (/h0))``); Apply Rle_monotony.
Apply Rabsolu_pos.
Apply (RiemannInt_P17 (RiemannInt_P10 ``-1`` H7 (RiemannInt_P14 x ``x+h0`` (f x))) (RiemannInt_P16 (RiemannInt_P10 ``-1`` H7 (RiemannInt_P14 x ``x+h0`` (f x))))); Assumption.
Apply Rle_lt_trans with ``(RiemannInt (RiemannInt_P14 x (x+h0) (eps/2)))*(Rabsolu (/h0))``.
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu (/h0))``); Apply Rle_monotony.
Apply Rabsolu_pos.
Apply RiemannInt_P19; Try Assumption.
Intros; Replace ``(f x1)+ -1*(fct_cte (f x) x1)`` with ``(f x1)-(f x)``.
Unfold fct_cte; Case (Req_EM x x1); Intro.
Rewrite H9; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Left; Assumption.
Elim H3; Intros; Left; Apply H11.
Repeat Split.
Assumption.
Rewrite Rabsolu_right.
Apply Rlt_anti_compatibility with x; Replace ``x+(x1-x)`` with x1; [Idtac | Ring].
Apply Rlt_le_trans with ``x+h0``.
Elim H8; Intros; Assumption.
Apply Rle_compatibility; Apply Rle_trans with del.
Left; Apply Rle_lt_trans with (Rabsolu h0); [Apply Rle_Rabsolu | Assumption].
Unfold del; Apply Rmin_l.
Apply Rge_minus; Apply Rle_sym1; Left; Elim H8; Intros; Assumption.
Unfold fct_cte; Ring.
Rewrite RiemannInt_P15.
Rewrite Rmult_assoc; Replace ``(x+h0-x)*(Rabsolu (/h0))`` with R1.
Rewrite Rmult_1r; Unfold Rdiv; Apply Rlt_monotony_contra with ``2``; [Sup0 | Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Pattern 1 eps; Rewrite <- Rplus_Or; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Rewrite Rabsolu_right.
Replace ``x+h0-x`` with h0; [Idtac | Ring].
Apply Rinv_r_sym.
Assumption.
Apply Rle_sym1; Left; Apply Rlt_Rinv.
Elim r; Intro.
Apply Rlt_anti_compatibility with x; Rewrite Rplus_Or; Assumption.
Elim H5; Symmetry; Apply r_Rplus_plus with x; Rewrite Rplus_Or; Assumption.
Apply Rle_lt_trans with ``(RiemannInt (RiemannInt_P16 (RiemannInt_P1 (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x+h0) (f x))))))*(Rabsolu (/h0))``.
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu (/h0))``); Apply Rle_monotony.
Apply Rabsolu_pos.
Replace (RiemannInt (RiemannInt_P10 ``-1`` H7 (RiemannInt_P14 x ``x+h0`` (f x)))) with ``-(RiemannInt (RiemannInt_P1 (RiemannInt_P10 (-1) H7 (RiemannInt_P14 x (x+h0) (f x)))))``.
Rewrite Rabsolu_Ropp; Apply (RiemannInt_P17 (RiemannInt_P1 (RiemannInt_P10 ``-1`` H7 (RiemannInt_P14 x ``x+h0`` (f x)))) (RiemannInt_P16 (RiemannInt_P1 (RiemannInt_P10 ``-1`` H7 (RiemannInt_P14 x ``x+h0`` (f x)))))); Auto with real.
Symmetry; Apply RiemannInt_P8.
Apply Rle_lt_trans with ``(RiemannInt (RiemannInt_P14 (x+h0) x (eps/2)))*(Rabsolu (/h0))``.
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu (/h0))``); Apply Rle_monotony.
Apply Rabsolu_pos.
Apply RiemannInt_P19.
Auto with real.
Intros; Replace ``(f x1)+ -1*(fct_cte (f x) x1)`` with ``(f x1)-(f x)``.
Unfold fct_cte; Case (Req_EM x x1); Intro.
Rewrite H9; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Left; Assumption.
Elim H3; Intros; Left; Apply H11.
Repeat Split.
Assumption.
Rewrite Rabsolu_left.
Apply Rlt_anti_compatibility with ``x1-x0``; Replace ``x1-x0+x0`` with x1; [Idtac | Ring].
Replace ``x1-x0+ -(x1-x)`` with ``x-x0``; [Idtac | Ring].
Apply Rle_lt_trans with ``x+h0``.
Unfold Rminus; Apply Rle_compatibility; Apply Ropp_Rle.
Rewrite Ropp_Ropp; Apply Rle_trans with (Rabsolu h0).
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu.
Apply Rle_trans with del; [Left; Assumption | Unfold del; Apply Rmin_l].
Elim H8; Intros; Assumption.
Apply Rlt_anti_compatibility with x; Rewrite Rplus_Or; Replace ``x+(x1-x)`` with x1; [Elim H8; Intros; Assumption | Ring].
Unfold fct_cte; Ring.
Rewrite RiemannInt_P15.
Rewrite Rmult_assoc; Replace ``(x-(x+h0))*(Rabsolu (/h0))`` with R1.
Rewrite Rmult_1r; Unfold Rdiv; Apply Rlt_monotony_contra with ``2``; [Sup0 | Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Pattern 1 eps; Rewrite <- Rplus_Or; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Rewrite Rabsolu_left.
Replace ``x-(x+h0)`` with ``-h0``; [Idtac | Ring].
Rewrite Ropp_mul1; Rewrite Ropp_mul3; Rewrite Ropp_Ropp; Apply Rinv_r_sym.
Assumption.
Apply Rlt_Rinv2.
Assert H8 : ``x+h0<x``.
Auto with real.
Apply Rlt_anti_compatibility with x; Rewrite Rplus_Or; Assumption.
Rewrite (RiemannInt_P13 H7 (RiemannInt_P14 x ``x+h0`` (f x)) (RiemannInt_P10 ``-1`` H7 (RiemannInt_P14 x ``x+h0`` (f x)))).
Ring.
Unfold Rdiv Rminus; Rewrite Rmult_Rplus_distrl; Ring.
Rewrite RiemannInt_P15; Apply r_Rmult_mult with h0; [Unfold Rdiv; Rewrite -> (Rmult_sym h0); Repeat Rewrite -> Rmult_assoc; Rewrite <- Rinv_l_sym; [Ring | Assumption] | Assumption].
Cut ``a<=x+h0``.
Cut ``x+h0<=b``.
Intros; Unfold primitive.
Case (total_order_Rle a ``x+h0``); Case (total_order_Rle ``x+h0`` b); Case (total_order_Rle a x); Case (total_order_Rle x b); Intros; Try (Elim n; Assumption Orelse Left; Assumption).
Rewrite <- (RiemannInt_P26 (FTC_P1 h C0 r0 r) H7 (FTC_P1 h C0 r2 r1)); Ring.
Apply Rle_anti_compatibility with ``-x``; Replace ``-x+(x+h0)`` with h0; [Idtac | Ring].
Rewrite Rplus_sym; Apply Rle_trans with (Rabsolu h0).
Apply Rle_Rabsolu.
Apply Rle_trans with del; [Left; Assumption | Unfold del; Apply Rle_trans with ``(Rmin (b-x) (x-a))``; [Apply Rmin_r | Apply Rmin_l]].
Apply Ropp_Rle; Apply Rle_anti_compatibility with ``x``; Replace ``x+-(x+h0)`` with ``-h0``; [Idtac | Ring].
Apply Rle_trans with (Rabsolu h0); [Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu | Apply Rle_trans with del; [Left; Assumption | Unfold del; Apply Rle_trans with ``(Rmin (b-x) (x-a))``; Apply Rmin_r]].
Qed.

Lemma RiemannInt_P28 : (f:R->R;a,b,x:R;h:``a<=b``;C0:((x:R)``a<=x<=b``->(continuity_pt f x))) ``a<=x<=b`` -> (derivable_pt_lim (primitive h (FTC_P1 h C0)) x (f x)).
Intro f; Intros; Elim h; Intro.
Elim H; Clear H; Intros; Elim H; Intro.
Elim H1; Intro.
Apply RiemannInt_P27; Split; Assumption.
Pose f_b := [x:R]``(f b)*(x-b)+(RiemannInt [(FTC_P1 h C0 h (FTC_P2 b))])``; Rewrite H3.
Assert H4 : (derivable_pt_lim f_b b (f b)).
Unfold f_b; Pattern 2 (f b); Replace (f b) with ``(f b)+0``.
Change (derivable_pt_lim (plus_fct (mult_fct (fct_cte (f b)) (minus_fct id (fct_cte b))) (fct_cte (RiemannInt (FTC_P1 h C0 h (FTC_P2 b))))) b ``(f b)+0``). 
Apply derivable_pt_lim_plus.
Pattern 2 (f b); Replace (f b) with ``0*((minus_fct id (fct_cte b)) b)+((fct_cte (f b)) b)*1``.
Apply derivable_pt_lim_mult.
Apply derivable_pt_lim_const.
Replace R1 with ``1-0``; [Idtac | Ring].
Apply derivable_pt_lim_minus.
Apply derivable_pt_lim_id.
Apply derivable_pt_lim_const.
Unfold fct_cte; Ring.
Apply derivable_pt_lim_const.
Ring.
Unfold derivable_pt_lim; Intros; Elim (H4 ? H5); Intros; Assert H7 : (continuity_pt f b).
Apply C0; Split; [Left; Assumption | Right; Reflexivity].
Assert H8 : ``0<eps/2``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Elim (H7 ? H8); Unfold D_x no_cond dist; Simpl; Unfold R_dist; Intros; Pose del := (Rmin x0 (Rmin x1 ``b-a``)); Assert H10 : ``0<del``.
Unfold del; Unfold Rmin; Case (total_order_Rle x1 ``b-a``); Intros.
Case (total_order_Rle x0 x1); Intro; [Apply (cond_pos x0) | Elim H9; Intros; Assumption].
Case (total_order_Rle x0 ``b-a``); Intro; [Apply (cond_pos x0) | Apply Rlt_Rminus; Assumption].
Split with (mkposreal ? H10); Intros; Case (case_Rabsolu h0); Intro.
Assert H14 : ``b+h0<b``.
Pattern 2 b; Rewrite <- Rplus_Or; Apply Rlt_compatibility; Assumption.
Assert H13 : (Riemann_integrable f ``b+h0`` b).
Apply continuity_implies_RiemannInt.
Left; Assumption.
Intros; Apply C0; Elim H13; Intros; Split; Try Assumption.
Apply Rle_trans with ``b+h0``; Try Assumption.
Apply Rle_anti_compatibility with ``-a-h0``.
Replace ``-a-h0+a`` with ``-h0``; [Idtac | Ring].
Replace ``-a-h0+(b+h0)`` with ``b-a``; [Idtac | Ring].
Apply Rle_trans with del.
Apply Rle_trans with (Rabsolu h0).
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu.
Left; Assumption.
Unfold del; Apply Rle_trans with (Rmin x1 ``b-a``); Apply Rmin_r.
Replace ``[(primitive h (FTC_P1 h C0) (b+h0))]-[(primitive h (FTC_P1 h C0) b)]`` with ``-(RiemannInt H13)``.
Replace (f b) with ``-[(RiemannInt (RiemannInt_P14 (b+h0) b (f b)))]/h0``.
Rewrite <- Rabsolu_Ropp; Unfold Rminus; Unfold Rdiv; Rewrite Ropp_mul1; Rewrite Ropp_distr1; Repeat Rewrite Ropp_Ropp; Replace ``(RiemannInt H13)*/h0+ -(RiemannInt (RiemannInt_P14 (b+h0) b (f b)))*/h0`` with ``((RiemannInt H13)-(RiemannInt (RiemannInt_P14 (b+h0) b (f b))))/h0``.
Replace ``(RiemannInt H13)-(RiemannInt (RiemannInt_P14 (b+h0) b (f b)))`` with (RiemannInt (RiemannInt_P10 ``-1`` H13 (RiemannInt_P14 ``b+h0`` b (f b)))).
Unfold Rdiv; Rewrite Rabsolu_mult; Apply Rle_lt_trans with ``(RiemannInt (RiemannInt_P16 (RiemannInt_P10 (-1) H13 (RiemannInt_P14 (b+h0) b (f b)))))*(Rabsolu (/h0))``.
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu (/h0))``); Apply Rle_monotony.
Apply Rabsolu_pos.
Apply (RiemannInt_P17 (RiemannInt_P10 ``-1`` H13 (RiemannInt_P14 ``b+h0`` b (f b))) (RiemannInt_P16 (RiemannInt_P10 ``-1`` H13 (RiemannInt_P14 ``b+h0`` b (f b))))); Left; Assumption.
Apply Rle_lt_trans with ``(RiemannInt (RiemannInt_P14 (b+h0) b (eps/2)))*(Rabsolu (/h0))``.
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu (/h0))``); Apply Rle_monotony.
Apply Rabsolu_pos.
Apply RiemannInt_P19.
Left; Assumption.
Intros; Replace ``(f x2)+ -1*(fct_cte (f b) x2)`` with ``(f x2)-(f b)``.
Unfold fct_cte; Case (Req_EM b x2); Intro.
Rewrite H16; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Left; Assumption.
Elim H9; Intros; Left; Apply H18.
Repeat Split.
Assumption.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Rewrite Rabsolu_right.
Apply Rlt_anti_compatibility with ``x2-x1``; Replace ``x2-x1+(b-x2)`` with ``b-x1``; [Idtac | Ring].
Replace ``x2-x1+x1`` with x2; [Idtac | Ring].
Apply Rlt_le_trans with ``b+h0``.
2:Elim H15; Intros; Left; Assumption.
Unfold Rminus; Apply Rlt_compatibility; Apply Ropp_Rlt; Rewrite Ropp_Ropp; Apply Rle_lt_trans with (Rabsolu h0).
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu.
Apply Rlt_le_trans with del; [Assumption | Unfold del; Apply Rle_trans with (Rmin x1 ``b-a``); [Apply Rmin_r | Apply Rmin_l]].
Apply Rle_sym1; Left; Apply Rlt_Rminus; Elim H15; Intros; Assumption.
Unfold fct_cte; Ring.
Rewrite RiemannInt_P15.
Rewrite Rmult_assoc; Replace ``(b-(b+h0))*(Rabsolu (/h0))`` with R1.
Rewrite Rmult_1r; Unfold Rdiv; Apply Rlt_monotony_contra with ``2``; [Sup0 | Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Pattern 1 eps; Rewrite <- Rplus_Or; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Rewrite Rabsolu_left.
Apply r_Rmult_mult with h0; [Do 2 Rewrite (Rmult_sym h0); Rewrite Rmult_assoc; Rewrite Ropp_mul1; Rewrite <- Rinv_l_sym; [ Ring | Assumption ] | Assumption].
Apply Rlt_Rinv2; Assumption.
Rewrite (RiemannInt_P13 H13 (RiemannInt_P14 ``b+h0`` b (f b)) (RiemannInt_P10 ``-1`` H13 (RiemannInt_P14 ``b+h0`` b (f b)))); Ring.
Unfold Rdiv Rminus; Rewrite Rmult_Rplus_distrl; Ring.
Rewrite RiemannInt_P15.
Rewrite <- Ropp_mul1; Apply r_Rmult_mult with h0; [Repeat Rewrite (Rmult_sym h0); Unfold Rdiv; Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Ring | Assumption] | Assumption].
Cut ``a<=b+h0``.
Cut ``b+h0<=b``.
Intros; Unfold primitive; Case (total_order_Rle a ``b+h0``); Case (total_order_Rle ``b+h0`` b); Case (total_order_Rle a b); Case (total_order_Rle b b); Intros; Try (Elim n; Right; Reflexivity) Orelse (Elim n; Left; Assumption).
Rewrite <- (RiemannInt_P26 (FTC_P1 h C0 r3 r2) H13 (FTC_P1 h C0 r1 r0)); Ring.
Elim n; Assumption.
Left; Assumption.
Apply Rle_anti_compatibility with ``-a-h0``.
Replace ``-a-h0+a`` with ``-h0``; [Idtac | Ring].
Replace ``-a-h0+(b+h0)`` with ``b-a``; [Idtac | Ring].
Apply Rle_trans with del.
Apply Rle_trans with (Rabsolu h0).
Rewrite <- Rabsolu_Ropp; Apply Rle_Rabsolu.
Left; Assumption.
Unfold del; Apply Rle_trans with (Rmin x1 ``b-a``); Apply Rmin_r.
Cut (primitive  h (FTC_P1 h C0) b)==(f_b b).
Intro; Cut (primitive  h (FTC_P1 h C0) ``b+h0``)==(f_b ``b+h0``).
Intro; Rewrite H13; Rewrite H14; Apply H6.
Assumption.
Apply Rlt_le_trans with del; [Assumption | Unfold del; Apply Rmin_l].
Assert H14 : ``b<b+h0``.
Pattern 1 b; Rewrite <- Rplus_Or; Apply Rlt_compatibility.
Assert H14 := (Rle_sym2 ? ? r); Elim H14; Intro.
Assumption.
Elim H11; Symmetry; Assumption.
Unfold primitive; Case (total_order_Rle a ``b+h0``); Case (total_order_Rle ``b+h0`` b); Intros; [Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r0 H14)) | Unfold f_b; Reflexivity | Elim n; Left; Apply Rlt_trans with b; Assumption | Elim n0; Left; Apply Rlt_trans with b; Assumption].
Unfold f_b; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rmult_Or; Rewrite Rplus_Ol; Unfold primitive; Case (total_order_Rle a b); Case (total_order_Rle b b); Intros; [Apply RiemannInt_P5 | Elim n; Right; Reflexivity | Elim n; Left; Assumption | Elim n; Right; Reflexivity].
(*****)
Pose f_a := [x:R]``(f a)*(x-a)``; Rewrite <- H2; Assert H3 : (derivable_pt_lim f_a a (f a)).
Unfold f_a; Change (derivable_pt_lim (mult_fct (fct_cte (f a)) (minus_fct id (fct_cte a))) a (f a)); Pattern 2 (f a); Replace (f a) with ``0*((minus_fct id (fct_cte a)) a)+((fct_cte (f a)) a)*1``.
Apply derivable_pt_lim_mult.
Apply derivable_pt_lim_const.
Replace R1 with ``1-0``; [Idtac | Ring].
Apply derivable_pt_lim_minus.
Apply derivable_pt_lim_id.
Apply derivable_pt_lim_const.
Unfold fct_cte; Ring.
Unfold derivable_pt_lim; Intros; Elim (H3 ? H4); Intros.
Assert H6 : (continuity_pt f a).
Apply C0; Split; [Right; Reflexivity | Left; Assumption].
Assert H7 : ``0<eps/2``.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Elim (H6 ? H7); Unfold D_x no_cond dist; Simpl; Unfold R_dist; Intros.
Pose del := (Rmin x0 (Rmin x1 ``b-a``)).
Assert H9 : ``0<del``.
Unfold del; Unfold Rmin.
Case (total_order_Rle x1 ``b-a``); Intros.
Case (total_order_Rle x0 x1); Intro.
Apply (cond_pos x0).
Elim H8; Intros; Assumption.
Case (total_order_Rle x0 ``b-a``); Intro.
Apply (cond_pos x0).
Apply Rlt_Rminus; Assumption.
Split with (mkposreal ? H9).
Intros; Case (case_Rabsolu h0); Intro.
Assert H12 : ``a+h0<a``.
Pattern 2 a; Rewrite <- Rplus_Or; Apply Rlt_compatibility; Assumption.
Unfold primitive.
Case (total_order_Rle a ``a+h0``); Case (total_order_Rle ``a+h0`` b); Case (total_order_Rle a a); Case (total_order_Rle a b); Intros; Try (Elim n; Left; Assumption) Orelse (Elim n; Right; Reflexivity).
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r3 H12)).
Elim n; Left; Apply Rlt_trans with a; Assumption.
Rewrite RiemannInt_P9; Replace R0 with (f_a a).
Replace ``(f a)*(a+h0-a)`` with (f_a ``a+h0``).
Apply H5; Try Assumption.
Apply Rlt_le_trans with del; [Assumption | Unfold del; Apply Rmin_l].
Unfold f_a; Ring.
Unfold f_a; Ring.
Elim n; Left; Apply Rlt_trans with a; Assumption.
Assert H12 : ``a<a+h0``.
Pattern 1 a; Rewrite <- Rplus_Or; Apply Rlt_compatibility.
Assert H12 := (Rle_sym2 ? ? r); Elim H12; Intro.
Assumption.
Elim H10; Symmetry; Assumption.
Assert H13 : (Riemann_integrable f a ``a+h0``).
Apply continuity_implies_RiemannInt.
Left; Assumption.
Intros; Apply C0; Elim H13; Intros; Split; Try Assumption.
Apply Rle_trans with ``a+h0``; Try Assumption.
Apply Rle_anti_compatibility with ``-b-h0``.
Replace ``-b-h0+b`` with ``-h0``; [Idtac | Ring].
Replace ``-b-h0+(a+h0)`` with ``a-b``; [Idtac | Ring].
Apply Ropp_Rle; Rewrite Ropp_Ropp; Rewrite Ropp_distr2; Apply Rle_trans with del.
Apply Rle_trans with (Rabsolu h0); [Apply Rle_Rabsolu | Left; Assumption].
Unfold del; Apply Rle_trans with (Rmin x1 ``b-a``); Apply Rmin_r.
Replace ``(primitive h (FTC_P1 h C0) (a+h0))-(primitive h (FTC_P1 h C0) a)`` with ``(RiemannInt H13)``.
Replace (f a) with ``(RiemannInt (RiemannInt_P14 a (a+h0) (f a)))/h0``.
Replace ``(RiemannInt H13)/h0-(RiemannInt (RiemannInt_P14 a (a+h0) (f a)))/h0`` with ``((RiemannInt H13)-(RiemannInt (RiemannInt_P14 a (a+h0) (f a))))/h0``.
Replace ``(RiemannInt H13)-(RiemannInt (RiemannInt_P14 a (a+h0) (f a)))`` with (RiemannInt (RiemannInt_P10 ``-1`` H13 (RiemannInt_P14  a ``a+h0`` (f a)))).
Unfold Rdiv; Rewrite Rabsolu_mult; Apply Rle_lt_trans with ``(RiemannInt (RiemannInt_P16 (RiemannInt_P10 (-1) H13 (RiemannInt_P14 a (a+h0) (f a)))))*(Rabsolu (/h0))``.
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu (/h0))``); Apply Rle_monotony.
Apply Rabsolu_pos.
Apply (RiemannInt_P17 (RiemannInt_P10 ``-1`` H13 (RiemannInt_P14 a ``a+h0`` (f a))) (RiemannInt_P16 (RiemannInt_P10 ``-1`` H13 (RiemannInt_P14 a ``a+h0`` (f a))))); Left; Assumption.
Apply Rle_lt_trans with ``(RiemannInt (RiemannInt_P14 a (a+h0) (eps/2)))*(Rabsolu (/h0))``.
Do 2 Rewrite <- (Rmult_sym ``(Rabsolu (/h0))``); Apply Rle_monotony.
Apply Rabsolu_pos.
Apply RiemannInt_P19.
Left; Assumption.
Intros; Replace ``(f x2)+ -1*(fct_cte (f a) x2)`` with ``(f x2)-(f a)``.
Unfold fct_cte; Case (Req_EM a x2); Intro.
Rewrite H15; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Left; Assumption.
Elim H8; Intros; Left; Apply H17; Repeat Split.
Assumption.
Rewrite Rabsolu_right.
Apply Rlt_anti_compatibility with a; Replace ``a+(x2-a)`` with x2; [Idtac | Ring].
Apply Rlt_le_trans with ``a+h0``.
Elim H14; Intros; Assumption.
Apply Rle_compatibility; Left; Apply Rle_lt_trans with (Rabsolu h0).
Apply Rle_Rabsolu.
Apply Rlt_le_trans with del; [Assumption | Unfold del; Apply Rle_trans with (Rmin x1 ``b-a``); [Apply Rmin_r | Apply Rmin_l]].
Apply Rle_sym1; Left; Apply Rlt_Rminus; Elim H14; Intros; Assumption.
Unfold fct_cte; Ring.
Rewrite RiemannInt_P15.
Rewrite Rmult_assoc; Replace ``((a+h0)-a)*(Rabsolu (/h0))`` with R1.
Rewrite Rmult_1r; Unfold Rdiv; Apply Rlt_monotony_contra with ``2``; [Sup0 | Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [Rewrite Rmult_1l; Pattern 1 eps; Rewrite <- Rplus_Or; Rewrite double; Apply Rlt_compatibility; Assumption | DiscrR]].
Rewrite Rabsolu_right.
Rewrite Rplus_sym; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or; Rewrite <- Rinv_r_sym; [ Reflexivity | Assumption ].
Apply Rle_sym1; Left; Apply Rlt_Rinv; Assert H14 := (Rle_sym2 ? ? r); Elim H14; Intro.
Assumption.
Elim H10; Symmetry; Assumption.
Rewrite (RiemannInt_P13 H13 (RiemannInt_P14 a ``a+h0`` (f a)) (RiemannInt_P10 ``-1`` H13 (RiemannInt_P14 a ``a+h0`` (f a)))); Ring.
Unfold Rdiv Rminus; Rewrite Rmult_Rplus_distrl; Ring.
Rewrite RiemannInt_P15.
Rewrite Rplus_sym; Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or; Unfold Rdiv; Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym; [ Ring | Assumption ].
Cut ``a<=a+h0``.
Cut ``a+h0<=b``.
Intros; Unfold primitive; Case (total_order_Rle a ``a+h0``); Case (total_order_Rle ``a+h0`` b); Case (total_order_Rle a a); Case (total_order_Rle a b); Intros; Try (Elim n; Right; Reflexivity) Orelse (Elim n; Left; Assumption).
Rewrite RiemannInt_P9; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply RiemannInt_P5.
Elim n; Assumption.
Elim n; Assumption.
2:Left; Assumption.
Apply Rle_anti_compatibility with ``-a``; Replace ``-a+(a+h0)`` with h0; [Idtac | Ring].
Rewrite Rplus_sym; Apply Rle_trans with del; [Apply Rle_trans with (Rabsolu h0); [Apply Rle_Rabsolu | Left; Assumption] | Unfold del; Apply Rle_trans with (Rmin x1 ``b-a``); Apply Rmin_r].
(*****)
Assert H1 : x==a.
Rewrite <- H0 in H; Elim H; Intros; Apply Rle_antisym; Assumption.
Pose f_a := [x:R]``(f a)*(x-a)``.
Assert H2 : (derivable_pt_lim f_a a (f a)).
Unfold f_a; Change (derivable_pt_lim (mult_fct (fct_cte (f a)) (minus_fct id (fct_cte a))) a (f a)); Pattern 2 (f a); Replace (f a) with ``0*((minus_fct id (fct_cte a)) a)+((fct_cte (f a)) a)*1``.
Apply derivable_pt_lim_mult.
Apply derivable_pt_lim_const.
Replace R1 with ``1-0``; [Idtac | Ring].
Apply derivable_pt_lim_minus.
Apply derivable_pt_lim_id.
Apply derivable_pt_lim_const.
Unfold fct_cte; Ring.
Pose f_b := [x:R]``(f b)*(x-b)+(RiemannInt (FTC_P1 h C0 b h (FTC_P2 b)))``.
Assert H3 : (derivable_pt_lim f_b b (f b)).
Unfold f_b; Pattern 2 (f b); Replace (f b) with ``(f b)+0``.
Change (derivable_pt_lim (plus_fct (mult_fct (fct_cte (f b)) (minus_fct id (fct_cte b))) (fct_cte (RiemannInt (FTC_P1 h C0 h (FTC_P2 b))))) b ``(f b)+0``). 
Apply derivable_pt_lim_plus.
Pattern 2 (f b); Replace (f b) with ``0*((minus_fct id (fct_cte b)) b)+((fct_cte (f b)) b)*1``.
Apply derivable_pt_lim_mult.
Apply derivable_pt_lim_const.
Replace R1 with ``1-0``; [Idtac | Ring].
Apply derivable_pt_lim_minus.
Apply derivable_pt_lim_id.
Apply derivable_pt_lim_const.
Unfold fct_cte; Ring.
Apply derivable_pt_lim_const.
Ring.
Unfold derivable_pt_lim; Intros; Elim (H2 ? H4); Intros; Elim (H3 ? H4); Intros; Pose del := (Rmin x0 x1).
Assert H7 : ``0<del``.
Unfold del; Unfold Rmin; Case (total_order_Rle x0 x1); Intro.
Apply (cond_pos x0).
Apply (cond_pos x1).
Split with (mkposreal ? H7); Intros; Case (case_Rabsolu h0); Intro.
Assert H10 : ``a+h0<a``.
Pattern 2 a; Rewrite <- Rplus_Or; Apply Rlt_compatibility; Assumption.
Rewrite H1; Unfold primitive; Case (total_order_Rle a ``a+h0``); Case (total_order_Rle ``a+h0`` b); Case (total_order_Rle a a); Case (total_order_Rle a b); Intros;  Try (Elim n; Right; Assumption Orelse Reflexivity).
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r3 H10)).
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r2 H10)).
Rewrite RiemannInt_P9; Replace R0 with (f_a a).
Replace ``(f a)*(a+h0-a)`` with (f_a ``a+h0``).
Apply H5; Try Assumption.
Apply Rlt_le_trans with del; Try Assumption.
Unfold del; Apply Rmin_l.
Unfold f_a; Ring.
Unfold f_a; Ring.
Elim n; Rewrite <- H0; Left; Assumption.
Assert H10 : ``a<a+h0``.
Pattern 1 a; Rewrite <- Rplus_Or; Apply Rlt_compatibility.
Assert H10 := (Rle_sym2 ? ? r); Elim H10; Intro.
Assumption.
Elim H8; Symmetry; Assumption.
Rewrite H0 in H1; Rewrite H1; Unfold primitive; Case (total_order_Rle a ``b+h0``); Case (total_order_Rle ``b+h0`` b); Case (total_order_Rle a b); Case (total_order_Rle b b); Intros;  Try (Elim n; Right; Assumption Orelse Reflexivity).
Rewrite H0 in H10; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r2 H10)).
Repeat Rewrite RiemannInt_P9.
Replace (RiemannInt (FTC_P1 h C0 r1 r0)) with (f_b b).
Fold (f_b ``b+h0``).
Apply H6; Try Assumption.
Apply Rlt_le_trans with del; Try Assumption.
Unfold del; Apply Rmin_r.
Unfold f_b; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rmult_Or; Rewrite Rplus_Ol; Apply RiemannInt_P5.
Elim n; Rewrite <- H0; Left; Assumption.
Elim n0; Rewrite <- H0; Left; Assumption.
Qed.

Lemma RiemannInt_P29 : (f:R->R;a,b;h:``a<=b``;C0:((x:R)``a<=x<=b``->(continuity_pt f x))) (antiderivative f (primitive h (FTC_P1 h C0)) a b).
Intro f; Intros; Unfold antiderivative; Split; Try Assumption; Intros; Assert H0 := (RiemannInt_P28 h C0 H); Assert H1 : (derivable_pt (primitive h (FTC_P1 h C0)) x); [Unfold derivable_pt; Split with (f x); Apply H0 | Split with H1; Symmetry; Apply derive_pt_eq_0; Apply H0].
Qed.

Lemma RiemannInt_P30 : (f:R->R;a,b:R) ``a<=b`` -> ((x:R)``a<=x<=b``->(continuity_pt f x)) -> (sigTT ? [g:R->R](antiderivative f g a b)).
Intros; Split with (primitive H (FTC_P1 H H0)); Apply RiemannInt_P29.
Qed.

Record C1_fun : Type := mkC1 {
c1 :> R->R;
diff0 : (derivable c1);
cont1 : (continuity (derive c1 diff0)) }.

Lemma RiemannInt_P31 : (f:C1_fun;a,b:R) ``a<=b`` -> (antiderivative (derive f (diff0 f)) f a b).
Intro f; Intros; Unfold antiderivative; Split; Try Assumption; Intros; Split with (diff0 f x); Reflexivity.
Qed.

Lemma RiemannInt_P32 : (f:C1_fun;a,b:R) (Riemann_integrable (derive f (diff0 f)) a b).
Intro f; Intros; Case (total_order_Rle a b); Intro; [Apply continuity_implies_RiemannInt; Try Assumption; Intros; Apply (cont1 f) | Assert H : ``b<=a``; [Auto with real | Apply RiemannInt_P1; Apply continuity_implies_RiemannInt; Try Assumption; Intros; Apply (cont1 f)]].
Qed.

Lemma RiemannInt_P33 : (f:C1_fun;a,b:R;pr:(Riemann_integrable (derive f (diff0 f)) a b)) ``a<=b`` -> (RiemannInt pr)==``(f b)-(f a)``.
Intro f; Intros; Assert H0 : (x:R)``a<=x<=b``->(continuity_pt (derive f (diff0 f)) x).
Intros; Apply (cont1 f).
Rewrite (RiemannInt_P20 H (FTC_P1 H H0) pr); Assert H1 := (RiemannInt_P29 H H0); Assert H2 := (RiemannInt_P31 f H); Elim (antiderivative_Ucte (derive f (diff0 f)) ? ? ? ? H1 H2); Intros C H3; Repeat Rewrite H3; [Ring | Split; [Right; Reflexivity | Assumption] | Split; [Assumption | Right; Reflexivity]].
Qed.

Lemma FTC_Riemann : (f:C1_fun;a,b:R;pr:(Riemann_integrable (derive f (diff0 f)) a b)) (RiemannInt pr)==``(f b)-(f a)``.
Intro f; Intros; Case (total_order_Rle a b); Intro; [Apply RiemannInt_P33; Assumption | Assert H : ``b<=a``; [Auto with real | Assert H0 := (RiemannInt_P1 pr); Rewrite (RiemannInt_P8 pr H0); Rewrite (RiemannInt_P33 H0 H); Ring]].
Qed.

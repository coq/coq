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
Require SeqSeries.
Require Rtrigo.
Require Ranalysis1.
Require Ranalysis3.
Require Exp_prop.
V7only [Import R_scope.]. Open Local Scope R_scope.

(**********)
Lemma derivable_pt_inv : (f:R->R;x:R) ``(f x)<>0`` -> (derivable_pt f x) -> (derivable_pt (inv_fct f) x).
Intros; Cut (derivable_pt (div_fct (fct_cte R1) f) x) -> (derivable_pt (inv_fct f) x).
Intro; Apply X0.
Apply derivable_pt_div.
Apply derivable_pt_const.
Assumption.
Assumption.
Unfold div_fct inv_fct fct_cte; Intro; Elim X0; Intros; Unfold derivable_pt; Apply Specif.existT with x0; Unfold derivable_pt_abs; Unfold derivable_pt_lim; Unfold derivable_pt_abs in p; Unfold derivable_pt_lim in p; Intros; Elim (p eps H0); Intros; Exists x1; Intros; Unfold Rdiv in H1; Unfold Rdiv; Rewrite <- (Rmult_1l ``/(f x)``); Rewrite <- (Rmult_1l ``/(f (x+h))``).
Apply H1; Assumption.
Qed.

(**********)
Lemma pr_nu_var : (f,g:R->R;x:R;pr1:(derivable_pt f x);pr2:(derivable_pt g x)) f==g -> (derive_pt f x pr1) == (derive_pt g x pr2).
Unfold derivable_pt derive_pt; Intros.
Elim pr1; Intros.
Elim pr2; Intros.
Simpl.
Rewrite H in p.
Apply unicite_limite with g x; Assumption.
Qed.

(**********)
Lemma pr_nu_var2 : (f,g:R->R;x:R;pr1:(derivable_pt f x);pr2:(derivable_pt g x)) ((h:R)(f h)==(g h)) -> (derive_pt f x pr1) == (derive_pt g x pr2).
Unfold derivable_pt derive_pt; Intros.
Elim pr1; Intros.
Elim pr2; Intros.
Simpl.
Assert H0 := (unicite_step2 ? ? ? p). 
Assert H1 := (unicite_step2 ? ? ? p0). 
Cut (limit1_in [h:R]``((f (x+h))-(f x))/h`` [h:R]``h <> 0`` x1 ``0``).
Intro; Assert H3 := (unicite_step1 ? ? ? ? H0 H2). 
Assumption.
Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Unfold limit1_in in H1; Unfold limit_in in H1; Unfold dist in H1; Simpl in H1; Unfold R_dist in H1.
Intros; Elim (H1 eps H2); Intros.
Elim H3; Intros.
Exists x2.
Split.
Assumption.
Intros; Do 2 Rewrite H; Apply H5; Assumption.
Qed.

(**********)
Lemma derivable_inv : (f:R->R) ((x:R)``(f x)<>0``)->(derivable f)->(derivable (inv_fct f)).
Intros.
Unfold derivable; Intro.
Apply derivable_pt_inv.
Apply (H x).
Apply (X x).
Qed.

Lemma derive_pt_inv : (f:R->R;x:R;pr:(derivable_pt f x);na:``(f x)<>0``) (derive_pt (inv_fct f) x (derivable_pt_inv f x na pr)) == ``-(derive_pt f x pr)/(Rsqr (f x))``.
Intros; Replace (derive_pt (inv_fct f) x (derivable_pt_inv f x na pr)) with (derive_pt (div_fct (fct_cte R1) f) x (derivable_pt_div (fct_cte R1) f x (derivable_pt_const R1 x) pr na)).
Rewrite derive_pt_div; Rewrite derive_pt_const; Unfold fct_cte; Rewrite Rmult_Ol; Rewrite Rmult_1r; Unfold Rminus; Rewrite Rplus_Ol; Reflexivity.
Apply pr_nu_var2.
Intro; Unfold div_fct fct_cte inv_fct.
Unfold Rdiv; Ring.
Qed.

(* Rabsolu *)
Lemma Rabsolu_derive_1 : (x:R) ``0<x`` -> (derivable_pt_lim Rabsolu x ``1``).
Intros.
Unfold derivable_pt_lim; Intros.
Exists (mkposreal x H); Intros.
Rewrite (Rabsolu_right x).
Rewrite (Rabsolu_right ``x+h``).
Rewrite Rplus_sym.
Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_r.
Rewrite Rplus_Or; Unfold Rdiv; Rewrite <- Rinv_r_sym.
Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply H0.
Apply H1.
Apply Rle_sym1.
Case (case_Rabsolu h); Intro.
Rewrite (Rabsolu_left h r) in H2.
Left; Rewrite Rplus_sym; Apply Rlt_anti_compatibility with ``-h``; Rewrite Rplus_Or; Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Apply H2.
Apply ge0_plus_ge0_is_ge0.
Left; Apply H.
Apply Rle_sym2; Apply r.
Left; Apply H.
Qed.

Lemma Rabsolu_derive_2 : (x:R) ``x<0`` -> (derivable_pt_lim Rabsolu x ``-1``).
Intros.
Unfold derivable_pt_lim; Intros.
Cut ``0< -x``.
Intro; Exists (mkposreal ``-x`` H1); Intros.
Rewrite (Rabsolu_left x).
Rewrite (Rabsolu_left ``x+h``).
Rewrite Rplus_sym.
Rewrite Ropp_distr1.
Unfold Rminus; Rewrite Ropp_Ropp; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l.
Rewrite Rplus_Or; Unfold Rdiv.
Rewrite Ropp_mul1.
Rewrite <- Rinv_r_sym.
Rewrite Ropp_Ropp; Rewrite Rplus_Ropp_l; Rewrite Rabsolu_R0; Apply H0.
Apply H2.
Case (case_Rabsolu h); Intro.
Apply Ropp_Rlt.
Rewrite Ropp_O; Rewrite Ropp_distr1; Apply gt0_plus_gt0_is_gt0.
Apply H1.
Apply Rgt_RO_Ropp; Apply r.
Rewrite (Rabsolu_right h r) in H3.
Apply Rlt_anti_compatibility with ``-x``; Rewrite Rplus_Or; Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Apply H3.
Apply H.
Apply Rgt_RO_Ropp; Apply H.
Qed.

(* Rabsolu is derivable for all x <> 0 *)
Lemma derivable_pt_Rabsolu : (x:R) ``x<>0`` -> (derivable_pt Rabsolu x).
Intros.
Case (total_order_T x R0); Intro.
Elim s; Intro.
Unfold derivable_pt; Apply Specif.existT with ``-1``.
Apply (Rabsolu_derive_2 x a).
Elim H; Exact b.
Unfold derivable_pt; Apply Specif.existT with ``1``.
Apply (Rabsolu_derive_1 x r).
Qed.

(* Rabsolu is continuous for all x *)
Lemma continuity_Rabsolu : (continuity Rabsolu).
Unfold continuity; Intro.
Case (Req_EM x R0); Intro.
Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros; Exists eps; Split.
Apply H0.
Intros; Rewrite H; Rewrite Rabsolu_R0; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu; Elim H1; Intros; Rewrite H in H3; Unfold Rminus in H3; Rewrite Ropp_O in H3; Rewrite Rplus_Or in H3; Apply H3.
Apply derivable_continuous_pt; Apply (derivable_pt_Rabsolu x H).
Qed.

(* Finite sums : Sum a_k x^k *)
Lemma continuity_finite_sum : (An:nat->R;N:nat) (continuity [y:R](sum_f_R0 [k:nat]``(An k)*(pow y k)`` N)).
Intros; Unfold continuity; Intro.
Induction N.
Simpl.
Apply continuity_pt_const.
Unfold constant; Intros; Reflexivity.
Replace [y:R](sum_f_R0 [k:nat]``(An k)*(pow y k)`` (S N)) with (plus_fct [y:R](sum_f_R0 [k:nat]``(An k)*(pow y k)`` N) [y:R]``(An (S N))*(pow y (S N))``).
Apply continuity_pt_plus.
Apply HrecN.
Replace [y:R]``(An (S N))*(pow y (S N))`` with (mult_real_fct (An (S N)) [y:R](pow y (S N))).
Apply continuity_pt_scal.
Apply derivable_continuous_pt.
Apply derivable_pt_pow.
Reflexivity.
Reflexivity.
Qed.

Lemma derivable_pt_lim_fs : (An:nat->R;x:R;N:nat) (lt O N) -> (derivable_pt_lim [y:R](sum_f_R0 [k:nat]``(An k)*(pow y k)`` N) x (sum_f_R0 [k:nat]``(INR (S k))*(An (S k))*(pow x k)`` (pred N))).
Intros; Induction N.
Elim (lt_n_n ? H).
Cut N=O\/(lt O N).
Intro; Elim H0; Intro.
Rewrite H1.
Simpl.
Replace [y:R]``(An O)*1+(An (S O))*(y*1)`` with (plus_fct (fct_cte ``(An O)*1``) (mult_real_fct ``(An (S O))`` (mult_fct id (fct_cte R1)))).
Replace ``1*(An (S O))*1`` with ``0+(An (S O))*(1*(fct_cte R1 x)+(id x)*0)``.
Apply derivable_pt_lim_plus.
Apply derivable_pt_lim_const.
Apply derivable_pt_lim_scal.
Apply derivable_pt_lim_mult.
Apply derivable_pt_lim_id.
Apply derivable_pt_lim_const.
Unfold fct_cte id; Ring.
Reflexivity.
Replace [y:R](sum_f_R0 [k:nat]``(An k)*(pow y k)`` (S N)) with (plus_fct [y:R](sum_f_R0 [k:nat]``(An k)*(pow y k)`` N) [y:R]``(An (S N))*(pow y (S N))``).
Replace (sum_f_R0 [k:nat]``(INR (S k))*(An (S k))*(pow x k)`` (pred (S N))) with (Rplus (sum_f_R0 [k:nat]``(INR (S k))*(An (S k))*(pow x k)`` (pred N)) ``(An (S N))*((INR (S (pred (S N))))*(pow x (pred (S N))))``).
Apply derivable_pt_lim_plus.
Apply HrecN.
Assumption.
Replace [y:R]``(An (S N))*(pow y (S N))`` with (mult_real_fct (An (S N)) [y:R](pow y (S N))).
Apply derivable_pt_lim_scal.
Replace (pred (S N)) with N; [Idtac | Reflexivity].
Pattern 3 N; Replace N with (pred (S N)).
Apply derivable_pt_lim_pow.
Reflexivity.
Reflexivity.
Cut (pred (S N)) = (S (pred N)).
Intro; Rewrite H2.
Rewrite tech5.
Apply Rplus_plus_r.
Rewrite <- H2.
Replace (pred (S N)) with N; [Idtac | Reflexivity].
Ring.
Simpl.
Apply S_pred with O; Assumption.
Unfold plus_fct.
Simpl; Reflexivity.
Inversion H.
Left; Reflexivity.
Right; Apply lt_le_trans with (1); [Apply lt_O_Sn | Assumption].
Qed.

Lemma derivable_pt_lim_finite_sum : (An:(nat->R); x:R; N:nat) (derivable_pt_lim [y:R](sum_f_R0 [k:nat]``(An k)*(pow y k)`` N) x (Cases N of O => R0 | _ => (sum_f_R0 [k:nat]``(INR (S k))*(An (S k))*(pow x k)`` (pred N)) end)).
Intros.
Induction N.
Simpl.
Rewrite Rmult_1r.
Replace [_:R]``(An O)`` with (fct_cte (An O)); [Apply derivable_pt_lim_const | Reflexivity].
Apply derivable_pt_lim_fs; Apply lt_O_Sn.
Qed.

Lemma derivable_pt_finite_sum : (An:nat->R;N:nat;x:R) (derivable_pt [y:R](sum_f_R0 [k:nat]``(An k)*(pow y k)`` N) x).
Intros.
Unfold derivable_pt.
Assert H := (derivable_pt_lim_finite_sum An x N).
Induction N.
Apply Specif.existT with R0; Apply H.
Apply Specif.existT with (sum_f_R0 [k:nat]``(INR (S k))*(An (S k))*(pow x k)`` (pred (S N))); Apply H.
Qed.

Lemma derivable_finite_sum : (An:nat->R;N:nat) (derivable [y:R](sum_f_R0 [k:nat]``(An k)*(pow y k)`` N)).
Intros; Unfold derivable; Intro; Apply derivable_pt_finite_sum.
Qed.

(* Regularity of hyperbolic functions *)
Lemma derivable_pt_lim_cosh : (x:R) (derivable_pt_lim cosh x ``(sinh x)``).
Intro.
Unfold cosh sinh; Unfold Rdiv.
Replace [x0:R]``((exp x0)+(exp ( -x0)))*/2`` with (mult_fct (plus_fct exp (comp exp (opp_fct id))) (fct_cte ``/2``)); [Idtac | Reflexivity].
Replace ``((exp x)-(exp ( -x)))*/2`` with ``((exp x)+((exp (-x))*-1))*((fct_cte (Rinv 2)) x)+((plus_fct exp (comp exp (opp_fct id))) x)*0``. 
Apply derivable_pt_lim_mult.
Apply derivable_pt_lim_plus.
Apply derivable_pt_lim_exp.
Apply derivable_pt_lim_comp.
Apply derivable_pt_lim_opp.
Apply derivable_pt_lim_id.
Apply derivable_pt_lim_exp.
Apply derivable_pt_lim_const.
Unfold plus_fct mult_real_fct comp opp_fct id fct_cte; Ring.
Qed.

Lemma derivable_pt_lim_sinh : (x:R) (derivable_pt_lim sinh x ``(cosh x)``).
Intro.
Unfold cosh sinh; Unfold Rdiv.
Replace [x0:R]``((exp x0)-(exp ( -x0)))*/2`` with (mult_fct (minus_fct exp (comp exp (opp_fct id))) (fct_cte ``/2``)); [Idtac | Reflexivity].
Replace ``((exp x)+(exp ( -x)))*/2`` with ``((exp x)-((exp (-x))*-1))*((fct_cte (Rinv 2)) x)+((minus_fct exp (comp exp (opp_fct id))) x)*0``. 
Apply derivable_pt_lim_mult.
Apply derivable_pt_lim_minus.
Apply derivable_pt_lim_exp.
Apply derivable_pt_lim_comp.
Apply derivable_pt_lim_opp.
Apply derivable_pt_lim_id.
Apply derivable_pt_lim_exp.
Apply derivable_pt_lim_const.
Unfold plus_fct mult_real_fct comp opp_fct id fct_cte; Ring.
Qed.

Lemma derivable_pt_exp : (x:R) (derivable_pt exp x).
Intro.
Unfold derivable_pt.
Apply Specif.existT with (exp x).
Apply derivable_pt_lim_exp.
Qed.

Lemma derivable_pt_cosh : (x:R) (derivable_pt cosh x).
Intro.
Unfold derivable_pt.
Apply Specif.existT with (sinh x).
Apply derivable_pt_lim_cosh.
Qed.

Lemma derivable_pt_sinh : (x:R) (derivable_pt sinh x).
Intro.
Unfold derivable_pt.
Apply Specif.existT with (cosh x).
Apply derivable_pt_lim_sinh.
Qed.

Lemma derivable_exp : (derivable exp).
Unfold derivable; Apply derivable_pt_exp.
Qed.

Lemma derivable_cosh : (derivable cosh).
Unfold derivable; Apply derivable_pt_cosh.
Qed.

Lemma derivable_sinh : (derivable sinh).
Unfold derivable; Apply derivable_pt_sinh.
Qed.

Lemma derive_pt_exp : (x:R) (derive_pt exp x (derivable_pt_exp x))==(exp x).
Intro; Apply derive_pt_eq_0.
Apply derivable_pt_lim_exp.
Qed.

Lemma derive_pt_cosh : (x:R) (derive_pt cosh x (derivable_pt_cosh x))==(sinh x).
Intro; Apply derive_pt_eq_0.
Apply derivable_pt_lim_cosh.
Qed.

Lemma derive_pt_sinh : (x:R) (derive_pt sinh x (derivable_pt_sinh x))==(cosh x).
Intro; Apply derive_pt_eq_0.
Apply derivable_pt_lim_sinh.
Qed.

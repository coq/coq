(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Rbase.
Require Rbasic_fun.
Require R_sqr.
Require Rlimit.
Require Rderiv.
Require DiscrR.
Require Rtrigo.
Require Ranalysis1.
Require R_sqrt.
Require Ranalysis2.
Require Ranalysis3.
Require Export Sqrt_reg.

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

(* Pow *)
Lemma derivable_pt_lim_pow_pos : (x:R;n:nat) (lt O n) -> (derivable_pt_lim [y:R](pow y n) x ``(INR n)*(pow x (pred n))``).
Intros.
Induction n.
Elim (lt_n_n ? H).
Cut n=O\/(lt O n).
Intro; Elim H0; Intro.
Rewrite H1; Simpl.
Replace [y:R]``y*1`` with (mult_fct id (fct_cte R1)).
Replace ``1*1`` with ``1*(fct_cte R1 x)+(id x)*0``.
Apply derivable_pt_lim_mult.
Apply derivable_pt_lim_id.
Apply derivable_pt_lim_const.
Unfold fct_cte id; Ring.
Reflexivity.
Replace [y:R](pow y (S n)) with [y:R]``y*(pow y n)``.
Replace (pred (S n)) with n; [Idtac | Reflexivity].
Replace [y:R]``y*(pow y n)`` with (mult_fct id [y:R](pow y n)).
Pose f := [y:R](pow y n).
Replace ``(INR (S n))*(pow x n)`` with (Rplus (Rmult R1 (f x)) (Rmult (id x) (Rmult (INR n) (pow x (pred n))))).
Apply derivable_pt_lim_mult.
Apply derivable_pt_lim_id.
Unfold f; Apply Hrecn; Assumption.
Unfold f.
Pattern 1 5 n; Replace n with (S (pred n)).
Unfold id; Rewrite S_INR; Simpl.
Ring.
Symmetry; Apply S_pred with O; Assumption.
Unfold mult_fct id; Reflexivity.
Reflexivity.
Inversion H.
Left; Reflexivity.
Right.
Apply lt_le_trans with (1).
Apply lt_O_Sn.
Assumption.
Qed.

Lemma derivable_pt_lim_pow : (x:R; n:nat) (derivable_pt_lim [y:R](pow y n) x ``(INR n)*(pow x (pred n))``).
Intros.
Induction n.
Simpl.
Rewrite Rmult_Ol.
Replace [_:R]``1`` with (fct_cte R1); [Apply derivable_pt_lim_const | Reflexivity].
Apply derivable_pt_lim_pow_pos.
Apply lt_O_Sn.
Qed.

Lemma derivable_pt_pow : (n:nat;x:R) (derivable_pt [y:R](pow y n) x).
Intros; Unfold derivable_pt.
Apply Specif.existT with ``(INR n)*(pow x (pred n))``.
Apply derivable_pt_lim_pow.
Qed.

Lemma derivable_pow : (n:nat) (derivable [y:R](pow y n)).
Intro; Unfold derivable; Intro; Apply derivable_pt_pow.
Qed.

Lemma derive_pt_pow : (n:nat;x:R) (derive_pt [y:R](pow y n) x (derivable_pt_pow n x))==``(INR n)*(pow x (pred n))``.
Intros; Apply derive_pt_eq_0.
Apply derivable_pt_lim_pow.
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
Axiom derivable_pt_lim_exp : (x:R) (derivable_pt_lim exp x (exp x)).   

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


Definition pow_fct [n:nat] : R->R := [y:R](pow y n).

(**********)
Tactic Definition IntroHypG trm :=
Match trm With
|[(plus_fct ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable ?)] -> IntroHypG ?1; IntroHypG ?2
 |[|-(continuity ?)] -> IntroHypG ?1; IntroHypG ?2
 | _ -> Idtac)
|[(minus_fct ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable ?)] -> IntroHypG ?1; IntroHypG ?2
 |[|-(continuity ?)] -> IntroHypG ?1; IntroHypG ?2
 | _ -> Idtac)
|[(mult_fct ?1 ?2)] ->
 (Match Context With
 |[|-(derivable ?)] -> IntroHypG ?1; IntroHypG ?2
 |[|-(continuity ?)] -> IntroHypG ?1; IntroHypG ?2
 | _ -> Idtac)
|[(div_fct ?1 ?2)] -> Let aux = ?2 In
 (Match Context With
 |[_:(x0:R)``(aux x0)<>0``|-(derivable ?)] -> IntroHypG ?1; IntroHypG ?2
 |[_:(x0:R)``(aux x0)<>0``|-(continuity ?)] -> IntroHypG ?1; IntroHypG ?2
 |[|-(derivable ?)] -> Cut ((x0:R)``(aux x0)<>0``); [Intro; IntroHypG ?1; IntroHypG ?2 | Try Assumption]
 |[|-(continuity ?)] -> Cut ((x0:R)``(aux x0)<>0``); [Intro; IntroHypG ?1; IntroHypG ?2 | Try Assumption]
 | _ -> Idtac)
|[(comp ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable ?)] -> IntroHypG ?1; IntroHypG ?2
 |[|-(continuity ?)] -> IntroHypG ?1; IntroHypG ?2
 | _ -> Idtac)
|[(opp_fct ?1)] -> 
 (Match Context With
 |[|-(derivable ?)] -> IntroHypG ?1
 |[|-(continuity ?)] -> IntroHypG ?1
 | _ -> Idtac)
|[(inv_fct ?1)] -> Let aux = ?1 In
 (Match Context With
 |[_:(x0:R)``(aux x0)<>0``|-(derivable ?)] -> IntroHypG ?1
 |[_:(x0:R)``(aux x0)<>0``|-(continuity ?)] -> IntroHypG ?1
 |[|-(derivable ?)] -> Cut ((x0:R)``(aux x0)<>0``); [Intro; IntroHypG ?1 | Try Assumption]
 |[|-(continuity ?)] -> Cut ((x0:R)``(aux x0)<>0``); [Intro; IntroHypG ?1| Try Assumption]
 | _ -> Idtac)
|[cos] -> Idtac
|[sin] -> Idtac
|[cosh] -> Idtac
|[sinh] -> Idtac
|[exp] -> Idtac
|[Rsqr] -> Idtac
|[sqrt] -> Idtac
|[id] -> Idtac
|[(fct_cte ?)] -> Idtac
|[(pow_fct ?)] -> Idtac
|[Rabsolu] -> Idtac
|[?1] -> Let p = ?1 In
 (Match Context With
 |[_:(derivable p)|- ?] -> Idtac
 |[|-(derivable p)] -> Idtac
 |[|-(derivable ?)] -> Cut True -> (derivable p); [Intro HYPPD; Cut (derivable p); [Intro; Clear HYPPD | Apply HYPPD; Clear HYPPD; Trivial] | Idtac]
 | [_:(continuity p)|- ?] -> Idtac
 |[|-(continuity p)] -> Idtac
 |[|-(continuity ?)] -> Cut True -> (continuity p); [Intro HYPPD; Cut (continuity p); [Intro; Clear HYPPD | Apply HYPPD; Clear HYPPD; Trivial] | Idtac]
 | _ -> Idtac).

(**********)
Tactic Definition IntroHypL trm pt :=
Match trm With
|[(plus_fct ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(continuity_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 | _ -> Idtac)
|[(minus_fct ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(continuity_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 | _ -> Idtac)
|[(mult_fct ?1 ?2)] ->
 (Match Context With
 |[|-(derivable_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(continuity_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 | _ -> Idtac)
|[(div_fct ?1 ?2)] -> Let aux = ?2 In
 (Match Context With
 |[_:``(aux pt)<>0``|-(derivable_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[_:``(aux pt)<>0``|-(continuity_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[_:``(aux pt)<>0``|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[id:(x0:R)``(aux x0)<>0``|-(derivable_pt ? ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt; IntroHypL ?2 pt
 |[id:(x0:R)``(aux x0)<>0``|-(continuity_pt ? ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt; IntroHypL ?2 pt
 |[id:(x0:R)``(aux x0)<>0``|-(eqT ? (derive_pt ? ? ?) ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(derivable_pt ? ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt; IntroHypL ?2 pt | Try Assumption]
 |[|-(continuity_pt ? ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt; IntroHypL ?2 pt | Try Assumption]
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt; IntroHypL ?2 pt | Try Assumption]
 | _ -> Idtac)
|[(comp ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable_pt ? ?)] -> Let pt_f1 = (Eval Cbv Beta in (?2 pt)) In IntroHypL ?1 pt_f1; IntroHypL ?2 pt
 |[|-(continuity_pt ? ?)] -> Let pt_f1 = (Eval Cbv Beta in (?2 pt)) In IntroHypL ?1 pt_f1; IntroHypL ?2 pt
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> Let pt_f1 = (Eval Cbv Beta in (?2 pt)) In IntroHypL ?1 pt_f1; IntroHypL ?2 pt
 | _ -> Idtac)
|[(opp_fct ?1)] -> 
 (Match Context With
 |[|-(derivable_pt ? ?)] -> IntroHypL ?1 pt
 |[|-(continuity_pt ? ?)] -> IntroHypL ?1 pt
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt
 | _ -> Idtac)
|[(inv_fct ?1)] -> Let aux = ?1 In
 (Match Context With
 |[_:``(aux pt)<>0``|-(derivable_pt ? ?)] -> IntroHypL ?1 pt
 |[_:``(aux pt)<>0``|-(continuity_pt ? ?)] -> IntroHypL ?1 pt
 |[_:``(aux pt)<>0``|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt
 |[id:(x0:R)``(aux x0)<>0``|-(derivable_pt ? ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt
 |[id:(x0:R)``(aux x0)<>0``|-(continuity_pt ? ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt
 |[id:(x0:R)``(aux x0)<>0``|-(eqT ? (derive_pt ? ? ?) ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt
 |[|-(derivable_pt ? ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt | Try Assumption]
 |[|-(continuity_pt ? ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt| Try Assumption]
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt | Try Assumption]
 | _ -> Idtac)
|[cos] -> Idtac
|[sin] -> Idtac
|[cosh] -> Idtac
|[sinh] -> Idtac
|[exp] -> Idtac
|[Rsqr] -> Idtac
|[id] -> Idtac
|[(fct_cte ?)] -> Idtac
|[(pow_fct ?)] -> Idtac
|[sqrt] ->
 (Match Context With
 |[|-(derivable_pt ? ?)] -> Cut ``0<pt``; [Intro | Try Assumption]
 |[|-(continuity_pt ? ?)] -> Cut ``0<=pt``; [Intro | Try Assumption]
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> Cut ``0<pt``; [Intro | Try Assumption]
 | _ -> Idtac)
|[Rabsolu] ->
 (Match Context With
 |[|-(derivable_pt ? ?)] -> Cut ``pt<>0``; [Intro | Try Assumption]
 | _ -> Idtac)
|[?1] -> Let p = ?1 In
 (Match Context With
 |[_:(derivable_pt p pt)|- ?] -> Idtac
 |[|-(derivable_pt p pt)] -> Idtac
 |[|-(derivable_pt ? ?)] -> Cut True -> (derivable_pt p pt); [Intro HYPPD; Cut (derivable_pt p pt); [Intro; Clear HYPPD | Apply HYPPD; Clear HYPPD; Trivial] | Idtac]
 |[_:(continuity_pt p pt)|- ?] -> Idtac
 |[|-(continuity_pt p pt)] -> Idtac
 |[|-(continuity_pt ? ?)] -> Cut True -> (continuity_pt p pt); [Intro HYPPD; Cut (continuity_pt p pt); [Intro; Clear HYPPD | Apply HYPPD; Clear HYPPD; Trivial] | Idtac]
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> Cut True -> (derivable_pt p pt); [Intro HYPPD; Cut (derivable_pt p pt); [Intro; Clear HYPPD | Apply HYPPD; Clear HYPPD; Trivial] | Idtac]
 | _ -> Idtac).
 
(**********)
Recursive Tactic Definition IsDiff_pt :=
Match Context With
 (* fonctions de base *)
 [|-(derivable_pt Rsqr ?)] -> Apply derivable_pt_Rsqr
|[|-(derivable_pt id ?1)] -> Apply (derivable_pt_id ?1)
|[|-(derivable_pt (fct_cte ?) ?)] -> Apply derivable_pt_const
|[|-(derivable_pt sin ?)] -> Apply derivable_pt_sin
|[|-(derivable_pt cos ?)] -> Apply derivable_pt_cos
|[|-(derivable_pt sinh ?)] -> Apply derivable_pt_sinh
|[|-(derivable_pt cosh ?)] -> Apply derivable_pt_cosh
|[|-(derivable_pt exp ?)] -> Apply derivable_pt_exp
|[|-(derivable_pt (pow_fct ?) ?)] -> Unfold pow_fct; Apply derivable_pt_pow
|[|-(derivable_pt sqrt ?1)] -> Apply (derivable_pt_sqrt ?1); Assumption Orelse Unfold plus_fct minus_fct opp_fct mult_fct div_fct inv_fct comp id fct_cte pow_fct
|[|-(derivable_pt Rabsolu ?1)] -> Apply (derivable_pt_Rabsolu ?1); Assumption Orelse Unfold plus_fct minus_fct opp_fct mult_fct div_fct inv_fct comp id fct_cte pow_fct
 (* regles de differentiabilite *)
 (* PLUS *)
|[|-(derivable_pt (plus_fct ?1 ?2) ?3)] -> Apply (derivable_pt_plus ?1 ?2 ?3); IsDiff_pt
 (* MOINS *)
|[|-(derivable_pt (minus_fct ?1 ?2) ?3)] -> Apply (derivable_pt_minus ?1 ?2 ?3); IsDiff_pt
 (* OPPOSE *)
|[|-(derivable_pt (opp_fct ?1) ?2)] -> Apply (derivable_pt_opp ?1 ?2); IsDiff_pt
 (* MULTIPLICATION PAR UN SCALAIRE *)
|[|-(derivable_pt (mult_real_fct ?1 ?2) ?3)] -> Apply (derivable_pt_scal ?2 ?1 ?3); IsDiff_pt
 (* MULTIPLICATION *)
|[|-(derivable_pt (mult_fct ?1 ?2) ?3)] -> Apply (derivable_pt_mult ?1 ?2 ?3); IsDiff_pt
  (* DIVISION *)
 |[|-(derivable_pt (div_fct ?1 ?2) ?3)] -> Apply (derivable_pt_div ?1 ?2 ?3); [IsDiff_pt | IsDiff_pt | Try Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct comp pow_fct id fct_cte]
  (* INVERSION *)
 |[|-(derivable_pt (inv_fct ?1) ?2)] -> Apply (derivable_pt_inv ?1 ?2); [Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct comp pow_fct id fct_cte | IsDiff_pt]
 (* COMPOSITION *)
|[|-(derivable_pt (comp ?1 ?2) ?3)] -> Apply (derivable_pt_comp ?2 ?1 ?3); IsDiff_pt
|[_:(derivable_pt ?1 ?2)|-(derivable_pt ?1 ?2)] -> Assumption
|[_:(derivable ?1) |- (derivable_pt ?1 ?2)] -> Cut (derivable ?1); [Intro HypDDPT; Apply HypDDPT | Assumption]
|[|-True->(derivable_pt ? ?)] -> Intro HypTruE; Clear HypTruE; IsDiff_pt
| _ -> Try Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct.

(**********)
Recursive Tactic Definition IsDiff_glob :=
Match Context With
 (* fonctions de base *)
  [|-(derivable Rsqr)] -> Apply derivable_Rsqr
 |[|-(derivable id)] -> Apply derivable_id
 |[|-(derivable (fct_cte ?))] -> Apply derivable_const
 |[|-(derivable sin)] -> Apply derivable_sin
 |[|-(derivable cos)] -> Apply derivable_cos
 |[|-(derivable cosh)] -> Apply derivable_cosh
 |[|-(derivable sinh)] -> Apply derivable_sinh
 |[|-(derivable exp)] -> Apply derivable_exp
 |[|-(derivable (pow_fct ?))] -> Unfold pow_fct; Apply derivable_pow
  (* regles de differentiabilite *)
  (* PLUS *)
 |[|-(derivable (plus_fct ?1 ?2))] -> Apply (derivable_plus ?1 ?2); IsDiff_glob
  (* MOINS *)
 |[|-(derivable (minus_fct ?1 ?2))] -> Apply (derivable_minus ?1 ?2); IsDiff_glob
  (* OPPOSE *)
 |[|-(derivable (opp_fct ?1))] -> Apply (derivable_opp ?1); IsDiff_glob
  (* MULTIPLICATION PAR UN SCALAIRE *)
 |[|-(derivable (mult_real_fct ?1 ?2))] -> Apply (derivable_scal ?2 ?1); IsDiff_glob
  (* MULTIPLICATION *)
 |[|-(derivable (mult_fct ?1 ?2))] -> Apply (derivable_mult ?1 ?2); IsDiff_glob
  (* DIVISION *)
 |[|-(derivable (div_fct ?1 ?2))] -> Apply (derivable_div ?1 ?2); [IsDiff_glob | IsDiff_glob | Try Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct]
  (* INVERSION *)
 |[|-(derivable (inv_fct ?1))] -> Apply (derivable_inv ?1); [Try Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct | IsDiff_glob]
  (* COMPOSITION *)
 |[|-(derivable (comp sqrt ?))] -> Unfold derivable; Intro; Try IsDiff_pt
 |[|-(derivable (comp Rabsolu ?))] -> Unfold derivable; Intro; Try IsDiff_pt
 |[|-(derivable (comp ?1 ?2))] -> Apply (derivable_comp ?2 ?1); IsDiff_glob
 |[_:(derivable ?1)|-(derivable ?1)] -> Assumption
 |[|-True->(derivable ?)] -> Intro HypTruE; Clear HypTruE; IsDiff_glob
 | _ -> Try Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct.

(**********)
Recursive Tactic Definition IsCont_pt :=
Match Context With
 (* fonctions de base *)
 [|-(continuity_pt Rsqr ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_Rsqr
|[|-(continuity_pt id ?1)] -> Apply derivable_continuous_pt; Apply (derivable_pt_id ?1)
|[|-(continuity_pt (fct_cte ?) ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_const
|[|-(continuity_pt sin ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_sin
|[|-(continuity_pt cos ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_cos
|[|-(continuity_pt sinh ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_sinh
|[|-(continuity_pt cosh ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_cosh
|[|-(continuity_pt exp ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_exp
|[|-(continuity_pt (pow_fct ?) ?)] -> Unfold pow_fct; Apply derivable_continuous_pt; Apply derivable_pt_pow
|[|-(continuity_pt sqrt ?1)] -> Apply continuity_pt_sqrt; Assumption Orelse Unfold plus_fct minus_fct opp_fct mult_fct div_fct inv_fct comp id fct_cte pow_fct
|[|-(continuity_pt Rabsolu ?1)] -> Apply (continuity_Rabsolu ?1)
 (* regles de differentiabilite *)
 (* PLUS *)
|[|-(continuity_pt (plus_fct ?1 ?2) ?3)] -> Apply (continuity_pt_plus ?1 ?2 ?3); IsCont_pt
 (* MOINS *)
|[|-(continuity_pt (minus_fct ?1 ?2) ?3)] -> Apply (continuity_pt_minus ?1 ?2 ?3); IsCont_pt
 (* OPPOSE *)
|[|-(continuity_pt (opp_fct ?1) ?2)] -> Apply (continuity_pt_opp ?1 ?2); IsCont_pt
 (* MULTIPLICATION PAR UN SCALAIRE *)
|[|-(continuity_pt (mult_real_fct ?1 ?2) ?3)] -> Apply (continuity_pt_scal ?2 ?1 ?3); IsCont_pt
 (* MULTIPLICATION *)
|[|-(continuity_pt (mult_fct ?1 ?2) ?3)] -> Apply (continuity_pt_mult ?1 ?2 ?3); IsCont_pt
  (* DIVISION *)
 |[|-(continuity_pt (div_fct ?1 ?2) ?3)] -> Apply (continuity_pt_div ?1 ?2 ?3); [IsCont_pt | IsCont_pt | Try Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct comp id fct_cte pow_fct]
  (* INVERSION *)
 |[|-(continuity_pt (inv_fct ?1) ?2)] -> Apply (continuity_pt_inv ?1 ?2); [IsCont_pt | Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct comp id fct_cte pow_fct]
 (* COMPOSITION *)
|[|-(continuity_pt (comp ?1 ?2) ?3)] -> Apply (continuity_pt_comp ?2 ?1 ?3); IsCont_pt
|[_:(continuity_pt ?1 ?2)|-(continuity_pt ?1 ?2)] -> Assumption
|[_:(continuity ?1) |- (continuity_pt ?1 ?2)] -> Cut (continuity ?1); [Intro HypDDPT; Apply HypDDPT | Assumption]
|[_:(derivable_pt ?1 ?2)|-(continuity_pt ?1 ?2)] -> Apply derivable_continuous_pt; Assumption
|[_:(derivable ?1)|-(continuity_pt ?1 ?2)] -> Cut (continuity ?1); [Intro HypDDPT; Apply HypDDPT | Apply derivable_continuous; Assumption]
|[|-True->(continuity_pt ? ?)] -> Intro HypTruE; Clear HypTruE; IsCont_pt
| _ -> Try Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct.

(**********)
Recursive Tactic Definition IsCont_glob :=
Match Context With
  (* fonctions de base *)
  [|-(continuity Rsqr)] -> Apply derivable_continuous; Apply derivable_Rsqr
 |[|-(continuity id)] -> Apply derivable_continuous; Apply derivable_id
 |[|-(continuity (fct_cte ?))] -> Apply derivable_continuous; Apply derivable_const
 |[|-(continuity sin)] -> Apply derivable_continuous; Apply derivable_sin
 |[|-(continuity cos)] -> Apply derivable_continuous; Apply derivable_cos
 |[|-(continuity exp)] -> Apply derivable_continuous; Apply derivable_exp
 |[|-(continuity (pow_fct ?))] -> Unfold pow_fct; Apply derivable_continuous; Apply derivable_pow
 |[|-(continuity sinh)] -> Apply derivable_continuous; Apply derivable_sinh
 |[|-(continuity cosh)] -> Apply derivable_continuous; Apply derivable_cosh
 |[|-(continuity Rabsolu)] -> Apply continuity_Rabsolu
 (* regles de continuite *)
 (* PLUS *)
|[|-(continuity (plus_fct ?1 ?2))] -> Apply (continuity_plus ?1 ?2); Try IsCont_glob Orelse Assumption
 (* MOINS *)
|[|-(continuity (minus_fct ?1 ?2))] -> Apply (continuity_minus ?1 ?2); Try IsCont_glob Orelse Assumption
 (* OPPOSE *)
|[|-(continuity (opp_fct ?1))] -> Apply (continuity_opp ?1); Try IsCont_glob Orelse Assumption
 (* INVERSE *)
|[|-(continuity (inv_fct ?1))] -> Apply (continuity_inv ?1); Try IsCont_glob Orelse Assumption
 (* MULTIPLICATION PAR UN SCALAIRE *)
|[|-(continuity (mult_real_fct ?1 ?2))] -> Apply (continuity_scal ?2 ?1); Try IsCont_glob Orelse Assumption
 (* MULTIPLICATION *)
|[|-(continuity (mult_fct ?1 ?2))] -> Apply (continuity_mult ?1 ?2); Try IsCont_glob Orelse Assumption
  (* DIVISION *)
 |[|-(continuity (div_fct ?1 ?2))] -> Apply (continuity_div ?1 ?2); [Try IsCont_glob Orelse Assumption | Try IsCont_glob Orelse Assumption | Try Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte pow_fct]
  (* COMPOSITION *)
 |[|-(continuity (comp sqrt ?))] -> Unfold continuity_pt; Intro; Try IsCont_pt
 |[|-(continuity (comp ?1 ?2))] -> Apply (continuity_comp ?2 ?1); Try IsCont_glob Orelse Assumption
 |[_:(continuity ?1)|-(continuity ?1)] -> Assumption
 |[|-True->(continuity ?)] -> Intro HypTruE; Clear HypTruE; IsCont_glob
 |[_:(derivable ?1)|-(continuity ?1)] -> Apply derivable_continuous; Assumption
 | _ -> Try Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct.

(**********)
Recursive Tactic Definition RewTerm trm :=
Match trm With
| [(Rplus ?1 ?2)] -> Let p1= (RewTerm ?1) And p2 = (RewTerm ?2) In 
  (Match p1 With
   [(fct_cte ?3)] -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(fct_cte (Rplus ?3 ?4))
    | _ -> '(plus_fct p1 p2))
  | _ -> '(plus_fct p1 p2))
| [(Rminus ?1 ?2)] -> Let p1 = (RewTerm ?1) And p2 = (RewTerm ?2) In
  (Match p1 With
   [(fct_cte ?3)] -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(fct_cte (Rminus ?3 ?4))
    | _ -> '(minus_fct p1 p2))
  | _ -> '(minus_fct p1 p2))
| [(Rdiv ?1 ?2)] -> Let p1 = (RewTerm ?1) And p2 = (RewTerm ?2) In
  (Match p1 With
   [(fct_cte ?3)] -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(fct_cte (Rdiv ?3 ?4))
    | _ -> '(div_fct p1 p2))
  | _ -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(mult_fct p1 (fct_cte (Rinv ?4)))
    | _ -> '(div_fct p1 p2)))
| [(Rmult ?1 (Rinv ?2))] -> Let p1 = (RewTerm ?1) And p2 = (RewTerm ?2) In
  (Match p1 With
   [(fct_cte ?3)] -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(fct_cte (Rdiv ?3 ?4))
    | _ -> '(div_fct p1 p2))
  | _ -> 
   (Match p2 With
   | [(fct_cte ?4)] -> '(mult_fct p1 (fct_cte (Rinv ?4)))
   | _ -> '(div_fct p1 p2)))
| [(Rmult ?1 ?2)] -> Let p1 = (RewTerm ?1) And p2 = (RewTerm ?2) In
  (Match p1 With
   [(fct_cte ?3)] -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(fct_cte (Rmult ?3 ?4))
    | _ -> '(mult_fct p1 p2))
  | _ -> '(mult_fct p1 p2))
| [(Ropp ?1)] -> Let p = (RewTerm ?1) In 
  (Match p With
   [(fct_cte ?2)] -> '(fct_cte (Ropp ?2))
   | _ -> '(opp_fct p))
| [(Rinv ?1)] -> Let p = (RewTerm ?1) In 
  (Match p With
   [(fct_cte ?2)] -> '(fct_cte (Rinv ?2))
   | _ -> '(inv_fct p))
| [(?1 PI)] -> '?1
| [(?1 ?2)] -> Let p = (RewTerm ?2) In 
 (Match p With
 | [(fct_cte ?3)] -> '(fct_cte (?1 ?3))
 | _ -> '(comp ?1 p))
| [PI] -> 'id
| [(pow PI ?1)] -> '(pow_fct ?1)
| [(pow ?1 ?2)] -> Let p = (RewTerm ?1) In 
 (Match p With
 | [(fct_cte ?3)] -> '(fct_cte (pow_fct ?2 ?3))
 | _ -> '(comp (pow_fct ?2) p))
| [?1]-> '(fct_cte ?1).

(**********)
Recursive Tactic Definition ConsProof trm pt :=
Match trm With
| [(plus_fct ?1 ?2)] -> Let p1 = (ConsProof ?1 pt) And p2 = (ConsProof ?2 pt) In '(derivable_pt_plus ?1 ?2 pt p1 p2)
| [(minus_fct ?1 ?2)] -> Let p1 = (ConsProof ?1 pt) And p2 = (ConsProof ?2 pt) In '(derivable_pt_minus ?1 ?2 pt p1 p2)
| [(mult_fct ?1 ?2)] -> Let p1 = (ConsProof ?1 pt) And p2 = (ConsProof ?2 pt) In '(derivable_pt_mult ?1 ?2 pt p1 p2)
| [(div_fct ?1 ?2)] ->
 (Match Context With
 |[id:~((?2 pt)==R0) |- ?] -> Let p1 = (ConsProof ?1 pt) And p2 = (ConsProof ?2 pt) In '(derivable_pt_div ?1 ?2 pt p1 p2 id)
 | _ -> 'False)
| [(inv_fct ?1)] ->
 (Match Context With
 |[id:~((?1 pt)==R0) |- ?] -> Let p1 = (ConsProof ?1 pt) In '(derivable_pt_inv ?1 pt p1 id)
 | _ -> 'False)
| [(comp ?1 ?2)] -> Let pt_f1 = (Eval Cbv Beta in (?2 pt)) In Let p1 = (ConsProof ?1 pt_f1) And p2 = (ConsProof ?2 pt) In '(derivable_pt_comp ?2 ?1 pt p2 p1)
| [(opp_fct ?1)] -> Let p1 = (ConsProof ?1 pt) In '(derivable_pt_opp ?1 pt p1)
| [sin] -> '(derivable_pt_sin pt)
| [cos] -> '(derivable_pt_cos pt)
| [sinh] -> '(derivable_pt_sinh pt)
| [cosh] -> '(derivable_pt_cosh pt)
| [exp] -> '(derivable_pt_exp pt)
| [id] -> '(derivable_pt_id pt)
| [Rsqr] -> '(derivable_pt_Rsqr pt)
| [sqrt] ->
 (Match Context With
 |[id:(Rlt R0 pt) |- ?] -> '(derivable_pt_sqrt pt id)
 | _ -> 'False)
| [(fct_cte ?1)] -> '(derivable_pt_const ?1 pt)
| [?1] -> Let aux = ?1 In
 (Match Context With
    [ id : (derivable_pt aux pt) |- ?] -> 'id
   |[ id : (derivable aux) |- ?] -> '(id pt)
   | _ -> 'False).

(**********)
Recursive Tactic Definition SimplifyDerive trm pt :=
Match trm With
| [(plus_fct ?1 ?2)] -> Try Rewrite derive_pt_plus; SimplifyDerive ?1 pt; SimplifyDerive ?2 pt
| [(minus_fct ?1 ?2)] -> Try Rewrite derive_pt_minus; SimplifyDerive ?1 pt; SimplifyDerive ?2 pt
| [(mult_fct ?1 ?2)] -> Try Rewrite derive_pt_mult; SimplifyDerive ?1 pt; SimplifyDerive ?2 pt
| [(div_fct ?1 ?2)] -> Try Rewrite derive_pt_div; SimplifyDerive ?1 pt; SimplifyDerive ?2 pt
| [(comp ?1 ?2)] -> Let pt_f1 = (Eval Cbv Beta in (?2 pt)) In Try Rewrite derive_pt_comp; SimplifyDerive ?1 pt_f1; SimplifyDerive ?2 pt
| [(opp_fct ?1)] -> Try Rewrite derive_pt_opp; SimplifyDerive ?1 pt
| [(inv_fct ?1)] -> Try Rewrite derive_pt_inv; SimplifyDerive ?1 pt
| [(fct_cte ?1)] -> Try Rewrite derive_pt_const
| [id] -> Try Rewrite derive_pt_id
| [sin] -> Try Rewrite derive_pt_sin
| [cos] -> Try Rewrite derive_pt_cos
| [sinh] -> Try Rewrite derive_pt_sinh
| [cosh] -> Try Rewrite derive_pt_cosh
| [exp] -> Try Rewrite derive_pt_exp
| [Rsqr] -> Try Rewrite derive_pt_Rsqr
| [sqrt] -> Try Rewrite derive_pt_sqrt
| [?1] -> Let aux = ?1 In
  (Match Context With
    [ id : (eqT ? (derive_pt aux pt ?2) ?); H : (derivable aux) |- ? ] -> Try Replace (derive_pt aux pt (H pt)) with (derive_pt aux pt ?2); [Rewrite id | Apply pr_nu]
    |[ id : (eqT ? (derive_pt aux pt ?2) ?); H : (derivable_pt aux pt) |- ? ] -> Try Replace (derive_pt aux pt H) with (derive_pt aux pt ?2); [Rewrite id | Apply pr_nu]
    | _ -> Idtac )
| _ -> Idtac.

(**********)
Tactic Definition Regularity () :=
Match Context With
| [|-(derivable_pt ?1 ?2)] -> 
Let trm = Eval Cbv Beta in (?1 PI) In
Let aux = (RewTerm trm) In IntroHypL aux ?2; Try (Change (derivable_pt aux ?2); IsDiff_pt) Orelse IsDiff_pt
| [|-(derivable ?1)] ->
Let trm = Eval Cbv Beta in (?1 PI) In
Let aux = (RewTerm trm) In IntroHypG aux; Try (Change (derivable aux); IsDiff_glob) Orelse IsDiff_glob
| [|-(continuity ?1)] ->
Let trm = Eval Cbv Beta in (?1 PI) In
Let aux = (RewTerm trm) In IntroHypG aux; Try (Change (continuity aux); IsCont_glob) Orelse IsCont_glob
| [|-(continuity_pt ?1 ?2)] ->
Let trm = Eval Cbv Beta in (?1 PI) In
Let aux = (RewTerm trm) In IntroHypL aux ?2; Try (Change (continuity_pt aux ?2); IsCont_pt) Orelse IsCont_pt
| [|-(eqT ? (derive_pt ?1 ?2 ?3) ?4)] -> 
Let trm = Eval Cbv Beta in (?1 PI) In
Let aux = (RewTerm trm) In
IntroHypL aux ?2; Let aux2 = (ConsProof aux ?2) In Try (Replace (derive_pt ?1 ?2 ?3) with (derive_pt aux ?2 aux2); [SimplifyDerive aux ?2; Try Unfold plus_fct minus_fct mult_fct div_fct id fct_cte inv_fct opp_fct; Try Ring | Try Apply pr_nu]) Orelse IsDiff_pt.

(**********)
Tactic Definition Reg () := Regularity ().

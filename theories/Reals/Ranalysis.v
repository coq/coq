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

(****************************************************)
(**           Basic operations on functions         *)
(****************************************************)
Definition plus_fct [f1,f2:R->R] : R->R := [x:R] ``(f1 x)+(f2 x)``.
Definition opp_fct [f:R->R] : R->R := [x:R] ``-(f x)``.
Definition mult_fct [f1,f2:R->R] : R->R := [x:R] ``(f1 x)*(f2 x)``.
Definition mult_real_fct [a:R;f:R->R] : R->R := [x:R] ``a*(f x)``.
Definition minus_fct [f1,f2:R->R] : R->R := [x:R] ``(f1 x)-(f2 x)``.
Definition div_fct [f1,f2:R->R] : R->R := [x:R] ``(f1 x)/(f2 x)``.
Definition div_real_fct [a:R;f:R->R] : R->R := [x:R] ``a/(f x)``.
Definition comp [f1,f2:R->R] : R->R := [x:R] ``(f1 (f2 x))``.

(****************************************************)
(**            Variations of functions              *)
(****************************************************)
Definition increasing [f:R->R] : Prop := (x,y:R) ``x<=y``->``(f x)<=(f y)``.
Definition decreasing [f:R->R] : Prop := (x,y:R) ``x<=y``->``(f y)<=(f x)``.
Definition strict_increasing [f:R->R] : Prop := (x,y:R) ``x<y``->``(f x)<(f y)``.
Definition strict_decreasing [f:R->R] : Prop := (x,y:R) ``x<y``->``(f y)<(f x)``.
Definition constant [f:R->R] : Prop := (x,y:R) ``(f x)==(f y)``.

(**********)
Axiom fct_eq : (A,B:Type) (f1,f2:A->B) ((x:A)(f1 x)==(f2 x))->f1==f2.
  
(**********) 
Definition no_cond : R->Prop := [x:R] True.
 
(***************************************************)
(**      Definition of continuity as a limit       *)
(***************************************************)

(**********)
Definition continuity_pt [f:R->R; x0:R] : Prop := (continue_in f no_cond x0).

(**********)
Lemma sum_continuous : (f1,f2:R->R; x0:R) (continuity_pt f1 x0) -> (continuity_pt f2 x0) -> (continuity_pt (plus_fct f1 f2) x0).
Unfold continuity_pt plus_fct; Unfold continue_in; Intros; Apply limit_plus; Assumption.
Save.

(**********) 
Lemma diff_continuous : (f1,f2:R->R; x0:R) (continuity_pt f1 x0) -> (continuity_pt f2 x0) -> (continuity_pt (minus_fct f1 f2) x0).
Unfold continuity_pt minus_fct; Unfold continue_in; Intros; Apply limit_minus; Assumption.
Save.

(**********)
Lemma prod_continuous : (f1,f2:R->R; x0:R) (continuity_pt f1 x0) -> (continuity_pt f2 x0) -> (continuity_pt (mult_fct f1 f2) x0).
Unfold continuity_pt mult_fct; Unfold continue_in; Intros; Apply limit_mul; Assumption.
Save.
  
(**********)
Lemma const_continuous : (f:R->R; x0:R) (constant f) -> (continuity_pt f x0).
Unfold constant continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Intros; Exists ``1``; Split; [Apply Rlt_R0_R1 | Intros; Generalize (H x x0); Intro; Rewrite H2; Simpl; Rewrite R_dist_eq; Assumption].
Save.

(**********)
Lemma scal_continuous : (f:R->R;a:R; x0:R) (continuity_pt f x0) -> (continuity_pt (mult_real_fct a f) x0).
Unfold continuity_pt mult_real_fct; Unfold continue_in; Intros; Apply (limit_mul ([x:R] a) f (D_x no_cond x0) a (f x0) x0).
Unfold limit1_in; Unfold limit_in; Intros; Exists ``1``; Split.
Apply Rlt_R0_R1.
Intros; Rewrite R_dist_eq; Assumption.
Assumption.
Save.

(**********)
Lemma opp_continuous : (f:R->R; x0:R) (continuity_pt f x0) -> (continuity_pt (opp_fct f) x0).
Unfold continuity_pt opp_fct; Unfold continue_in; Intros; Apply limit_Ropp; Assumption.
Save.

(**********)
Lemma inv_continuous : (f:R->R; x0:R) (continuity_pt f x0) -> ~``(f x0)==0`` ->
(continuity_pt ([x:R] ``/(f x)``) x0).
Unfold continuity_pt; Unfold continue_in; Intros; Apply limit_inv; Assumption.
Save.
 
Lemma div_eq_inv : (f1,f2:R->R) (div_fct f1 f2)==(mult_fct f1 ([x:R]``/(f2 x)``)).
Intros; Unfold div_fct; Unfold mult_fct; Unfold Rdiv; Apply fct_eq; Intro x; Reflexivity.
Save.
 
(**********)
Lemma div_continuous : (f1,f2:R->R; x0:R) (continuity_pt f1 x0) -> (continuity_pt f2 x0) -> ~``(f2 x0)==0`` -> (continuity_pt (div_fct f1 f2) x0).
Intros; Rewrite -> (div_eq_inv f1 f2); Apply prod_continuous; [Assumption | Apply inv_continuous; Assumption].
Save.
 
(**********) 
Definition continuity [f:R->R] : Prop := (x:R) (continuity_pt f x).
 
Lemma sum_continuity : (f1,f2:R->R) (continuity f1)->(continuity f2)->(continuity (plus_fct f1 f2)).
Unfold continuity; Intros; Apply (sum_continuous f1 f2 x (H x) (H0 x)).
Save.

Lemma diff_continuity : (f1,f2:R->R) (continuity f1)->(continuity f2)->(continuity (minus_fct f1 f2)).
Unfold continuity; Intros; Apply (diff_continuous f1 f2 x (H x) (H0 x)).
Save.
 
Lemma prod_continuity : (f1,f2:R->R) (continuity f1)->(continuity f2)->(continuity (mult_fct f1 f2)).
Unfold continuity; Intros; Apply (prod_continuous f1 f2 x (H x) (H0 x)).
Save.
 
Lemma const_continuity : (f:R->R) (constant f) -> (continuity f).
Unfold continuity; Intros; Apply (const_continuous f x H).
Save.
 
Lemma scal_continuity : (f:R->R;a:R) (continuity f) -> (continuity (mult_real_fct a f)).
Unfold continuity; Intros; Apply (scal_continuous f a x (H x)).
Save.
  
Lemma opp_continuity : (f:R->R) (continuity f)->(continuity (opp_fct f)).
Unfold continuity; Intros; Apply (opp_continuous f x (H x)).
Save.
 
Lemma div_continuity : (f1,f2:R->R) (continuity f1)->(continuity f2)->((x:R) ~``(f2 x)==0``)->(continuity (div_fct f1 f2)).
Unfold continuity; Intros; Apply (div_continuous f1 f2 x (H x) (H0 x) (H1 x)).
Save.
 
Lemma inv_continuity : (f:R->R) (continuity f)->((x:R) ~``(f x)==0``)->(continuity ([x:R] ``/(f x)``)).
Unfold continuity; Intros; Apply (inv_continuous f x (H x) (H0 x)).
Save.
 
(*****************************************************)
(**  Derivative's definition using Landau's kernel   *)
(*****************************************************)
Definition derivable_pt [f:R->R; x:R] : Prop := (EXT l : R | ((eps:R) ``0<eps``->(EXT delta : posreal | ((h:R) ~``h==0``->``(Rabsolu h)<delta`` -> ``(Rabsolu ((((f (x+h))-(f x))/h)-l))<eps``)))).

Definition derivable [f:R->R] : Prop := (x:R) (derivable_pt f x).

Parameter derive_pt : (R->R)->R->R.

Axiom derive_pt_def : (f:R->R;x,l:R) ((eps:R) ``0<eps``->(EXT delta : posreal | ((h:R) ~``h==0``->``(Rabsolu h)<delta`` -> ``(Rabsolu ((((f (x+h))-(f x))/h)-l))<eps``))) <-> (derive_pt f x)==l.

(**********)
Lemma derive_pt_def_0 : (f:R->R;x,l:R) ((eps:R) ``0<eps``->(EXT delta : posreal | ((h:R) ~``h==0``->``(Rabsolu h)<delta`` -> ``(Rabsolu ((((f (x+h))-(f x))/h)-l))<eps``))) -> (derive_pt f x)==l.
Intros; Elim (derive_pt_def f x l); Intros; Apply (H0 H).
Save.

(**********)
Lemma derive_pt_def_1 : (f:R->R;x,l:R) (derive_pt f x)==l -> ((eps:R) ``0<eps``->(EXT delta : posreal | ((h:R) ~``h==0``->``(Rabsolu h)<delta`` -> ``(Rabsolu ((((f (x+h))-(f x))/h)-l))<eps``))).
Intros; Elim (derive_pt_def f x l); Intros; Apply (H2 H eps H0).
Save.

(**********)
Definition derive [f:R->R] := [x:R] (derive_pt f x).

(************************************)
(** Class of differential functions *)
(************************************)
Record Differential : Type := mkDifferential {
d1 :> R->R;
cond_diff : (derivable d1) }.
 
Record Differential_D2 : Type := mkDifferential_D2 {
d2 :> R->R;
cond_D1 : (derivable d2);
cond_D2 : (derivable (derive d2)) }.

(**********)
Lemma derivable_derive : (f:R->R;x:R) (derivable_pt f x) -> (EXT l : R | (derive_pt f x)==l).
Intros f x; Unfold derivable_pt; Intro H; Elim H; Intros l H0; Rewrite (derive_pt_def_0 f x l); [Exists l; Reflexivity | Assumption].
Save.

(**********)
Lemma derive_derivable : (f:R->R;x,l:R) (derive_pt f x)==l -> (derivable_pt f x).
Intros; Unfold derivable_pt; Generalize (derive_pt_def_1 f x l H); Intro H0; Exists l; Assumption.
Save.

(********************************************************************)
(** Equivalence of this definition with the one using limit concept *)
(********************************************************************)
Lemma derive_pt_D_in : (f,df:R->R;x:R) (D_in f df no_cond x) <-> (derive_pt
f x)==(df x).
Intros; Split.
Unfold D_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros.
Apply derive_pt_def_0. 
Intros; Elim (H eps H0); Intros alpha H1; Elim H1; Intros;  Exists (mkposreal alpha H2); Intros; Generalize (H3 ``x+h``); Intro; Cut ``x+h-x==h``; [Intro; Cut ``(D_x no_cond x (x+h))``/\``(Rabsolu (x+h-x)) < alpha``; [Intro; Generalize (H6 H8); Rewrite H7; Intro; Assumption | Split; [Unfold D_x; Split; [Unfold no_cond; Trivial | Apply Rminus_not_eq_right; Rewrite H7; Assumption] | Rewrite H7; Assumption]] | Ring].
Intro; Generalize (derive_pt_def_1 f x (df x) H); Intro; Unfold D_in; Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Intros; Elim (H0 eps H1); Intros alpha H2; Exists (pos alpha); Split.
Apply (cond_pos alpha).
Intros; Elim H3; Intros; Unfold D_x in H4; Elim H4; Intros; Cut ``x0-x<>0``.
Intro; Generalize (H2 ``x0-x`` H8 H5); Replace ``x+(x0-x)`` with x0.
Intro; Assumption.
Ring.
Auto with real.
Save.

Definition fct_cte [a:R] : R->R := [x:R]a.

(***********************************)
(**   derivability -> continuity   *)
(***********************************)
Theorem derivable_continuous_pt : (f:R->R;x:R) (derivable_pt f x) -> (continuity_pt f x).
Intros.
Generalize (derivable_derive f x H); Intro.
Elim H0; Intros l H1.
Cut l==((fct_cte l) x).
Intro.
Rewrite H2 in H1.
Generalize (derive_pt_D_in f (fct_cte l) x); Intro.
Elim H3; Intros.
Generalize (H5 H1); Intro.
Unfold continuity_pt.
Apply (cont_deriv f (fct_cte l) no_cond x H6).
Unfold fct_cte; Reflexivity.
Save.
 
Theorem derivable_continuous : (f:R->R) (derivable f) -> (continuity f).
Unfold derivable continuity; Intros; Apply (derivable_continuous_pt f x (H x)).
Save.

(****************************************************************)
(**                      Main rules                             *)
(****************************************************************)

(* Addition *)
Lemma deriv_sum : (f1,f2:R->R;x:R) (derivable_pt f1 x) -> (derivable_pt f2 x) -> ``(derive_pt (plus_fct f1 f2) x)==(derive_pt f1 x)+(derive_pt f2 x)``.
Intros; Generalize (derivable_derive f1 x H); Intro H1; Generalize (derivable_derive f2 x H0); Intro H2; Elim H1; Clear H1; Intros l1 H1; Elim H2; Clear H2; Intros l2 H2; Unfold plus_fct; Rewrite H1; Rewrite H2; Apply derive_pt_def_0; Intros; Generalize (derive_pt_def_1 f1 x l1 H1); Clear H1; Intro H1; Generalize (derive_pt_def_1 f2 x l2 H2); Clear H2; Intro H2; Cut ~(O=(2)).
Intro Haux; Generalize (lt_INR_0 (2) (neq_O_lt (2) Haux)); Rewrite INR_eq_INR2; Unfold INR2; Intro Haux1; Generalize (Rlt_Rinv ``2`` Haux1); Clear Haux1; Intro Haux1; Generalize (Rmult_lt_pos eps ``/2`` H3 Haux1); Clear Haux1; Intro Haux1; Elim (H1 ``eps/2`` Haux1); Intros delta1 H4; Elim (H2 ``eps/2`` Haux1); Intros delta2 H5; Exists (mkposreal (Rmin delta1 delta2) (Rmin_stable_in_posreal delta1 delta2)); Intros h H6 H7; Unfold plus_fct; Replace ``((f1 (x+h))+(f2 (x+h))-((f1 x)+(f2 x)))/h-(l1+l2)`` with ``(((f1 (x+h))-(f1 x))/h-l1)+(((f2 (x+h))-(f2 x))/h-l2)``.
Apply Rle_lt_trans with ``(Rabsolu ((f1 (x+h))-(f1 x))/h-l1)+(Rabsolu ((f2 (x+h))-(f2 x))/h-l2)``.
Apply Rabsolu_triang.
Generalize (H5 h H6 (Rlt_le_trans (Rabsolu h) (Rmin delta1 delta2) delta2 H7 (Rmin_r delta1 delta2))); Intro H8; Generalize (H4 h H6 (Rlt_le_trans (Rabsolu h) (Rmin delta1 delta2) delta1 H7 (Rmin_l delta1 delta2))); Intro H9.
Generalize (Rplus_lt ``(Rabsolu (((f1 (x+h))-(f1 x))/h-l1))`` ``eps/2`` ``(Rabsolu (((f2 (x+h))-(f2 x))/h-l2))`` ``eps/2`` H9 H8).
Replace ``eps/2+eps/2`` with ``eps``.
Intro H10; Assumption.
Field; DiscrR.
Field; Assumption.
Discriminate.  
Save.

Lemma sum_derivable_pt : (f1,f2:R->R;x:R) (derivable_pt f1 x)->(derivable_pt f2 x)->(derivable_pt (plus_fct f1 f2) x).
Intros; Generalize (derivable_derive f1 x H); Intro; Generalize (derivable_derive f2 x H0); Intro; Elim H1; Clear H1; Intros l1 H1; Elim H2; Clear H2; Intros l2 H2; Apply (derive_derivable (plus_fct f1 f2) x ``l1+l2``); Rewrite <- H1; Rewrite <- H2; Apply deriv_sum; Assumption.
Save.

Lemma sum_derivable : (f1,f2:R->R) (derivable f1) -> (derivable f2) -> (derivable (plus_fct f1 f2)).
Unfold derivable; Intros f1 f2 H1 H2 x; Apply sum_derivable_pt; [Exact (H1 x) | Exact (H2 x)].
Save.

Lemma sum_derivable_pt_var : (f1,f2:R->R;x:R) (derivable_pt f1 x) -> (derivable_pt f2 x) -> (derivable_pt ([y:R]``(f1 y)+(f2 y)``) x).
Intros; Generalize (sum_derivable_pt f1 f2 x H H0); Unfold plus_fct; Intro; Assumption.
Save.

Lemma derive_sum : (f1,f2:R->R;x:R) (derivable_pt f1 x) -> (derivable_pt f2 x) -> (derive_pt ([y:R]``(f1 y)+(f2 y)``) x)==``(derive_pt f1 x)+(derive_pt f2 x)``.
Intros; Generalize (deriv_sum f1 f2 x H H0); Unfold plus_fct; Intro; Assumption.
Save.

(* Opposite *)
Lemma deriv_opposite : (f:R->R;x:R) (derivable_pt f x) -> ``(derive_pt (opp_fct f) x)==-(derive_pt f x)``.
Intros; Generalize (derivable_derive f x H); Intro H0; Elim H0; Intros l H1; Rewrite H1; Unfold opp_fct; Apply derive_pt_def_0; Intros; Generalize (derive_pt_def_1 f x l H1); Intro H3; Elim (H3 eps H2); Intros delta H4; Exists delta; Intros; Replace ``( -(f (x+h))- -(f x))/h- -l`` with ``- (((f (x+h))-(f x))/h-l)``; [Rewrite Rabsolu_Ropp; Apply (H4 h H5 H6) | Field; Assumption].
Save.

Lemma opposite_derivable_pt : (f:R->R;x:R) (derivable_pt f x) -> (derivable_pt (opp_fct f) x).
Unfold opp_fct derivable_pt; Intros; Elim H; Intros; Exists ``-x0``; Intros; Elim (H0 eps H1); Intros; Exists x1; Intros; Generalize (H2 h H3 H4); Intro H5; Replace ``( -(f (x+h))- -(f x))/h- -x0`` with ``- (((f (x+h))-(f x))/h-x0)``; [Rewrite Rabsolu_Ropp; Assumption | Field; Assumption].
Save.

Lemma opposite_derivable : (f:R->R) (derivable f) -> (derivable (opp_fct f)).
Unfold derivable; Intros f H1 x; Apply opposite_derivable_pt; Exact (H1 x).
Save. 

(* Difference *)
Lemma diff_plus_opp : (f1,f2:R->R) (minus_fct f1 f2)==(plus_fct f1 (opp_fct f2)).
Intros; Unfold minus_fct plus_fct opp_fct; Apply fct_eq; Intro x; Ring.
Save.

Lemma deriv_diff : (f1,f2:R->R;x:R) (derivable_pt f1 x) -> (derivable_pt f2 x) -> ``(derive_pt (minus_fct f1 f2) x)==(derive_pt f1 x)-(derive_pt f2 x)``.
Intros; Rewrite diff_plus_opp; Unfold Rminus; Rewrite <- (deriv_opposite f2 x H0); Apply deriv_sum; [Assumption | Apply opposite_derivable_pt; Assumption].
Save.

Lemma diff_derivable_pt : (f1,f2:R->R;x:R) (derivable_pt f1 x)->(derivable_pt f2 x)->(derivable_pt (minus_fct f1 f2) x).
Intros; Rewrite (diff_plus_opp f1 f2); Apply sum_derivable_pt; [Assumption | Apply opposite_derivable_pt; Assumption].
Save.

Lemma diff_derivable : (f1,f2:R->R) (derivable f1) -> (derivable f2) -> (derivable (minus_fct f1 f2)).
Unfold derivable; Intros f1 f2 H1 H2 x; Apply diff_derivable_pt; [ Exact (H1 x) | Exact (H2 x)].
Save. 

Lemma derive_diff : (f1,f2:R->R;x:R) (derivable_pt f1 x)
-> (derivable_pt f2 x) -> (derive_pt ([y:R]``(f1 y)-(f2 y)``) x)==``(derive_pt f1 x)-(derive_pt f2 x)``.
Intros; Generalize (deriv_diff f1 f2 x H H0); Unfold minus_fct; Intro; Assumption.
Save.

(**********)
Lemma deriv_scal : (f:R->R;a,x:R) (derivable_pt f x) -> ``(derive_pt (mult_real_fct a f) x)==a*(derive_pt f x)``.
Intros f a x Ha; Unfold mult_real_fct; Generalize (derivable_derive f x Ha); Intro Hb; Elim Hb; Intros l Hc; Rewrite Hc; Apply derive_pt_def_0; Generalize (Req_EM a R0); Intro H0; Elim H0; Intro H1.
Intros; Exists (mkposreal ``1`` Rlt_R0_R1); Intros; Rewrite H1; Repeat Rewrite Rmult_Ol; Repeat Rewrite minus_R0; Unfold Rdiv; Rewrite Rmult_Ol; Rewrite Rabsolu_R0; Assumption.
Intros; Generalize (derive_pt_def_1 f x l Hc); Intro H2; Elim (H2 ``eps/(Rabsolu a)``).
Intros; Exists x0; Intros; Replace ``(a*(f (x+h))-a*(f x))/h-a*l`` with ``a*(((f (x+h))-(f x))/h-l)``.
Rewrite Rabsolu_mult; Replace ``eps`` with ``(Rabsolu a)*(eps/(Rabsolu a))``.
Apply Rlt_monotony.
Apply (Rabsolu_pos_lt a H1).
Apply (H3 h H4 H5).
Rewrite <- Rmult_sym; Unfold Rdiv; Rewrite Rmult_assoc; Rewrite <- (Rinv_l_sym (Rabsolu a)); [Apply Rmult_1r | Apply (Rabsolu_no_R0 a H1)].
Field; Assumption.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply (Rabsolu_pos_lt a H1)].
Save. 

Lemma scal_derivable_pt : (f:R->R;a:R; x:R) (derivable_pt f x) ->
(derivable_pt (mult_real_fct a f) x).
Unfold mult_real_fct derivable_pt; Intros; Generalize (Req_EM a R0); Intro H0; Elim H0; Intro H1.
Intros; Exists ``0``; Intros; Exists (mkposreal ``1`` Rlt_R0_R1); Intros; Rewrite H1; Repeat Rewrite Rmult_Ol; Unfold Rminus; Repeat Rewrite Ropp_O; Repeat Rewrite Rplus_Or; Unfold Rdiv; Rewrite Rmult_Ol; Rewrite Rabsolu_R0; Assumption.
Elim H; Intros l H2; Exists ``a*l``; Intros; Elim (H2 ``eps/(Rabsolu a)``); Intros.
Exists x0; Intros; Replace ``(a*(f (x+h))-a*(f x))/h-a*l`` with ``a*(((f (x+h))-(f x))/h-l)``.
Rewrite Rabsolu_mult; Replace ``eps`` with ``(Rabsolu a)*(eps/(Rabsolu a))``.
Apply Rlt_monotony.
Apply (Rabsolu_pos_lt a H1).
Apply (H4 h H5 H6).
Rewrite <- Rmult_sym; Unfold Rdiv; Rewrite Rmult_assoc; Rewrite <- (Rinv_l_sym (Rabsolu a)); [Apply Rmult_1r | Apply (Rabsolu_no_R0 a H1)].
Field; Assumption.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply (Rabsolu_pos_lt a H1)].
Save.

Lemma scal_derivable_pt_var : (f:R->R;a:R; x:R) (derivable_pt f x) -> (derivable_pt ([y:R]``a*(f y)``) x).
Intros; Generalize (scal_derivable_pt f a x H); Unfold mult_real_fct; Intro; Assumption.
Save.

Lemma scal_derivable : (f:R->R;a:R) (derivable f) -> (derivable (mult_real_fct a f)).
Unfold derivable; Intros f a H1 x; Apply scal_derivable_pt; Exact
(H1 x).
Save.

Lemma derive_scal : (f:R->R;a,x:R) (derivable_pt f x) -> (derive_pt ([x:R]``a*(f x)``) x)==``a*(derive_pt f x)``.
Intros; Generalize (deriv_scal f a x H); Unfold mult_real_fct; Intro; Assumption.
Save.

(* Multiplication *)
Lemma deriv_prod : (f1,f2:R->R;x:R) (derivable_pt f1 x) -> (derivable_pt f2 x) -> ``(derive_pt (mult_fct f1 f2) x)==(derive_pt f1 x)*(f2 x)+(derive_pt f2 x)*(f1 x)``.
Intros; Generalize (derivable_derive f1 x H); Intro; Generalize (derivable_derive f2 x H0); Intro; Elim H1; Clear H1; Intros l1 H1; Elim H2; Clear H2; Intros l2 H2; Cut l1==((fct_cte l1) x).
Cut l2==((fct_cte l2) x).
Intros; Rewrite H3 in H2; Rewrite H4 in H1; Generalize derive_pt_D_in; Intro; Generalize (H5 f1 (fct_cte l1) x); Intro; Generalize (H5 f2 (fct_cte l2) x); Intro; Elim H6; Elim H7; Intros; Generalize (H11 H1); Intro; Generalize (H9 H2); Intro; Rewrite H1; Rewrite H2; Replace ``(fct_cte l1 x)*(f2 x)+(fct_cte l2 x)*(f1 x)`` with ``((plus_fct (mult_fct (fct_cte l1) f2) (mult_fct f1 (fct_cte l2))) x)``.
Generalize (H5 (mult_fct f1 f2) (plus_fct (mult_fct (fct_cte l1) f2) (mult_fct f1 (fct_cte l2))) x); Intro; Elim H14; Intros; Apply H15; Unfold mult_fct plus_fct; Apply Dmult; Assumption.
Unfold plus_fct mult_fct fct_cte; Ring.
Unfold fct_cte; Reflexivity.
Unfold fct_cte; Reflexivity.
Save.

Lemma prod_derivable_pt : (f1,f2:R->R;x:R) (derivable_pt f1 x)->(derivable_pt f2 x)->(derivable_pt (mult_fct f1 f2) x).
Intros; Generalize (deriv_prod f1 f2 x H H0); Intro; Apply (derive_derivable (mult_fct f1 f2) x ``(derive_pt f1 x)*(f2 x)+(derive_pt f2 x)*(f1 x)`` H1).
Save.

Lemma prod_derivable : (f1,f2:R->R) (derivable f1) -> (derivable f2) -> (derivable (mult_fct f1 f2)).
Unfold derivable; Intros f1 f2 H1 H2 x; Apply prod_derivable_pt; [ Exact (H1 x) | Exact (H2 x)].
Save.

Lemma derive_prod : (f1,f2:R->R;x:R) (derivable_pt f1 x)
-> (derivable_pt f2 x) -> (derive_pt ([x:R]``(f1 x)*(f2 x)``) x)==``(derive_pt f1 x)*(f2 x)+(derive_pt f2 x)*(f1 x)``.
Intros; Generalize (deriv_prod f1 f2 x H H0); Unfold mult_fct; Intro; Assumption.
Save.

(**********)
Lemma deriv_const : (a:R;x:R) (derive_pt ([x:R] a) x)==``0``.
Intros; Apply derive_pt_def_0; Intros; Exists (mkposreal ``1`` Rlt_R0_R1); Intros; Replace ``a-a`` with ``0``; [Unfold Rdiv; Rewrite Rmult_Ol; Rewrite minus_R0; Rewrite Rabsolu_R0; Assumption | Ring].
Save.

Lemma const_derivable : (a:R) (derivable ([x:R] a)).
Unfold derivable; Unfold derivable_pt; Intros; Exists ``0``; Intros; Exists (mkposreal ``1`` Rlt_R0_R1); Intros; Unfold Rminus; Rewrite Rplus_Ropp_r; Unfold Rdiv; Rewrite Rmult_Ol; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Save.

(**********)
Lemma deriv_id : (x:R) (derive_pt ([y:R] y) x)==``1``.
Intro x; Apply derive_pt_def_0; Intros; Exists (mkposreal ``1`` Rlt_R0_R1); Intros; Replace ``(x+h-x)/h-1`` with ``0``.
Rewrite Rabsolu_R0; Assumption.
Field; Assumption.
Save.

Lemma diff_id : (derivable ([x:R] x)).
Unfold derivable; Intro x; Unfold derivable_pt; Exists ``1``; Intros eps Heps; Exists (mkposreal eps Heps); Intros h H1 H2; Replace ``(x+h-x)/h-1`` with ``0``; [Rewrite Rabsolu_R0; Apply Rle_lt_trans with ``(Rabsolu h)``; [Apply Rabsolu_pos | Assumption] | Field; Assumption].
Save.

(**********)
Lemma sum_fct_cte_derive_pt : (f:R->R;t,a:R) (derivable_pt f t) -> (derive_pt ([x:R]``(f x)+a``) t)==(derive_pt f t).
Intros; Generalize (derivable_derive f t H); Intro; Elim H0; Intros l H1; Rewrite H1; Apply derive_pt_def_0; Intros; Generalize (derive_pt_def_1 f t l H1); Intros; Elim (H3 eps H2); Intros delta H4; Exists delta; Intros; Replace ``(f (t+h))+a-((f t)+a)`` with ``(f (t+h))-(f t)``; [Apply (H4 h H5 H6) | Ring].
Save.

Lemma sum_fct_cte_derivable_pt : (f:R->R;t,a:R) (derivable_pt f t)->(derivable_pt ([t:R]``(f t)+a``) t).
Unfold derivable_pt; Intros; Elim H; Intros; Exists x; Intros; Elim (H0 eps H1); Intros; Exists x0; Intro h; Replace ``(f (t+h))+a-((f t)+a)`` with ``(f (t+h))-(f t)``; [Exact (H2 h) | Ring].
Save. 

Lemma sum_fct_cte_derivable : (f:R->R;a:R) (derivable f)->(derivable ([t:R]``(f t)+a``)).
Unfold derivable; Intros; Apply sum_fct_cte_derivable_pt; Apply (H x).
Save.

(**********)
Lemma deriv_Rsqr : (x:R) (derive Rsqr x)==``2*x``.
Intro x; Unfold Rsqr; Unfold derive; Apply (derive_pt_def_0 ([x0:R]``x0*x0``) x); Intros eps Heps; Exists (mkposreal eps Heps); Intros h H1 H2; Replace ``((x+h)*(x+h)-x*x)/h-2*x`` with ``h``; [Assumption | Field; Assumption].
Save.

Lemma diff_Rsqr : (derivable Rsqr).
Unfold derivable; Intro x; Unfold Rsqr; Unfold derivable_pt; Exists ``2*x``; Intros eps Heps; Exists (mkposreal eps Heps); Intros h H1 H2; Replace ``((x+h)*(x+h)-x*x)/h-2*x`` with ``h``; [Assumption | Field; Assumption].
Save.

Lemma Rsqr_derivable_pt : (f:R->R;t:R) (derivable_pt f t) -> (derivable_pt ([x:R](Rsqr (f x))) t).
Unfold Rsqr; Intros; Generalize (prod_derivable_pt f f t H H); Unfold mult_fct; Intro H0; Assumption.
Save.

Lemma Rsqr_derivable : (f:R->R) (derivable f)->(derivable ([x:R](Rsqr (f x)))).
Unfold derivable; Intros; Apply (Rsqr_derivable_pt f x (H x)).
Save.

(* SQRT *)
Axiom deriv_sqrt : (x:R) ``0<x`` -> (derive sqrt)==[y:R] ``1/(2*(sqrt y))``.

Lemma eq_fct : (x:R;f1,f2:R->R) f1==f2 -> (f1 x)==(f2 x).
Intros; Rewrite H; Reflexivity.
Save.

Lemma diff_sqrt : (x:R) ``0<x`` -> (derivable_pt sqrt x).
Intros; Generalize (deriv_sqrt x H); Unfold derive; Intro; Generalize (eq_fct x ([x:R](derive_pt sqrt x)) ([y:R]``1/(2*(sqrt y))``) H0); Intro; Apply (derive_derivable sqrt x ``1/(2*(sqrt x))`` H1).
Save.

(* Composition *)
Axiom prov : (f:R->R) (Dgf no_cond no_cond f)==no_cond.

Lemma deriv_composition : (f,g:R->R;x:R) (derivable_pt f x) -> (derivable_pt g (f x)) -> ``(derive_pt (comp g f) x)==(derive_pt g (f x))*(derive_pt f x)``. 
Intros; Generalize (derivable_derive f x H); Intro; Generalize (derivable_derive g (f x) H0); Intro; Elim H1; Clear H1; Intros l1 H1; Elim H2; Clear H2; Intros l2 H2.
Cut l1==((fct_cte l1) x).
Cut l2==((fct_cte l2) x).
Intros; Rewrite H3 in H2; Rewrite H4 in H1; Rewrite H1; Rewrite H2; Generalize derive_pt_D_in; Intro; Elim (H5 f (fct_cte l1) x); Intros; Elim (H5 g (fct_cte l2) (f x)); Intros; Generalize (H9 H2); Intro; Generalize (H7 H1); Intro; Replace ``(fct_cte l2 x)*(fct_cte l1 x)`` with ``((mult_fct (fct_cte l1) (fct_cte l2)) x)``.
Elim (H5 (comp g f) (mult_fct (fct_cte l1) (fct_cte l2)) x); Intros; Apply H12.
Unfold comp mult_fct; Generalize (prov f); Intro; Rewrite <- H14; Apply (Dcomp no_cond no_cond (fct_cte l1) (fct_cte l2) f g x); Assumption.
Unfold mult_fct fct_cte; Rewrite Rmult_sym; Reflexivity.
Unfold fct_cte; Reflexivity.
Unfold fct_cte; Reflexivity.
Save.

Lemma composition_derivable : (f,g:R->R;x:R) (derivable_pt f x) -> (derivable_pt g (f x)) -> (derivable_pt (comp g f) x).
Intros; Generalize (deriv_composition f g x H H0); Intro; Apply (derive_derivable (comp g f) x ``(derive_pt g (f x))*(derive_pt f x)`` H1).
Save.

Lemma derive_composition : (f,g:R->R;x:R) (derivable_pt f x) -> (derivable_pt g (f x)) -> (derive_pt ([x:R]``(g (f x))``) x)==``(derive_pt g (f x))*(derive_pt f x)``.
Intros; Generalize (deriv_composition f g x H H0); Unfold comp; Intro; Assumption.
Save.

Lemma composition_derivable_var : (f,g:R->R;x:R) (derivable_pt f x) -> (derivable_pt g (f x)) -> (derivable_pt ([x:R](g (f x))) x).
Intros; Generalize (composition_derivable f g x H H0); Unfold comp; Intro; Assumption.
Save.

Lemma diff_comp : (f,g:R->R) (derivable f)->(derivable g)->(derivable (comp g f)).
Intros f g; Unfold derivable; Intros H1 H2 x; Apply (composition_derivable f g x (H1 x) (H2 (f x))).
Save.

Lemma Rsqr_derive : (f:R->R;t:R) (derivable_pt f t)->(derive_pt ([x:R](Rsqr (f x))) t)==(Rmult ``2`` (Rmult (derive_pt f t) (f t))).
Intros; Generalize diff_Rsqr; Unfold derivable; Intro H0; Generalize (deriv_composition f Rsqr t H (H0 (f t))); Unfold comp; Intro H1; Rewrite H1; Generalize (deriv_Rsqr (f t)); Unfold derive; Intro H2; Rewrite H2; Rewrite Rmult_assoc; Rewrite <- (Rmult_sym (derive_pt f t)); Reflexivity.
Save.

(* SIN and COS *)
Axiom deriv_sin : (derive sin)==cos.
 
Lemma diff_sin : (derivable sin).
Unfold derivable; Intro; Generalize deriv_sin; Unfold derive; Intro; Generalize
(eq_fct x ([x:R](derive_pt sin x)) cos H); Intro; Apply (derive_derivable sin x
(cos x) H0).
Save.
 
Lemma diff_cos : (derivable cos).
Unfold derivable; Intro; Cut ([x:R]``(sin (x+PI/2))``)==cos.
Intro; Rewrite <- H; Apply (composition_derivable_var ([x:R]``x+PI/2``) sin x).
Apply (sum_fct_cte_derivable_pt ([x:R]x) x ``PI/2``); Apply diff_id.
Apply diff_sin.
Apply fct_eq; Intro; Symmetry; Rewrite Rplus_sym; Apply cos_sin.
Save.
 
Lemma derive_pt_sin : (x:R) (derive_pt sin x)==(cos x).
Intro; Generalize deriv_sin; Unfold derive; Intro; Apply (eq_fct x [x:R](derive_pt sin x) cos H).
Save.

Lemma deriv_cos : (derive cos)==(opp_fct sin).
Unfold opp_fct derive; Apply fct_eq; Intro; Cut ([x:R]``(sin (x+PI/2))``)==cos.
Intro; Rewrite <- H; Rewrite (derive_composition ([x:R]``x+PI/2``) sin x).
Rewrite (derive_pt_sin ``x+PI/2``); Rewrite (sum_fct_cte_derive_pt ([x:R]``x``) x ``PI/2``).
Generalize (deriv_id x); Intro; Unfold derive in H0; Rewrite H0; Rewrite Rmult_1r; Rewrite Rplus_sym; Rewrite sin_cos; Rewrite Ropp_Ropp; Reflexivity.
Apply diff_id.
Apply (sum_fct_cte_derivable_pt ([x:R]x) x ``PI/2``); Apply diff_id.
Apply diff_sin.
Apply fct_eq; Intro; Symmetry; Rewrite Rplus_sym; Apply cos_sin.
Save.

Lemma derive_pt_cos : (x:R) (derive_pt cos x)==``-(sin x)``.
Intro; Generalize deriv_cos; Unfold derive; Intro; Unfold opp_fct in H; Apply (eq_fct x [x:R](derive_pt cos x) [x:R]``-(sin x)`` H).
Save.

(************************************************************)
(**             Local extremum's condition                  *)
(************************************************************)
Theorem deriv_maximum : (f:R->R;a,b,c:R) ``a<c``->``c<b``->(derivable_pt f c)->((x:R) ``a<x``->``x<b``->``(f x)<=(f c)``)->``(derive_pt f c)==0``.
Intros; Case (total_order R0 (derive_pt f c)); Intro.
Generalize (derivable_derive f c H1); Intro; Elim H4; Intros l H5; Rewrite H5 in H3; Generalize (derive_pt_def_1 f c l H5); Intro.
Cut ``0<l/2``.
Intro; Elim (H6 ``l/2`` H7); Intros delta H8.
Cut ``0<(b-c)/2``.
Intro; Cut ``(Rmin delta/2 ((b-c)/2))<>0``.
Intro; Cut ``(Rabsolu (Rmin delta/2 ((b-c)/2)))<delta``.
Intro; Generalize (H8 ``(Rmin delta/2 ((b-c)/2))`` H10 H11); Intro; Cut ``0<(Rmin (delta/2) ((b-c)/2))``.
Intro; Cut ``a<c+(Rmin (delta/2) ((b-c)/2))``.
Cut ``c+(Rmin (delta/2) ((b-c)/2))<b``.
Intros; Generalize (H2 ``c+(Rmin (delta/2) ((b-c)/2))`` H15 H14); Intro; Cut ``((f (c+(Rmin (delta/2) ((b-c)/2))))-(f c))/(Rmin (delta/2) ((b-c)/2))<=0``.
Intro; Cut ``-l<0``.
Intro; Unfold Rminus in H12.
Cut ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l<0``.
Intro; Cut ``(Rabsolu (((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l)) < l/2``.
Unfold Rabsolu; Case (case_Rabsolu ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l``); Intro.
Replace `` -(((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l)`` with ``l+ -(((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2)))``.
Intro; Generalize (Rlt_compatibility ``-l`` ``l+ -(((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2)))`` ``l/2`` H20); Repeat Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Replace ``-l+l/2`` with ``-(l/2)``.
Intro; Generalize (Rlt_Ropp ``-(((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2)))`` ``-(l/2)`` H21); Repeat Rewrite Ropp_Ropp; Intro; Generalize (Rlt_trans ``0`` ``l/2`` ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))`` H7 H22); Intro; Elim (Rlt_antirefl ``0`` (Rlt_le_trans ``0`` ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))`` ``0`` H23 H17)).
Field; DiscrR.
Ring.
Intro; Generalize (Rle_sym2 ``0`` ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l`` r); Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l`` ``0`` H21 H19)).
Assumption.
Rewrite <- Ropp_O; Replace ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l`` with ``-(l+ -(((f (c+(Rmin (delta/2) ((b+ -c)/2))))-(f c))/(Rmin (delta/2) ((b+ -c)/2))))``.
Apply Rgt_Ropp; Change ``0<l+ -(((f (c+(Rmin (delta/2) ((b+ -c)/2))))-(f c))/(Rmin (delta/2) ((b+ -c)/2)))``; Apply gt0_plus_ge0_is_gt0; [Assumption | Rewrite <- Ropp_O; Apply Rge_Ropp; Apply Rle_sym1; Assumption].
Ring.
Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Replace ``((f (c+(Rmin (delta/2) ((b-c)/2))))-(f c))/(Rmin (delta/2) ((b-c)/2))`` with ``- (((f c)-(f (c+(Rmin (delta/2) ((b-c)/2)))))/(Rmin (delta/2) ((b-c)/2)))``.
Rewrite <- Ropp_O; Apply Rge_Ropp; Apply Rle_sym1; Unfold Rdiv; Apply Rmult_le_pos; [Generalize (Rle_compatibility_r ``-(f (c+(Rmin (delta*/2) ((b-c)*/2))))`` ``(f (c+(Rmin (delta*/2) ((b-c)*/2))))`` (f c) H16); Rewrite Rplus_Ropp_r; Intro; Assumption | Left; Apply Rlt_Rinv; Assumption].
Field; Assumption.
Generalize (Rmin_r ``(delta/2)`` ``((b-c)/2)``); Intro; Generalize (Rle_compatibility ``c`` ``(Rmin (delta/2) ((b-c)/2))`` ``(b-c)/2`` H14); Intro; Apply Rle_lt_trans with ``c+(b-c)/2``.
Assumption.
Apply Rlt_monotony_contra with ``2``.
Apply Rgt_2_0.
Replace ``2*(c+(b-c)/2)`` with ``c+b``.
Replace ``2*b`` with ``b+b``.
Apply Rlt_compatibility_r; Assumption.
Ring.
Field; DiscrR.
Apply Rlt_trans with c.
Assumption.
Pattern 1 c; Rewrite <- (Rplus_Or c); Apply Rlt_compatibility; Assumption.
Cut ``0<delta/2``.
Intro; Apply (Rmin_stable_in_posreal (mkposreal ``delta/2`` H13) (mkposreal ``(b-c)/2`` H9)).
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Apply Rgt_2_0].
Unfold Rabsolu; Case (case_Rabsolu (Rmin ``delta/2`` ``(b-c)/2``)).
Intro.
Cut ``0<delta/2``.
Intro.
Generalize (Rmin_stable_in_posreal (mkposreal ``delta/2`` H11) (mkposreal ``(b-c)/2`` H9)); Simpl; Intro; Elim (Rlt_antirefl ``0`` (Rlt_trans ``0`` ``(Rmin (delta/2) ((b-c)/2))`` ``0`` H12 r)).
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Apply Rgt_2_0].
Intro; Apply Rle_lt_trans with ``delta/2``.
Apply Rmin_l.
Unfold Rdiv; Apply Rlt_monotony_contra with ``2``.
Apply Rgt_2_0.
Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l.
Replace ``2*delta`` with ``delta+delta``. 
Pattern 2 delta; Rewrite <- (Rplus_Or delta); Apply Rlt_compatibility.
Rewrite Rplus_Or; Apply (cond_pos delta).
Ring.
DiscrR.
Cut ``0<delta/2``.
Intro; Generalize (Rmin_stable_in_posreal (mkposreal ``delta/2`` H10) (mkposreal ``(b-c)/2`` H9)); Simpl; Intro; Red; Intro; Rewrite H12 in H11; Elim (Rlt_antirefl ``0`` H11).
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Apply Rgt_2_0].
Unfold Rdiv; Apply Rmult_lt_pos.
Generalize (Rlt_compatibility_r ``-c`` c b H0); Rewrite Rplus_Ropp_r; Intro; Assumption.
Apply Rlt_Rinv; Apply Rgt_2_0.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rgt_2_0].
Elim H3; Intro.
Symmetry; Assumption.
Generalize (derivable_derive f c H1); Intro; Elim H5; Intros l H6; Rewrite H6 in H4; Generalize (derive_pt_def_1 f c l H6); Intro; Cut ``0< -(l/2)``.
Intro; Elim (H7 ``-(l/2)`` H8); Intros delta H9.
Cut ``0<(c-a)/2``.
Intro; Cut ``(Rmax (-(delta/2)) ((a-c)/2))<0``.
Intro; Cut ``(Rmax (-(delta/2)) ((a-c)/2))<>0``.
Intro; Cut ``(Rabsolu (Rmax (-(delta/2)) ((a-c)/2)))<delta``.
Intro; Generalize (H9 ``(Rmax (-(delta/2)) ((a-c)/2))`` H12 H13); Intro; Cut ``a<c+(Rmax (-(delta/2)) ((a-c)/2))``.
Cut ``c+(Rmax (-(delta/2)) ((a-c)/2))<b``.
Intros; Generalize (H2 ``c+(Rmax (-(delta/2)) ((a-c)/2))`` H16 H15); Intro; Cut ``0<=((f (c+(Rmax (-(delta/2)) ((a-c)/2))))-(f c))/(Rmax (-(delta/2)) ((a-c)/2))``.
Intro; Cut ``0< -l``.
Intro; Unfold Rminus in H14; Cut ``0<((f (c+(Rmax (-(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax (-(delta/2)) ((a+ -c)/2))+ -l``.
Intro; Cut ``(Rabsolu (((f (c+(Rmax (-(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax (-(delta/2)) ((a+ -c)/2))+ -l)) < -(l/2)``.
Unfold Rabsolu; Case (case_Rabsolu ``((f (c+(Rmax (-(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax (-(delta/2)) ((a+ -c)/2))+ -l``).
Intro; Elim (Rlt_antirefl ``0`` (Rlt_trans ``0`` ``((f (c+(Rmax ( -(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax ( -(delta/2)) ((a+ -c)/2))+ -l`` ``0`` H20 r)).
Intros; Generalize (Rlt_compatibility_r ``l`` ``(((f (c+(Rmax (-(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax (-(delta/2)) ((a+ -c)/2)))+ -l`` ``-(l/2)`` H21); Repeat Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Replace ``-(l/2)+l`` with ``l/2``.
Cut ``l/2<0``.
Intros; Generalize (Rlt_trans ``((f (c+(Rmax ( -(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax ( -(delta/2)) ((a+ -c)/2))`` ``l/2`` ``0`` H23 H22); Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` ``((f (c+(Rmax ( -(delta/2)) ((a-c)/2))))-(f c))/(Rmax ( -(delta/2)) ((a-c)/2))`` ``0`` H18 H24)).
Rewrite <- (Ropp_Ropp ``l/2``); Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Field; DiscrR.
Assumption.
Apply ge0_plus_gt0_is_gt0; Assumption.
Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Unfold Rdiv; Replace ``((f (c+(Rmax ( -(delta*/2)) ((a-c)*/2))))-(f c))*/(Rmax ( -(delta*/2)) ((a-c)*/2))`` with ``(-((f (c+(Rmax ( -(delta*/2)) ((a-c)*/2))))-(f c)))*/(-(Rmax ( -(delta*/2)) ((a-c)*/2)))``.
Apply Rmult_le_pos.
Generalize (Rle_compatibility ``-(f (c+(Rmax (-(delta*/2)) ((a-c)*/2))))`` ``(f (c+(Rmax (-(delta*/2)) ((a-c)*/2))))`` (f c) H17); Rewrite Rplus_Ropp_l; Replace ``-((f (c+(Rmax ( -(delta*/2)) ((a-c)*/2))))-(f c))`` with ``-((f (c+(Rmax ( -(delta*/2)) ((a-c)*/2)))))+(f c)``.
Intro; Assumption.
Ring.
Left; Apply Rlt_Rinv; Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Field; Apply prod_neq_R0; [Apply Ropp_neq; Assumption | Assumption].
Generalize (Rlt_compatibility c ``(Rmax ( -(delta/2)) ((a-c)/2))`` ``0`` H11); Rewrite Rplus_Or; Intro; Apply Rlt_trans with ``c``; Assumption.
Generalize (RmaxLess2 ``(-(delta/2))`` ``((a-c)/2)``); Intro; Generalize (Rle_compatibility c ``(a-c)/2`` ``(Rmax ( -(delta/2)) ((a-c)/2))`` H15); Intro; Apply Rlt_le_trans with ``c+(a-c)/2``.
Apply Rlt_monotony_contra with ``2``.
Apply Rgt_2_0.
Replace ``2*(c+(a-c)/2)`` with ``a+c``.
Replace ``2*a`` with ``a+a``.
Apply Rlt_compatibility; Assumption.
Ring.
Field; DiscrR.
Assumption.
Unfold Rabsolu; Case (case_Rabsolu (Rmax ``-(delta/2)`` ``(a-c)/2``)).
Intro; Generalize (RmaxLess1 ``-(delta/2)`` ``(a-c)/2``); Intro; Generalize (Rle_Ropp ``-(delta/2)`` ``(Rmax ( -(delta/2)) ((a-c)/2))`` H13); Rewrite Ropp_Ropp; Intro; Generalize (Rle_sym2 ``-(Rmax ( -(delta/2)) ((a-c)/2))`` ``delta/2`` H14); Intro; Apply Rle_lt_trans with ``delta/2``.
Assumption.
Apply Rlt_monotony_contra with ``2``. 
Apply Rgt_2_0.
Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Replace ``2*delta`` with ``delta+delta``.
Pattern 2 delta; Rewrite <- (Rplus_Or delta); Apply Rlt_compatibility; Rewrite Rplus_Or; Apply (cond_pos delta).
Ring. 
DiscrR.
Cut ``-(delta/2) < 0``.
Cut ``(a-c)/2<0``.
Intros; Generalize (Rmax_stable_in_negreal (mknegreal ``-(delta/2)`` H14) (mknegreal ``(a-c)/2`` H13)); Simpl; Intro; Generalize (Rle_sym2 ``0`` ``(Rmax ( -(delta/2)) ((a-c)/2))`` r); Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` ``(Rmax ( -(delta/2)) ((a-c)/2))`` ``0`` H16 H15)).
Rewrite <- Ropp_O; Rewrite <- (Ropp_Ropp ``(a-c)/2``); Apply Rlt_Ropp; Replace ``-((a-c)/2)`` with ``(c-a)/2``; [Assumption | Field; DiscrR].
Rewrite <- Ropp_O; Apply Rlt_Ropp; Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply (Rlt_Rinv ``2`` Rgt_2_0)].
Red; Intro; Rewrite H12 in H11; Elim (Rlt_antirefl ``0`` H11).
Cut ``(a-c)/2<0``.
Intro; Cut ``-(delta/2)<0``.
Intro; Apply (Rmax_stable_in_negreal (mknegreal ``-(delta/2)`` H12) (mknegreal ``(a-c)/2`` H11)).
Rewrite <- Ropp_O; Apply Rlt_Ropp; Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply (Rlt_Rinv ``2`` Rgt_2_0)].
Rewrite <- Ropp_O; Rewrite <- (Ropp_Ropp ``(a-c)/2``); Apply Rlt_Ropp; Replace ``-((a-c)/2)`` with ``(c-a)/2``; [Assumption | Field; DiscrR].
Unfold Rdiv; Apply Rmult_lt_pos; [Generalize (Rlt_compatibility_r ``-a`` a c H); Rewrite Rplus_Ropp_r; Intro; Assumption | Apply (Rlt_Rinv ``2`` Rgt_2_0)].
Replace ``-(l/2)`` with ``(-l)/2``; [Unfold Rdiv; Apply Rmult_lt_pos; [Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption | Apply (Rlt_Rinv ``2`` Rgt_2_0)] | Field; DiscrR].
Save.

Theorem deriv_minimum : (f:R->R;a,b,c:R) ``a<c``->``c<b``->(derivable_pt f c)->((x:R) ``a<x``->``x<b``->``(f c)<=(f x)``)->``(derive_pt f c)==0``.
Intros; Generalize (opposite_derivable_pt f c H1); Intro; Rewrite <- (Ropp_Ropp (derive_pt f c)); Apply eq_RoppO; Rewrite <- (deriv_opposite f c H1); Apply (deriv_maximum (opp_fct f) a b c H H0 H3); Intros; Unfold opp_fct; Apply Rge_Ropp; Apply Rle_sym1; Apply (H2 x H4 H5).
Save.

Theorem deriv_constant2 : (f:R->R;a,b,c:R) ``a<c``->``c<b``->(derivable_pt f c)->((x:R) ``a<x``->``x<b``->``(f x)==(f c)``)->``(derive_pt f c)==0``.
Intros; Apply (deriv_maximum f a b c H H0 H1); Intros; Right; Apply (H2 x H3 H4).
Save.

(**********)
Lemma nonneg_derivative_0 : (f:R->R) (derivable f)->(increasing f) -> ((x:R) ``0<=(derive_pt f x)``).
Intros; Unfold increasing in H0; Generalize (derivable_derive f x (H x)); Intro; Elim H1; Intros l H2.
Rewrite H2; Case (total_order R0 l); Intro.
Left; Assumption.
Elim H3; Intro.
Right; Assumption.
Generalize (derive_pt_def_1 f x l H2); Intros; Cut ``0< -(l/2)``.
Intro; Elim (H5 ``-(l/2)`` H6); Intros delta H7; Cut ``delta/2<>0``/\``0<delta/2``/\``(Rabsolu delta/2)<delta``.
Intro; Decompose [and] H8; Intros; Generalize (H7 ``delta/2`` H9 H12); Cut ``0<=((f (x+delta/2))-(f x))/(delta/2)``.
Intro; Cut ``0<=((f (x+delta/2))-(f x))/(delta/2)-l``.
Intro; Unfold Rabsolu; Case (case_Rabsolu ``((f (x+delta/2))-(f x))/(delta/2)-l``).
Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` ``((f (x+delta/2))-(f x))/(delta/2)-l`` ``0`` H13 r)).
Intros; Generalize (Rlt_compatibility_r l ``((f (x+delta/2))-(f x))/(delta/2)-l`` ``-(l/2)`` H14); Unfold Rminus; Replace ``-(l/2)+l`` with ``l/2``.
Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Intro; Generalize (Rle_lt_trans ``0`` ``((f (x+delta/2))-(f x))/(delta/2)`` ``l/2`` H10 H15); Intro; Cut ``l/2<0``.
Intro; Elim (Rlt_antirefl ``0`` (Rlt_trans ``0`` ``l/2`` ``0`` H16 H17)).
Rewrite <- Ropp_O in H6; Generalize (Rlt_Ropp ``-0`` ``-(l/2)`` H6); Repeat Rewrite Ropp_Ropp; Intro; Assumption.
Field; DiscrR.
Unfold Rminus; Apply ge0_plus_ge0_is_ge0.
Unfold Rdiv; Apply Rmult_le_pos.
Cut ``x<=(x+(delta*/2))``.
Intro; Generalize (H0 x ``x+(delta*/2)`` H13); Intro; Generalize (Rle_compatibility ``-(f x)`` ``(f x)`` ``(f (x+delta*/2))`` H14); Rewrite Rplus_Ropp_l; Rewrite Rplus_sym; Intro; Assumption.
Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Left; Assumption.
Left; Apply Rlt_Rinv; Assumption.
Left; Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Unfold Rdiv; Apply Rmult_le_pos.
Cut ``x<=(x+(delta*/2))``.
Intro; Generalize (H0 x ``x+(delta*/2)`` H10); Intro; Generalize (Rle_compatibility ``-(f x)`` ``(f x)`` ``(f (x+delta*/2))`` H13); Rewrite Rplus_Ropp_l; Rewrite Rplus_sym; Intro; Assumption.
Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Left; Assumption.
Left; Apply Rlt_Rinv; Assumption.
Split.
Unfold Rdiv; Apply prod_neq_R0.
Generalize (cond_pos delta); Intro; Red; Intro H9; Rewrite H9 in H8; Elim (Rlt_antirefl ``0`` H8).
Apply Rinv_neq_R0; DiscrR.
Split.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Apply Rgt_2_0].
Unfold Rabsolu; Case (case_Rabsolu ``delta/2``).
Unfold Rdiv; Intro; Generalize (Rlt_monotony_r ``2`` ``delta*/2`` ``0`` Rgt_2_0 r); Rewrite Rmult_Ol; Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Intro; Elim (Rlt_antirefl ``0`` (Rlt_trans ``0`` delta ``0`` (cond_pos delta) H8)).
DiscrR.
Intro; Unfold Rdiv; Pattern 1 delta; Replace ``(pos delta)`` with ``2*(delta*/2)``.
Replace ``2*(delta*/2)`` with ``delta*/2+delta*/2``.
Pattern 2 delta; Rewrite <- (Rplus_Or ``delta*/2``).
Apply Rlt_compatibility.
Rewrite Rplus_Or.
Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Apply Rgt_2_0].
Ring.
Field; DiscrR.
Rewrite <- Ropp_O; Apply Rlt_Ropp; Unfold Rdiv; Generalize (Rlt_monotony_r ``/2`` l ``0`` (Rlt_Rinv ``2`` Rgt_2_0) H4); Rewrite Rmult_Ol; Intro; Assumption.
Save.

(**********)
Axiom nonneg_derivative_1 : (f:R->R) (derivable f)->((x:R) ``0<=(derive_pt f x)``) -> (increasing f).

(**********)
Lemma nonpos_derivative_0 : (f:R->R) (derivable f)->(decreasing f) -> ((x:R) ``(derive_pt f x)<=0``).
Intros; Unfold decreasing in H0; Generalize (derivable_derive f x (H x)); Intro; Elim H1; Intros l H2.
Rewrite H2; Case (total_order l R0); Intro.
Left; Assumption.
Elim H3; Intro.
Right; Assumption.
Generalize (derive_pt_def_1 f x l H2); Intros; Cut ``0< (l/2)``.
Intro; Elim (H5 ``(l/2)`` H6); Intros delta H7; Cut ``delta/2<>0``/\``0<delta/2``/\``(Rabsolu delta/2)<delta``.
Intro; Decompose [and] H8; Intros; Generalize (H7 ``delta/2`` H9 H12); Cut ``((f (x+delta/2))-(f x))/(delta/2)<=0``.
Intro; Cut ``0< -(((f (x+delta/2))-(f x))/(delta/2)-l)``.
Intro; Unfold Rabsolu; Case (case_Rabsolu ``((f (x+delta/2))-(f x))/(delta/2)-l``).
Intros; Generalize (Rlt_compatibility_r ``-l`` ``-(((f (x+delta/2))-(f x))/(delta/2)-l)`` ``(l/2)`` H14); Unfold Rminus.
Replace ``(l/2)+ -l`` with ``-(l/2)``.
Replace `` -(((f (x+delta/2))+ -(f x))/(delta/2)+ -l)+ -l`` with ``-(((f (x+delta/2))+ -(f x))/(delta/2))``.
Intro.
Generalize (Rlt_Ropp ``-(((f (x+delta/2))+ -(f x))/(delta/2))`` ``-(l/2)`` H15). 
Repeat Rewrite Ropp_Ropp.
Intro.
Generalize (Rlt_trans ``0`` ``l/2`` ``((f (x+delta/2))-(f x))/(delta/2)`` H6 H16); Intro.
Elim (Rlt_antirefl ``0`` (Rlt_le_trans ``0`` ``((f (x+delta/2))-(f x))/(delta/2)`` ``0`` H17 H10)).
Ring.
Field; DiscrR.
Intros.
Generalize (Rge_Ropp ``((f (x+delta/2))-(f x))/(delta/2)-l`` ``0`` r).
Rewrite Ropp_O.
Intro.
Elim (Rlt_antirefl ``0`` (Rlt_le_trans ``0`` ``-(((f (x+delta/2))-(f x))/(delta/2)-l)`` ``0`` H13 H15)).
Replace ``-(((f (x+delta/2))-(f x))/(delta/2)-l)`` with ``(((f (x))-(f (x+delta/2)))/(delta/2)) +l``.
Unfold Rminus.
Apply ge0_plus_gt0_is_gt0.
Unfold Rdiv; Apply Rmult_le_pos.
Cut ``x<=(x+(delta*/2))``.
Intro; Generalize (H0 x ``x+(delta*/2)`` H13); Intro; Generalize (Rle_compatibility ``-(f (x+delta/2))`` ``(f (x+delta/2))`` ``(f x)`` H14); Rewrite Rplus_Ropp_l; Rewrite Rplus_sym; Intro; Assumption.
Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Left; Assumption.
Left; Apply Rlt_Rinv; Assumption.
Assumption.
Field.
DiscrR.
Case delta; Intros.
Apply prod_neq_R0.
Red; Intro H13; Rewrite H13 in cond_pos; Elim (Rlt_antirefl ``0`` cond_pos).
Apply Rinv_neq_R0; DiscrR.
Replace ``((f (x+delta/2))-(f x))/(delta/2)`` with ``-(((f x)-(f (x+delta/2)))/(delta/2))``.
Rewrite <- Ropp_O.
Apply Rge_Ropp.
Apply Rle_sym1.
Unfold Rdiv; Apply Rmult_le_pos.
Cut ``x<=(x+(delta*/2))``.
Intro; Generalize (H0 x ``x+(delta*/2)`` H10); Intro.
Generalize (Rle_compatibility ``-(f (x+delta/2))`` ``(f (x+delta/2))`` ``(f x)`` H13); Rewrite Rplus_Ropp_l; Rewrite Rplus_sym; Intro; Assumption.
Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Left; Assumption.
Left; Apply Rlt_Rinv; Assumption.
Field.
Case delta; Intros.
Apply prod_neq_R0.
Red; Intro H13; Rewrite H13 in cond_pos; Elim (Rlt_antirefl ``0`` cond_pos).
Apply Rinv_neq_R0; DiscrR.
Split.
Unfold Rdiv; Apply prod_neq_R0.
Generalize (cond_pos delta); Intro; Red; Intro H9; Rewrite H9 in H8; Elim (Rlt_antirefl ``0`` H8).
Apply Rinv_neq_R0; DiscrR.
Split.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Apply Rgt_2_0].
Unfold Rabsolu; Case (case_Rabsolu ``delta/2``).
Unfold Rdiv; Intro; Generalize (Rlt_monotony_r ``2`` ``delta*/2`` ``0`` Rgt_2_0 r); Rewrite Rmult_Ol; Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Intro; Elim (Rlt_antirefl ``0`` (Rlt_trans ``0`` delta ``0`` (cond_pos delta) H8)).
DiscrR.
Intro; Unfold Rdiv; Pattern 1 delta; Replace ``(pos delta)`` with ``2*(delta*/2)``.
Replace ``2*(delta*/2)`` with ``delta*/2+delta*/2``.
Pattern 2 delta; Rewrite <- (Rplus_Or ``delta*/2``).
Apply Rlt_compatibility.
Rewrite Rplus_Or.
Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Apply Rgt_2_0].
Ring.
Field; DiscrR.
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv; Apply Rgt_2_0.
Save.

(**********)
Lemma increasing_decreasing_opp : (f:R->R) (increasing f) -> (decreasing (opp_fct f)).
Unfold increasing decreasing opp_fct; Intros; Generalize (H x y H0); Intro; Apply Rge_Ropp; Apply Rle_sym1; Assumption.
Save.

(**********)
Lemma opp_opp_fct : (f:R->R) (opp_fct (opp_fct f))==f.
Intro; Unfold opp_fct; Apply fct_eq; Intro; Rewrite Ropp_Ropp; Reflexivity.
Save.

(**********)
Lemma nonpos_derivative_1 : (f:R->R) (derivable f)->((x:R) ``(derive_pt f x)<=0``) -> (decreasing f).
Intros; Rewrite <- (opp_opp_fct f); Apply increasing_decreasing_opp.
Cut (derivable (opp_fct f)).
Cut (x:R)``0<=(derive_pt (opp_fct f) x)``.
Intros; Apply (nonneg_derivative_1 (opp_fct f) H2 H1).
Intros; Rewrite (deriv_opposite f x (H x)); Rewrite <- Ropp_O; Apply Rge_Ropp; Apply Rle_sym1; Apply (H0 x).
Apply (opposite_derivable f H).
Save.

(**********)
Axiom positive_derivative : (f:R->R) (derivable f)->((x:R) ``0<(derive_pt f x)``)->(strict_increasing f).

(**********)
Lemma strictincreasing_strictdecreasing_opp : (f:R->R) (strict_increasing f) -> (strict_decreasing (opp_fct f)).
Unfold strict_increasing strict_decreasing opp_fct; Intros; Generalize (H x y H0); Intro; Apply Rlt_Ropp; Assumption.
Save.

(**********)
Lemma negative_derivative : (f:R->R) (derivable f)->((x:R) ``(derive_pt f x)<0``)->(strict_decreasing f).
Intros; Rewrite <- (opp_opp_fct f); Apply strictincreasing_strictdecreasing_opp.
Cut (derivable (opp_fct f)).
Cut (x:R)``0<(derive_pt (opp_fct f) x)``.
Intros; Apply (positive_derivative (opp_fct f) H2 H1).
Intros; Rewrite (deriv_opposite f x (H x)); Rewrite <- Ropp_O; Apply Rlt_Ropp; Apply (H0 x).
Apply (opposite_derivable f H).
Save.

(**********)
Lemma null_derivative_0 : (f:R->R) (constant f)->((x:R) ``(derive_pt f x)==0``). 
Intros; Unfold constant in H; Apply derive_pt_def_0; Intros; Exists (mkposreal ``1`` Rlt_R0_R1); Intros; Rewrite (H x ``x+h``); Unfold Rminus; Unfold Rdiv; Rewrite Rplus_Ropp_r; Rewrite Rmult_Ol; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Save.

(**********)
Lemma increasing_decreasing : (f:R->R) (increasing f) -> (decreasing f) -> (constant f).
Unfold increasing decreasing constant; Intros; Case (total_order x y); Intro.
Generalize (Rlt_le x y H1); Intro; Apply (Rle_antisym (f x) (f y) (H x y H2) (H0 x y H2)).
Elim H1; Intro.
Rewrite H2; Reflexivity.
Generalize (Rlt_le y x H2); Intro; Symmetry; Apply (Rle_antisym (f y) (f x) (H y x H3) (H0 y x H3)).
Save.

(**********)
Lemma null_derivative_1 : (f:R->R) (derivable f)->((x:R) ``(derive_pt f x)==0``)->(constant f).
Intros.
Cut (x:R)``(derive_pt f x) <= 0``.
Cut (x:R)``0 <= (derive_pt f x)``.
Intros.
Generalize (nonneg_derivative_1 f H H1); Intro.
Generalize (nonpos_derivative_1 f H H2); Intro.
Apply increasing_decreasing; Assumption.
Intro.
Right; Symmetry; Apply (H0 x).
Intro; Right; Apply (H0 x).
Save.

(**********)
Axiom derive_increasing_interv_ax : (a,b:R;f:R->R) ``a<b``-> (((t:R) ``a<t<b`` -> ``0<(derive_pt f t)``) -> ((x,y:R) ``a<=x<=b``->``a<=y<=b``->``x<y``->``(f x)<(f y)``)) /\ (((t:R) ``a<t<b`` -> ``0<=(derive_pt f t)``) -> ((x,y:R) ``a<=x<=b``->``a<=y<=b``->``x<y``->``(f x)<=(f y)``)).

(**********)
Lemma derive_increasing_interv : (a,b:R;f:R->R) ``a<b``-> ((t:R) ``a<t<b`` -> ``0<(derive_pt f t)``) -> ((x,y:R) ``a<=x<=b``->``a<=y<=b``->``x<y``->``(f x)<(f y)``).
Intros; Generalize (derive_increasing_interv_ax a b f H); Intro; Elim H4; Intros H5 _; Apply (H5 H0 x y H1 H2 H3).
Save.

(**********)
Lemma derive_increasing_interv_var : (a,b:R;f:R->R) ``a<b``-> ((t:R) ``a<t<b`` -> ``0<=(derive_pt f t)``) -> ((x,y:R) ``a<=x<=b``->``a<=y<=b``->``x<y``->``(f x)<=(f y)``).
Intros; Generalize (derive_increasing_interv_ax a b f H); Intro; Elim H4; Intros _ H5; Apply (H5 H0 x y H1 H2 H3).
Save.

(**********)
(**********)
Axiom IAF : (f,g:R->R;a,b:R) ``a<=b`` -> (derivable f) -> (derivable g) -> ((c:R) ``a<=c<=b`` -> ``(derive_pt g c)<=(derive_pt f c)``) -> ``(g b)-(g a)<=(f b)-(f a)``. 

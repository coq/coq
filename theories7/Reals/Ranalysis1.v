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
Require Export Rlimit.
Require Export Rderiv.
V7only [Import R_scope.]. Open Local Scope R_scope.
Implicit Variable Type f:R->R.

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
Definition inv_fct [f:R->R] : R->R := [x:R]``/(f x)``.

V8Infix "+" plus_fct : Rfun_scope.
V8Notation "- x" := (opp_fct x) : Rfun_scope.
V8Infix "*" mult_fct : Rfun_scope.
V8Infix "-" minus_fct : Rfun_scope.
V8Infix "/" div_fct : Rfun_scope.
Notation Local "f1 'o' f2" := (comp f1 f2) (at level 2, right associativity)
  : Rfun_scope 
  V8only (at level 20, right associativity).
V8Notation "/ x" := (inv_fct x) : Rfun_scope.

Delimits Scope Rfun_scope with F.

Definition fct_cte [a:R] : R->R := [x:R]a.
Definition id := [x:R]x.

(****************************************************)
(**            Variations of functions              *)
(****************************************************)
Definition increasing [f:R->R] : Prop := (x,y:R) ``x<=y``->``(f x)<=(f y)``.
Definition decreasing [f:R->R] : Prop := (x,y:R) ``x<=y``->``(f y)<=(f x)``.
Definition strict_increasing [f:R->R] : Prop := (x,y:R) ``x<y``->``(f x)<(f y)``.
Definition strict_decreasing [f:R->R] : Prop := (x,y:R) ``x<y``->``(f y)<(f x)``.
Definition constant [f:R->R] : Prop := (x,y:R) ``(f x)==(f y)``.
  
(**********) 
Definition no_cond : R->Prop := [x:R] True.

(**********)
Definition constant_D_eq [f:R->R;D:R->Prop;c:R] : Prop := (x:R) (D x) -> (f x)==c.

(***************************************************)
(**      Definition of continuity as a limit       *)
(***************************************************)

(**********)
Definition continuity_pt [f:R->R; x0:R] : Prop := (continue_in f no_cond x0).
Definition continuity [f:R->R] : Prop := (x:R) (continuity_pt f x).

Arguments Scope continuity_pt [Rfun_scope R_scope].
Arguments Scope continuity [Rfun_scope].

(**********)
Lemma continuity_pt_plus : (f1,f2:R->R; x0:R) (continuity_pt f1 x0) -> (continuity_pt f2 x0) -> (continuity_pt (plus_fct f1 f2) x0).
Unfold continuity_pt plus_fct; Unfold continue_in; Intros; Apply limit_plus; Assumption.
Qed.

Lemma continuity_pt_opp : (f:R->R; x0:R) (continuity_pt f x0) -> (continuity_pt (opp_fct f) x0).
Unfold continuity_pt opp_fct; Unfold continue_in; Intros; Apply limit_Ropp; Assumption.
Qed.
 
Lemma continuity_pt_minus : (f1,f2:R->R; x0:R) (continuity_pt f1 x0) -> (continuity_pt f2 x0) -> (continuity_pt (minus_fct f1 f2) x0).
Unfold continuity_pt minus_fct; Unfold continue_in; Intros; Apply limit_minus; Assumption.
Qed.

Lemma continuity_pt_mult : (f1,f2:R->R; x0:R) (continuity_pt f1 x0) -> (continuity_pt f2 x0) -> (continuity_pt (mult_fct f1 f2) x0).
Unfold continuity_pt mult_fct; Unfold continue_in; Intros; Apply limit_mul; Assumption.
Qed.

Lemma continuity_pt_const : (f:R->R; x0:R) (constant f) -> (continuity_pt f x0).
Unfold constant continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Intros; Exists ``1``; Split; [Apply Rlt_R0_R1 | Intros; Generalize (H x x0); Intro; Rewrite H2; Simpl; Rewrite R_dist_eq; Assumption].
Qed.

Lemma continuity_pt_scal : (f:R->R;a:R; x0:R) (continuity_pt f x0) -> (continuity_pt (mult_real_fct a f) x0).
Unfold continuity_pt mult_real_fct; Unfold continue_in; Intros; Apply (limit_mul ([x:R] a) f (D_x no_cond x0) a (f x0) x0).
Unfold limit1_in; Unfold limit_in; Intros; Exists ``1``; Split.
Apply Rlt_R0_R1.
Intros; Rewrite R_dist_eq; Assumption.
Assumption.
Qed.

Lemma continuity_pt_inv : (f:R->R; x0:R) (continuity_pt f x0) -> ~``(f x0)==0`` -> (continuity_pt (inv_fct f) x0).
Intros.
Replace (inv_fct f) with [x:R]``/(f x)``.
Unfold continuity_pt; Unfold continue_in; Intros; Apply limit_inv; Assumption.
Unfold inv_fct; Reflexivity.
Qed.
 
Lemma div_eq_inv : (f1,f2:R->R) (div_fct f1 f2)==(mult_fct f1 (inv_fct f2)).
Intros; Reflexivity.
Qed.
 
Lemma continuity_pt_div : (f1,f2:R->R; x0:R) (continuity_pt f1 x0) -> (continuity_pt f2 x0) -> ~``(f2 x0)==0`` -> (continuity_pt (div_fct f1 f2) x0).
Intros; Rewrite -> (div_eq_inv f1 f2); Apply continuity_pt_mult; [Assumption | Apply continuity_pt_inv; Assumption].
Qed.

Lemma continuity_pt_comp : (f1,f2:R->R;x:R) (continuity_pt f1 x) -> (continuity_pt f2 (f1 x)) -> (continuity_pt (comp f2 f1) x).
Unfold continuity_pt; Unfold continue_in; Intros; Unfold comp.
Cut (limit1_in [x0:R](f2 (f1 x0)) (Dgf (D_x no_cond x) (D_x no_cond (f1 x)) f1)
(f2 (f1 x)) x) -> (limit1_in [x0:R](f2 (f1 x0)) (D_x no_cond x) (f2 (f1 x)) x).
Intro; Apply H1.
EApply limit_comp.
Apply H.
Apply H0.
Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Intros.
Assert H3 := (H1 eps H2).
Elim H3; Intros.
Exists x0.
Split.
Elim H4; Intros; Assumption.
Intros; Case (Req_EM (f1 x) (f1 x1)); Intro.
Rewrite H6; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Elim H4; Intros; Apply H8.
Split.
Unfold Dgf D_x no_cond.
Split.
Split.
Trivial.
Elim H5; Unfold D_x no_cond; Intros.
Elim H9; Intros; Assumption.
Split.
Trivial.
Assumption.
Elim H5; Intros; Assumption.
Qed.

(**********) 
Lemma continuity_plus : (f1,f2:R->R) (continuity f1)->(continuity f2)->(continuity (plus_fct f1 f2)).
Unfold continuity; Intros; Apply (continuity_pt_plus f1 f2 x (H x) (H0 x)).
Qed.

Lemma continuity_opp : (f:R->R) (continuity f)->(continuity (opp_fct f)).
Unfold continuity; Intros; Apply (continuity_pt_opp f x (H x)).
Qed.

Lemma continuity_minus : (f1,f2:R->R) (continuity f1)->(continuity f2)->(continuity (minus_fct f1 f2)).
Unfold continuity; Intros; Apply (continuity_pt_minus f1 f2 x (H x) (H0 x)).
Qed.
 
Lemma continuity_mult : (f1,f2:R->R) (continuity f1)->(continuity f2)->(continuity (mult_fct f1 f2)).
Unfold continuity; Intros; Apply (continuity_pt_mult f1 f2 x (H x) (H0 x)).
Qed.

Lemma continuity_const : (f:R->R) (constant f) -> (continuity f).
Unfold continuity; Intros; Apply (continuity_pt_const f x H).
Qed.

Lemma continuity_scal : (f:R->R;a:R) (continuity f) -> (continuity (mult_real_fct a f)).
Unfold continuity; Intros; Apply (continuity_pt_scal f a x (H x)).
Qed.
  
Lemma continuity_inv : (f:R->R) (continuity f)->((x:R) ~``(f x)==0``)->(continuity (inv_fct f)).
Unfold continuity; Intros; Apply (continuity_pt_inv f x (H x) (H0 x)).
Qed.

Lemma continuity_div : (f1,f2:R->R) (continuity f1)->(continuity f2)->((x:R) ~``(f2 x)==0``)->(continuity (div_fct f1 f2)).
Unfold continuity; Intros; Apply (continuity_pt_div f1 f2 x (H x) (H0 x) (H1 x)).
Qed.
 
Lemma continuity_comp : (f1,f2:R->R) (continuity f1) -> (continuity f2) -> (continuity (comp f2 f1)).
Unfold continuity; Intros.
Apply (continuity_pt_comp f1 f2 x (H x) (H0 (f1 x))).
Qed.


(*****************************************************)
(**  Derivative's definition using Landau's kernel   *)
(*****************************************************)

Definition derivable_pt_lim [f:R->R;x,l:R] : Prop := ((eps:R) ``0<eps``->(EXT delta : posreal | ((h:R) ~``h==0``->``(Rabsolu h)<delta`` -> ``(Rabsolu ((((f (x+h))-(f x))/h)-l))<eps``))).

Definition derivable_pt_abs [f:R->R;x:R] : R -> Prop := [l:R](derivable_pt_lim f x l).

Definition derivable_pt [f:R->R;x:R] := (SigT R (derivable_pt_abs f x)).
Definition derivable [f:R->R] := (x:R)(derivable_pt f x).

Definition derive_pt [f:R->R;x:R;pr:(derivable_pt f x)] := (projT1 ? ? pr).
Definition derive [f:R->R;pr:(derivable f)] := [x:R](derive_pt f x (pr x)).

Arguments Scope derivable_pt_lim [Rfun_scope R_scope].
Arguments Scope derivable_pt_abs [Rfun_scope R_scope R_scope].
Arguments Scope derivable_pt [Rfun_scope R_scope].
Arguments Scope derivable [Rfun_scope].
Arguments Scope derive_pt [Rfun_scope R_scope _].
Arguments Scope derive [Rfun_scope _].

Definition antiderivative [f,g:R->R;a,b:R] : Prop := ((x:R)``a<=x<=b``->(EXT pr : (derivable_pt g x) | (f x)==(derive_pt g x pr)))/\``a<=b``.
(************************************)
(** Class of differential functions *)
(************************************)
Record Differential : Type := mkDifferential {
d1 :> R->R;
cond_diff : (derivable d1) }.
 
Record Differential_D2 : Type := mkDifferential_D2 {
d2 :> R->R;
cond_D1 : (derivable d2);
cond_D2 : (derivable (derive d2 cond_D1)) }.

(**********)
Lemma unicite_step1 : (f:R->R;x,l1,l2:R) (limit1_in [h:R]``((f (x+h))-(f x))/h`` [h:R]``h<>0`` l1 R0) -> (limit1_in [h:R]``((f (x+h))-(f x))/h`` [h:R]``h<>0`` l2 R0) -> l1 == l2.
Intros; Apply (single_limit [h:R]``((f (x+h))-(f x))/h`` [h:R]``h<>0`` l1 l2 R0); Try Assumption.
Unfold adhDa; Intros; Exists ``alp/2``.
Split.
Unfold Rdiv; Apply prod_neq_R0.
Red; Intro; Rewrite H2 in H1; Elim (Rlt_antirefl ? H1).
Apply Rinv_neq_R0; DiscrR.
Unfold R_dist; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Unfold Rdiv; Rewrite Rabsolu_mult.
Replace ``(Rabsolu (/2))`` with ``/2``.
Replace (Rabsolu alp) with alp.
Apply Rlt_monotony_contra with ``2``.
Sup0.
Rewrite (Rmult_sym ``2``); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Idtac | DiscrR]; Rewrite Rmult_1r; Rewrite double; Pattern 1 alp; Replace alp with ``alp+0``; [Idtac | Ring]; Apply Rlt_compatibility; Assumption.
Symmetry; Apply Rabsolu_right; Left; Assumption.
Symmetry; Apply Rabsolu_right; Left; Change ``0</2``; Apply Rlt_Rinv; Sup0. 
Qed.

Lemma unicite_step2 : (f:R->R;x,l:R) (derivable_pt_lim f x l) -> (limit1_in [h:R]``((f (x+h))-(f x))/h`` [h:R]``h<>0`` l R0).
Unfold derivable_pt_lim; Intros; Unfold limit1_in; Unfold limit_in; Intros.
Assert H1 := (H eps H0).
Elim H1 ; Intros.
Exists (pos x0).
Split.
Apply (cond_pos x0).
Simpl; Unfold R_dist; Intros.
Elim H3; Intros.
Apply H2; [Assumption |Unfold Rminus in H5; Rewrite Ropp_O in H5; Rewrite Rplus_Or in H5; Assumption].
Qed.

Lemma unicite_step3 : (f:R->R;x,l:R) (limit1_in [h:R]``((f (x+h))-(f x))/h`` [h:R]``h<>0`` l R0) -> (derivable_pt_lim f x l).
Unfold limit1_in derivable_pt_lim; Unfold limit_in; Unfold dist; Simpl; Intros.
Elim (H eps H0).
Intros; Elim H1; Intros.
Exists (mkposreal x0 H2).
Simpl; Intros; Unfold R_dist in H3; Apply (H3 h).
Split; [Assumption | Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Assumption].
Qed.

Lemma unicite_limite : (f:R->R;x,l1,l2:R) (derivable_pt_lim f x l1) -> (derivable_pt_lim f x l2) -> l1==l2.
Intros.
Assert H1 := (unicite_step2 ? ? ? H).
Assert H2 := (unicite_step2 ? ? ? H0).
Assert H3 := (unicite_step1 ? ? ? ? H1 H2).
Assumption.
Qed.

Lemma derive_pt_eq : (f:R->R;x,l:R;pr:(derivable_pt f x)) (derive_pt f x pr)==l <-> (derivable_pt_lim f x l).
Intros; Split.
Intro; Assert H1 := (projT2 ? ? pr); Unfold derive_pt in H; Rewrite H in H1; Assumption.
Intro; Assert H1 := (projT2 ? ? pr); Unfold derivable_pt_abs in H1.
Assert H2 := (unicite_limite ? ? ? ? H H1).
Unfold derive_pt; Unfold derivable_pt_abs.
Symmetry; Assumption.
Qed.

(**********)
Lemma derive_pt_eq_0 : (f:R->R;x,l:R;pr:(derivable_pt f x)) (derivable_pt_lim f x l) -> (derive_pt f x pr)==l.
Intros; Elim (derive_pt_eq f x l pr); Intros.
Apply (H1 H).
Qed.

(**********)
Lemma derive_pt_eq_1 : (f:R->R;x,l:R;pr:(derivable_pt f x)) (derive_pt f x pr)==l -> (derivable_pt_lim f x l).
Intros; Elim (derive_pt_eq f x l pr); Intros.
Apply (H0 H).
Qed.


(********************************************************************)
(** Equivalence of this definition with the one using limit concept *)
(********************************************************************)
Lemma derive_pt_D_in : (f,df:R->R;x:R;pr:(derivable_pt f x)) (D_in f df no_cond x) <-> (derive_pt f x pr)==(df x).
Intros; Split.
Unfold D_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros.
Apply derive_pt_eq_0. 
Unfold derivable_pt_lim.
Intros; Elim (H eps H0); Intros alpha H1; Elim H1; Intros;  Exists (mkposreal alpha H2); Intros; Generalize (H3 ``x+h``); Intro; Cut ``x+h-x==h``; [Intro; Cut ``(D_x no_cond x (x+h))``/\``(Rabsolu (x+h-x)) < alpha``; [Intro; Generalize (H6 H8); Rewrite H7; Intro; Assumption | Split; [Unfold D_x; Split; [Unfold no_cond; Trivial | Apply Rminus_not_eq_right; Rewrite H7; Assumption] | Rewrite H7; Assumption]] | Ring].
Intro.
Assert H0 := (derive_pt_eq_1 f x (df x) pr H).
Unfold D_in; Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Intros.
Elim (H0 eps H1); Intros alpha H2; Exists (pos alpha); Split.
Apply (cond_pos alpha).
Intros; Elim H3; Intros; Unfold D_x in H4; Elim H4; Intros; Cut ``x0-x<>0``.
Intro; Generalize (H2 ``x0-x`` H8 H5); Replace ``x+(x0-x)`` with x0.
Intro; Assumption.
Ring.
Auto with real.
Qed.

Lemma derivable_pt_lim_D_in : (f,df:R->R;x:R) (D_in f df no_cond x) <-> (derivable_pt_lim f x (df x)).
Intros; Split.
Unfold D_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros.
Unfold derivable_pt_lim.
Intros; Elim (H eps H0); Intros alpha H1; Elim H1; Intros;  Exists (mkposreal alpha H2); Intros; Generalize (H3 ``x+h``); Intro; Cut ``x+h-x==h``; [Intro; Cut ``(D_x no_cond x (x+h))``/\``(Rabsolu (x+h-x)) < alpha``; [Intro; Generalize (H6 H8); Rewrite H7; Intro; Assumption | Split; [Unfold D_x; Split; [Unfold no_cond; Trivial | Apply Rminus_not_eq_right; Rewrite H7; Assumption] | Rewrite H7; Assumption]] | Ring].
Intro.
Unfold derivable_pt_lim in H.
Unfold D_in; Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Intros.
Elim (H eps H0); Intros alpha H2; Exists (pos alpha); Split.
Apply (cond_pos alpha).
Intros.
Elim H1; Intros; Unfold D_x in H3; Elim H3; Intros; Cut ``x0-x<>0``.
Intro; Generalize (H2 ``x0-x`` H7 H4); Replace ``x+(x0-x)`` with x0.
Intro; Assumption.
Ring.
Auto with real.
Qed.


(***********************************)
(**   derivability -> continuity   *)
(***********************************)
(**********)
Lemma derivable_derive : (f:R->R;x:R;pr:(derivable_pt f x)) (EXT l : R | (derive_pt f x pr)==l).
Intros; Exists (projT1  ? ? pr).
Unfold derive_pt; Reflexivity.
Qed.

Theorem derivable_continuous_pt : (f:R->R;x:R) (derivable_pt f x) -> (continuity_pt f x).
Intros.
Generalize (derivable_derive f x X); Intro.
Elim H; Intros l H1.
Cut l==((fct_cte l) x).
Intro.
Rewrite H0 in H1.
Generalize (derive_pt_D_in f (fct_cte l) x); Intro.
Elim (H2 X); Intros.
Generalize (H4 H1); Intro.
Unfold continuity_pt.
Apply (cont_deriv f (fct_cte l) no_cond x H5).
Unfold fct_cte; Reflexivity.
Qed.

Theorem derivable_continuous : (f:R->R) (derivable f) -> (continuity f).
Unfold derivable continuity; Intros.
Apply (derivable_continuous_pt f x (X x)).
Qed.

(****************************************************************)
(**                      Main rules                             *)
(****************************************************************)

Lemma derivable_pt_lim_plus : (f1,f2:R->R;x,l1,l2:R) (derivable_pt_lim f1 x l1) -> (derivable_pt_lim f2 x l2) -> (derivable_pt_lim (plus_fct f1 f2) x ``l1+l2``).
Intros.
Apply unicite_step3.
Assert H1 := (unicite_step2 ? ? ? H).
Assert H2 := (unicite_step2 ? ? ? H0).
Unfold  plus_fct.
Cut (h:R)``((f1 (x+h))+(f2 (x+h))-((f1 x)+(f2 x)))/h``==``((f1 (x+h))-(f1 x))/h+((f2 (x+h))-(f2 x))/h``.
Intro.
Generalize(limit_plus [h':R]``((f1 (x+h'))-(f1 x))/h'`` [h':R]``((f2 (x+h'))-(f2 x))/h'`` [h:R]``h <> 0`` l1 l2 ``0`` H1 H2).
Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Intros.
Elim (H4 eps H5); Intros.
Exists x0.
Elim H6; Intros.
Split.
Assumption.
Intros; Rewrite H3; Apply H8; Assumption.
Intro; Unfold Rdiv; Ring.
Qed.

Lemma derivable_pt_lim_opp : (f:R->R;x,l:R) (derivable_pt_lim f x l) -> (derivable_pt_lim (opp_fct f) x (Ropp l)).
Intros.
Apply unicite_step3.
Assert H1 := (unicite_step2 ? ? ? H).
Unfold opp_fct.
Cut (h:R) ``( -(f (x+h))- -(f x))/h``==(Ropp ``((f (x+h))-(f x))/h``).
Intro.
Generalize (limit_Ropp [h:R]``((f (x+h))-(f x))/h``[h:R]``h <> 0`` l ``0`` H1).
Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Intros.
Elim (H2 eps H3); Intros.
Exists x0.
Elim H4; Intros.
Split.
Assumption.
Intros; Rewrite H0; Apply H6; Assumption.
Intro; Unfold Rdiv; Ring.
Qed.

Lemma derivable_pt_lim_minus : (f1,f2:R->R;x,l1,l2:R) (derivable_pt_lim f1 x l1) -> (derivable_pt_lim f2 x l2) -> (derivable_pt_lim (minus_fct f1 f2) x ``l1-l2``).
Intros.
Apply unicite_step3.
Assert H1 := (unicite_step2 ? ? ? H).
Assert H2 := (unicite_step2 ? ? ? H0).
Unfold  minus_fct.
Cut (h:R)``((f1 (x+h))-(f1 x))/h-((f2 (x+h))-(f2 x))/h``==``((f1 (x+h))-(f2 (x+h))-((f1 x)-(f2 x)))/h``.
Intro.
Generalize (limit_minus [h':R]``((f1 (x+h'))-(f1 x))/h'`` [h':R]``((f2 (x+h'))-(f2 x))/h'`` [h:R]``h <> 0`` l1 l2 ``0`` H1 H2).
Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Intros.
Elim (H4 eps H5); Intros.
Exists x0.
Elim H6; Intros.
Split.
Assumption.
Intros; Rewrite <- H3; Apply H8; Assumption.
Intro; Unfold Rdiv; Ring.
Qed.

Lemma derivable_pt_lim_mult : (f1,f2:R->R;x,l1,l2:R) (derivable_pt_lim f1 x l1) -> (derivable_pt_lim f2 x l2) -> (derivable_pt_lim (mult_fct f1 f2) x ``l1*(f2 x)+(f1 x)*l2``).
Intros.
Assert H1 := (derivable_pt_lim_D_in f1 [y:R]l1 x).
Elim H1; Intros.
Assert H4 := (H3 H).
Assert H5 := (derivable_pt_lim_D_in f2 [y:R]l2 x).
Elim H5; Intros.
Assert H8 := (H7 H0).
Clear H1 H2 H3 H5 H6 H7.
Assert H1 := (derivable_pt_lim_D_in (mult_fct f1 f2) [y:R]``l1*(f2 x)+(f1 x)*l2`` x).
Elim H1; Intros.
Clear H1 H3.
Apply H2.
Unfold mult_fct.
Apply (Dmult no_cond [y:R]l1 [y:R]l2 f1 f2 x); Assumption.
Qed.

Lemma derivable_pt_lim_const : (a,x:R) (derivable_pt_lim (fct_cte a) x ``0``).
Intros; Unfold fct_cte derivable_pt_lim.
Intros; Exists (mkposreal ``1`` Rlt_R0_R1); Intros; Unfold Rminus; Rewrite Rplus_Ropp_r; Unfold Rdiv; Rewrite Rmult_Ol; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Qed.

Lemma derivable_pt_lim_scal : (f:R->R;a,x,l:R) (derivable_pt_lim f x l) -> (derivable_pt_lim (mult_real_fct a f) x ``a*l``).
Intros.
Assert H0 := (derivable_pt_lim_const a x).
Replace (mult_real_fct a f) with (mult_fct (fct_cte a) f).
Replace ``a*l`` with ``0*(f x)+a*l``; [Idtac | Ring].
Apply (derivable_pt_lim_mult (fct_cte a) f x ``0`` l); Assumption.
Unfold mult_real_fct mult_fct fct_cte; Reflexivity.
Qed.

Lemma derivable_pt_lim_id : (x:R) (derivable_pt_lim id x ``1``).
Intro; Unfold derivable_pt_lim.
Intros eps Heps; Exists (mkposreal eps Heps); Intros h H1 H2; Unfold id; Replace ``(x+h-x)/h-1`` with ``0``.
Rewrite Rabsolu_R0; Apply Rle_lt_trans with ``(Rabsolu h)``.
Apply Rabsolu_pos.
Assumption.
Unfold Rminus; Rewrite Rplus_assoc; Rewrite (Rplus_sym x); Rewrite Rplus_assoc.
Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Unfold Rdiv; Rewrite <- Rinv_r_sym.
Symmetry; Apply Rplus_Ropp_r.
Assumption.
Qed.

Lemma derivable_pt_lim_Rsqr : (x:R) (derivable_pt_lim Rsqr x ``2*x``).
Intro; Unfold derivable_pt_lim.
Unfold Rsqr; Intros eps Heps; Exists (mkposreal eps Heps); Intros h H1 H2; Replace ``((x+h)*(x+h)-x*x)/h-2*x`` with ``h``.
Assumption.
Replace ``(x+h)*(x+h)-x*x`` with ``2*x*h+h*h``; [Idtac | Ring].
Unfold Rdiv; Rewrite Rmult_Rplus_distrl.
Repeat Rewrite Rmult_assoc.
Repeat Rewrite <- Rinv_r_sym; [Idtac | Assumption].
Ring.
Qed.

Lemma derivable_pt_lim_comp : (f1,f2:R->R;x,l1,l2:R) (derivable_pt_lim f1 x l1) -> (derivable_pt_lim f2 (f1 x) l2) -> (derivable_pt_lim (comp f2 f1) x ``l2*l1``).
Intros; Assert H1 := (derivable_pt_lim_D_in f1 [y:R]l1 x).
Elim H1; Intros.
Assert H4 := (H3 H).
Assert H5 := (derivable_pt_lim_D_in f2 [y:R]l2 (f1 x)).
Elim H5; Intros.
Assert H8 := (H7 H0).
Clear H1 H2 H3 H5 H6 H7.
Assert H1 := (derivable_pt_lim_D_in (comp f2 f1) [y:R]``l2*l1`` x).
Elim H1; Intros.
Clear H1 H3; Apply H2.
Unfold comp; Cut (D_in [x0:R](f2 (f1 x0)) [y:R]``l2*l1`` (Dgf no_cond no_cond f1) x) -> (D_in [x0:R](f2 (f1 x0)) [y:R]``l2*l1`` no_cond x).
Intro; Apply H1.
Rewrite Rmult_sym; Apply (Dcomp no_cond no_cond [y:R]l1 [y:R]l2 f1 f2 x); Assumption.
Unfold Dgf D_in no_cond; Unfold limit1_in; Unfold limit_in; Unfold dist; Simpl; Unfold R_dist; Intros.
Elim (H1 eps H3); Intros.
Exists x0; Intros; Split.
Elim H5; Intros; Assumption.
Intros; Elim H5; Intros; Apply H9; Split.
Unfold D_x; Split.
Split; Trivial.
Elim H6; Intros; Unfold D_x in H10; Elim H10; Intros; Assumption.
Elim H6; Intros; Assumption.
Qed.

Lemma derivable_pt_plus : (f1,f2:R->R;x:R) (derivable_pt f1 x) -> (derivable_pt f2 x) -> (derivable_pt (plus_fct f1 f2) x).
Unfold derivable_pt; Intros.
Elim X; Intros.
Elim X0; Intros.
Apply Specif.existT with ``x0+x1``.
Apply derivable_pt_lim_plus; Assumption.
Qed.

Lemma derivable_pt_opp : (f:R->R;x:R) (derivable_pt f x) -> (derivable_pt (opp_fct f) x).
Unfold derivable_pt; Intros.
Elim X; Intros.
Apply Specif.existT with ``-x0``.
Apply derivable_pt_lim_opp; Assumption.
Qed.

Lemma derivable_pt_minus : (f1,f2:R->R;x:R) (derivable_pt f1 x) -> (derivable_pt f2 x) -> (derivable_pt (minus_fct f1 f2) x).
Unfold derivable_pt; Intros.
Elim X; Intros.
Elim X0; Intros.
Apply Specif.existT with ``x0-x1``.
Apply derivable_pt_lim_minus; Assumption.
Qed.

Lemma derivable_pt_mult : (f1,f2:R->R;x:R) (derivable_pt f1 x) -> (derivable_pt f2 x) -> (derivable_pt (mult_fct f1 f2) x).
Unfold derivable_pt; Intros.
Elim X; Intros.
Elim X0; Intros.
Apply Specif.existT with ``x0*(f2 x)+(f1 x)*x1``.
Apply derivable_pt_lim_mult; Assumption.
Qed.

Lemma derivable_pt_const : (a,x:R) (derivable_pt (fct_cte a) x).
Intros; Unfold derivable_pt.
Apply Specif.existT with ``0``.
Apply derivable_pt_lim_const.
Qed.

Lemma derivable_pt_scal : (f:R->R;a,x:R) (derivable_pt f x) -> (derivable_pt (mult_real_fct a f) x).
Unfold derivable_pt; Intros.
Elim X; Intros.
Apply Specif.existT with ``a*x0``.
Apply derivable_pt_lim_scal; Assumption.
Qed.

Lemma derivable_pt_id : (x:R) (derivable_pt id x).
Unfold derivable_pt; Intro.
Exists ``1``.
Apply derivable_pt_lim_id.
Qed.

Lemma derivable_pt_Rsqr : (x:R) (derivable_pt Rsqr x).
Unfold derivable_pt; Intro; Apply Specif.existT with ``2*x``.
Apply derivable_pt_lim_Rsqr.
Qed.

Lemma derivable_pt_comp : (f1,f2:R->R;x:R) (derivable_pt f1 x) -> (derivable_pt f2 (f1 x)) -> (derivable_pt (comp f2 f1) x).
Unfold derivable_pt; Intros.
Elim X; Intros.
Elim X0 ;Intros.
Apply Specif.existT with ``x1*x0``.
Apply derivable_pt_lim_comp; Assumption.
Qed.

Lemma derivable_plus : (f1,f2:R->R) (derivable f1) -> (derivable f2) -> (derivable (plus_fct f1 f2)).
Unfold derivable; Intros.
Apply (derivable_pt_plus ? ? x (X ?) (X0 ?)).
Qed.

Lemma derivable_opp : (f:R->R) (derivable f) -> (derivable (opp_fct f)).
Unfold derivable; Intros.
Apply (derivable_pt_opp ? x (X ?)).
Qed.

Lemma derivable_minus : (f1,f2:R->R) (derivable f1) -> (derivable f2) -> (derivable (minus_fct f1 f2)).
Unfold derivable; Intros.
Apply (derivable_pt_minus ? ? x (X ?) (X0 ?)).
Qed.

Lemma derivable_mult : (f1,f2:R->R) (derivable f1) -> (derivable f2) -> (derivable (mult_fct f1 f2)).
Unfold derivable; Intros.
Apply (derivable_pt_mult ? ? x (X ?) (X0 ?)).
Qed.

Lemma derivable_const : (a:R) (derivable (fct_cte a)).
Unfold derivable; Intros.
Apply derivable_pt_const.
Qed.

Lemma derivable_scal : (f:R->R;a:R) (derivable f) -> (derivable (mult_real_fct a f)).
Unfold derivable; Intros.
Apply (derivable_pt_scal ? a x (X ?)).
Qed.

Lemma derivable_id : (derivable id).
Unfold derivable; Intro; Apply derivable_pt_id.
Qed.

Lemma derivable_Rsqr : (derivable Rsqr).
Unfold derivable; Intro; Apply derivable_pt_Rsqr.
Qed.

Lemma derivable_comp : (f1,f2:R->R) (derivable f1) -> (derivable f2) -> (derivable (comp f2 f1)).
Unfold derivable; Intros.
Apply (derivable_pt_comp ? ? x (X ?) (X0 ?)).
Qed.

Lemma derive_pt_plus : (f1,f2:R->R;x:R;pr1:(derivable_pt f1 x);pr2:(derivable_pt f2 x)) ``(derive_pt (plus_fct f1 f2) x (derivable_pt_plus ? ? ? pr1 pr2)) == (derive_pt f1 x pr1) + (derive_pt f2 x pr2)``.
Intros.
Assert H := (derivable_derive f1 x pr1).
Assert H0 := (derivable_derive f2 x pr2).
Assert H1 := (derivable_derive (plus_fct f1 f2) x (derivable_pt_plus ? ? ? pr1 pr2)).
Elim H; Clear H; Intros l1 H.
Elim H0; Clear H0; Intros l2 H0.
Elim H1; Clear H1; Intros l H1.
Rewrite H; Rewrite H0; Apply derive_pt_eq_0.
Assert H3 := (projT2 ? ? pr1).
Unfold derive_pt in H; Rewrite H in H3.
Assert H4 := (projT2 ? ? pr2).
Unfold derive_pt in H0; Rewrite H0 in H4.
Apply derivable_pt_lim_plus; Assumption.
Qed.

Lemma derive_pt_opp : (f:R->R;x:R;pr1:(derivable_pt f x)) ``(derive_pt (opp_fct f) x (derivable_pt_opp ? ? pr1)) == -(derive_pt f x pr1)``.
Intros.
Assert H := (derivable_derive f x pr1).
Assert H0 := (derivable_derive (opp_fct f) x (derivable_pt_opp ? ? pr1)).
Elim H; Clear H; Intros l1 H.
Elim H0; Clear H0; Intros l2 H0.
Rewrite H; Apply derive_pt_eq_0.
Assert H3 := (projT2 ? ? pr1).
Unfold derive_pt in H; Rewrite H in H3.
Apply derivable_pt_lim_opp; Assumption.
Qed.

Lemma derive_pt_minus : (f1,f2:R->R;x:R;pr1:(derivable_pt f1 x);pr2:(derivable_pt f2 x)) ``(derive_pt (minus_fct f1 f2) x (derivable_pt_minus ? ? ? pr1 pr2)) == (derive_pt f1 x pr1) - (derive_pt f2 x pr2)``.
Intros.
Assert H := (derivable_derive f1 x pr1).
Assert H0 := (derivable_derive f2 x pr2).
Assert H1 := (derivable_derive (minus_fct f1 f2) x (derivable_pt_minus ? ? ? pr1 pr2)).
Elim H; Clear H; Intros l1 H.
Elim H0; Clear H0; Intros l2 H0.
Elim H1; Clear H1; Intros l H1.
Rewrite H; Rewrite H0; Apply derive_pt_eq_0.
Assert H3 := (projT2 ? ? pr1).
Unfold derive_pt in H; Rewrite H in H3.
Assert H4 := (projT2 ? ? pr2).
Unfold derive_pt in H0; Rewrite H0 in H4.
Apply derivable_pt_lim_minus; Assumption.
Qed.

Lemma derive_pt_mult : (f1,f2:R->R;x:R;pr1:(derivable_pt f1 x);pr2:(derivable_pt f2 x)) ``(derive_pt (mult_fct f1 f2) x (derivable_pt_mult ? ? ? pr1 pr2)) == (derive_pt f1 x pr1)*(f2 x) + (f1 x)*(derive_pt f2 x pr2)``.
Intros.
Assert H := (derivable_derive f1 x pr1).
Assert H0 := (derivable_derive f2 x pr2).
Assert H1 := (derivable_derive (mult_fct f1 f2) x (derivable_pt_mult ? ? ? pr1 pr2)).
Elim H; Clear H; Intros l1 H.
Elim H0; Clear H0; Intros l2 H0.
Elim H1; Clear H1; Intros l H1.
Rewrite H; Rewrite H0; Apply derive_pt_eq_0.
Assert H3 := (projT2 ? ? pr1).
Unfold derive_pt in H; Rewrite H in H3.
Assert H4 := (projT2 ? ? pr2).
Unfold derive_pt in H0; Rewrite H0 in H4.
Apply derivable_pt_lim_mult; Assumption.
Qed.

Lemma derive_pt_const : (a,x:R) (derive_pt (fct_cte a) x (derivable_pt_const a x)) == R0.
Intros.
Apply derive_pt_eq_0.
Apply derivable_pt_lim_const.
Qed.

Lemma derive_pt_scal : (f:R->R;a,x:R;pr:(derivable_pt f x)) ``(derive_pt (mult_real_fct a f) x (derivable_pt_scal ? ? ? pr)) == a * (derive_pt f x pr)``.
Intros.
Assert H := (derivable_derive f x pr).
Assert H0 := (derivable_derive (mult_real_fct a f) x (derivable_pt_scal ? ? ? pr)).
Elim H; Clear H; Intros l1 H.
Elim H0; Clear H0; Intros l2 H0.
Rewrite H; Apply derive_pt_eq_0.
Assert H3 := (projT2 ? ? pr).
Unfold derive_pt in H; Rewrite H in H3.
Apply derivable_pt_lim_scal; Assumption.
Qed.

Lemma derive_pt_id : (x:R) (derive_pt id x (derivable_pt_id ?))==R1.
Intros.
Apply derive_pt_eq_0.
Apply derivable_pt_lim_id.
Qed.

Lemma derive_pt_Rsqr : (x:R) (derive_pt Rsqr x (derivable_pt_Rsqr ?)) == ``2*x``.
Intros.
Apply derive_pt_eq_0.
Apply derivable_pt_lim_Rsqr.
Qed.

Lemma derive_pt_comp : (f1,f2:R->R;x:R;pr1:(derivable_pt f1 x);pr2:(derivable_pt f2 (f1 x))) ``(derive_pt (comp f2 f1) x (derivable_pt_comp ? ? ? pr1 pr2)) == (derive_pt f2 (f1 x) pr2) * (derive_pt f1 x pr1)``.
Intros.
Assert H := (derivable_derive f1 x pr1).
Assert H0 := (derivable_derive f2 (f1 x) pr2).
Assert H1 := (derivable_derive (comp f2 f1) x (derivable_pt_comp ? ? ? pr1 pr2)).
Elim H; Clear H; Intros l1 H.
Elim H0; Clear H0; Intros l2 H0.
Elim H1; Clear H1; Intros l H1.
Rewrite H; Rewrite H0; Apply derive_pt_eq_0.
Assert H3 := (projT2 ? ? pr1).
Unfold derive_pt in H; Rewrite H in H3.
Assert H4 := (projT2 ? ? pr2).
Unfold derive_pt in H0; Rewrite H0 in H4.
Apply derivable_pt_lim_comp; Assumption.
Qed.

(* Pow *)
Definition pow_fct [n:nat] : R->R := [y:R](pow y n).

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

Lemma pr_nu : (f:R->R;x:R;pr1,pr2:(derivable_pt f x)) (derive_pt f x pr1)==(derive_pt f x pr2). 
Intros.
Unfold derivable_pt in pr1.
Unfold derivable_pt in pr2.
Elim pr1; Intros.
Elim pr2; Intros.
Unfold derivable_pt_abs in p.
Unfold derivable_pt_abs in p0.
Simpl.
Apply (unicite_limite f x x0 x1 p p0).
Qed.


(************************************************************)
(**             Local extremum's condition                  *)
(************************************************************)

Theorem deriv_maximum : (f:R->R;a,b,c:R;pr:(derivable_pt f c)) ``a<c``->``c<b``->((x:R) ``a<x``->``x<b``->``(f x)<=(f c)``)->``(derive_pt f c pr)==0``.
Intros; Case (total_order R0 (derive_pt f c pr)); Intro.
Assert H3 := (derivable_derive f c pr).
Elim H3; Intros l H4; Rewrite H4 in H2.
Assert H5 := (derive_pt_eq_1 f c l pr H4).
Cut ``0<l/2``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0]].
Elim (H5 ``l/2`` H6); Intros delta H7.
Cut ``0<(b-c)/2``.
Intro; Cut ``(Rmin delta/2 ((b-c)/2))<>0``.
Intro; Cut ``(Rabsolu (Rmin delta/2 ((b-c)/2)))<delta``.
Intro.
Assert H11 := (H7 ``(Rmin delta/2 ((b-c)/2))`` H9 H10).
Cut ``0<(Rmin (delta/2) ((b-c)/2))``.
Intro; Cut ``a<c+(Rmin (delta/2) ((b-c)/2))``.
Intro; Cut ``c+(Rmin (delta/2) ((b-c)/2))<b``.
Intro; Assert H15 := (H1 ``c+(Rmin (delta/2) ((b-c)/2))`` H13 H14).
Cut ``((f (c+(Rmin (delta/2) ((b-c)/2))))-(f c))/(Rmin (delta/2) ((b-c)/2))<=0``.
Intro; Cut ``-l<0``.
Intro; Unfold Rminus in H11.
Cut ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l<0``.
Intro; Cut ``(Rabsolu (((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l)) < l/2``.
Unfold Rabsolu; Case (case_Rabsolu ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l``); Intro.
Replace `` -(((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l)`` with ``l+ -(((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2)))``.
Intro; Generalize (Rlt_compatibility ``-l`` ``l+ -(((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2)))`` ``l/2`` H19); Repeat Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol; Replace ``-l+l/2`` with ``-(l/2)``.
Intro; Generalize (Rlt_Ropp ``-(((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2)))`` ``-(l/2)`` H20); Repeat Rewrite Ropp_Ropp; Intro; Generalize (Rlt_trans ``0`` ``l/2`` ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))`` H6 H21); Intro; Elim (Rlt_antirefl ``0`` (Rlt_le_trans ``0`` ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))`` ``0`` H22 H16)).
Pattern 2 l; Rewrite double_var.
Ring.
Ring.
Intro.
Assert H20 := (Rle_sym2 ``0`` ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l`` r).
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H20 H18)). 
Assumption.
Rewrite <- Ropp_O; Replace ``((f (c+(Rmin (delta/2) ((b+ -c)/2))))+ -(f c))/(Rmin (delta/2) ((b+ -c)/2))+ -l`` with ``-(l+ -(((f (c+(Rmin (delta/2) ((b+ -c)/2))))-(f c))/(Rmin (delta/2) ((b+ -c)/2))))``.
Apply Rgt_Ropp; Change ``0<l+ -(((f (c+(Rmin (delta/2) ((b+ -c)/2))))-(f c))/(Rmin (delta/2) ((b+ -c)/2)))``; Apply gt0_plus_ge0_is_gt0; [Assumption | Rewrite <- Ropp_O; Apply Rge_Ropp; Apply Rle_sym1; Assumption].
Ring.
Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Replace ``((f (c+(Rmin (delta/2) ((b-c)/2))))-(f c))/(Rmin (delta/2) ((b-c)/2))`` with ``- (((f c)-(f (c+(Rmin (delta/2) ((b-c)/2)))))/(Rmin (delta/2) ((b-c)/2)))``.
Rewrite <- Ropp_O; Apply Rge_Ropp; Apply Rle_sym1; Unfold Rdiv; Apply Rmult_le_pos; [Generalize (Rle_compatibility_r ``-(f (c+(Rmin (delta*/2) ((b-c)*/2))))`` ``(f (c+(Rmin (delta*/2) ((b-c)*/2))))`` (f c) H15); Rewrite Rplus_Ropp_r; Intro; Assumption | Left; Apply Rlt_Rinv; Assumption].
Unfold Rdiv.
Rewrite <- Ropp_mul1.
Repeat Rewrite <- (Rmult_sym ``/(Rmin (delta*/2) ((b-c)*/2))``).
Apply r_Rmult_mult with ``(Rmin (delta*/2) ((b-c)*/2))``.
Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_r_sym.
Repeat Rewrite Rmult_1l.
Ring.
Red; Intro.
Unfold Rdiv in H12; Rewrite H16 in H12; Elim (Rlt_antirefl ``0`` H12).
Red; Intro.
Unfold Rdiv in H12; Rewrite H16 in H12; Elim (Rlt_antirefl ``0`` H12).
Assert H14 := (Rmin_r ``(delta/2)`` ``((b-c)/2)``).
Assert H15 := (Rle_compatibility ``c`` ``(Rmin (delta/2) ((b-c)/2))`` ``(b-c)/2`` H14).
Apply Rle_lt_trans with ``c+(b-c)/2``.
Assumption.
Apply Rlt_monotony_contra with ``2``.
Sup0.
Replace ``2*(c+(b-c)/2)`` with ``c+b``.
Replace ``2*b`` with ``b+b``.
Apply Rlt_compatibility_r; Assumption.
Ring.
Unfold Rdiv; Rewrite Rmult_Rplus_distr.
Repeat Rewrite (Rmult_sym ``2``).
Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Ring.
DiscrR.
Apply Rlt_trans with c.
Assumption.
Pattern 1 c; Rewrite <- (Rplus_Or c); Apply Rlt_compatibility; Assumption.
Cut ``0<delta/2``.
Intro; Apply (Rmin_stable_in_posreal (mkposreal ``delta/2`` H12) (mkposreal ``(b-c)/2`` H8)).
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Sup0].
Unfold Rabsolu; Case (case_Rabsolu (Rmin ``delta/2`` ``(b-c)/2``)).
Intro.
Cut ``0<delta/2``.
Intro.
Generalize (Rmin_stable_in_posreal (mkposreal ``delta/2`` H10) (mkposreal ``(b-c)/2`` H8)); Simpl; Intro; Elim (Rlt_antirefl ``0`` (Rlt_trans ``0`` ``(Rmin (delta/2) ((b-c)/2))`` ``0`` H11 r)).
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Sup0].
Intro; Apply Rle_lt_trans with ``delta/2``.
Apply Rmin_l.
Unfold Rdiv; Apply Rlt_monotony_contra with ``2``.
Sup0.
Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l.
Replace ``2*delta`` with ``delta+delta``. 
Pattern 2 delta; Rewrite <- (Rplus_Or delta); Apply Rlt_compatibility.
Rewrite Rplus_Or; Apply (cond_pos delta).
Symmetry; Apply double.
DiscrR.
Cut ``0<delta/2``.
Intro; Generalize (Rmin_stable_in_posreal (mkposreal ``delta/2`` H9) (mkposreal ``(b-c)/2`` H8)); Simpl; Intro; Red; Intro; Rewrite H11 in H10; Elim (Rlt_antirefl ``0`` H10).
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Sup0].
Unfold Rdiv; Apply Rmult_lt_pos.
Generalize (Rlt_compatibility_r ``-c`` c b H0); Rewrite Rplus_Ropp_r; Intro; Assumption.
Apply Rlt_Rinv; Sup0.
Elim H2; Intro.
Symmetry; Assumption.
Generalize (derivable_derive f c pr); Intro; Elim H4; Intros l H5.
Rewrite H5 in H3; Generalize (derive_pt_eq_1 f c l pr H5); Intro; Cut ``0< -(l/2)``.
Intro; Elim (H6 ``-(l/2)`` H7); Intros delta H9.
Cut ``0<(c-a)/2``.
Intro; Cut ``(Rmax (-(delta/2)) ((a-c)/2))<0``.
Intro; Cut ``(Rmax (-(delta/2)) ((a-c)/2))<>0``.
Intro; Cut ``(Rabsolu (Rmax (-(delta/2)) ((a-c)/2)))<delta``.
Intro; Generalize (H9 ``(Rmax (-(delta/2)) ((a-c)/2))`` H11 H12); Intro; Cut ``a<c+(Rmax (-(delta/2)) ((a-c)/2))``.
Cut ``c+(Rmax (-(delta/2)) ((a-c)/2))<b``.
Intros; Generalize (H1 ``c+(Rmax (-(delta/2)) ((a-c)/2))`` H15 H14); Intro; Cut ``0<=((f (c+(Rmax (-(delta/2)) ((a-c)/2))))-(f c))/(Rmax (-(delta/2)) ((a-c)/2))``.
Intro; Cut ``0< -l``.
Intro; Unfold Rminus in H13; Cut ``0<((f (c+(Rmax (-(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax (-(delta/2)) ((a+ -c)/2))+ -l``.
Intro; Cut ``(Rabsolu (((f (c+(Rmax (-(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax (-(delta/2)) ((a+ -c)/2))+ -l)) < -(l/2)``.
Unfold Rabsolu; Case (case_Rabsolu ``((f (c+(Rmax (-(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax (-(delta/2)) ((a+ -c)/2))+ -l``).
Intro; Elim (Rlt_antirefl ``0`` (Rlt_trans ``0`` ``((f (c+(Rmax ( -(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax ( -(delta/2)) ((a+ -c)/2))+ -l`` ``0`` H19 r)).
Intros; Generalize (Rlt_compatibility_r ``l`` ``(((f (c+(Rmax (-(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax (-(delta/2)) ((a+ -c)/2)))+ -l`` ``-(l/2)`` H20); Repeat Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Replace ``-(l/2)+l`` with ``l/2``.
Cut ``l/2<0``.
Intros; Generalize (Rlt_trans ``((f (c+(Rmax ( -(delta/2)) ((a+ -c)/2))))+ -(f c))/(Rmax ( -(delta/2)) ((a+ -c)/2))`` ``l/2`` ``0`` H22 H21); Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` ``((f (c+(Rmax ( -(delta/2)) ((a-c)/2))))-(f c))/(Rmax ( -(delta/2)) ((a-c)/2))`` ``0`` H17 H23)).
Rewrite <- (Ropp_Ropp ``l/2``); Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Pattern 3 l; Rewrite double_var.
Ring.
Assumption.
Apply ge0_plus_gt0_is_gt0; Assumption.
Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Unfold Rdiv; Replace ``((f (c+(Rmax ( -(delta*/2)) ((a-c)*/2))))-(f c))*/(Rmax ( -(delta*/2)) ((a-c)*/2))`` with ``(-((f (c+(Rmax ( -(delta*/2)) ((a-c)*/2))))-(f c)))*/(-(Rmax ( -(delta*/2)) ((a-c)*/2)))``.
Apply Rmult_le_pos.
Generalize (Rle_compatibility ``-(f (c+(Rmax (-(delta*/2)) ((a-c)*/2))))`` ``(f (c+(Rmax (-(delta*/2)) ((a-c)*/2))))`` (f c) H16); Rewrite Rplus_Ropp_l; Replace ``-((f (c+(Rmax ( -(delta*/2)) ((a-c)*/2))))-(f c))`` with ``-((f (c+(Rmax ( -(delta*/2)) ((a-c)*/2)))))+(f c)``.
Intro; Assumption.
Ring.
Left; Apply Rlt_Rinv; Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Unfold Rdiv.
Rewrite <- Ropp_Rinv.
Rewrite Ropp_mul2.
Reflexivity.
Unfold Rdiv in H11; Assumption.
Generalize (Rlt_compatibility c ``(Rmax ( -(delta/2)) ((a-c)/2))`` ``0`` H10); Rewrite Rplus_Or; Intro; Apply Rlt_trans with ``c``; Assumption.
Generalize (RmaxLess2 ``(-(delta/2))`` ``((a-c)/2)``); Intro; Generalize (Rle_compatibility c ``(a-c)/2`` ``(Rmax ( -(delta/2)) ((a-c)/2))`` H14); Intro; Apply Rlt_le_trans with ``c+(a-c)/2``.
Apply Rlt_monotony_contra with ``2``.
Sup0.
Replace ``2*(c+(a-c)/2)`` with ``a+c``.
Rewrite double.
Apply Rlt_compatibility; Assumption.
Ring.
Rewrite <- Rplus_assoc.
Rewrite <- double_var.
Ring.
Assumption.
Unfold Rabsolu; Case (case_Rabsolu (Rmax ``-(delta/2)`` ``(a-c)/2``)).
Intro; Generalize (RmaxLess1 ``-(delta/2)`` ``(a-c)/2``); Intro; Generalize (Rle_Ropp ``-(delta/2)`` ``(Rmax ( -(delta/2)) ((a-c)/2))`` H12); Rewrite Ropp_Ropp; Intro; Generalize (Rle_sym2 ``-(Rmax ( -(delta/2)) ((a-c)/2))`` ``delta/2`` H13); Intro; Apply Rle_lt_trans with ``delta/2``.
Assumption.
Apply Rlt_monotony_contra with ``2``. 
Sup0.
Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Rewrite double.
Pattern 2 delta; Rewrite <- (Rplus_Or delta); Apply Rlt_compatibility; Rewrite Rplus_Or; Apply (cond_pos delta).
DiscrR. 
Cut ``-(delta/2) < 0``.
Cut ``(a-c)/2<0``.
Intros; Generalize (Rmax_stable_in_negreal (mknegreal ``-(delta/2)`` H13) (mknegreal ``(a-c)/2`` H12)); Simpl; Intro; Generalize (Rle_sym2 ``0`` ``(Rmax ( -(delta/2)) ((a-c)/2))`` r); Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` ``(Rmax ( -(delta/2)) ((a-c)/2))`` ``0`` H15 H14)).
Rewrite <- Ropp_O; Rewrite <- (Ropp_Ropp ``(a-c)/2``); Apply Rlt_Ropp; Replace ``-((a-c)/2)`` with ``(c-a)/2``.
Assumption.
Unfold Rdiv.
Rewrite <- Ropp_mul1. 
Rewrite (Ropp_distr2 a c).
Reflexivity.
Rewrite <- Ropp_O; Apply Rlt_Ropp; Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Assert Hyp : ``0<2``; [Sup0 | Apply (Rlt_Rinv ``2`` Hyp)]].
Red; Intro; Rewrite H11 in H10; Elim (Rlt_antirefl ``0`` H10).
Cut ``(a-c)/2<0``.
Intro; Cut ``-(delta/2)<0``.
Intro; Apply (Rmax_stable_in_negreal (mknegreal ``-(delta/2)`` H11) (mknegreal ``(a-c)/2`` H10)).
Rewrite <- Ropp_O; Apply Rlt_Ropp; Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Assert Hyp : ``0<2``; [Sup0 | Apply (Rlt_Rinv ``2`` Hyp)]].
Rewrite <- Ropp_O; Rewrite <- (Ropp_Ropp ``(a-c)/2``); Apply Rlt_Ropp; Replace ``-((a-c)/2)`` with ``(c-a)/2``.
Assumption.
Unfold Rdiv.
Rewrite <- Ropp_mul1. 
Rewrite (Ropp_distr2 a c).
Reflexivity.
Unfold Rdiv; Apply Rmult_lt_pos; [Generalize (Rlt_compatibility_r ``-a`` a c H); Rewrite Rplus_Ropp_r; Intro; Assumption | Assert Hyp : ``0<2``; [Sup0 | Apply (Rlt_Rinv ``2`` Hyp)]].
Replace ``-(l/2)`` with ``(-l)/2``.
Unfold Rdiv; Apply Rmult_lt_pos.
Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Assert Hyp : ``0<2``; [Sup0 | Apply (Rlt_Rinv ``2`` Hyp)].
Unfold Rdiv; Apply Ropp_mul1.
Qed.

Theorem deriv_minimum : (f:R->R;a,b,c:R;pr:(derivable_pt f c)) ``a<c``->``c<b``->((x:R) ``a<x``->``x<b``->``(f c)<=(f x)``)->``(derive_pt f c pr)==0``.
Intros.
Rewrite <- (Ropp_Ropp (derive_pt f c pr)).
Apply eq_RoppO.
Rewrite <- (derive_pt_opp f c pr).
Cut (x:R)(``a<x``->``x<b``->``((opp_fct f) x)<=((opp_fct f) c)``).
Intro.
Apply (deriv_maximum (opp_fct f) a b c (derivable_pt_opp ? ? pr) H H0 H2).
Intros; Unfold opp_fct; Apply Rge_Ropp; Apply Rle_sym1.
Apply (H1 x H2 H3).
Qed.
 
Theorem deriv_constant2 : (f:R->R;a,b,c:R;pr:(derivable_pt f c)) ``a<c``->``c<b``->((x:R) ``a<x``->``x<b``->``(f x)==(f c)``)->``(derive_pt f c pr)==0``.
Intros.
EApply deriv_maximum with a b; Try Assumption.
Intros; Right; Apply (H1 x H2 H3).
Qed.

(**********)
Lemma nonneg_derivative_0 : (f:R->R;pr:(derivable f)) (increasing f) -> ((x:R) ``0<=(derive_pt f x (pr x))``).
Intros; Unfold increasing in H.
Assert H0 := (derivable_derive f x (pr x)).
Elim H0; Intros l H1.
Rewrite H1; Case (total_order R0 l); Intro.
Left; Assumption.
Elim H2; Intro.
Right; Assumption.
Assert H4 := (derive_pt_eq_1 f x l (pr x) H1).
Cut ``0< -(l/2)``.
Intro; Elim (H4 ``-(l/2)`` H5); Intros delta H6.
Cut ``delta/2<>0``/\``0<delta/2``/\``(Rabsolu delta/2)<delta``.
Intro; Decompose [and] H7; Intros; Generalize (H6 ``delta/2`` H8 H11); Cut ``0<=((f (x+delta/2))-(f x))/(delta/2)``.
Intro; Cut ``0<=((f (x+delta/2))-(f x))/(delta/2)-l``.
Intro; Unfold Rabsolu; Case (case_Rabsolu ``((f (x+delta/2))-(f x))/(delta/2)-l``).
Intro; Elim (Rlt_antirefl ``0`` (Rle_lt_trans ``0`` ``((f (x+delta/2))-(f x))/(delta/2)-l`` ``0`` H12 r)).
Intros; Generalize (Rlt_compatibility_r l ``((f (x+delta/2))-(f x))/(delta/2)-l`` ``-(l/2)`` H13); Unfold Rminus; Replace ``-(l/2)+l`` with ``l/2``.
Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Intro; Generalize (Rle_lt_trans ``0`` ``((f (x+delta/2))-(f x))/(delta/2)`` ``l/2`` H9 H14); Intro; Cut ``l/2<0``.
Intro; Elim (Rlt_antirefl ``0`` (Rlt_trans ``0`` ``l/2`` ``0`` H15 H16)).
Rewrite <- Ropp_O in H5; Generalize (Rlt_Ropp ``-0`` ``-(l/2)`` H5); Repeat Rewrite Ropp_Ropp; Intro; Assumption.
Pattern 3 l ; Rewrite double_var.
Ring.
Unfold Rminus; Apply ge0_plus_ge0_is_ge0.
Unfold Rdiv; Apply Rmult_le_pos.
Cut ``x<=(x+(delta*/2))``.
Intro; Generalize (H x ``x+(delta*/2)`` H12); Intro; Generalize (Rle_compatibility ``-(f x)`` ``(f x)`` ``(f (x+delta*/2))`` H13); Rewrite Rplus_Ropp_l; Rewrite Rplus_sym; Intro; Assumption.
Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Left; Assumption.
Left; Apply Rlt_Rinv; Assumption.
Left; Rewrite <- Ropp_O; Apply Rlt_Ropp; Assumption.
Unfold Rdiv; Apply Rmult_le_pos.
Cut ``x<=(x+(delta*/2))``.
Intro; Generalize (H x ``x+(delta*/2)`` H9); Intro; Generalize (Rle_compatibility ``-(f x)`` ``(f x)`` ``(f (x+delta*/2))`` H12); Rewrite Rplus_Ropp_l; Rewrite Rplus_sym; Intro; Assumption.
Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Left; Assumption. 
Left; Apply Rlt_Rinv; Assumption.
Split.
Unfold Rdiv; Apply prod_neq_R0.
Generalize (cond_pos delta); Intro; Red; Intro H9; Rewrite H9 in H7; Elim (Rlt_antirefl ``0`` H7).
Apply Rinv_neq_R0; DiscrR.
Split.
Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Sup0].
Replace ``(Rabsolu delta/2)`` with ``delta/2``.
Unfold Rdiv; Apply Rlt_monotony_contra with ``2``.
Sup0.
Rewrite (Rmult_sym ``2``).
Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym; [Idtac | DiscrR].
Rewrite Rmult_1r.
Rewrite double.
Pattern 1 (pos delta); Rewrite <- Rplus_Or.
Apply Rlt_compatibility; Apply (cond_pos delta).
Symmetry; Apply Rabsolu_right.
Left; Change ``0<delta/2``; Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos delta) | Apply Rlt_Rinv; Sup0].
Unfold Rdiv; Rewrite <- Ropp_mul1; Apply Rmult_lt_pos.
Apply Rlt_anti_compatibility with l.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rplus_Or; Assumption.
Apply Rlt_Rinv; Sup0.
Qed.

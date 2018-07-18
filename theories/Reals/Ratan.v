(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Lra.
Require Import Rbase.
Require Import PSeries_reg.
Require Import Rtrigo1.
Require Import Ranalysis_reg.
Require Import Rfunctions.
Require Import AltSeries.
Require Import Rseries.
Require Import SeqProp.
Require Import Ranalysis5.
Require Import SeqSeries.
Require Import PartSum.
Require Import Omega.

Local Open Scope R_scope.

(** Tools *)

Lemma Ropp_div : forall x y, -x/y = -(x/y).
Proof.
intros x y; unfold Rdiv; rewrite <-Ropp_mult_distr_l_reverse; reflexivity.
Qed.

Definition pos_half_prf : 0 < /2.
Proof. lra. Qed.

Definition pos_half := mkposreal (/2) pos_half_prf.

Lemma Boule_half_to_interval :
  forall x , Boule (/2) pos_half x -> 0 <= x <= 1.
Proof.
unfold Boule, pos_half; simpl.
intros x b; apply Rabs_def2 in b; destruct b; split; lra.
Qed.

Lemma Boule_lt : forall c r x, Boule c r x -> Rabs x < Rabs c + r.
Proof.
unfold Boule; intros c r x h.
apply Rabs_def2 in h; destruct h; apply Rabs_def1;
 (destruct (Rle_lt_dec 0 c);[rewrite Rabs_pos_eq; lra |
    rewrite <- Rabs_Ropp, Rabs_pos_eq; lra]).
Qed.

(* The following lemma does not belong here. *)
Lemma Un_cv_ext :
  forall un vn, (forall n, un n = vn n) ->
  forall l, Un_cv un l -> Un_cv vn l.
Proof.
intros un vn quv l P eps ep; destruct (P eps ep) as [N Pn]; exists N.
intro n; rewrite <- quv; apply Pn.
Qed.

(* The following two lemmas are general purposes about alternated series.
  They do not belong here. *)
Lemma Alt_first_term_bound :forall f l N n,
   Un_decreasing f -> Un_cv f 0 ->
   Un_cv (sum_f_R0 (tg_alt f)) l ->
   (N <= n)%nat ->
   R_dist (sum_f_R0 (tg_alt f) n) l <= f N.
Proof.
intros f l.
assert (WLOG :
   forall n P, (forall k, (0 < k)%nat -> P k) ->
         ((forall k, (0 < k)%nat -> P k) -> P 0%nat) -> P n).
clear.
intros [ | n] P Hs Ho;[solve[apply Ho, Hs] | apply Hs; auto with arith].
intros N; pattern N; apply WLOG; clear N.
intros [ | N] Npos n decr to0 cv nN.
  clear -Npos; elimtype False; omega.
 assert (decr' : Un_decreasing (fun i => f (S N + i)%nat)).
  intros k; replace (S N+S k)%nat with (S (S N+k)) by ring.
  apply (decr (S N + k)%nat).
 assert (to' : Un_cv (fun i => f (S N + i)%nat) 0).
  intros eps ep; destruct (to0 eps ep) as [M PM].
  exists M; intros k kM; apply PM; omega.
 assert (cv' : Un_cv
         (sum_f_R0 (tg_alt (fun i => ((-1) ^ S N * f(S N + i)%nat))))
             (l - sum_f_R0 (tg_alt f) N)).
  intros eps ep; destruct (cv eps ep) as [M PM]; exists M.
  intros n' nM. 
  match goal with |- ?C => set (U := C) end.
  assert (nM' : (n' + S N >= M)%nat) by omega.
   generalize (PM _ nM'); unfold R_dist.
  rewrite (tech2 (tg_alt f) N (n' + S N)).
  assert (t : forall a b c, (a + b) - c = b - (c - a)) by (intros; ring).
  rewrite t; clear t; unfold U, R_dist; clear U.
  replace (n' + S N - S N)%nat with n' by omega.
  rewrite <- (sum_eq (tg_alt (fun i => (-1) ^ S N * f(S N + i)%nat))).
   tauto.
   intros i _; unfold tg_alt.
   rewrite <- Rmult_assoc, <- pow_add, !(plus_comm i); reflexivity.
  omega.
  assert (cv'' : Un_cv (sum_f_R0 (tg_alt (fun i => f (S N + i)%nat)))
                   ((-1) ^ S N * (l - sum_f_R0 (tg_alt f) N))).
  apply (Un_cv_ext (fun n => (-1) ^ S N * 
            sum_f_R0 (tg_alt (fun i : nat => (-1) ^ S N * f (S N + i)%nat)) n)).
   intros n0; rewrite scal_sum; apply sum_eq; intros i _.
   unfold tg_alt; ring_simplify; replace (((-1) ^ S N) ^ 2) with 1.
    ring.
   rewrite <- pow_mult, mult_comm, pow_mult; replace ((-1) ^2) with 1 by ring.
   rewrite pow1; reflexivity.
  apply CV_mult.
   solve[intros eps ep; exists 0%nat; intros; rewrite R_dist_eq; auto].
  assumption.
 destruct (even_odd_cor N) as [p [Neven | Nodd]].
  rewrite Neven; destruct (alternated_series_ineq _ _ p decr to0 cv) as [B C].
  case (even_odd_cor n) as [p' [neven | nodd]].
   rewrite neven.
   destruct (alternated_series_ineq _ _ p' decr to0 cv) as [D E].
   unfold R_dist; rewrite Rabs_pos_eq;[ | lra].
   assert (dist : (p <= p')%nat) by omega.
   assert (t := decreasing_prop _ _ _ (CV_ALT_step1 f decr) dist).
   apply Rle_trans with (sum_f_R0 (tg_alt f) (2 * p) - l).
    unfold Rminus; apply Rplus_le_compat_r; exact t.
   match goal with _ : ?a <= l, _ : l <= ?b |- _ => 
    replace (f (S (2 * p))) with (b - a) by
     (rewrite tech5; unfold tg_alt; rewrite pow_1_odd; ring); lra
   end.
  rewrite nodd; destruct (alternated_series_ineq _ _ p' decr to0 cv) as [D E].
   unfold R_dist; rewrite <- Rabs_Ropp, Rabs_pos_eq, Ropp_minus_distr;
     [ | lra].
   assert (dist : (p <= p')%nat) by omega.
   apply Rle_trans with (l - sum_f_R0 (tg_alt f) (S (2 * p))).
    unfold Rminus; apply Rplus_le_compat_l, Ropp_le_contravar.
    solve[apply Rge_le, (growing_prop _ _ _ (CV_ALT_step0 f decr) dist)].
   unfold Rminus; rewrite tech5, Ropp_plus_distr, <- Rplus_assoc.
   unfold tg_alt at 2; rewrite pow_1_odd; lra.
 rewrite Nodd; destruct (alternated_series_ineq _ _ p decr to0 cv) as [B _].
 destruct (alternated_series_ineq _ _ (S p) decr to0 cv) as [_ C].
 assert (keep : (2 * S p = S (S ( 2 * p)))%nat) by ring.
 case (even_odd_cor n) as [p' [neven | nodd]].
   rewrite neven;
   destruct (alternated_series_ineq _ _ p' decr to0 cv) as [D E].
   unfold R_dist; rewrite Rabs_pos_eq;[ | lra].
   assert (dist : (S p < S p')%nat) by omega.
   apply Rle_trans with (sum_f_R0 (tg_alt f) (2 * S p) - l).
   unfold Rminus; apply Rplus_le_compat_r,
     (decreasing_prop _ _ _ (CV_ALT_step1 f decr)).
   omega.
  rewrite keep, tech5; unfold tg_alt at 2; rewrite <- keep, pow_1_even.
  lra.
 rewrite nodd; destruct (alternated_series_ineq _ _ p' decr to0 cv) as [D E].
 unfold R_dist; rewrite <- Rabs_Ropp, Rabs_pos_eq;[ | lra].
 rewrite Ropp_minus_distr.
 apply Rle_trans with (l - sum_f_R0 (tg_alt f) (S (2 * p))).
  unfold Rminus; apply Rplus_le_compat_l, Ropp_le_contravar, Rge_le,
   (growing_prop _ _ _ (CV_ALT_step0 f decr)); omega.
 generalize C; rewrite keep, tech5; unfold tg_alt.
 rewrite <- keep, pow_1_even.
 assert (t : forall a b c, a <= b + 1 * c -> a - b <= c) by (intros; lra).
 solve[apply t].
clear WLOG; intros Hyp [ | n] decr to0 cv _.
 generalize (alternated_series_ineq f l 0 decr to0 cv).
 unfold R_dist, tg_alt; simpl; rewrite !Rmult_1_l, !Rmult_1_r.
 assert (f 1%nat <= f 0%nat) by apply decr.
 intros [A B]; rewrite Rabs_pos_eq; lra.
apply Rle_trans with (f 1%nat).
 apply (Hyp 1%nat (le_n 1) (S n) decr to0 cv).
 omega.
solve[apply decr].
Qed.

Lemma Alt_CVU : forall (f : nat -> R -> R) g h c r,
   (forall x, Boule c r x ->Un_decreasing (fun n => f n x)) -> 
   (forall x, Boule c r x -> Un_cv (fun n => f n x) 0) ->
   (forall x, Boule c r x -> 
       Un_cv (sum_f_R0 (tg_alt  (fun i => f i x))) (g x)) ->
   (forall x n, Boule c r x -> f n x <= h n) ->
   (Un_cv h 0) ->
   CVU (fun N x => sum_f_R0 (tg_alt (fun i => f i x)) N) g c r.
Proof.
intros f g h c r decr to0 to_g bound bound0 eps ep.  
assert (ep' : 0 <eps/2) by lra.
destruct (bound0 _ ep) as [N Pn]; exists N.
intros n y nN dy.
rewrite <- Rabs_Ropp, Ropp_minus_distr; apply Rle_lt_trans with (f n y).
 solve[apply (Alt_first_term_bound (fun i => f i y) (g y) n n); auto].
apply Rle_lt_trans with (h n).
 apply bound; assumption.
clear - nN Pn.
generalize (Pn _ nN); unfold R_dist; rewrite Rminus_0_r; intros t.
apply Rabs_def2 in t; tauto.
Qed.

(* The following lemmas are general purpose lemmas about squares. 
  They do not belong here *)

Lemma pow2_ge_0 : forall x, 0 <= x ^ 2.
Proof.
intros x; destruct (Rle_lt_dec 0 x).
 replace (x ^ 2) with (x * x) by field.
 apply Rmult_le_pos; assumption.
 replace (x ^ 2) with ((-x) * (-x)) by field.
apply Rmult_le_pos; lra.
Qed.

Lemma pow2_abs : forall x,  Rabs x ^ 2 = x ^ 2.
Proof.
intros x; destruct (Rle_lt_dec 0 x).
 rewrite Rabs_pos_eq;[field | assumption].
rewrite <- Rabs_Ropp, Rabs_pos_eq;[field | lra].
Qed.

(** * Properties of tangent *)

Lemma derivable_pt_tan : forall x, -PI/2 < x < PI/2 -> derivable_pt tan x.
Proof.
intros x xint.
 unfold derivable_pt, tan. 
 apply derivable_pt_div ; [reg | reg | ].
 apply Rgt_not_eq.
 unfold Rgt ; apply cos_gt_0;
  [unfold Rdiv; rewrite <- Ropp_mult_distr_l_reverse; fold (-PI/2) |];tauto.
Qed.

Lemma derive_pt_tan : forall (x:R),
 forall (Pr1: -PI/2 < x < PI/2),
 derive_pt tan x (derivable_pt_tan x Pr1) = 1 + (tan x)^2.
Proof.
intros x pr.
assert (cos x <> 0).
 apply Rgt_not_eq, cos_gt_0; rewrite <- ?Ropp_div; tauto.
unfold tan; reg; unfold pow, Rsqr; field; assumption.
Qed.

(** Proof that tangent is a bijection *)
(* to be removed? *)

Lemma derive_increasing_interv :
  forall (a b:R) (f:R -> R),
    a < b ->
    forall (pr:forall x, a < x < b -> derivable_pt f x),
    (forall t:R, forall (t_encad : a < t < b), 0 < derive_pt f t (pr t t_encad)) ->
    forall x y:R, a < x < b -> a < y < b -> x < y -> f x < f y.
Proof.
intros a b f a_lt_b pr Df_gt_0 x y x_encad y_encad x_lt_y.
 assert (derivable_id_interv : forall c : R, x < c < y -> derivable_pt id c).
  intros ; apply derivable_pt_id.
 assert (derivable_f_interv :  forall c : R, x < c < y -> derivable_pt f c).
  intros c c_encad. apply pr. split.
  apply Rlt_trans with (r2:=x) ; [exact (proj1 x_encad) | exact (proj1 c_encad)].
  apply Rlt_trans with (r2:=y) ; [exact (proj2 c_encad) | exact (proj2 y_encad)].
 assert (f_cont_interv : forall c : R, x <= c <= y -> continuity_pt f c).
  intros c c_encad; apply derivable_continuous_pt ; apply pr. split.
  apply Rlt_le_trans with (r2:=x) ; [exact (proj1 x_encad) | exact (proj1 c_encad)].
  apply Rle_lt_trans with (r2:=y) ; [ exact (proj2 c_encad) | exact (proj2 y_encad)].
 assert (id_cont_interv : forall c : R, x <= c <= y -> continuity_pt id c).
  intros ; apply derivable_continuous_pt ; apply derivable_pt_id. 
 elim (MVT f id x y derivable_f_interv derivable_id_interv x_lt_y f_cont_interv id_cont_interv).
  intros c Temp ; elim Temp ; clear Temp ; intros Pr eq.
   replace (id y - id x) with (y - x) in eq by intuition.
   replace (derive_pt id c (derivable_id_interv c Pr)) with 1 in eq.
   assert (Hyp : f y - f x > 0).
    rewrite Rmult_1_r in eq. rewrite <- eq.
    apply Rmult_gt_0_compat.
    apply Rgt_minus ; assumption.
    assert (c_encad2 : a <= c < b).
     split.
     apply Rlt_le ; apply Rlt_trans with (r2:=x) ; [exact (proj1 x_encad) | exact (proj1 Pr)].
     apply Rle_lt_trans with (r2:=y) ; [apply Rlt_le ; exact (proj2 Pr) | exact (proj2 y_encad)].
     assert (c_encad : a < c < b).
      split.
      apply Rlt_trans with (r2:=x) ; [exact (proj1 x_encad) | exact (proj1 Pr)].
      apply Rle_lt_trans with (r2:=y) ; [apply Rlt_le ; exact (proj2 Pr) | exact (proj2 y_encad)].
     assert (Temp := Df_gt_0 c c_encad).
     assert (Temp2 := pr_nu f c (derivable_f_interv c Pr) (pr c c_encad)).
     rewrite Temp2 ; apply Temp.
   apply Rminus_gt ; exact Hyp.
   symmetry ; rewrite derive_pt_eq ; apply derivable_pt_lim_id.
Qed.

(* begin hide *)
Lemma plus_Rsqr_gt_0 : forall x, 1 + x ^ 2 > 0.
Proof.
intro m. replace 0 with (0+0) by intuition.
 apply Rplus_gt_ge_compat. intuition.
 elim (total_order_T m 0) ; intro s'. case s'.
 intros m_cond. replace 0 with (0*0) by intuition.
  replace (m ^ 2) with ((-m)^2).
  apply Rle_ge ; apply Rmult_le_compat ; intuition ; apply Rlt_le ; rewrite Rmult_1_r ; intuition.
  field.
  intro H' ; rewrite H' ; right ; field.
   left. intuition.
Qed.
(* end hide *)

(* The following lemmas about PI should probably be in Rtrigo. *)

Lemma PI2_lower_bound :
  forall x, 0 < x < 2 -> 0 < cos x  -> x < PI/2.
Proof.
intros x [xp xlt2] cx.
destruct (Rtotal_order x (PI/2)) as [xltpi2 | [xeqpi2 | xgtpi2]].
  assumption.
 now case (Rgt_not_eq _ _ cx); rewrite xeqpi2, cos_PI2.
destruct (MVT_cor1 cos (PI/2) x derivable_cos xgtpi2) as
   [c [Pc [cint1 cint2]]].
revert Pc; rewrite cos_PI2, Rminus_0_r. 
rewrite <- (pr_nu cos c (derivable_pt_cos c)), derive_pt_cos.
assert (0 < c < 2) by (split; assert (t := PI2_RGT_0); lra).
assert (0 < sin c) by now apply sin_pos_tech.
intros Pc.
case (Rlt_not_le _ _ cx).
rewrite <- (Rplus_0_l (cos x)), Pc, Ropp_mult_distr_l_reverse.
apply Rle_minus, Rmult_le_pos;[apply Rlt_le; assumption | lra ].
Qed.

Lemma PI2_3_2 : 3/2 < PI/2.
Proof.
apply PI2_lower_bound;[split; lra | ].
destruct (pre_cos_bound (3/2) 1) as [t _]; [lra | lra | ].
apply Rlt_le_trans with (2 := t); clear t.
unfold cos_approx; simpl; unfold cos_term.
rewrite !INR_IZR_INZ.
simpl.
field_simplify.
unfold Rdiv.
rewrite Rmult_0_l.
apply Rdiv_lt_0_compat ; now apply IZR_lt.
Qed.

Lemma PI2_1 : 1 < PI/2.
Proof. assert (t := PI2_3_2); lra. Qed.

Lemma tan_increasing :
  forall x y:R,
    -PI/2 < x ->
    x < y -> 
    y < PI/2 -> tan x < tan y.
Proof.
intros x y Z_le_x x_lt_y y_le_1.
 assert (x_encad : -PI/2 < x < PI/2).
  split ; [assumption | apply Rlt_trans with (r2:=y) ; assumption].
 assert (y_encad : -PI/2 < y < PI/2).
  split ; [apply Rlt_trans with (r2:=x) ; intuition | intuition ].
 assert (local_derivable_pt_tan : forall x : R, -PI/2 < x < PI/2 ->
          derivable_pt tan x).
  intros ; apply derivable_pt_tan ; intuition.
 apply derive_increasing_interv with (a:=-PI/2) (b:=PI/2) (pr:=local_derivable_pt_tan) ; intuition.
 lra.
 assert (Temp := pr_nu tan t (derivable_pt_tan t t_encad) (local_derivable_pt_tan t t_encad)) ;
 rewrite <- Temp ; clear Temp.
 assert (Temp := derive_pt_tan t t_encad) ; rewrite Temp ; clear Temp.
 apply plus_Rsqr_gt_0.
Qed.

Lemma tan_is_inj : forall x y, -PI/2 < x < PI/2 -> -PI/2 < y < PI/2 ->
   tan x = tan y -> x = y.
Proof.
  intros a b a_encad b_encad fa_eq_fb.
  case(total_order_T a b).
  intro s ; case s ; clear s.
  intro Hf.
  assert (Hfalse := tan_increasing a b (proj1 a_encad) Hf (proj2 b_encad)).
  case (Rlt_not_eq (tan a) (tan b)) ; assumption.
  intuition.
  intro Hf. assert (Hfalse := tan_increasing b a (proj1 b_encad) Hf (proj2 a_encad)).
  case (Rlt_not_eq (tan b) (tan a)) ; [|symmetry] ; assumption.
Qed.

Lemma exists_atan_in_frame :
 forall lb ub y, lb < ub -> -PI/2 < lb -> ub < PI/2 ->
 tan lb < y < tan ub -> {x | lb < x < ub /\ tan x = y}.
Proof.
intros lb ub y lb_lt_ub lb_cond ub_cond y_encad.
 case y_encad ; intros y_encad1 y_encad2.
     assert (f_cont : forall a : R, lb <= a <= ub -> continuity_pt tan a).
      intros a a_encad. apply derivable_continuous_pt ; apply derivable_pt_tan.
      split. apply Rlt_le_trans with (r2:=lb) ; intuition.
      apply Rle_lt_trans with (r2:=ub) ; intuition.
     assert (Cont : forall a : R, lb <= a <= ub -> continuity_pt (fun x => tan x - y) a).
      intros a a_encad. unfold continuity_pt, continue_in, limit1_in, limit_in ; simpl ; unfold R_dist.
      intros eps eps_pos. elim (f_cont a a_encad eps eps_pos).
      intros alpha alpha_pos. destruct alpha_pos as (alpha_pos,Temp).
      exists alpha. split.
      assumption. intros x  x_cond.
      replace (tan x - y - (tan a - y)) with (tan x - tan a) by field.
      exact (Temp x x_cond).
     assert (H1 : (fun x : R => tan x - y) lb < 0).
       apply Rlt_minus. assumption.
      assert (H2 : 0 < (fun x : R => tan x - y) ub).
       apply Rgt_minus. assumption.
     destruct (IVT_interv (fun x => tan x - y) lb ub Cont lb_lt_ub H1 H2) as (x,Hx).
     exists x.
     destruct Hx as (Hyp,Result).
     intuition.
     assert (Temp2 : x <> lb).
      intro Hfalse. rewrite Hfalse in Result.
      assert (Temp2 : y <> tan lb).
       apply Rgt_not_eq ; assumption.
      clear - Temp2 Result. apply Temp2.
      intuition.
     clear -Temp2 H3.
      case H3 ; intuition. apply False_ind ; apply Temp2 ; symmetry ; assumption.
      assert (Temp : x <> ub).
      intro Hfalse. rewrite Hfalse in Result.
      assert (Temp2 : y <> tan ub).
       apply Rlt_not_eq ; assumption.
      clear - Temp2 Result. apply Temp2.
      intuition.
      case H4 ; intuition.
Qed.

(** * Definition of arctangent as the reciprocal function of tangent and proof of this status *)
Lemma tan_1_gt_1 : tan 1 > 1.
Proof.
assert (0 < cos 1) by (apply cos_gt_0; assert (t:=PI2_1); lra).
assert (t1 : cos 1 <= 1 - 1/2 + 1/24).
 destruct (pre_cos_bound 1 0) as [_ t]; try lra; revert t.
 unfold cos_approx, cos_term; simpl; intros t; apply Rle_trans with (1:=t).
 clear t; apply Req_le; field.
assert (t2 : 1 - 1/6 <= sin 1).
 destruct (pre_sin_bound 1 0) as [t _]; try lra; revert t.
 unfold sin_approx, sin_term; simpl; intros t; apply Rle_trans with (2:=t).
 clear t; apply Req_le; field.
pattern 1 at 2; replace 1 with
  (cos 1 / cos 1) by (field; apply Rgt_not_eq; lra).
apply Rlt_gt; apply (Rmult_lt_compat_r (/ cos 1) (cos 1) (sin 1)).
 apply Rinv_0_lt_compat; assumption.
apply Rle_lt_trans with (1 := t1); apply Rlt_le_trans with (2 := t2).
lra.
Qed.

Definition frame_tan y : {x | 0 < x < PI/2 /\ Rabs y < tan x}.
Proof.
destruct (total_order_T (Rabs y) 1) as [Hs|Hgt].
 assert (yle1 : Rabs y <= 1) by (destruct Hs; lra).
 clear Hs; exists 1; split;[split; [exact Rlt_0_1 | exact PI2_1] | ].
 apply Rle_lt_trans with (1 := yle1); exact tan_1_gt_1.
assert (0 < / (Rabs y + 1)).
 apply Rinv_0_lt_compat; lra.
set (u := /2 * / (Rabs y + 1)).
assert (0 < u).
 apply Rmult_lt_0_compat; [lra | assumption].
assert (vlt1 : / (Rabs y + 1) < 1).
 apply Rmult_lt_reg_r with (Rabs y + 1).
  assert (t := Rabs_pos y); lra.
 rewrite Rinv_l; [rewrite Rmult_1_l | apply Rgt_not_eq]; lra.
assert (vlt2 : u < 1).
 apply Rlt_trans with (/ (Rabs y + 1)).
  rewrite double_var.
  assert (t : forall x, 0 < x -> x < x + x) by (clear; intros; lra).
  unfold u; rewrite Rmult_comm; apply t.
  unfold Rdiv; rewrite Rmult_comm; assumption.
 assumption.
assert(int : 0 < PI / 2 - u < PI / 2).
 split.
  assert (t := PI2_1); apply Rlt_Rminus, Rlt_trans with (2 := t); assumption.
 assert (dumb : forall x y, 0 < y -> x - y < x) by (clear; intros; lra).
 apply dumb; clear dumb; assumption.
exists (PI/2 - u).
assert (tmp : forall x y, 0 < x -> y < 1 -> x * y < x).
 clear; intros x y x0 y1; pattern x at 2; rewrite <- (Rmult_1_r x).
 apply Rmult_lt_compat_l; assumption.
assert (0 < sin u).
 apply sin_gt_0;[ assumption | ].
 assert (t := PI2_Rlt_PI); assert (t' := PI2_1).
 apply Rlt_trans with (2 := Rlt_trans _ _ _ t' t); assumption.
split.
 assumption.
 apply Rlt_trans with (/2 * / cos(PI / 2 - u)).
 rewrite cos_shift.
 assert (sin u < u).
  assert (t1 : 0 <= u) by (apply Rlt_le; assumption).
  assert (t2 : u <= 4) by
   (apply Rle_trans with 1;[apply Rlt_le | lra]; assumption).
  destruct (pre_sin_bound u 0 t1 t2) as [_ t].
  apply Rle_lt_trans with (1 := t); clear t1 t2 t.
  unfold sin_approx; simpl; unfold sin_term; simpl ((-1) ^ 0);
  replace ((-1) ^ 2) with 1 by ring; simpl ((-1) ^ 1);
  rewrite !Rmult_1_r, !Rmult_1_l; simpl plus; simpl (INR (fact 1)).
  rewrite <- (fun x => tech_pow_Rmult x 0), <- (fun x => tech_pow_Rmult x 2),
    <- (fun x => tech_pow_Rmult x 4).
  rewrite (Rmult_comm (-1)); simpl ((/(Rabs y + 1)) ^ 0).
  unfold Rdiv; rewrite Rinv_1, !Rmult_assoc, <- !Rmult_plus_distr_l.
  apply tmp;[assumption | ].
  rewrite Rplus_assoc, Rmult_1_l; pattern 1 at 2; rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l.
  rewrite <- Rmult_assoc.
  match goal with |- (?a * (-1)) + _ < 0 =>
   rewrite <- (Rplus_opp_l a); change (-1) with (-(1)); rewrite Ropp_mult_distr_r_reverse, Rmult_1_r
  end.
  apply Rplus_lt_compat_l.
  assert (0 < u ^ 2) by (apply pow_lt; assumption).
  replace (u ^ 4) with (u ^ 2 * u ^ 2) by ring.
 rewrite Rmult_assoc; apply Rmult_lt_compat_l; auto.
  apply Rlt_trans with (u ^ 2 * /INR (fact 3)).
   apply Rmult_lt_compat_l; auto.
   apply Rinv_lt_contravar.
    solve[apply Rmult_lt_0_compat; apply INR_fact_lt_0].
   rewrite !INR_IZR_INZ; apply IZR_lt; reflexivity.
  rewrite Rmult_comm; apply tmp.
   solve[apply Rinv_0_lt_compat, INR_fact_lt_0].
  apply Rlt_trans with (2 := vlt2).
  simpl; unfold u; apply tmp; auto; rewrite Rmult_1_r; assumption.
 apply Rlt_trans with (Rabs y + 1);[lra | ].
 pattern (Rabs y + 1) at 1; rewrite <- (Rinv_involutive (Rabs y + 1));
  [ | apply Rgt_not_eq; lra].
 rewrite <- Rinv_mult_distr.
   apply Rinv_lt_contravar.
    apply Rmult_lt_0_compat.
     apply Rmult_lt_0_compat;[lra | assumption].
    assumption.
   replace (/(Rabs y + 1)) with (2 * u).
    lra.
   unfold u; field; apply Rgt_not_eq; clear -Hgt; lra.
  solve[discrR].
 apply Rgt_not_eq; assumption.
unfold tan.
set (u' := PI / 2); unfold Rdiv; apply Rmult_lt_compat_r; unfold u'.
 apply Rinv_0_lt_compat. 
 rewrite cos_shift; assumption.
assert (vlt3 : u < /4).
 replace (/4) with (/2 * /2) by field.
 unfold u; apply Rmult_lt_compat_l;[lra | ].
 apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat; lra.
 lra.
assert (1 < PI / 2 - u) by (assert (t := PI2_3_2); lra).
apply Rlt_trans with (sin 1).
 assert (t' : 1 <= 4) by lra.
 destruct (pre_sin_bound 1 0 (Rlt_le _ _ Rlt_0_1) t') as [t _].
 apply Rlt_le_trans with (2 := t); clear t.
 simpl plus; replace (sin_approx 1 1) with (5/6);[lra | ].
 unfold sin_approx, sin_term; simpl; field.
apply sin_increasing_1.
    assert (t := PI2_1); lra.
   apply Rlt_le, PI2_1.
  assert (t := PI2_1); lra.
 lra.
assumption.
Qed.

Lemma ub_opp : forall x, x < PI/2 -> -PI/2 < -x.
Proof.
intros x h; rewrite Ropp_div; apply Ropp_lt_contravar; assumption.
Qed.

Lemma pos_opp_lt : forall x, 0 < x -> -x < x.
Proof. intros; lra. Qed.

Lemma tech_opp_tan : forall x y, -tan x < y -> tan (-x) < y.
Proof.
intros; rewrite tan_neg; assumption.
Qed.

Definition pre_atan (y : R) : {x : R | -PI/2 < x < PI/2 /\ tan x = y}.
Proof.
destruct (frame_tan y) as [ub [[ub0 ubpi2] Ptan_ub]].
set (pr := (conj (tech_opp_tan _ _ (proj2 (Rabs_def2 _ _ Ptan_ub)))
     (proj1 (Rabs_def2 _ _ Ptan_ub)))).
destruct (exists_atan_in_frame (-ub) ub y (pos_opp_lt _ ub0) (ub_opp _ ubpi2)
             ubpi2 pr) as [v [[vl vu] vq]].
exists v; clear pr.
split;[rewrite Ropp_div; split; lra | assumption].
Qed.

Definition atan x := let (v, _) := pre_atan x in v.

Lemma atan_bound : forall x, -PI/2 < atan x < PI/2.
Proof.
intros x; unfold atan; destruct (pre_atan x) as [v [int _]]; exact int.
Qed.

Lemma atan_right_inv : forall x, tan (atan x) = x.
Proof.
intros x; unfold atan; destruct (pre_atan x) as [v [_ q]]; exact q.
Qed.

Lemma atan_opp : forall x, atan (- x) = - atan x.
Proof.
intros x; generalize (atan_bound (-x)); rewrite Ropp_div;intros [a b].
generalize (atan_bound x); rewrite Ropp_div; intros [c d].
apply tan_is_inj; try rewrite Ropp_div; try split; try lra.
rewrite tan_neg, !atan_right_inv; reflexivity.
Qed.

Lemma derivable_pt_atan : forall x, derivable_pt atan x.
Proof.
intros x.
destruct (frame_tan x) as [ub [[ub0 ubpi] P]].
assert (lb_lt_ub : -ub < ub) by apply pos_opp_lt, ub0.
assert (xint : tan(-ub) < x < tan ub).
 assert (xint' : x < tan ub /\ -(tan ub) < x) by apply Rabs_def2, P.
  rewrite tan_neg; tauto.
assert (inv_p : forall x, tan(-ub) <= x -> x <= tan ub -> 
                     comp tan atan x = id x).
 intros; apply atan_right_inv.
assert (int_tan : forall y, tan (- ub) <= y -> y <= tan ub ->
                       -ub <= atan y <= ub).
 clear -ub0 ubpi; intros y lo up; split.
  destruct (Rle_lt_dec (-ub) (atan y)) as [h | abs]; auto.
  assert (y < tan (-ub)).
   rewrite <- (atan_right_inv y); apply tan_increasing.
     destruct (atan_bound y); assumption.
    assumption.
   lra.
  lra.
 destruct (Rle_lt_dec (atan y) ub) as [h | abs]; auto.
  assert (tan ub < y).
   rewrite <- (atan_right_inv y); apply tan_increasing.
    rewrite Ropp_div; lra.
   assumption.
  destruct (atan_bound y); assumption.
 lra.
assert (incr : forall x y, -ub <= x -> x < y -> y <= ub -> tan x < tan y).
 intros y z l yz u; apply tan_increasing.
   rewrite Ropp_div; lra.
  assumption.
 lra.
assert (der : forall a, -ub <= a <= ub -> derivable_pt tan a).
 intros a [la ua]; apply derivable_pt_tan.
 rewrite Ropp_div; split; lra.
assert (df_neq : derive_pt tan (atan x)
     (derivable_pt_recip_interv_prelim1 tan atan 
        (- ub) ub x lb_lt_ub xint inv_p int_tan incr der) <> 0).
 rewrite <- (pr_nu tan (atan x)
              (derivable_pt_tan (atan x) (atan_bound x))).
 rewrite derive_pt_tan.
 solve[apply Rgt_not_eq, plus_Rsqr_gt_0].
apply (derivable_pt_recip_interv tan atan (-ub) ub x
      lb_lt_ub xint inv_p int_tan incr der).
exact df_neq.
Qed.

Lemma atan_increasing : forall x y, x < y -> atan x < atan y.
Proof.
intros x y d.
assert (t1 := atan_bound x).
assert (t2 := atan_bound y).
destruct (Rlt_le_dec (atan x) (atan y)) as [lt | bad].
 assumption.
apply Rlt_not_le in d.
case d.
rewrite <- (atan_right_inv y), <- (atan_right_inv x).
destruct bad as [ylt | yx].
 apply Rlt_le, tan_increasing; try tauto.
solve[rewrite yx; apply Rle_refl].
Qed.

Lemma atan_0 : atan 0 = 0.
Proof.
apply tan_is_inj; try (apply atan_bound).
 assert (t := PI_RGT_0); rewrite Ropp_div; split; lra.
rewrite atan_right_inv, tan_0.
reflexivity.
Qed.

Lemma atan_1 : atan 1 = PI/4.
Proof.
assert (ut := PI_RGT_0).
assert (-PI/2 < PI/4 < PI/2) by (rewrite Ropp_div; split; lra).
assert (t := atan_bound 1).
apply tan_is_inj; auto.
rewrite tan_PI4, atan_right_inv; reflexivity.
Qed.

(** atan's derivative value is the function 1 / (1+x²) *)

Lemma derive_pt_atan : forall x,
      derive_pt atan x (derivable_pt_atan x) =
         1 / (1 + x²).
Proof.
intros x.
destruct (frame_tan x) as [ub [[ub0 ubpi] Pub]].
assert (lb_lt_ub : -ub < ub) by apply pos_opp_lt, ub0.
assert (xint : tan(-ub) < x < tan ub).
 assert (xint' : x < tan ub /\ -(tan ub) < x) by apply Rabs_def2, Pub.
  rewrite tan_neg; tauto.
assert (inv_p : forall x, tan(-ub) <= x -> x <= tan ub -> 
                     comp tan atan x = id x).
 intros; apply atan_right_inv.
assert (int_tan : forall y, tan (- ub) <= y -> y <= tan ub ->
                       -ub <= atan y <= ub).
 clear -ub0 ubpi; intros y lo up; split.
  destruct (Rle_lt_dec (-ub) (atan y)) as [h | abs]; auto.
  assert (y < tan (-ub)).
   rewrite <- (atan_right_inv y); apply tan_increasing.
     destruct (atan_bound y); assumption.
    assumption.
   lra.
  lra.
 destruct (Rle_lt_dec (atan y) ub) as [h | abs]; auto.
  assert (tan ub < y).
   rewrite <- (atan_right_inv y); apply tan_increasing.
    rewrite Ropp_div; lra.
   assumption.
  destruct (atan_bound y); assumption.
 lra.
assert (incr : forall x y, -ub <= x -> x < y -> y <= ub -> tan x < tan y).
 intros y z l yz u; apply tan_increasing.
   rewrite Ropp_div; lra.
  assumption.
 lra.
assert (der : forall a, -ub <= a <= ub -> derivable_pt tan a).
 intros a [la ua]; apply derivable_pt_tan.
 rewrite Ropp_div; split; lra.
assert (df_neq : derive_pt tan (atan x)
     (derivable_pt_recip_interv_prelim1 tan atan 
        (- ub) ub x lb_lt_ub xint inv_p int_tan incr der) <> 0).
 rewrite <- (pr_nu tan (atan x)
              (derivable_pt_tan (atan x) (atan_bound x))).
 rewrite derive_pt_tan.
 solve[apply Rgt_not_eq, plus_Rsqr_gt_0].
assert (t := derive_pt_recip_interv tan atan (-ub) ub x lb_lt_ub
        xint incr int_tan der inv_p df_neq).
rewrite <- (pr_nu atan x (derivable_pt_recip_interv tan atan (- ub) ub
      x lb_lt_ub xint inv_p int_tan incr der df_neq)).
rewrite t.
assert (t' := atan_bound x).
rewrite <- (pr_nu tan (atan x) (derivable_pt_tan _ t')). 
rewrite derive_pt_tan, atan_right_inv.
replace (Rsqr x) with (x ^ 2) by (unfold Rsqr; ring).
reflexivity.
Qed.

Lemma derivable_pt_lim_atan :
  forall x, derivable_pt_lim atan x (/(1 + x^2)).
Proof.
intros x.
apply derive_pt_eq_1 with (derivable_pt_atan x).
replace (x ^ 2) with (x * x) by ring.
rewrite <- (Rmult_1_l (Rinv _)).
apply derive_pt_atan.
Qed.

(** * Definition of the arctangent function as the sum of the arctan power series *)
(* Proof taken from Guillaume Melquiond's interval package for Coq *)

Definition Ratan_seq x :=  fun n => (x ^ (2 * n + 1) / INR (2 * n + 1))%R.

Lemma Ratan_seq_decreasing : forall x, (0 <= x <= 1)%R -> Un_decreasing (Ratan_seq x).
Proof.
intros x Hx n.
 unfold Ratan_seq, Rdiv.
 apply Rmult_le_compat. apply pow_le.
 exact (proj1 Hx).
 apply Rlt_le.
 apply Rinv_0_lt_compat.
 apply lt_INR_0.
 omega.
 destruct (proj1 Hx) as [Hx1|Hx1].
 destruct (proj2 Hx) as [Hx2|Hx2].
 (* . 0 < x < 1 *)
 rewrite <- (Rinv_involutive x).
 assert (/ x <> 0)%R by auto with real.
 repeat rewrite <- Rinv_pow with (1 := H).
 apply Rlt_le.
 apply Rinv_lt_contravar.
 apply Rmult_lt_0_compat ; apply pow_lt ; auto with real.
 apply Rlt_pow.
 rewrite <- Rinv_1.
 apply Rinv_lt_contravar.
 rewrite Rmult_1_r.
 exact Hx1.
 exact Hx2.
 omega.
 apply Rgt_not_eq.
 exact Hx1.
 (* . x = 1 *)
 rewrite Hx2.
 do 2 rewrite pow1.
 apply Rle_refl.
 (* . x = 0 *)
 rewrite <- Hx1.
 do 2 (rewrite pow_i ; [ idtac | omega ]).
 apply Rle_refl.
 apply Rlt_le.
 apply Rinv_lt_contravar.
 apply Rmult_lt_0_compat ; apply lt_INR_0 ; omega.
 apply lt_INR.
 omega.
Qed.

Lemma Ratan_seq_converging : forall x, (0 <= x <= 1)%R -> Un_cv (Ratan_seq x) 0.
Proof.
intros x Hx eps Heps.
 destruct (archimed (/ eps)) as (HN,_).
 assert (0 < up (/ eps))%Z.
  apply lt_IZR.
  apply Rlt_trans with (2 := HN).
  apply Rinv_0_lt_compat.
  exact Heps.
 case_eq (up (/ eps)) ;
  intros ; rewrite H0 in H ; try discriminate H.
   rewrite H0 in HN.
   simpl in HN.
   pose (N := Pos.to_nat p).
   fold N in HN.
   clear H H0.
   exists N.
  intros n Hn.
   unfold R_dist.
   rewrite Rminus_0_r.
   unfold Ratan_seq.
   rewrite Rabs_right.
   apply Rle_lt_trans with (1 ^ (2 * n + 1) / INR (2 * n + 1))%R.
   unfold Rdiv.
   apply Rmult_le_compat_r.
   apply Rlt_le.
   apply Rinv_0_lt_compat.
   apply lt_INR_0.
   omega.
   apply pow_incr.
   exact Hx.
   rewrite pow1.
   apply Rle_lt_trans with (/ INR (2 * N + 1))%R.
   unfold Rdiv.
   rewrite Rmult_1_l.
   apply Rinv_le_contravar.
   apply lt_INR_0.
   omega.
   apply le_INR.
   omega.
   rewrite <- (Rinv_involutive eps).
   apply Rinv_lt_contravar.
   apply Rmult_lt_0_compat.
   auto with real.
   apply lt_INR_0.
   omega.
   apply Rlt_trans with (INR N).
   destruct (archimed (/ eps)) as (H,_).
   assert (0 < up (/ eps))%Z.
   apply lt_IZR.
   apply Rlt_trans with (2 := H).
   apply Rinv_0_lt_compat.
   exact Heps.
   unfold N.
   rewrite INR_IZR_INZ, positive_nat_Z.
   exact HN.
   apply lt_INR.
   omega.
   apply Rgt_not_eq.
   exact Heps.
   apply Rle_ge.
   unfold Rdiv.
   apply Rmult_le_pos.
   apply pow_le.
   exact (proj1 Hx).
   apply Rlt_le.
   apply Rinv_0_lt_compat.
   apply lt_INR_0.
   omega.
Qed.

Definition ps_atan_exists_01 (x : R) (Hx:0 <= x <= 1) :
   {l : R | Un_cv (fun N : nat => sum_f_R0 (tg_alt (Ratan_seq x)) N) l}.
Proof.
exact (alternated_series (Ratan_seq x)
  (Ratan_seq_decreasing _ Hx) (Ratan_seq_converging _ Hx)).
Defined.

Lemma Ratan_seq_opp : forall x n, Ratan_seq (-x) n = -Ratan_seq x n.
Proof.
intros x n; unfold Ratan_seq.
rewrite !pow_add, !pow_mult, !pow_1.
unfold Rdiv; replace ((-x) ^ 2) with (x ^ 2) by ring; ring.
Qed.

Lemma sum_Ratan_seq_opp : 
  forall x n, sum_f_R0 (tg_alt (Ratan_seq (- x))) n =
     - sum_f_R0 (tg_alt (Ratan_seq x)) n.
Proof.
intros x n; replace (-sum_f_R0 (tg_alt (Ratan_seq x)) n) with 
  (-1 * sum_f_R0 (tg_alt (Ratan_seq x)) n) by ring.
rewrite scal_sum; apply sum_eq; intros i _; unfold tg_alt.
rewrite Ratan_seq_opp; ring.
Qed.

Definition ps_atan_exists_1 (x : R) (Hx : -1 <= x <= 1) :
   {l : R | Un_cv (fun N : nat => sum_f_R0 (tg_alt (Ratan_seq x)) N) l}.
Proof.
destruct (Rle_lt_dec 0 x).
 assert (pr : 0 <= x <= 1) by tauto.
 exact (ps_atan_exists_01 x pr).
assert (pr : 0 <= -x <= 1) by (destruct Hx; split; lra).
destruct (ps_atan_exists_01 _ pr) as [v Pv].
exists (-v).
 apply (Un_cv_ext (fun n => (- 1) * sum_f_R0 (tg_alt (Ratan_seq (- x))) n)).
 intros n; rewrite sum_Ratan_seq_opp; ring.
replace (-v) with (-1 * v) by ring.
apply CV_mult;[ | assumption].
solve[intros; exists 0%nat; intros; rewrite R_dist_eq; auto].
Qed.

Definition in_int (x : R) : {-1 <= x <= 1}+{~ -1 <= x <= 1}.
Proof.
destruct (Rle_lt_dec x 1).
 destruct (Rle_lt_dec (-1) x).
  left;split; auto.
 right;intros [a1 a2]; lra.
right;intros [a1 a2]; lra.
Qed.

Definition ps_atan (x : R) : R :=
 match in_int x with
   left h => let (v, _) := ps_atan_exists_1 x h in v
 | right h => atan x
 end.

(** * Proof of the equivalence of the two definitions between -1 and 1 *)

Lemma ps_atan0_0 : ps_atan 0 = 0.
Proof.
unfold ps_atan.
 destruct (in_int 0) as [h1 | h2].
 destruct (ps_atan_exists_1 0 h1) as [v P].
 apply (UL_sequence _ _ _ P).
  apply (Un_cv_ext (fun n => 0)).
  symmetry;apply sum_eq_R0.
  intros i _; unfold tg_alt, Ratan_seq; rewrite plus_comm; simpl.
  unfold Rdiv; rewrite !Rmult_0_l, Rmult_0_r; reflexivity.
 intros eps ep; exists 0%nat; intros n _; unfold R_dist.
 rewrite Rminus_0_r, Rabs_pos_eq; auto with real.
case h2; split; lra.
Qed.

Lemma ps_atan_exists_1_opp :
  forall x h h', proj1_sig (ps_atan_exists_1 (-x) h) = 
     -(proj1_sig (ps_atan_exists_1 x h')).
Proof.
intros x h h'; destruct (ps_atan_exists_1 (-x) h) as [v Pv].
destruct (ps_atan_exists_1 x h') as [u Pu]; simpl.
assert (Pu' : Un_cv (fun N => (-1) * sum_f_R0 (tg_alt (Ratan_seq x)) N) (-1 * u)).
 apply CV_mult;[ | assumption].
 intros eps ep; exists 0%nat; intros; rewrite R_dist_eq; assumption.  
assert (Pv' : Un_cv
           (fun N : nat => -1 * sum_f_R0 (tg_alt (Ratan_seq x)) N) v).
 apply Un_cv_ext with (2 := Pv); intros n; rewrite sum_Ratan_seq_opp; ring.
replace (-u) with (-1 * u) by ring.
apply UL_sequence with (1:=Pv') (2:= Pu').
Qed.

Lemma ps_atan_opp : forall x, ps_atan (-x) = -ps_atan x.
Proof.
intros x; unfold ps_atan.
destruct (in_int (- x)) as [inside | outside].
 destruct (in_int x) as [ins' | outs'].
 generalize (ps_atan_exists_1_opp x inside ins').
  intros h; exact h.
 destruct inside; case outs'; split; lra.
destruct (in_int x) as [ins' | outs'].
 destruct outside; case ins'; split; lra.
apply atan_opp.
Qed.

(** atan = ps_atan *)

Lemma ps_atanSeq_continuity_pt_1 : forall (N:nat) (x:R),
      0 <= x ->
      x <= 1 ->
      continuity_pt (fun x => sum_f_R0 (tg_alt (Ratan_seq x)) N) x.
Proof.
assert (Sublemma : forall (x:R) (N:nat), sum_f_R0 (tg_alt (Ratan_seq x)) N = x * (comp (fun x => sum_f_R0 (fun n => (fun i : nat => (-1) ^ i / INR (2 * i + 1)) n * x ^ n) N) (fun x => x ^ 2) x)).
 intros x N.
  induction N.
   unfold tg_alt, Ratan_seq, comp ; simpl ; field.
   simpl sum_f_R0 at 1.
   rewrite IHN.
   replace (comp (fun x => sum_f_R0 (fun n : nat => (-1) ^ n / INR (2 * n + 1) * x ^ n) (S N)) (fun x => x ^ 2))
     with (comp (fun x => sum_f_R0 (fun n : nat => (-1) ^ n / INR (2 * n + 1) * x ^ n) N + (-1) ^ (S N) / INR (2 * (S N) + 1) * x ^ (S N)) (fun x => x ^ 2)).
   unfold comp.
   rewrite Rmult_plus_distr_l.
   apply Rplus_eq_compat_l.
   unfold tg_alt, Ratan_seq.
   rewrite <- Rmult_assoc.
   case (Req_dec x 0) ; intro Hyp.
   rewrite Hyp ; rewrite pow_i. rewrite Rmult_0_l ; rewrite Rmult_0_l.
   unfold Rdiv ; rewrite Rmult_0_l ; rewrite Rmult_0_r ; reflexivity.
   intuition.
   replace (x * ((-1) ^ S N / INR (2 * S N + 1)) * (x ^ 2) ^ S N) with (x ^ (2 * S N + 1) * ((-1) ^ S N / INR (2 * S N + 1))).
   rewrite Rmult_comm ; unfold Rdiv at 1.
   rewrite Rmult_assoc ; apply Rmult_eq_compat_l.
   field. apply Rgt_not_eq ; intuition.
   rewrite Rmult_assoc.
   replace (x * ((-1) ^ S N / INR (2 * S N + 1) * (x ^ 2) ^ S N)) with (((-1) ^ S N / INR (2 * S N + 1) * (x ^ 2) ^ S N) * x).
   rewrite Rmult_assoc.
   replace ((x ^ 2) ^ S N * x) with (x ^ (2 * S N + 1)).
   rewrite Rmult_comm at 1 ; reflexivity.
   rewrite <- pow_mult.
   assert (Temp : forall x n, x ^ n * x = x ^ (n+1)).
    intros a n ; induction n. rewrite pow_O. simpl ; intuition.
    simpl ; rewrite Rmult_assoc ; rewrite IHn ; intuition.
   rewrite Temp ; reflexivity.
   rewrite Rmult_comm ; reflexivity.
   intuition.
intros N x x_lb x_ub.
 intros eps eps_pos.
 assert (continuity_id : continuity id).
 apply derivable_continuous ; exact derivable_id.
assert (Temp := continuity_mult id (comp
        (fun x1 : R =>
         sum_f_R0 (fun n : nat => (-1) ^ n / INR (2 * n + 1) * x1 ^ n) N)
        (fun x1 : R => x1 ^ 2))
           continuity_id).
assert (Temp2 : continuity
    (comp
       (fun x1 : R =>
        sum_f_R0 (fun n : nat => (-1) ^ n / INR (2 * n + 1) * x1 ^ n) N)
       (fun x1 : R => x1 ^ 2))).
 apply continuity_comp.
 reg.
 apply continuity_finite_sum.
 elim (Temp Temp2 x eps eps_pos) ; clear Temp Temp2 ; intros alpha T ; destruct T as (alpha_pos, T).
 exists alpha ; split.
 intuition.
intros x0 x0_cond.
 rewrite Sublemma ; rewrite Sublemma.
apply T.
intuition.
Qed.

(** Definition of ps_atan's derivative *)

Definition Datan_seq := fun (x:R) (n:nat) => x ^ (2*n).

Lemma pow_lt_1_compat : forall x n, 0 <= x < 1 -> (0 < n)%nat ->
   0 <= x ^ n < 1.
Proof.
intros x n hx; induction 1; simpl.
 rewrite Rmult_1_r; tauto.
split.
 apply Rmult_le_pos; tauto.
rewrite <- (Rmult_1_r 1); apply Rmult_le_0_lt_compat; intuition.
Qed.

Lemma Datan_seq_Rabs : forall x n, Datan_seq (Rabs x) n = Datan_seq x n.
Proof.
intros x n; unfold Datan_seq; rewrite !pow_mult, pow2_abs; reflexivity.
Qed.

Lemma Datan_seq_pos : forall x n, 0 < x -> 0 < Datan_seq x n.
Proof.
intros x n x_lb ; unfold Datan_seq ; induction n.
 simpl ; intuition.
 replace (x ^ (2 * S n)) with ((x ^ 2) * (x ^ (2 * n))).
 apply Rmult_gt_0_compat.
 replace (x^2) with (x*x) by field ; apply Rmult_gt_0_compat ; assumption.
 assumption.
 replace (2 * S n)%nat with (S (S (2 * n))) by intuition.
 simpl ; field.
Qed.

Lemma Datan_sum_eq :forall x n,
  sum_f_R0 (tg_alt (Datan_seq x)) n = (1 - (- x ^ 2) ^ S n)/(1 + x ^ 2).
Proof.
intros x n.
assert (dif : - x ^ 2 <> 1).
apply Rlt_not_eq; apply Rle_lt_trans with 0;[ | apply Rlt_0_1].
assert (t := pow2_ge_0 x); lra.
replace (1 + x ^ 2) with (1 - - (x ^ 2)) by ring; rewrite <- (tech3 _ n dif).
apply sum_eq; unfold tg_alt, Datan_seq; intros i _.
rewrite pow_mult, <- Rpow_mult_distr.
f_equal.
ring.
Qed.

Lemma Datan_seq_increasing : forall x y n, (n > 0)%nat -> 0 <= x < y -> Datan_seq x n < Datan_seq y n.
Proof.
intros x y n n_lb x_encad ; assert (x_pos : x >= 0) by intuition.
 assert (y_pos : y > 0). apply Rle_lt_trans with (r2:=x) ; intuition.
 induction n.
 apply False_ind ; intuition.
 clear -x_encad x_pos y_pos ; induction n ; unfold Datan_seq.
 case x_pos ; clear x_pos ; intro x_pos.
 simpl ; apply Rmult_gt_0_lt_compat ; intuition. lra.
 rewrite x_pos ; rewrite pow_i. replace (y ^ (2*1)) with (y*y).
 apply Rmult_gt_0_compat ; assumption.
 simpl ; field.
 intuition.
 assert (Hrew : forall a, a^(2 * S (S n)) = (a ^ 2) * (a ^ (2 * S n))).
  clear ; intro a ; replace (2 * S (S n))%nat with (S (S (2 * S n)))%nat by intuition.
  simpl ; field.
 case x_pos ; clear x_pos ; intro x_pos.
 rewrite Hrew ; rewrite Hrew.
 apply Rmult_gt_0_lt_compat ; intuition.
 apply Rmult_gt_0_lt_compat ; intuition ; lra.
 rewrite x_pos.
 rewrite pow_i ; intuition.
Qed.

Lemma Datan_seq_decreasing : forall x,  -1 < x -> x < 1 -> Un_decreasing (Datan_seq x).
Proof.
intros x x_lb x_ub n.
unfold Datan_seq.
replace (2 * S n)%nat with (2 + 2 * n)%nat by ring.
rewrite <- (Rmult_1_l (x ^ (2 * n))).
rewrite pow_add.
apply Rmult_le_compat_r.
rewrite pow_mult; apply pow_le, pow2_ge_0.
apply Rlt_le; rewrite <- pow2_abs.
assert (intabs : 0 <= Rabs x < 1).
 split;[apply Rabs_pos | apply Rabs_def1]; tauto.
apply (pow_lt_1_compat (Rabs x) 2) in intabs.
 tauto.
omega.
Qed.

Lemma Datan_seq_CV_0 : forall x, -1 < x -> x < 1 -> Un_cv (Datan_seq x) 0.
Proof.
intros x x_lb x_ub eps eps_pos.
assert (x_ub2 : Rabs (x^2) < 1).
 rewrite Rabs_pos_eq;[ | apply pow2_ge_0].
 rewrite <- pow2_abs.
 assert (H: 0 <= Rabs x < 1)
   by (split;[apply Rabs_pos | apply Rabs_def1; auto]).
 apply (pow_lt_1_compat _ 2) in H;[tauto | omega].
elim (pow_lt_1_zero (x^2) x_ub2 eps eps_pos) ; intros N HN ; exists N ; intros n Hn.
unfold R_dist, Datan_seq.
replace (x ^ (2 * n) - 0) with ((x ^ 2) ^ n). apply HN ; assumption.
rewrite pow_mult ; field.
Qed.

Lemma Datan_lim : forall x, -1 < x -> x < 1 ->
    Un_cv (fun N : nat => sum_f_R0 (tg_alt (Datan_seq x)) N) (/ (1 + x ^ 2)).
Proof.
intros x x_lb x_ub eps eps_pos.
assert (Tool0 : 0 <= x ^ 2) by apply pow2_ge_0.
assert (Tool1 : 0 < (1 + x ^ 2)).
 solve[apply Rplus_lt_le_0_compat ; intuition].
assert (Tool2 : / (1 + x ^ 2) > 0).
 apply Rinv_0_lt_compat ; tauto.
assert (x_ub2' : 0<= Rabs (x^2) < 1).
 rewrite Rabs_pos_eq, <- pow2_abs;[ | apply pow2_ge_0].
 apply pow_lt_1_compat;[split;[apply Rabs_pos | ] | omega].
 apply Rabs_def1; assumption.
assert (x_ub2 : Rabs (x^2) < 1) by tauto.
assert (eps'_pos : ((1+x^2)*eps) > 0).
  apply Rmult_gt_0_compat ; assumption.
elim (pow_lt_1_zero _ x_ub2 _ eps'_pos) ; intros N HN ; exists N.
intros n Hn.
assert (H1 : - x^2 <> 1).
 apply Rlt_not_eq; apply Rle_lt_trans with (2 := Rlt_0_1).
assert (t := pow2_ge_0 x); lra.
rewrite Datan_sum_eq. 
unfold R_dist.
assert (tool : forall a b, a / b - /b = (-1 + a) /b).
 intros a b; rewrite <- (Rmult_1_l (/b)); unfold Rdiv, Rminus.
 rewrite <- Ropp_mult_distr_l_reverse, Rmult_plus_distr_r, Rplus_comm.
 reflexivity.
set (u := 1 + x ^ 2); rewrite tool; unfold Rminus; rewrite <- Rplus_assoc.
unfold Rdiv, u.
change (-1) with (-(1)).
rewrite Rplus_opp_l, Rplus_0_l, Ropp_mult_distr_l_reverse, Rabs_Ropp.
rewrite Rabs_mult; clear tool u.
assert (tool : forall k, Rabs ((-x ^ 2) ^ k) = Rabs ((x ^ 2) ^ k)).
 clear -Tool0; induction k;[simpl; rewrite Rabs_R1;tauto | ].
 rewrite <- !(tech_pow_Rmult _ k), !Rabs_mult, Rabs_Ropp, IHk, Rabs_pos_eq.
  reflexivity.
 exact Tool0.
rewrite tool, (Rabs_pos_eq (/ _)); clear tool;[ | apply Rlt_le; assumption].
assert (tool : forall a b c, 0 < b -> a < b * c -> a * / b < c).
 intros a b c bp h; replace c with (b * c * /b).
  apply Rmult_lt_compat_r.  
   apply Rinv_0_lt_compat; assumption.
  assumption.
 field; apply Rgt_not_eq; exact bp.
apply tool;[exact Tool1 | ].
apply HN; omega.
Qed.

Lemma Datan_CVU_prelim : forall c (r : posreal), Rabs c + r < 1 ->
 CVU (fun N x => sum_f_R0 (tg_alt (Datan_seq x)) N)
     (fun y : R => / (1 + y ^ 2)) c r.
Proof.
intros c r ub_ub eps eps_pos.
apply (Alt_CVU (fun x n => Datan_seq n x) 
         (fun x => /(1 + x ^ 2))
         (Datan_seq (Rabs c + r)) c r).
     intros x inb; apply Datan_seq_decreasing;
      try (apply Boule_lt in inb; apply Rabs_def2 in inb;
         destruct inb; lra).
    intros x inb; apply Datan_seq_CV_0;
      try (apply Boule_lt in inb; apply Rabs_def2 in inb;
         destruct inb; lra).
   intros x inb; apply (Datan_lim x);
      try (apply Boule_lt in inb; apply Rabs_def2 in inb;
         destruct inb; lra).
  intros x [ | n] inb.
   solve[unfold Datan_seq; apply Rle_refl].
  rewrite <- (Datan_seq_Rabs x); apply Rlt_le, Datan_seq_increasing.
   omega.
  apply Boule_lt in inb; intuition.
  solve[apply Rabs_pos].
 apply Datan_seq_CV_0.
  apply Rlt_trans with 0;[lra | ].
  apply Rplus_le_lt_0_compat.
   solve[apply Rabs_pos].
  destruct r; assumption.
 assumption.
assumption.
Qed.

Lemma Datan_is_datan : forall (N:nat) (x:R),
      -1 <= x ->
      x < 1 ->
derivable_pt_lim (fun x => sum_f_R0 (tg_alt (Ratan_seq x)) N) x (sum_f_R0 (tg_alt (Datan_seq x)) N).
Proof.
assert (Tool : forall N, (-1) ^ (S (2 * N))  = - 1).
 intro n ; induction n.
  simpl ; field.
  replace ((-1) ^ S (2 * S n)) with ((-1) ^ 2 * (-1) ^ S (2*n)).
  rewrite IHn ; field.
  rewrite <- pow_add.
  replace (2 + S (2 * n))%nat with (S (2 * S n))%nat.
  reflexivity.
  intuition.
intros N x x_lb x_ub.
 induction N.
  unfold Datan_seq, Ratan_seq, tg_alt ; simpl.
  intros eps eps_pos.
   elim (derivable_pt_lim_id x eps eps_pos) ; intros delta Hdelta ; exists delta.
   intros h hneq h_b.
    replace (1 * ((x + h) * 1 / 1) - 1 * (x * 1 / 1)) with (id (x + h) - id x). 
    rewrite Rmult_1_r.
    apply Hdelta ; assumption.
    unfold id ; field ; assumption.
  intros eps eps_pos.
  assert (eps_3_pos : (eps/3) > 0) by lra.
  elim (IHN (eps/3) eps_3_pos) ; intros delta1 Hdelta1.
  assert (Main : derivable_pt_lim (fun x : R =>tg_alt (Ratan_seq x) (S N)) x ((tg_alt (Datan_seq x)) (S N))).
   clear -Tool ; intros eps' eps'_pos.
   elim (derivable_pt_lim_pow x (2 * (S N) + 1) eps' eps'_pos) ; intros delta Hdelta ; exists delta.
   intros h h_neq h_b ; unfold tg_alt, Ratan_seq, Datan_seq.
   replace (((-1) ^ S N * ((x + h) ^ (2 * S N + 1) / INR (2 * S N + 1)) -
    (-1) ^ S N * (x ^ (2 * S N + 1) / INR (2 * S N + 1))) / h -
    (-1) ^ S N * x ^ (2 * S N)) 
    with (((-1)^(S N)) * ((((x + h) ^ (2 * S N + 1) / INR (2 * S N + 1)) -
    (x ^ (2 * S N + 1) / INR (2 * S N + 1))) / h - x ^ (2 * S N))).
   rewrite Rabs_mult ; rewrite pow_1_abs ; rewrite Rmult_1_l.
   replace (((x + h) ^ (2 * S N + 1) / INR (2 * S N + 1) -
    x ^ (2 * S N + 1) / INR (2 * S N + 1)) / h - x ^ (2 * S N))
    with ((/INR (2* S N + 1)) * (((x + h) ^ (2 * S N + 1) - x ^ (2 * S N + 1)) / h -
    INR (2 * S N + 1) * x ^ pred (2 * S N + 1))).
   rewrite Rabs_mult.
   case (Req_dec (((x + h) ^ (2 * S N + 1) - x ^ (2 * S N + 1)) / h -
     INR (2 * S N + 1) * x ^ pred (2 * S N + 1)) 0) ; intro Heq.
   rewrite Heq ; rewrite Rabs_R0 ; rewrite Rmult_0_r ; assumption.
   apply Rlt_trans with (r2:=Rabs
           (((x + h) ^ (2 * S N + 1) - x ^ (2 * S N + 1)) / h -
            INR (2 * S N + 1) * x ^ pred (2 * S N + 1))).
   rewrite <- Rmult_1_l ; apply Rmult_lt_compat_r.
   apply Rabs_pos_lt ; assumption.
   rewrite Rabs_right.
   replace 1 with (/1) by field.
   apply Rinv_1_lt_contravar ; intuition.
   apply Rgt_ge ; replace (INR (2 * S N + 1)) with (INR (2*S N) + 1) ;
   [apply RiemannInt.RinvN_pos | ].
   replace (2 * S N + 1)%nat with (S (2 * S N))%nat by intuition ;
   rewrite S_INR ; reflexivity.
   apply Hdelta ; assumption.
   rewrite Rmult_minus_distr_l.
   replace (/ INR (2 * S N + 1) * (INR (2 * S N + 1) * x ^ pred (2 * S N + 1))) with (x ^ (2 * S N)).
   unfold Rminus ; rewrite Rplus_comm.
   replace (((x + h) ^ (2 * S N + 1) / INR (2 * S N + 1) +
      - (x ^ (2 * S N + 1) / INR (2 * S N + 1))) / h + - x ^ (2 * S N))
      with (- x ^ (2 * S N) + (((x + h) ^ (2 * S N + 1) / INR (2 * S N + 1) +
      - (x ^ (2 * S N + 1) / INR (2 * S N + 1))) / h)) by intuition.
   apply Rplus_eq_compat_l. field.
   split ; [apply Rgt_not_eq|] ; intuition.
   clear ; replace (pred (2 * S N + 1)) with (2 * S N)%nat by intuition.
   field ; apply Rgt_not_eq ; intuition.
   field ; split ; [apply Rgt_not_eq |] ; intuition.
   elim (Main (eps/3) eps_3_pos) ; intros delta2 Hdelta2.
   destruct delta1 as (delta1, delta1_pos) ; destruct delta2 as (delta2, delta2_pos).
   pose (mydelta := Rmin delta1 delta2).
   assert (mydelta_pos : mydelta > 0).
    unfold mydelta ; rewrite Rmin_Rgt ; split ; assumption.
   pose (delta := mkposreal mydelta mydelta_pos) ; exists delta ; intros h h_neq h_b.
   clear Main IHN.
   unfold Rminus at 1.
   apply Rle_lt_trans with (r2:=eps/3 + eps / 3).
   assert (Temp : (sum_f_R0 (tg_alt (Ratan_seq (x + h))) (S N) -
    sum_f_R0 (tg_alt (Ratan_seq x)) (S N)) / h +
    - sum_f_R0 (tg_alt (Datan_seq x)) (S N) = ((sum_f_R0 (tg_alt (Ratan_seq (x + h))) N -
              sum_f_R0 (tg_alt (Ratan_seq x)) N) / h) + (-
             sum_f_R0 (tg_alt (Datan_seq x)) N) + ((tg_alt (Ratan_seq (x + h)) (S N) - tg_alt (Ratan_seq x) (S N)) /
             h - tg_alt (Datan_seq x) (S N))).
    simpl ; field ; intuition.
   apply Rle_trans with (r2:= Rabs ((sum_f_R0 (tg_alt (Ratan_seq (x + h))) N -
        sum_f_R0 (tg_alt (Ratan_seq x)) N) / h +
       - sum_f_R0 (tg_alt (Datan_seq x)) N) +
       Rabs ((tg_alt (Ratan_seq (x + h)) (S N) - tg_alt (Ratan_seq x) (S N)) / h -
        tg_alt (Datan_seq x) (S N))).
   rewrite Temp ; clear Temp ; apply Rabs_triang.
   apply Rplus_le_compat ; apply Rlt_le ; [apply Hdelta1 | apply Hdelta2] ;
   intuition ; apply Rlt_le_trans with (r2:=delta) ; intuition unfold delta, mydelta.
   apply Rmin_l.
   apply Rmin_r.
   lra.
Qed.

Lemma Ratan_CVU' :
  CVU (fun N x => sum_f_R0 (tg_alt (Ratan_seq x)) N)
                     ps_atan (/2) (mkposreal (/2) pos_half_prf).
Proof.
apply (Alt_CVU (fun i r => Ratan_seq r i) ps_atan PI_tg (/2) pos_half);
  lazy beta.
    now intros; apply Ratan_seq_decreasing, Boule_half_to_interval.
   now intros; apply Ratan_seq_converging, Boule_half_to_interval.
  intros x b; apply Boule_half_to_interval in b.
  unfold ps_atan; destruct (in_int x) as [inside | outside];
   [ | destruct b; case outside; split; lra].
  destruct (ps_atan_exists_1 x inside) as [v Pv].
  apply Un_cv_ext with (2 := Pv);[reflexivity].
 intros x n b; apply Boule_half_to_interval in b.
 rewrite <- (Rmult_1_l (PI_tg n)); unfold Ratan_seq, PI_tg. 
 apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat, (lt_INR 0); omega.
 rewrite <- (pow1 (2 * n + 1)); apply pow_incr; assumption.
exact PI_tg_cv.
Qed.

Lemma Ratan_CVU :
  CVU (fun N x => sum_f_R0 (tg_alt (Ratan_seq x)) N)
                     ps_atan 0  (mkposreal 1 Rlt_0_1).
Proof.
intros eps ep; destruct (Ratan_CVU' eps ep) as [N Pn].
exists N; intros n x nN b_y.
case (Rtotal_order 0 x) as [xgt0 | [x0 | x0]].
  assert (Boule (/2) {| pos := / 2; cond_pos := pos_half_prf|} x).
   revert b_y; unfold Boule; simpl; intros b_y; apply Rabs_def2 in b_y.
   destruct b_y; unfold Boule; simpl; apply Rabs_def1; lra.
  apply Pn; assumption.
 rewrite <- x0, ps_atan0_0.
 rewrite <- (sum_eq (fun _ => 0)), sum_cte, Rmult_0_l, Rminus_0_r, Rabs_pos_eq.
   assumption.
  apply Rle_refl.
 intros i _; unfold tg_alt, Ratan_seq, Rdiv; rewrite plus_comm; simpl.
 solve[rewrite !Rmult_0_l, Rmult_0_r; auto].
replace (ps_atan x - sum_f_R0 (tg_alt (Ratan_seq x)) n) with
  (-(ps_atan (-x) - sum_f_R0 (tg_alt (Ratan_seq (-x))) n)).
 rewrite Rabs_Ropp.
 assert (Boule (/2) {| pos := / 2; cond_pos := pos_half_prf|} (-x)).
  revert b_y; unfold Boule; simpl; intros b_y; apply Rabs_def2 in b_y.
  destruct b_y; unfold Boule; simpl; apply Rabs_def1; lra.
 apply Pn; assumption.
unfold Rminus; rewrite ps_atan_opp, Ropp_plus_distr, sum_Ratan_seq_opp.
rewrite !Ropp_involutive; reflexivity.
Qed.

Lemma Alt_PI_tg : forall n, PI_tg n = Ratan_seq 1 n.
Proof.
intros n; unfold PI_tg, Ratan_seq, Rdiv; rewrite pow1, Rmult_1_l.
reflexivity.
Qed.

Lemma Ratan_is_ps_atan : forall eps, eps > 0 ->
       exists N, forall n, (n >= N)%nat -> forall x, -1 < x -> x < 1 ->
       Rabs (sum_f_R0 (tg_alt (Ratan_seq x)) n - ps_atan x) < eps.
Proof.
intros eps ep.
destruct (Ratan_CVU _ ep) as [N1 PN1].
exists N1; intros n nN x xm1 x1; rewrite <- Rabs_Ropp, Ropp_minus_distr.
apply PN1; [assumption | ].
unfold Boule; simpl; rewrite Rminus_0_r; apply Rabs_def1; assumption.
Qed.

Lemma Datan_continuity : continuity (fun x => /(1+x ^ 2)).
Proof.
apply continuity_inv.
apply continuity_plus.
apply continuity_const ; unfold constant ; intuition.
apply derivable_continuous ; apply derivable_pow.
intro x ; apply Rgt_not_eq ; apply Rge_gt_trans with (1+0) ; [|lra] ;
 apply Rplus_ge_compat_l.
 replace (x^2) with (x²).
 apply Rle_ge ; apply Rle_0_sqr.
 unfold Rsqr ; field.
Qed.

Lemma derivable_pt_lim_ps_atan : forall x, -1 < x < 1 ->
  derivable_pt_lim ps_atan x ((fun y => /(1 + y ^ 2)) x).
Proof.
intros x x_encad.
destruct (boule_in_interval (-1) 1 x x_encad) as [c [r [Pcr1 [P1 P2]]]].
change (/ (1 + x ^ 2)) with ((fun u => /(1 + u ^ 2)) x).
assert (t := derivable_pt_lim_CVU).
apply derivable_pt_lim_CVU with 
          (fn := (fun N x => sum_f_R0 (tg_alt (Ratan_seq x)) N))
          (fn' := (fun N x => sum_f_R0 (tg_alt (Datan_seq x)) N))
          (c := c) (r := r).
    assumption.
   intros y N inb; apply Rabs_def2 in inb; destruct inb.
   apply Datan_is_datan.
    lra.
   lra.
  intros y inb; apply Rabs_def2 in inb; destruct inb.
  assert (y_gt_0 : -1 < y) by lra.
  assert (y_lt_1 : y < 1) by lra.
  intros eps eps_pos ; elim (Ratan_is_ps_atan eps eps_pos).
  intros N HN ; exists N; intros n n_lb ; apply HN ; tauto.
 apply Datan_CVU_prelim.
 replace ((c - r + (c + r)) / 2) with c by field.
 unfold mkposreal_lb_ub; simpl.
 replace ((c + r - (c - r)) / 2) with (r :R) by field.
 assert (Rabs c < 1 - r).
  unfold Boule in Pcr1; destruct r; simpl in *; apply Rabs_def1;
  apply Rabs_def2 in Pcr1; destruct Pcr1; lra.
 lra.
intros; apply Datan_continuity.
Qed.

Lemma derivable_pt_ps_atan :
   forall x, -1 < x < 1 -> derivable_pt ps_atan x.
Proof.
intros x x_encad.
exists (/(1+x^2)) ; apply derivable_pt_lim_ps_atan; assumption.
Qed.

Lemma ps_atan_continuity_pt_1 : forall eps : R,
       eps > 0 ->
       exists alp : R,
       alp > 0 /\
       (forall x, x < 1 -> 0 < x -> R_dist x 1 < alp ->
       dist R_met (ps_atan x) (Alt_PI/4) < eps).
Proof.
intros eps eps_pos.
assert (eps_3_pos : eps / 3 > 0) by lra.
elim (Ratan_is_ps_atan (eps / 3) eps_3_pos) ; intros N1 HN1.
unfold Alt_PI.
destruct exist_PI as [v Pv]; replace ((4 * v)/4) with v by field.
assert (Pv' : Un_cv (sum_f_R0 (tg_alt (Ratan_seq 1))) v).
 apply Un_cv_ext with (2:= Pv).
 intros; apply sum_eq; intros; unfold tg_alt; rewrite Alt_PI_tg; tauto.
destruct (Pv' (eps / 3) eps_3_pos) as [N2 HN2].
set (N := (N1 + N2)%nat).
assert (O_lb : 0 <= 1) by intuition ; assert (O_ub : 1 <= 1) by intuition ;
 elim (ps_atanSeq_continuity_pt_1 N 1 O_lb O_ub (eps / 3) eps_3_pos) ; intros alpha Halpha ;
 clear -HN1 HN2 Halpha eps_3_pos; destruct Halpha as (alpha_pos, Halpha).
exists alpha ; split;[assumption | ].
intros x x_ub x_lb x_bounds.
simpl ; unfold R_dist.
replace (ps_atan x - v) with ((ps_atan x - sum_f_R0 (tg_alt (Ratan_seq x)) N)
     + (sum_f_R0 (tg_alt (Ratan_seq x)) N - sum_f_R0 (tg_alt (Ratan_seq 1)) N)
     + (sum_f_R0 (tg_alt (Ratan_seq 1)) N - v)).
apply Rle_lt_trans with (r2:=Rabs (ps_atan x - sum_f_R0 (tg_alt (Ratan_seq x)) N) +
      Rabs ((sum_f_R0 (tg_alt (Ratan_seq x)) N - sum_f_R0 (tg_alt (Ratan_seq 1)) N) +
   (sum_f_R0 (tg_alt (Ratan_seq 1)) N - v))).
rewrite Rplus_assoc ; apply Rabs_triang.
   replace eps with (2 / 3 * eps + eps / 3).
   rewrite Rplus_comm.
   apply Rplus_lt_compat.
   apply Rle_lt_trans with (r2 := Rabs (sum_f_R0 (tg_alt (Ratan_seq x)) N - sum_f_R0 (tg_alt (Ratan_seq 1)) N) +
      Rabs (sum_f_R0 (tg_alt (Ratan_seq 1)) N - v)).
   apply Rabs_triang.
   apply Rlt_le_trans with (r2:= eps / 3 + eps / 3).
   apply Rplus_lt_compat.
   simpl in Halpha ; unfold R_dist in Halpha.
   apply Halpha ; split.
   unfold D_x, no_cond ; split ; [ | apply Rgt_not_eq ] ; intuition.
   intuition.
   apply HN2; unfold N; omega.
   lra.
  rewrite <- Rabs_Ropp, Ropp_minus_distr; apply HN1.
     unfold N; omega.  
    lra.
  assumption.
 field.
ring.
Qed.

Lemma Datan_eq_DatanSeq_interv : forall x, -1 < x < 1 ->
 forall (Pratan:derivable_pt ps_atan x) (Prmymeta:derivable_pt atan x),
      derive_pt ps_atan x Pratan = derive_pt atan x Prmymeta.
Proof.
assert (freq : 0 < tan 1) by apply (Rlt_trans _ _ _ Rlt_0_1 tan_1_gt_1).
intros x x_encad Pratan Prmymeta.
 rewrite pr_nu_var2_interv with (g:=ps_atan) (lb:=-1) (ub:=tan 1)
   (pr2 := derivable_pt_ps_atan x x_encad).
 rewrite pr_nu_var2_interv with (f:=atan) (g:=atan) (lb:=-1) (ub:= 1) (pr2:=derivable_pt_atan x).
 assert (Temp := derivable_pt_lim_ps_atan x x_encad).
 assert (Hrew1 : derive_pt ps_atan x (derivable_pt_ps_atan x x_encad) = (/(1+x^2))).
  apply derive_pt_eq_0 ; assumption.
  rewrite derive_pt_atan.
  rewrite Hrew1.
  replace (Rsqr x) with (x ^ 2) by (unfold Rsqr; ring).
  unfold Rdiv; rewrite Rmult_1_l; reflexivity.
     lra.
    assumption.
   intros; reflexivity.
  lra.
 assert (t := tan_1_gt_1); split;destruct x_encad; lra.
intros; reflexivity.
Qed.

Lemma atan_eq_ps_atan :
 forall x, 0 < x < 1 -> atan x = ps_atan x.
Proof.
intros x x_encad.
assert (pr1 : forall c : R, 0 < c < x -> derivable_pt (atan - ps_atan) c).
 intros c c_encad.
 apply derivable_pt_minus.
  exact (derivable_pt_atan c).
 apply derivable_pt_ps_atan.
  destruct x_encad; destruct c_encad; split; lra.
assert (pr2 : forall c : R, 0 < c < x -> derivable_pt id c).
 intros ; apply derivable_pt_id; lra.
assert (delta_cont : forall c : R, 0 <= c <= x -> continuity_pt (atan - ps_atan) c).
 intros c [[c_encad1 | c_encad1 ] [c_encad2 | c_encad2]];
        apply continuity_pt_minus.
        apply derivable_continuous_pt ; apply derivable_pt_atan. 
       apply derivable_continuous_pt ; apply derivable_pt_ps_atan.
       split; destruct x_encad; lra.
      apply derivable_continuous_pt, derivable_pt_atan.
     apply derivable_continuous_pt, derivable_pt_ps_atan.
     subst c; destruct x_encad; split; lra.
    apply derivable_continuous_pt, derivable_pt_atan.
   apply derivable_continuous_pt, derivable_pt_ps_atan.
   subst c; split; lra.
  apply derivable_continuous_pt, derivable_pt_atan.
 apply derivable_continuous_pt, derivable_pt_ps_atan.
 subst c; destruct x_encad; split; lra.
assert (id_cont : forall c : R, 0 <= c <= x -> continuity_pt id c).
    intros ; apply derivable_continuous ; apply derivable_id.
assert (x_lb : 0 < x) by (destruct x_encad; lra).
elim (MVT (atan - ps_atan)%F id 0 x pr1 pr2 x_lb delta_cont id_cont) ; intros d Temp ; elim Temp ; intros d_encad Main.
clear - Main x_encad.
assert (Temp : forall (pr: derivable_pt (atan - ps_atan) d), derive_pt (atan - ps_atan) d pr = 0).
 intro pr.
 assert (d_encad3 : -1 < d < 1).
  destruct d_encad; destruct x_encad; split; lra.
 pose (pr3 := derivable_pt_minus atan ps_atan d (derivable_pt_atan d) (derivable_pt_ps_atan d d_encad3)).
 rewrite <- pr_nu_var2_interv with (f:=(atan - ps_atan)%F) (g:=(atan - ps_atan)%F) (lb:=0) (ub:=x) (pr1:=pr3) (pr2:=pr).
    unfold pr3. rewrite derive_pt_minus.
    rewrite Datan_eq_DatanSeq_interv with (Prmymeta := derivable_pt_atan d).
     intuition.
    assumption. 
   destruct d_encad; lra.
  assumption.
 reflexivity.
assert (iatan0 : atan 0 = 0).
 apply tan_is_inj.
   apply atan_bound.
  rewrite Ropp_div; assert (t := PI2_RGT_0); split; lra.
 rewrite tan_0, atan_right_inv; reflexivity.
generalize Main; rewrite Temp, Rmult_0_r.
replace ((atan - ps_atan)%F x) with (atan x - ps_atan x) by intuition.
replace ((atan - ps_atan)%F 0) with (atan 0 - ps_atan 0) by intuition.
rewrite iatan0, ps_atan0_0, !Rminus_0_r.
replace (derive_pt id d (pr2 d d_encad)) with 1. 
 rewrite Rmult_1_r.
 solve[intros M; apply Rminus_diag_uniq; auto].
rewrite pr_nu_var with (g:=id) (pr2:=derivable_pt_id d).
 symmetry ; apply derive_pt_id.
tauto.
Qed.


Theorem Alt_PI_eq : Alt_PI = PI.
Proof.
apply Rmult_eq_reg_r with (/4); fold (Alt_PI/4); fold (PI/4);
  [ | apply Rgt_not_eq; lra].
assert (0 < PI/6) by (apply PI6_RGT_0).
assert (t1:= PI2_1).
assert (t2 := PI_4).
assert (m := Alt_PI_RGT_0).
assert (-PI/2 < 1 < PI/2) by (rewrite Ropp_div; split; lra).
apply cond_eq; intros eps ep.
change (R_dist (Alt_PI/4) (PI/4) < eps).
assert (ca : continuity_pt atan 1).
  apply derivable_continuous_pt, derivable_pt_atan.
assert (Xe : exists eps', exists eps'',
  eps' + eps'' <= eps /\ 0 < eps' /\ 0 < eps'').
 exists (eps/2); exists (eps/2); repeat apply conj; lra.
destruct Xe as [eps' [eps'' [eps_ineq [ep' ep'']]]].
destruct (ps_atan_continuity_pt_1 _ ep') as [alpha [a0 Palpha]].
destruct (ca _ ep'') as [beta [b0 Pbeta]].
assert (Xa : exists a, 0 < a < 1 /\ R_dist a 1 < alpha /\
                R_dist a 1 < beta).
 exists (Rmax (/2) (Rmax (1 - alpha /2) (1 - beta /2))).
 assert (/2 <= Rmax (/2) (Rmax (1 - alpha /2) (1 - beta /2))) by apply Rmax_l.
 assert (Rmax (1 - alpha /2) (1 - beta /2) <=
         Rmax (/2) (Rmax (1 - alpha /2) (1 - beta /2))) by apply Rmax_r.
 assert ((1 - alpha /2) <= Rmax (1 - alpha /2) (1 - beta /2)) by apply Rmax_l.
 assert ((1 - beta /2) <= Rmax (1 - alpha /2) (1 - beta /2)) by apply Rmax_r.
 assert (Rmax (1 - alpha /2) (1 - beta /2) < 1)
   by (apply Rmax_lub_lt; lra).
 split;[split;[ | apply Rmax_lub_lt]; lra | ].
 assert (0 <= 1 - Rmax (/ 2) (Rmax (1 - alpha / 2) (1 - beta / 2))).
  assert (Rmax (/2) (Rmax (1 - alpha / 2) 
            (1 - beta /2)) <= 1) by (apply Rmax_lub; lra).
  lra.
 split; unfold R_dist; rewrite <-Rabs_Ropp, Ropp_minus_distr,
   Rabs_pos_eq;lra.
destruct Xa as [a [[Pa0 Pa1] [P1 P2]]].
apply Rle_lt_trans with (1 := R_dist_tri _ _ (ps_atan a)).
apply Rlt_le_trans with (2 := eps_ineq).
apply Rplus_lt_compat.
rewrite R_dist_sym; apply Palpha; assumption.
rewrite <- atan_eq_ps_atan.
 rewrite <- atan_1; apply (Pbeta a); auto.
 split; [ | exact P2].
split;[exact I | apply Rgt_not_eq; assumption].
split; assumption.
Qed.

Lemma PI_ineq :
  forall N : nat,
    sum_f_R0 (tg_alt PI_tg) (S (2 * N)) <= PI / 4 <=
    sum_f_R0 (tg_alt PI_tg) (2 * N).
Proof.
intros; rewrite <- Alt_PI_eq; apply Alt_PI_ineq.
Qed.


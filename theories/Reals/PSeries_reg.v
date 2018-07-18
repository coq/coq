(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Ranalysis1.
Require Import MVT.
Require Import Max.
Require Import Even.
Require Import Lra.
Local Open Scope R_scope.

(* Boule is French for Ball *)

Definition Boule (x:R) (r:posreal) (y:R) : Prop := Rabs (y - x) < r.

(* General properties of balls. *)

Lemma Boule_convex : forall c d x y z,
  Boule c d x -> Boule c d y -> x <= z <= y -> Boule c d z.
Proof.
intros c d x y z bx b_y intz.
unfold Boule in bx, b_y; apply Rabs_def2 in bx;
apply Rabs_def2 in b_y; apply Rabs_def1;
 [apply Rle_lt_trans with (y - c);[apply Rplus_le_compat_r|]|
  apply Rlt_le_trans with (x - c);[|apply Rplus_le_compat_r]];tauto.
Qed.

Definition boule_of_interval x y (h : x < y) :
  {c :R & {r : posreal | c - r = x /\ c + r = y}}.
Proof.
exists ((x + y)/2).
assert (radius : 0 < (y - x)/2).
 unfold Rdiv; apply Rmult_lt_0_compat.
  apply Rlt_Rminus; assumption.
 now apply Rinv_0_lt_compat, Rlt_0_2.
 exists (mkposreal _ radius).
 simpl; split; unfold Rdiv; field.
Qed.

Definition boule_in_interval x y z (h : x < z < y) :
  {c : R & {r | Boule c r z /\  x < c - r /\ c + r < y}}.
Proof.
assert (cmp : x * /2 + z * /2 < z * /2 + y * /2).
destruct h as [h1 h2].
rewrite Rplus_comm; apply Rplus_lt_compat_l, Rmult_lt_compat_r.
 apply Rinv_0_lt_compat, Rlt_0_2.
apply Rlt_trans with z; assumption.
destruct (boule_of_interval _ _ cmp) as [c [r [P1 P2]]].
assert (0 < /2) by (apply Rinv_0_lt_compat, Rlt_0_2).
exists c, r; split.
 destruct h; unfold Boule; simpl; apply Rabs_def1.
  apply Rplus_lt_reg_l with c; rewrite P2;
  replace (c + (z - c)) with (z * / 2 + z * / 2) by field.
  apply Rplus_lt_compat_l, Rmult_lt_compat_r;assumption.
 apply Rplus_lt_reg_l with c; change (c + - r) with (c - r);
 rewrite P1;
 replace (c + (z - c)) with (z * / 2 + z * / 2) by field.
 apply Rplus_lt_compat_r, Rmult_lt_compat_r;assumption.
destruct h; split.
 replace x with (x * / 2 + x * / 2) by field; rewrite P1.
 apply Rplus_lt_compat_l, Rmult_lt_compat_r;assumption.
replace y with (y * / 2 + y * /2) by field; rewrite P2.
apply Rplus_lt_compat_r, Rmult_lt_compat_r;assumption.
Qed.

Lemma Ball_in_inter : forall c1 c2 r1 r2 x,
  Boule c1 r1 x -> Boule c2 r2 x ->
  {r3 : posreal | forall y, Boule x r3 y -> Boule c1 r1 y /\ Boule c2 r2 y}.
Proof.
intros c1 c2 [r1 r1p] [r2 r2p] x; unfold Boule; simpl; intros in1 in2.
assert (Rmax (c1 - r1)(c2 - r2) < x).
 apply Rmax_lub_lt;[revert in1 | revert in2]; intros h;
  apply Rabs_def2 in h; destruct h as [_ u];
  apply (fun h => Rplus_lt_reg_r _ _ _ (Rle_lt_trans _ _ _ h u)), Req_le; ring.
assert (x < Rmin (c1 + r1) (c2 + r2)).
 apply Rmin_glb_lt;[revert in1 | revert in2]; intros h;
 apply Rabs_def2 in h; destruct h as [u _];
 apply (fun h => Rplus_lt_reg_r _ _ _ (Rlt_le_trans _ _ _ u h)), Req_le; ring.
assert (t: 0 < Rmin (x - Rmax (c1 - r1) (c2 - r2))
              (Rmin (c1 + r1) (c2 + r2) - x)).
 apply Rmin_glb_lt; apply Rlt_Rminus; assumption.
exists (mkposreal _ t).
apply Rabs_def2 in in1; destruct in1.
apply Rabs_def2 in in2; destruct in2.
assert (c1 - r1 <= Rmax (c1 - r1) (c2 - r2)) by apply Rmax_l.
assert (c2 - r2 <= Rmax (c1 - r1) (c2 - r2)) by apply Rmax_r.
assert (Rmin (c1 + r1) (c2 + r2) <= c1 + r1) by apply Rmin_l.
assert (Rmin (c1 + r1) (c2 + r2) <= c2 + r2) by apply Rmin_r.
assert (Rmin (x - Rmax (c1 - r1) (c2 - r2)) 
         (Rmin (c1 + r1) (c2 + r2) - x) <= x - Rmax (c1 - r1) (c2 - r2))
 by apply Rmin_l.
assert (Rmin (x - Rmax (c1 - r1) (c2 - r2)) 
         (Rmin (c1 + r1) (c2 + r2) - x) <= Rmin (c1 + r1) (c2 + r2) - x)
 by apply Rmin_r.
simpl.
intros y h; apply Rabs_def2 in h; destruct h as [h h'].
apply Rmin_Rgt in h; destruct h as [cmp1 cmp2].
apply Rplus_lt_reg_r in cmp2; apply Rmin_Rgt in cmp2.
rewrite Ropp_Rmin, Ropp_minus_distr in h'.
apply Rmax_Rlt in h'; destruct h' as [cmp3 cmp4];
apply Rplus_lt_reg_r in cmp3; apply Rmax_Rlt in cmp3;
split; apply Rabs_def1.
apply (fun h => Rplus_lt_reg_l _ _ _ (Rle_lt_trans _ _ _ h (proj1 cmp2))), Req_le;
 ring.
apply (fun h => Rplus_lt_reg_l _ _ _ (Rlt_le_trans _ _ _ (proj1 cmp3) h)), Req_le;
 ring.
apply (fun h => Rplus_lt_reg_l _ _ _ (Rle_lt_trans _ _ _ h (proj2 cmp2))), Req_le;
 ring.
apply (fun h => Rplus_lt_reg_l _ _ _ (Rlt_le_trans _ _ _ (proj2 cmp3) h)), Req_le;
 ring.
Qed.

Lemma Boule_center : forall x r, Boule x r x.
Proof.
intros x [r rpos]; unfold Boule, Rminus; simpl; rewrite Rplus_opp_r.
rewrite Rabs_pos_eq;[assumption | apply Rle_refl].
Qed.

(** Uniform convergence *)
Definition CVU (fn:nat -> R -> R) (f:R -> R) (x:R)
  (r:posreal) : Prop :=
  forall eps:R,
    0 < eps ->
    exists N : nat,
      (forall (n:nat) (y:R),
        (N <= n)%nat -> Boule x r y -> Rabs (f y - fn n y) < eps).

(** Normal convergence *)
Definition CVN_r (fn:nat -> R -> R) (r:posreal) : Type :=
  { An:nat -> R &
    { l:R |
      Un_cv (fun n:nat => sum_f_R0 (fun k:nat => Rabs (An k)) n) l /\
      (forall (n:nat) (y:R), Boule 0 r y -> Rabs (fn n y) <= An n) } }.

Definition CVN_R (fn:nat -> R -> R) : Type := forall r:posreal, CVN_r fn r.

Definition SFL (fn:nat -> R -> R)
  (cv:forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l })
  (y:R) : R := let (a,_) := cv y in a.

(** In a complete space, normal convergence implies uniform convergence *)
Lemma CVN_CVU :
  forall (fn:nat -> R -> R)
    (cv:forall x:R, {l:R | Un_cv (fun N:nat => SP fn N x) l })
    (r:posreal), CVN_r fn r -> CVU (fun n:nat => SP fn n) (SFL fn cv) 0 r.
Proof.
  intros; unfold CVU; intros.
  unfold CVN_r in X.
  elim X; intros An X0.
  elim X0; intros s H0.
  elim H0; intros.
  cut (Un_cv (fun n:nat => sum_f_R0 (fun k:nat => Rabs (An k)) n - s) 0).
  intro; unfold Un_cv in H3.
  elim (H3 eps H); intros N0 H4.
  exists N0; intros.
  apply Rle_lt_trans with (Rabs (sum_f_R0 (fun k:nat => Rabs (An k)) n - s)).
  rewrite <- (Rabs_Ropp (sum_f_R0 (fun k:nat => Rabs (An k)) n - s));
    rewrite Ropp_minus_distr';
      rewrite (Rabs_right (s - sum_f_R0 (fun k:nat => Rabs (An k)) n)).
  eapply sum_maj1.
  unfold SFL; case (cv y); intro.
  trivial.
  apply H1.
  intro; elim H0; intros.
  rewrite (Rabs_right (An n0)).
  apply H8; apply H6.
  apply Rle_ge; apply Rle_trans with (Rabs (fn n0 y)).
  apply Rabs_pos.
  apply H8; apply H6.
  apply Rle_ge;
    apply Rplus_le_reg_l with (sum_f_R0 (fun k:nat => Rabs (An k)) n).
  rewrite Rplus_0_r; unfold Rminus; rewrite (Rplus_comm s);
    rewrite <- Rplus_assoc; rewrite Rplus_opp_r; rewrite Rplus_0_l;
      apply sum_incr.
  apply H1.
  intro; apply Rabs_pos.
  unfold R_dist in H4; unfold Rminus in H4; rewrite Ropp_0 in H4.
  assert (H7 := H4 n H5).
  rewrite Rplus_0_r in H7; apply H7.
  unfold Un_cv in H1; unfold Un_cv; intros.
  elim (H1 _ H3); intros.
  exists x; intros.
  unfold R_dist; unfold R_dist in H4.
  rewrite Rminus_0_r; apply H4; assumption.
Qed.

(** Each limit of a sequence of functions which converges uniformly is continue *)
Lemma CVU_continuity :
  forall (fn:nat -> R -> R) (f:R -> R) (x:R) (r:posreal),
    CVU fn f x r ->
    (forall (n:nat) (y:R), Boule x r y -> continuity_pt (fn n) y) ->
    forall y:R, Boule x r y -> continuity_pt f y.
Proof.
  intros; unfold continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
      simpl; unfold R_dist; intros.
  unfold CVU in H.
  cut (0 < eps / 3);
    [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  elim (H _ H3); intros N0 H4.
  assert (H5 := H0 N0 y H1).
  cut (exists del : posreal, (forall h:R, Rabs h < del -> Boule x r (y + h))).
  intro.
  elim H6; intros del1 H7.
  unfold continuity_pt in H5; unfold continue_in in H5; unfold limit1_in in H5;
    unfold limit_in in H5; simpl in H5; unfold R_dist in H5.
  elim (H5 _ H3); intros del2 H8.
  set (del := Rmin del1 del2).
  exists del; intros.
  split.
  unfold del; unfold Rmin; case (Rle_dec del1 del2); intro.
  apply (cond_pos del1).
  elim H8; intros; assumption.
  intros;
    apply Rle_lt_trans with (Rabs (f x0 - fn N0 x0) + Rabs (fn N0 x0 - f y)).
  replace (f x0 - f y) with (f x0 - fn N0 x0 + (fn N0 x0 - f y));
  [ apply Rabs_triang | ring ].
  apply Rle_lt_trans with
    (Rabs (f x0 - fn N0 x0) + Rabs (fn N0 x0 - fn N0 y) + Rabs (fn N0 y - f y)).
  rewrite Rplus_assoc; apply Rplus_le_compat_l.
  replace (fn N0 x0 - f y) with (fn N0 x0 - fn N0 y + (fn N0 y - f y));
  [ apply Rabs_triang | ring ].
  replace eps with (eps / 3 + eps / 3 + eps / 3).
  repeat apply Rplus_lt_compat.
  apply H4.
  apply le_n.
  replace x0 with (y + (x0 - y)); [ idtac | ring ]; apply H7.
  elim H9; intros.
  apply Rlt_le_trans with del.
  assumption.
  unfold del; apply Rmin_l.
  elim H8; intros.
  apply H11.
  split.
  elim H9; intros; assumption.
  elim H9; intros; apply Rlt_le_trans with del.
  assumption.
  unfold del; apply Rmin_r.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr'; apply H4.
  apply le_n.
  assumption.
  apply Rmult_eq_reg_l with 3.
  do 2 rewrite Rmult_plus_distr_l; unfold Rdiv; rewrite <- Rmult_assoc;
    rewrite Rinv_r_simpl_m.
  ring.
  discrR.
  discrR.
  cut (0 < r - Rabs (x - y)).
  intro; exists (mkposreal _ H6).
  simpl; intros.
  unfold Boule; replace (y + h - x) with (h + (y - x));
    [ idtac | ring ]; apply Rle_lt_trans with (Rabs h + Rabs (y - x)).
  apply Rabs_triang.
  apply Rplus_lt_reg_l with (- Rabs (x - y)).
  rewrite <- (Rabs_Ropp (y - x)); rewrite Ropp_minus_distr'.
  replace (- Rabs (x - y) + r) with (r - Rabs (x - y)).
  replace (- Rabs (x - y) + (Rabs h + Rabs (x - y))) with (Rabs h).
  apply H7.
  ring.
  ring.
  unfold Boule in H1; rewrite <- (Rabs_Ropp (x - y)); rewrite Ropp_minus_distr';
    apply Rplus_lt_reg_l with (Rabs (y - x)).
  rewrite Rplus_0_r; replace (Rabs (y - x) + (r - Rabs (y - x))) with (pos r);
    [ apply H1 | ring ].
Qed.

(**********)
Lemma continuity_pt_finite_SF :
  forall (fn:nat -> R -> R) (N:nat) (x:R),
    (forall n:nat, (n <= N)%nat -> continuity_pt (fn n) x) ->
    continuity_pt (fun y:R => sum_f_R0 (fun k:nat => fn k y) N) x.
Proof.
  intros; induction  N as [| N HrecN].
  simpl; apply (H 0%nat); apply le_n.
  simpl;
    replace (fun y:R => sum_f_R0 (fun k:nat => fn k y) N + fn (S N) y) with
    ((fun y:R => sum_f_R0 (fun k:nat => fn k y) N) + (fun y:R => fn (S N) y))%F;
    [ idtac | reflexivity ].
  apply continuity_pt_plus.
  apply HrecN.
  intros; apply H.
  apply le_trans with N; [ assumption | apply le_n_Sn ].
  apply (H (S N)); apply le_n.
Qed.

(** Continuity and normal convergence *)
Lemma SFL_continuity_pt :
  forall (fn:nat -> R -> R)
    (cv:forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l })
    (r:posreal),
    CVN_r fn r ->
    (forall (n:nat) (y:R), Boule 0 r y -> continuity_pt (fn n) y) ->
    forall y:R, Boule 0 r y -> continuity_pt (SFL fn cv) y.
Proof.
  intros; eapply CVU_continuity.
  apply CVN_CVU.
  apply X.
  intros; unfold SP; apply continuity_pt_finite_SF.
  intros; apply H.
  apply H1.
  apply H0.
Qed.

Lemma SFL_continuity :
  forall (fn:nat -> R -> R)
    (cv:forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l }),
    CVN_R fn -> (forall n:nat, continuity (fn n)) -> continuity (SFL fn cv).
Proof.
  intros; unfold continuity; intro.
  cut (0 < Rabs x + 1);
    [ intro | apply Rplus_le_lt_0_compat; [ apply Rabs_pos | apply Rlt_0_1 ] ].
  cut (Boule 0 (mkposreal _ H0) x).
  intro; eapply SFL_continuity_pt with (mkposreal _ H0).
  apply X.
  intros; apply (H n y).
  apply H1.
  unfold Boule; simpl; rewrite Rminus_0_r;
    pattern (Rabs x) at 1; rewrite <- Rplus_0_r;
      apply Rplus_lt_compat_l; apply Rlt_0_1.
Qed.

(** As R is complete, normal convergence implies that (fn) is simply-uniformly convergent *)
Lemma CVN_R_CVS :
  forall fn:nat -> R -> R,
    CVN_R fn -> forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l }.
Proof.
  intros; apply R_complete.
  unfold SP; set (An := fun N:nat => fn N x).
  change (Cauchy_crit_series An).
  apply cauchy_abs.
  unfold Cauchy_crit_series; apply CV_Cauchy.
  unfold CVN_R in X; cut (0 < Rabs x + 1).
  intro; assert (H0 := X (mkposreal _ H)).
  unfold CVN_r in H0; elim H0; intros Bn H1.
  elim H1; intros l H2.
  elim H2; intros.
  apply Rseries_CV_comp with Bn.
  intro; split.
  apply Rabs_pos.
  unfold An; apply H4; unfold Boule; simpl;
    rewrite Rminus_0_r.
  pattern (Rabs x) at 1; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l;
    apply Rlt_0_1.
  exists l.
  cut (forall n:nat, 0 <= Bn n).
  intro; unfold Un_cv in H3; unfold Un_cv; intros.
  elim (H3 _ H6); intros.
  exists x0; intros.
  replace (sum_f_R0 Bn n) with (sum_f_R0 (fun k:nat => Rabs (Bn k)) n).
  apply H7; assumption.
  apply sum_eq; intros; apply Rabs_right; apply Rle_ge; apply H5.
  intro; apply Rle_trans with (Rabs (An n)).
  apply Rabs_pos.
  unfold An; apply H4; unfold Boule; simpl;
    rewrite Rminus_0_r; pattern (Rabs x) at 1;
      rewrite <- Rplus_0_r; apply Rplus_lt_compat_l; apply Rlt_0_1.
  apply Rplus_le_lt_0_compat; [ apply Rabs_pos | apply Rlt_0_1 ].
Qed.

(* Uniform convergence implies pointwise simple convergence *)
Lemma CVU_cv : forall f g c d, CVU f g c d ->
   forall x, Boule c d x -> Un_cv (fun n => f n x) (g x).
Proof.
intros f g c d cvu x bx eps ep; destruct (cvu eps ep) as [N Pn].
 exists N; intros n nN; rewrite R_dist_sym; apply Pn; assumption.
Qed.

(* convergence is preserved through extensional equality *)
Lemma CVU_ext_lim :
  forall f g1 g2 c d, CVU f g1 c d -> (forall x, Boule c d x -> g1 x = g2 x) ->
    CVU f g2 c d.
Proof.
intros f g1 g2 c d cvu q eps ep; destruct (cvu _ ep) as [N Pn].
exists N; intros; rewrite <- q; auto.
Qed.

(* When a sequence of derivable functions converge pointwise towards
  a function g, with the derivatives converging uniformly towards
  a function g', then the function g' is the derivative of g. *)

Lemma CVU_derivable :
  forall f f' g g' c d,
   CVU f' g' c d ->
   (forall x, Boule c d x -> Un_cv (fun n => f n x) (g x)) ->
   (forall n x, Boule c d x -> derivable_pt_lim (f n) x (f' n x)) ->
   forall x, Boule c d x -> derivable_pt_lim g x (g' x).
Proof.
intros f f' g g' c d cvu cvp dff' x bx.
set (rho_ :=
       fun n y =>
           if Req_EM_T y x then
              f' n x
           else ((f n y - f n x)/ (y - x))).
set (rho := fun y =>
               if Req_EM_T y x then
                  g' x
               else (g y - g x)/(y - x)).
assert (ctrho : forall n z, Boule c d z -> continuity_pt (rho_ n) z).
 intros n z bz.
 destruct (Req_EM_T x z) as [xz | xnz].
  rewrite <- xz.
  intros eps' ep'.
  destruct (dff' n x bx eps' ep') as [alp Pa].
  exists (pos alp);split;[apply cond_pos | ].
  intros z'; unfold rho_, D_x, dist, R_met; simpl; intros [[_ xnz'] dxz'].
   destruct (Req_EM_T z' x) as [abs | _].
    case xnz'; symmetry; exact abs.
   destruct (Req_EM_T x x) as [_ | abs];[ | case abs; reflexivity].
  pattern z' at 1; replace z' with (x + (z' - x)) by ring.
  apply Pa;[intros h; case xnz';
    replace z' with (z' - x + x) by ring; rewrite h, Rplus_0_l;
       reflexivity | exact dxz'].
 destruct (Ball_in_inter c c d d z bz bz) as [delta Pd].
 assert (dz :  0 < Rmin delta (Rabs (z - x))).
  now apply Rmin_glb_lt;[apply cond_pos | apply Rabs_pos_lt; intros zx0; case xnz;
                       replace z with (z - x + x) by ring; rewrite zx0, Rplus_0_l].
 assert (t' : forall y : R,
      R_dist y z < Rmin delta (Rabs (z - x)) ->
      (fun z : R => (f n z - f n x) / (z - x)) y = rho_ n y).
  intros y dyz; unfold rho_; destruct (Req_EM_T y x) as [xy | xny].
   rewrite xy in dyz.
   destruct (Rle_dec  delta (Rabs (z - x))).
    rewrite Rmin_left, R_dist_sym in dyz; unfold R_dist in dyz; lra.
   rewrite Rmin_right, R_dist_sym in dyz; unfold R_dist in dyz;
      [case (Rlt_irrefl _ dyz) |apply Rlt_le, Rnot_le_gt; assumption].
  reflexivity.
 apply (continuity_pt_locally_ext (fun z => (f n z - f n x)/(z - x))
             (rho_ n) _ z dz t'); clear t'.
 apply continuity_pt_div.
   apply continuity_pt_minus.
    apply derivable_continuous_pt; eapply exist; apply dff'; assumption.
   apply continuity_pt_const; intro; intro; reflexivity.
  apply continuity_pt_minus;
   [apply derivable_continuous_pt; exists 1; apply derivable_pt_lim_id
   | apply continuity_pt_const; intro; reflexivity].
 intros zx0; case xnz; replace z with (z - x + x) by ring.
 rewrite zx0, Rplus_0_l; reflexivity.
assert (CVU rho_ rho c d ).
 intros eps ep.
 assert (ep8 : 0 < eps/8).
  lra.
 destruct (cvu _ ep8) as [N Pn1].
 assert (cauchy1 : forall n p, (N <= n)%nat -> (N <= p)%nat ->
           forall z, Boule c d z -> Rabs (f' n z - f' p z) < eps/4).
  intros n p nN pN z bz; replace (eps/4) with (eps/8 + eps/8) by field.
  rewrite <- Rabs_Ropp.
  replace (-(f' n z - f' p z)) with (g' z - f' n z - (g' z - f' p z)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp.
  apply Rplus_lt_compat; apply Pn1; assumption.
 assert (step_2 : forall n p, (N <= n)%nat -> (N <= p)%nat ->
         forall y, Boule c d y -> x <> y ->
         Rabs ((f n y - f n x)/(y - x) - (f p y - f p x)/(y - x)) < eps/4).
  intros n p nN pN y b_y xny.
  assert (mm0 : (Rmin x y = x /\ Rmax x y = y) \/ 
                (Rmin x y = y /\ Rmax x y = x)).
   destruct (Rle_dec x y) as [H | H].
    rewrite Rmin_left, Rmax_right.
      left; split; reflexivity.
     assumption.
    assumption.
   rewrite Rmin_right, Rmax_left.
     right; split; reflexivity.
    apply Rlt_le, Rnot_le_gt; assumption.
   apply Rlt_le, Rnot_le_gt; assumption.
  assert (mm : Rmin x y < Rmax x y).
   destruct mm0 as [[q1 q2] | [q1 q2]]; generalize (Rminmax x y); rewrite q1, q2.
    intros h; destruct h;[ assumption| contradiction].
   intros h; destruct h as [h | h];[assumption | rewrite h in xny; case xny; reflexivity].
  assert (dm : forall z, Rmin x y <= z <= Rmax x y ->
            derivable_pt_lim (fun x => f n x - f p x) z (f' n z - f' p z)).
   intros z intz; apply derivable_pt_lim_minus.
    apply dff'; apply Boule_convex with (Rmin x y) (Rmax x y);
      destruct mm0 as [[q1 q2] | [q1 q2]]; revert intz; rewrite ?q1, ?q2; intros;
     try assumption.
   apply dff'; apply Boule_convex with (Rmin x y) (Rmax x y);
      destruct mm0 as [[q1 q2] | [q1 q2]]; revert intz; rewrite ?q1, ?q2; intros;
     try assumption.

  replace ((f n y - f n x) / (y - x) - (f p y - f p x) / (y - x))
    with (((f n y - f p y) - (f n x - f p x))/(y - x)) by
    (field; intros yx0; case xny; replace y with (y - x + x) by ring;
     rewrite yx0, Rplus_0_l; reflexivity).
  destruct (MVT_cor2 (fun x => f n x - f p x) (fun x => f' n x - f' p x)
             (Rmin x y) (Rmax x y) mm dm) as [z [Pz inz]].
  destruct mm0 as [[q1 q2] | [q1 q2]].
   replace ((f n y - f p y - (f n x - f p x))/(y - x)) with
    ((f n (Rmax x y) - f p (Rmax x y) - (f  n (Rmin x y) - f p (Rmin x y)))/
      (Rmax x y - Rmin x y)) by (rewrite q1, q2; reflexivity).
   unfold Rdiv; rewrite Pz, Rmult_assoc, Rinv_r, Rmult_1_r.
    apply cauchy1; auto.
    apply Boule_convex with (Rmin x y) (Rmax x y);
      revert inz; rewrite ?q1, ?q2; intros;
     try assumption.
    split; apply Rlt_le; tauto.
   rewrite q1, q2; apply Rminus_eq_contra, not_eq_sym; assumption.
  replace ((f n y - f p y - (f n x - f p x))/(y - x)) with
    ((f n (Rmax x y) - f p (Rmax x y) - (f  n (Rmin x y) - f p (Rmin x y)))/
      (Rmax x y - Rmin x y)).
   unfold Rdiv; rewrite Pz, Rmult_assoc, Rinv_r, Rmult_1_r.
    apply cauchy1; auto.
    apply Boule_convex with (Rmin x y) (Rmax x y);
     revert inz; rewrite ?q1, ?q2; intros;
    try assumption; split; apply Rlt_le; tauto.
   rewrite q1, q2; apply Rminus_eq_contra; assumption.
  rewrite q1, q2; field; split; 
    apply Rminus_eq_contra;[apply not_eq_sym |]; assumption.
 assert (unif_ac :
  forall n p, (N <= n)%nat -> (N <= p)%nat ->
     forall y, Boule c d y ->
       Rabs (rho_ n y - rho_ p y) <= eps/2).
  intros n p nN pN y b_y.
  destruct (Req_dec x y) as [xy | xny].
   destruct (Ball_in_inter c c d d x bx bx) as [delta Pdelta].
   destruct (ctrho n y b_y _ ep8) as [d' [dp Pd]].
   destruct (ctrho p y b_y _ ep8) as [d2 [dp2 Pd2]].
   assert (mmpos : 0 < (Rmin (Rmin d' d2) delta)/2).
    apply Rmult_lt_0_compat; repeat apply Rmin_glb_lt; try assumption.
     apply cond_pos.
    apply Rinv_0_lt_compat, Rlt_0_2.
   apply Rle_trans with (1 := R_dist_tri _ _ (rho_ n (y + Rmin (Rmin d' d2) delta/2))).
   replace (eps/2) with (eps/8 + (eps/4 + eps/8)) by field.
   apply Rplus_le_compat.
    rewrite R_dist_sym; apply Rlt_le, Pd;split;[split;[exact I | ] | ].
      apply Rminus_not_eq_right; rewrite Rplus_comm; unfold Rminus;
      rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r; apply Rgt_not_eq; assumption.
    simpl; unfold R_dist.
    unfold Rminus; rewrite (Rplus_comm y), Rplus_assoc, Rplus_opp_r, Rplus_0_r.
    rewrite Rabs_pos_eq;[ |apply Rlt_le; assumption ].
    apply Rlt_le_trans with (Rmin (Rmin d' d2) delta);[lra | ].
    apply Rle_trans with (Rmin d' d2); apply Rmin_l.
   apply Rle_trans with (1 := R_dist_tri _ _ (rho_ p (y + Rmin (Rmin d' d2) delta/2))).
   apply Rplus_le_compat.
    apply Rlt_le.
    replace (rho_ n (y + Rmin (Rmin d' d2) delta / 2)) with
          ((f n (y + Rmin (Rmin d' d2) delta / 2) - f n x)/
            ((y + Rmin (Rmin d' d2) delta / 2) - x)).
     replace (rho_ p (y + Rmin (Rmin d' d2) delta / 2)) with
          ((f p (y + Rmin (Rmin d' d2) delta / 2) - f p x)/
             ((y + Rmin (Rmin d' d2) delta / 2) - x)).
      apply step_2; auto; try lra.
      assert (0 < pos delta) by (apply cond_pos).
      apply Boule_convex with y (y + delta/2).
        assumption.
       destruct (Pdelta (y + delta/2)); auto.
       rewrite xy; unfold Boule; rewrite Rabs_pos_eq; try lra; auto.
      split; try lra.
      apply Rplus_le_compat_l, Rmult_le_compat_r;[ | apply Rmin_r].
       now apply Rlt_le, Rinv_0_lt_compat, Rlt_0_2.
     unfold rho_.
     destruct (Req_EM_T (y + Rmin (Rmin d' d2) delta/2) x) as [ymx | ymnx].
      case (RIneq.Rle_not_lt _ _ (Req_le _ _ ymx)); lra.
     reflexivity.
    unfold rho_.
    destruct (Req_EM_T (y + Rmin (Rmin d' d2) delta / 2) x) as [ymx | ymnx].
     case (RIneq.Rle_not_lt _ _ (Req_le _ _ ymx)); lra.
    reflexivity.
   apply Rlt_le, Pd2; split;[split;[exact I | apply Rlt_not_eq; lra] | ].
   simpl; unfold R_dist.
   unfold Rminus; rewrite (Rplus_comm y), Rplus_assoc, Rplus_opp_r, Rplus_0_r.
   rewrite Rabs_pos_eq;[ | lra].
   apply Rlt_le_trans with (Rmin (Rmin d' d2) delta); [lra |].
   apply Rle_trans with (Rmin d' d2).
    solve[apply Rmin_l].
   solve[apply Rmin_r].
  apply Rlt_le, Rlt_le_trans with (eps/4);[ | lra].
  unfold rho_; destruct (Req_EM_T y x); solve[auto].
 assert (unif_ac' : forall p, (N <= p)%nat ->
           forall y, Boule c d y -> Rabs (rho y - rho_ p y) < eps).
  assert (cvrho : forall y, Boule c d y -> Un_cv (fun n => rho_ n y) (rho y)).
   intros y b_y; unfold rho_, rho; destruct (Req_EM_T y x).
    intros eps' ep'; destruct (cvu eps' ep') as [N2 Pn2].
    exists N2; intros n nN2; rewrite R_dist_sym; apply Pn2; assumption.
   apply CV_mult.
    apply CV_minus.
     apply cvp; assumption.
    apply cvp; assumption.
   intros eps' ep'; simpl; exists 0%nat; intros; rewrite R_dist_eq; assumption.
  intros p pN y b_y.
  replace eps with (eps/2 + eps/2) by field.
  assert (ep2 : 0 < eps/2) by lra.
  destruct (cvrho y b_y _ ep2) as [N2 Pn2].
  apply Rle_lt_trans with (1 := R_dist_tri _ _ (rho_ (max N N2) y)).
  apply Rplus_lt_le_compat.
   solve[rewrite R_dist_sym; apply Pn2, Max.le_max_r].
  apply unif_ac; auto; solve [apply Max.le_max_l].
 exists N; intros; apply unif_ac'; solve[auto].
intros eps ep.
destruct (CVU_continuity _ _ _ _ H ctrho x bx eps ep) as [delta [dp Pd]].
exists (mkposreal _ dp); intros h hn0 dh.
replace ((g (x + h) - g x) / h) with (rho (x + h)).
 replace (g' x) with (rho x).
  apply Pd; unfold D_x, no_cond;split;[split;[solve[auto] | ] | ].
   intros xxh; case hn0; replace h with (x + h - x) by ring; rewrite <- xxh; ring.
  simpl; unfold R_dist; replace (x + h - x) with h by ring; exact dh.
 unfold rho; destruct (Req_EM_T x x) as [ _ | abs];[ | case abs]; reflexivity.
unfold rho; destruct (Req_EM_T (x + h) x) as [abs | _];[ | ].
 case hn0; replace h with (x + h - x) by ring; rewrite abs; ring.
replace (x + h - x) with h by ring; reflexivity.
Qed.

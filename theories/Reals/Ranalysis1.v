(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Rbase.
Require Import Rfunctions.
Require Export Rlimit.
Require Export Rderiv.
Open Local Scope R_scope.
Implicit Type f : R -> R.

(****************************************************)
(** *         Basic operations on functions         *)
(****************************************************)
Definition plus_fct f1 f2 (x:R) : R := f1 x + f2 x.
Definition opp_fct f (x:R) : R := - f x.
Definition mult_fct f1 f2 (x:R) : R := f1 x * f2 x.
Definition mult_real_fct (a:R) f (x:R) : R := a * f x.
Definition minus_fct f1 f2 (x:R) : R := f1 x - f2 x.
Definition div_fct f1 f2 (x:R) : R := f1 x / f2 x.
Definition div_real_fct (a:R) f (x:R) : R := a / f x.
Definition comp f1 f2 (x:R) : R := f1 (f2 x).
Definition inv_fct f (x:R) : R := / f x.

Delimit Scope Rfun_scope with F.

Arguments Scope plus_fct [Rfun_scope Rfun_scope R_scope].
Arguments Scope mult_fct [Rfun_scope Rfun_scope R_scope].
Arguments Scope minus_fct [Rfun_scope Rfun_scope R_scope].
Arguments Scope div_fct [Rfun_scope Rfun_scope R_scope].
Arguments Scope inv_fct [Rfun_scope R_scope].
Arguments Scope opp_fct [Rfun_scope R_scope].
Arguments Scope mult_real_fct [R_scope Rfun_scope R_scope].
Arguments Scope div_real_fct [R_scope Rfun_scope R_scope].
Arguments Scope comp [Rfun_scope Rfun_scope R_scope].

Infix "+" := plus_fct : Rfun_scope.
Notation "- x" := (opp_fct x) : Rfun_scope.
Infix "*" := mult_fct : Rfun_scope.
Infix "-" := minus_fct : Rfun_scope.
Infix "/" := div_fct : Rfun_scope.
Notation Local "f1 'o' f2" := (comp f1 f2)
  (at level 20, right associativity) : Rfun_scope.
Notation "/ x" := (inv_fct x) : Rfun_scope.

Definition fct_cte (a x:R) : R := a.
Definition id (x:R) := x.

(****************************************************)
(** *          Variations of functions              *)
(****************************************************)
Definition increasing f : Prop := forall x y:R, x <= y -> f x <= f y.
Definition decreasing f : Prop := forall x y:R, x <= y -> f y <= f x.
Definition strict_increasing f : Prop := forall x y:R, x < y -> f x < f y.
Definition strict_decreasing f : Prop := forall x y:R, x < y -> f y < f x.
Definition constant f : Prop := forall x y:R, f x = f y.

(**********)
Definition no_cond (x:R) : Prop := True.

(**********)
Definition constant_D_eq f (D:R -> Prop) (c:R) : Prop :=
  forall x:R, D x -> f x = c.

(***************************************************)
(** *    Definition of continuity as a limit       *)
(***************************************************)

(**********)
Definition continuity_pt f (x0:R) : Prop := continue_in f no_cond x0.
Definition continuity f : Prop := forall x:R, continuity_pt f x.

Arguments Scope continuity_pt [Rfun_scope R_scope].
Arguments Scope continuity [Rfun_scope].

(**********)
Lemma continuity_pt_plus :
  forall f1 f2 (x0:R),
    continuity_pt f1 x0 -> continuity_pt f2 x0 -> continuity_pt (f1 + f2) x0.
Proof.
  unfold continuity_pt, plus_fct in |- *; unfold continue_in in |- *; intros;
    apply limit_plus; assumption.
Qed.

Lemma continuity_pt_opp :
  forall f (x0:R), continuity_pt f x0 -> continuity_pt (- f) x0.
Proof.
  unfold continuity_pt, opp_fct in |- *; unfold continue_in in |- *; intros;
    apply limit_Ropp; assumption.
Qed.

Lemma continuity_pt_minus :
  forall f1 f2 (x0:R),
    continuity_pt f1 x0 -> continuity_pt f2 x0 -> continuity_pt (f1 - f2) x0.
Proof.
  unfold continuity_pt, minus_fct in |- *; unfold continue_in in |- *; intros;
    apply limit_minus; assumption.
Qed.

Lemma continuity_pt_mult :
  forall f1 f2 (x0:R),
    continuity_pt f1 x0 -> continuity_pt f2 x0 -> continuity_pt (f1 * f2) x0.
Proof.
  unfold continuity_pt, mult_fct in |- *; unfold continue_in in |- *; intros;
    apply limit_mul; assumption.
Qed.

Lemma continuity_pt_const : forall f (x0:R), constant f -> continuity_pt f x0.
Proof.
  unfold constant, continuity_pt in |- *; unfold continue_in in |- *;
    unfold limit1_in in |- *; unfold limit_in in |- *;
      intros; exists 1; split;
        [ apply Rlt_0_1
          | intros; generalize (H x x0); intro; rewrite H2; simpl in |- *;
            rewrite R_dist_eq; assumption ].
Qed.

Lemma continuity_pt_scal :
  forall f (a x0:R),
    continuity_pt f x0 -> continuity_pt (mult_real_fct a f) x0.
Proof.
  unfold continuity_pt, mult_real_fct in |- *; unfold continue_in in |- *;
    intros; apply (limit_mul (fun x:R => a) f (D_x no_cond x0) a (f x0) x0).
  unfold limit1_in in |- *; unfold limit_in in |- *; intros; exists 1; split.
  apply Rlt_0_1.
  intros; rewrite R_dist_eq; assumption.
  assumption.
Qed.

Lemma continuity_pt_inv :
  forall f (x0:R), continuity_pt f x0 -> f x0 <> 0 -> continuity_pt (/ f) x0.
Proof.
  intros.
  replace (/ f)%F with (fun x:R => / f x).
  unfold continuity_pt in |- *; unfold continue_in in |- *; intros;
    apply limit_inv; assumption.
  unfold inv_fct in |- *; reflexivity.
Qed.

Lemma div_eq_inv : forall f1 f2, (f1 / f2)%F = (f1 * / f2)%F.
Proof.
  intros; reflexivity.
Qed.

Lemma continuity_pt_div :
  forall f1 f2 (x0:R),
    continuity_pt f1 x0 ->
    continuity_pt f2 x0 -> f2 x0 <> 0 -> continuity_pt (f1 / f2) x0.
Proof.
  intros; rewrite (div_eq_inv f1 f2); apply continuity_pt_mult;
    [ assumption | apply continuity_pt_inv; assumption ].
Qed.

Lemma continuity_pt_comp :
  forall f1 f2 (x:R),
    continuity_pt f1 x -> continuity_pt f2 (f1 x) -> continuity_pt (f2 o f1) x.
Proof.
  unfold continuity_pt in |- *; unfold continue_in in |- *; intros;
    unfold comp in |- *.
  cut
    (limit1_in (fun x0:R => f2 (f1 x0))
      (Dgf (D_x no_cond x) (D_x no_cond (f1 x)) f1) (
        f2 (f1 x)) x ->
      limit1_in (fun x0:R => f2 (f1 x0)) (D_x no_cond x) (f2 (f1 x)) x).
  intro; apply H1.
  eapply limit_comp.
  apply H.
  apply H0.
  unfold limit1_in in |- *; unfold limit_in in |- *; unfold dist in |- *;
    simpl in |- *; unfold R_dist in |- *; intros.
  assert (H3 := H1 eps H2).
  elim H3; intros.
  exists x0.
  split.
  elim H4; intros; assumption.
  intros; case (Req_dec (f1 x) (f1 x1)); intro.
  rewrite H6; unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rabs_R0;
    assumption.
  elim H4; intros; apply H8.
  split.
  unfold Dgf, D_x, no_cond in |- *.
  split.
  split.
  trivial.
  elim H5; unfold D_x, no_cond in |- *; intros.
  elim H9; intros; assumption.
  split.
  trivial.
  assumption.
  elim H5; intros; assumption.
Qed.

(**********)
Lemma continuity_plus :
  forall f1 f2, continuity f1 -> continuity f2 -> continuity (f1 + f2).
Proof.
  unfold continuity in |- *; intros;
    apply (continuity_pt_plus f1 f2 x (H x) (H0 x)).
Qed.

Lemma continuity_opp : forall f, continuity f -> continuity (- f).
Proof.
  unfold continuity in |- *; intros; apply (continuity_pt_opp f x (H x)).
Qed.

Lemma continuity_minus :
  forall f1 f2, continuity f1 -> continuity f2 -> continuity (f1 - f2).
Proof.
  unfold continuity in |- *; intros;
    apply (continuity_pt_minus f1 f2 x (H x) (H0 x)).
Qed.

Lemma continuity_mult :
  forall f1 f2, continuity f1 -> continuity f2 -> continuity (f1 * f2).
Proof.
  unfold continuity in |- *; intros;
    apply (continuity_pt_mult f1 f2 x (H x) (H0 x)).
Qed.

Lemma continuity_const : forall f, constant f -> continuity f.
Proof.
  unfold continuity in |- *; intros; apply (continuity_pt_const f x H).
Qed.

Lemma continuity_scal :
  forall f (a:R), continuity f -> continuity (mult_real_fct a f).
Proof.
  unfold continuity in |- *; intros; apply (continuity_pt_scal f a x (H x)).
Qed.

Lemma continuity_inv :
  forall f, continuity f -> (forall x:R, f x <> 0) -> continuity (/ f).
Proof.
  unfold continuity in |- *; intros; apply (continuity_pt_inv f x (H x) (H0 x)).
Qed.

Lemma continuity_div :
  forall f1 f2,
    continuity f1 ->
    continuity f2 -> (forall x:R, f2 x <> 0) -> continuity (f1 / f2).
Proof.
  unfold continuity in |- *; intros;
    apply (continuity_pt_div f1 f2 x (H x) (H0 x) (H1 x)).
Qed.

Lemma continuity_comp :
  forall f1 f2, continuity f1 -> continuity f2 -> continuity (f2 o f1).
Proof.
  unfold continuity in |- *; intros.
  apply (continuity_pt_comp f1 f2 x (H x) (H0 (f1 x))).
Qed.


(*****************************************************)
(** * Derivative's definition using Landau's kernel  *)
(*****************************************************)

Definition derivable_pt_lim f (x l:R) : Prop :=
  forall eps:R,
    0 < eps ->
    exists delta : posreal,
      (forall h:R,
        h <> 0 -> Rabs h < delta -> Rabs ((f (x + h) - f x) / h - l) < eps).

Definition derivable_pt_abs f (x l:R) : Prop := derivable_pt_lim f x l.

Definition derivable_pt f (x:R) := { l:R | derivable_pt_abs f x l }.
Definition derivable f := forall x:R, derivable_pt f x.

Definition derive_pt f (x:R) (pr:derivable_pt f x) := proj1_sig pr.
Definition derive f (pr:derivable f) (x:R) := derive_pt f x (pr x).

Arguments Scope derivable_pt_lim [Rfun_scope R_scope].
Arguments Scope derivable_pt_abs [Rfun_scope R_scope R_scope].
Arguments Scope derivable_pt [Rfun_scope R_scope].
Arguments Scope derivable [Rfun_scope].
Arguments Scope derive_pt [Rfun_scope R_scope _].
Arguments Scope derive [Rfun_scope _].

Definition antiderivative f (g:R -> R) (a b:R) : Prop :=
  (forall x:R,
    a <= x <= b ->  exists pr : derivable_pt g x, f x = derive_pt g x pr) /\
  a <= b.
(**************************************)
(** * Class of differential functions *)
(**************************************)
Record Differential : Type := mkDifferential
  {d1 :> R -> R; cond_diff : derivable d1}.

Record Differential_D2 : Type := mkDifferential_D2
  {d2 :> R -> R;
    cond_D1 : derivable d2;
    cond_D2 : derivable (derive d2 cond_D1)}.

(**********)
Lemma uniqueness_step1 :
  forall f (x l1 l2:R),
    limit1_in (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> 0) l1 0 ->
    limit1_in (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> 0) l2 0 ->
    l1 = l2.
Proof.
  intros;
    apply
      (single_limit (fun h:R => (f (x + h) - f x) / h) (
        fun h:R => h <> 0) l1 l2 0); try assumption.
  unfold adhDa in |- *; intros; exists (alp / 2).
  split.
  unfold Rdiv in |- *; apply prod_neq_R0.
  red in |- *; intro; rewrite H2 in H1; elim (Rlt_irrefl _ H1).
  apply Rinv_neq_0_compat; discrR.
  unfold R_dist in |- *; unfold Rminus in |- *; rewrite Ropp_0;
    rewrite Rplus_0_r; unfold Rdiv in |- *; rewrite Rabs_mult.
  replace (Rabs (/ 2)) with (/ 2).
  replace (Rabs alp) with alp.
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  rewrite (Rmult_comm 2); rewrite Rmult_assoc; rewrite <- Rinv_l_sym;
    [ idtac | discrR ]; rewrite Rmult_1_r; rewrite double;
      pattern alp at 1 in |- *; replace alp with (alp + 0);
        [ idtac | ring ]; apply Rplus_lt_compat_l; assumption.
  symmetry  in |- *; apply Rabs_right; left; assumption.
  symmetry  in |- *; apply Rabs_right; left; change (0 < / 2) in |- *;
    apply Rinv_0_lt_compat; prove_sup0.
Qed.

Lemma uniqueness_step2 :
  forall f (x l:R),
    derivable_pt_lim f x l ->
    limit1_in (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> 0) l 0.
Proof.
  unfold derivable_pt_lim in |- *; intros; unfold limit1_in in |- *;
    unfold limit_in in |- *; intros.
  assert (H1 := H eps H0).
  elim H1; intros.
  exists (pos x0).
  split.
  apply (cond_pos x0).
  simpl in |- *; unfold R_dist in |- *; intros.
  elim H3; intros.
  apply H2;
    [ assumption
      | unfold Rminus in H5; rewrite Ropp_0 in H5; rewrite Rplus_0_r in H5;
        assumption ].
Qed.

Lemma uniqueness_step3 :
  forall f (x l:R),
    limit1_in (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> 0) l 0 ->
    derivable_pt_lim f x l.
Proof.
  unfold limit1_in, derivable_pt_lim in |- *; unfold limit_in in |- *;
    unfold dist in |- *; simpl in |- *; intros.
  elim (H eps H0).
  intros; elim H1; intros.
  exists (mkposreal x0 H2).
  simpl in |- *; intros; unfold R_dist in H3; apply (H3 h).
  split;
    [ assumption
      | unfold Rminus in |- *; rewrite Ropp_0; rewrite Rplus_0_r; assumption ].
Qed.

Lemma uniqueness_limite :
  forall f (x l1 l2:R),
    derivable_pt_lim f x l1 -> derivable_pt_lim f x l2 -> l1 = l2.
Proof.
  intros.
  assert (H1 := uniqueness_step2 _ _ _ H).
  assert (H2 := uniqueness_step2 _ _ _ H0).
  assert (H3 := uniqueness_step1 _ _ _ _ H1 H2).
  assumption.
Qed.

Lemma derive_pt_eq :
  forall f (x l:R) (pr:derivable_pt f x),
    derive_pt f x pr = l <-> derivable_pt_lim f x l.
Proof.
  intros; split.
  intro; assert (H1 := proj2_sig pr); unfold derive_pt in H; rewrite H in H1;
    assumption.
  intro; assert (H1 := proj2_sig pr); unfold derivable_pt_abs in H1.
  assert (H2 := uniqueness_limite _ _ _ _ H H1).
  unfold derive_pt in |- *; unfold derivable_pt_abs in |- *.
  symmetry  in |- *; assumption.
Qed.

(**********)
Lemma derive_pt_eq_0 :
  forall f (x l:R) (pr:derivable_pt f x),
    derivable_pt_lim f x l -> derive_pt f x pr = l.
Proof.
  intros; elim (derive_pt_eq f x l pr); intros.
  apply (H1 H).
Qed.

(**********)
Lemma derive_pt_eq_1 :
  forall f (x l:R) (pr:derivable_pt f x),
    derive_pt f x pr = l -> derivable_pt_lim f x l.
Proof.
  intros; elim (derive_pt_eq f x l pr); intros.
  apply (H0 H).
Qed.


(**********************************************************************)
(** * Equivalence of this definition with the one using limit concept *)
(**********************************************************************)
Lemma derive_pt_D_in :
  forall f (df:R -> R) (x:R) (pr:derivable_pt f x),
    D_in f df no_cond x <-> derive_pt f x pr = df x.
Proof.
  intros; split.
  unfold D_in in |- *; unfold limit1_in in |- *; unfold limit_in in |- *;
    simpl in |- *; unfold R_dist in |- *; intros.
  apply derive_pt_eq_0.
  unfold derivable_pt_lim in |- *.
  intros; elim (H eps H0); intros alpha H1; elim H1; intros;
    exists (mkposreal alpha H2); intros; generalize (H3 (x + h));
      intro; cut (x + h - x = h);
        [ intro; cut (D_x no_cond x (x + h) /\ Rabs (x + h - x) < alpha);
          [ intro; generalize (H6 H8); rewrite H7; intro; assumption
            | split;
              [ unfold D_x in |- *; split;
                [ unfold no_cond in |- *; trivial
                  | apply Rminus_not_eq_right; rewrite H7; assumption ]
                | rewrite H7; assumption ] ]
          | ring ].
  intro.
  assert (H0 := derive_pt_eq_1 f x (df x) pr H).
  unfold D_in in |- *; unfold limit1_in in |- *; unfold limit_in in |- *;
    unfold dist in |- *; simpl in |- *; unfold R_dist in |- *;
      intros.
  elim (H0 eps H1); intros alpha H2; exists (pos alpha); split.
  apply (cond_pos alpha).
  intros; elim H3; intros; unfold D_x in H4; elim H4; intros; cut (x0 - x <> 0).
  intro; generalize (H2 (x0 - x) H8 H5); replace (x + (x0 - x)) with x0.
  intro; assumption.
  ring.
  auto with real.
Qed.

Lemma derivable_pt_lim_D_in :
  forall f (df:R -> R) (x:R),
    D_in f df no_cond x <-> derivable_pt_lim f x (df x).
Proof.
  intros; split.
  unfold D_in in |- *; unfold limit1_in in |- *; unfold limit_in in |- *;
    simpl in |- *; unfold R_dist in |- *; intros.
  unfold derivable_pt_lim in |- *.
  intros; elim (H eps H0); intros alpha H1; elim H1; intros;
    exists (mkposreal alpha H2); intros; generalize (H3 (x + h));
      intro; cut (x + h - x = h);
        [ intro; cut (D_x no_cond x (x + h) /\ Rabs (x + h - x) < alpha);
          [ intro; generalize (H6 H8); rewrite H7; intro; assumption
            | split;
              [ unfold D_x in |- *; split;
                [ unfold no_cond in |- *; trivial
                  | apply Rminus_not_eq_right; rewrite H7; assumption ]
                | rewrite H7; assumption ] ]
          | ring ].
  intro.
  unfold derivable_pt_lim in H.
  unfold D_in in |- *; unfold limit1_in in |- *; unfold limit_in in |- *;
    unfold dist in |- *; simpl in |- *; unfold R_dist in |- *;
      intros.
  elim (H eps H0); intros alpha H2; exists (pos alpha); split.
  apply (cond_pos alpha).
  intros.
  elim H1; intros; unfold D_x in H3; elim H3; intros; cut (x0 - x <> 0).
  intro; generalize (H2 (x0 - x) H7 H4); replace (x + (x0 - x)) with x0.
  intro; assumption.
  ring.
  auto with real.
Qed.


(***********************************)
(** * derivability -> continuity   *)
(***********************************)
(**********)
Lemma derivable_derive :
  forall f (x:R) (pr:derivable_pt f x),  exists l : R, derive_pt f x pr = l.
Proof.
  intros; exists (proj1_sig pr).
  unfold derive_pt in |- *; reflexivity.
Qed.

Theorem derivable_continuous_pt :
  forall f (x:R), derivable_pt f x -> continuity_pt f x.
Proof.
  intros f x X.
  generalize (derivable_derive f x X); intro.
  elim H; intros l H1.
  cut (l = fct_cte l x).
  intro.
  rewrite H0 in H1.
  generalize (derive_pt_D_in f (fct_cte l) x); intro.
  elim (H2 X); intros.
  generalize (H4 H1); intro.
  unfold continuity_pt in |- *.
  apply (cont_deriv f (fct_cte l) no_cond x H5).
  unfold fct_cte in |- *; reflexivity.
Qed.

Theorem derivable_continuous : forall f, derivable f -> continuity f.
Proof.
  unfold derivable, continuity in |- *; intros f X x.
  apply (derivable_continuous_pt f x (X x)).
Qed.

(****************************************************************)
(** *                    Main rules                             *)
(****************************************************************)

Lemma derivable_pt_lim_plus :
  forall f1 f2 (x l1 l2:R),
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 x l2 -> derivable_pt_lim (f1 + f2) x (l1 + l2).
  intros.
  apply uniqueness_step3.
  assert (H1 := uniqueness_step2 _ _ _ H).
  assert (H2 := uniqueness_step2 _ _ _ H0).
  unfold plus_fct in |- *.
  cut
    (forall h:R,
      (f1 (x + h) + f2 (x + h) - (f1 x + f2 x)) / h =
      (f1 (x + h) - f1 x) / h + (f2 (x + h) - f2 x) / h).
  intro.
  generalize
    (limit_plus (fun h':R => (f1 (x + h') - f1 x) / h')
      (fun h':R => (f2 (x + h') - f2 x) / h') (fun h:R => h <> 0) l1 l2 0 H1 H2).
  unfold limit1_in in |- *; unfold limit_in in |- *; unfold dist in |- *;
    simpl in |- *; unfold R_dist in |- *; intros.
  elim (H4 eps H5); intros.
  exists x0.
  elim H6; intros.
  split.
  assumption.
  intros; rewrite H3; apply H8; assumption.
  intro; unfold Rdiv in |- *; ring.
Qed.

Lemma derivable_pt_lim_opp :
  forall f (x l:R), derivable_pt_lim f x l -> derivable_pt_lim (- f) x (- l).
Proof.
  intros.
  apply uniqueness_step3.
  assert (H1 := uniqueness_step2 _ _ _ H).
  unfold opp_fct in |- *.
  cut (forall h:R, (- f (x + h) - - f x) / h = - ((f (x + h) - f x) / h)).
  intro.
  generalize
    (limit_Ropp (fun h:R => (f (x + h) - f x) / h) (fun h:R => h <> 0) l 0 H1).
  unfold limit1_in in |- *; unfold limit_in in |- *; unfold dist in |- *;
    simpl in |- *; unfold R_dist in |- *; intros.
  elim (H2 eps H3); intros.
  exists x0.
  elim H4; intros.
  split.
  assumption.
  intros; rewrite H0; apply H6; assumption.
  intro; unfold Rdiv in |- *; ring.
Qed.

Lemma derivable_pt_lim_minus :
  forall f1 f2 (x l1 l2:R),
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 x l2 -> derivable_pt_lim (f1 - f2) x (l1 - l2).
Proof.
  intros.
  apply uniqueness_step3.
  assert (H1 := uniqueness_step2 _ _ _ H).
  assert (H2 := uniqueness_step2 _ _ _ H0).
  unfold minus_fct in |- *.
  cut
    (forall h:R,
      (f1 (x + h) - f1 x) / h - (f2 (x + h) - f2 x) / h =
      (f1 (x + h) - f2 (x + h) - (f1 x - f2 x)) / h).
  intro.
  generalize
    (limit_minus (fun h':R => (f1 (x + h') - f1 x) / h')
      (fun h':R => (f2 (x + h') - f2 x) / h') (fun h:R => h <> 0) l1 l2 0 H1 H2).
  unfold limit1_in in |- *; unfold limit_in in |- *; unfold dist in |- *;
    simpl in |- *; unfold R_dist in |- *; intros.
  elim (H4 eps H5); intros.
  exists x0.
  elim H6; intros.
  split.
  assumption.
  intros; rewrite <- H3; apply H8; assumption.
  intro; unfold Rdiv in |- *; ring.
Qed.

Lemma derivable_pt_lim_mult :
  forall f1 f2 (x l1 l2:R),
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 x l2 ->
    derivable_pt_lim (f1 * f2) x (l1 * f2 x + f1 x * l2).
Proof.
  intros.
  assert (H1 := derivable_pt_lim_D_in f1 (fun y:R => l1) x).
  elim H1; intros.
  assert (H4 := H3 H).
  assert (H5 := derivable_pt_lim_D_in f2 (fun y:R => l2) x).
  elim H5; intros.
  assert (H8 := H7 H0).
  clear H1 H2 H3 H5 H6 H7.
  assert
    (H1 :=
      derivable_pt_lim_D_in (f1 * f2)%F (fun y:R => l1 * f2 x + f1 x * l2) x).
  elim H1; intros.
  clear H1 H3.
  apply H2.
  unfold mult_fct in |- *.
  apply (Dmult no_cond (fun y:R => l1) (fun y:R => l2) f1 f2 x); assumption.
Qed.

Lemma derivable_pt_lim_const : forall a x:R, derivable_pt_lim (fct_cte a) x 0.
Proof.
  intros; unfold fct_cte, derivable_pt_lim in |- *.
  intros; exists (mkposreal 1 Rlt_0_1); intros; unfold Rminus in |- *;
    rewrite Rplus_opp_r; unfold Rdiv in |- *; rewrite Rmult_0_l;
      rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
Qed.

Lemma derivable_pt_lim_scal :
  forall f (a x l:R),
    derivable_pt_lim f x l -> derivable_pt_lim (mult_real_fct a f) x (a * l).
Proof.
  intros.
  assert (H0 := derivable_pt_lim_const a x).
  replace (mult_real_fct a f) with (fct_cte a * f)%F.
  replace (a * l) with (0 * f x + a * l); [ idtac | ring ].
  apply (derivable_pt_lim_mult (fct_cte a) f x 0 l); assumption.
  unfold mult_real_fct, mult_fct, fct_cte in |- *; reflexivity.
Qed.

Lemma derivable_pt_lim_id : forall x:R, derivable_pt_lim id x 1.
Proof.
  intro; unfold derivable_pt_lim in |- *.
  intros eps Heps; exists (mkposreal eps Heps); intros h H1 H2;
    unfold id in |- *; replace ((x + h - x) / h - 1) with 0.
  rewrite Rabs_R0; apply Rle_lt_trans with (Rabs h).
  apply Rabs_pos.
  assumption.
  unfold Rminus in |- *; rewrite Rplus_assoc; rewrite (Rplus_comm x);
    rewrite Rplus_assoc.
  rewrite Rplus_opp_l; rewrite Rplus_0_r; unfold Rdiv in |- *;
    rewrite <- Rinv_r_sym.
  symmetry  in |- *; apply Rplus_opp_r.
  assumption.
Qed.

Lemma derivable_pt_lim_Rsqr : forall x:R, derivable_pt_lim Rsqr x (2 * x).
Proof.
  intro; unfold derivable_pt_lim in |- *.
  unfold Rsqr in |- *; intros eps Heps; exists (mkposreal eps Heps);
    intros h H1 H2; replace (((x + h) * (x + h) - x * x) / h - 2 * x) with h.
  assumption.
  replace ((x + h) * (x + h) - x * x) with (2 * x * h + h * h);
  [ idtac | ring ].
  unfold Rdiv in |- *; rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  repeat rewrite <- Rinv_r_sym; [ idtac | assumption ].
  ring.
Qed.

Lemma derivable_pt_lim_comp :
  forall f1 f2 (x l1 l2:R),
    derivable_pt_lim f1 x l1 ->
    derivable_pt_lim f2 (f1 x) l2 -> derivable_pt_lim (f2 o f1) x (l2 * l1).
Proof.
  intros; assert (H1 := derivable_pt_lim_D_in f1 (fun y:R => l1) x).
  elim H1; intros.
  assert (H4 := H3 H).
  assert (H5 := derivable_pt_lim_D_in f2 (fun y:R => l2) (f1 x)).
  elim H5; intros.
  assert (H8 := H7 H0).
  clear H1 H2 H3 H5 H6 H7.
  assert (H1 := derivable_pt_lim_D_in (f2 o f1)%F (fun y:R => l2 * l1) x).
  elim H1; intros.
  clear H1 H3; apply H2.
  unfold comp in |- *;
    cut
      (D_in (fun x0:R => f2 (f1 x0)) (fun y:R => l2 * l1)
        (Dgf no_cond no_cond f1) x ->
        D_in (fun x0:R => f2 (f1 x0)) (fun y:R => l2 * l1) no_cond x).
  intro; apply H1.
  rewrite Rmult_comm;
    apply (Dcomp no_cond no_cond (fun y:R => l1) (fun y:R => l2) f1 f2 x);
      assumption.
  unfold Dgf, D_in, no_cond in |- *; unfold limit1_in in |- *;
    unfold limit_in in |- *; unfold dist in |- *; simpl in |- *;
      unfold R_dist in |- *; intros.
  elim (H1 eps H3); intros.
  exists x0; intros; split.
  elim H5; intros; assumption.
  intros; elim H5; intros; apply H9; split.
  unfold D_x in |- *; split.
  split; trivial.
  elim H6; intros; unfold D_x in H10; elim H10; intros; assumption.
  elim H6; intros; assumption.
Qed.

Lemma derivable_pt_plus :
  forall f1 f2 (x:R),
    derivable_pt f1 x -> derivable_pt f2 x -> derivable_pt (f1 + f2) x.
Proof.
  unfold derivable_pt in |- *; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x0 + x1).
  apply derivable_pt_lim_plus; assumption.
Qed.

Lemma derivable_pt_opp :
  forall f (x:R), derivable_pt f x -> derivable_pt (- f) x.
Proof.
  unfold derivable_pt in |- *; intros f x X.
  elim X; intros.
  exists (- x0).
  apply derivable_pt_lim_opp; assumption.
Qed.

Lemma derivable_pt_minus :
  forall f1 f2 (x:R),
    derivable_pt f1 x -> derivable_pt f2 x -> derivable_pt (f1 - f2) x.
Proof.
  unfold derivable_pt in |- *; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x0 - x1).
  apply derivable_pt_lim_minus; assumption.
Qed.

Lemma derivable_pt_mult :
  forall f1 f2 (x:R),
    derivable_pt f1 x -> derivable_pt f2 x -> derivable_pt (f1 * f2) x.
Proof.
  unfold derivable_pt in |- *; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x0 * f2 x + f1 x * x1).
  apply derivable_pt_lim_mult; assumption.
Qed.

Lemma derivable_pt_const : forall a x:R, derivable_pt (fct_cte a) x.
Proof.
  intros; unfold derivable_pt in |- *.
  exists 0.
  apply derivable_pt_lim_const.
Qed.

Lemma derivable_pt_scal :
  forall f (a x:R), derivable_pt f x -> derivable_pt (mult_real_fct a f) x.
Proof.
  unfold derivable_pt in |- *; intros f1 a x X.
  elim X; intros.
  exists (a * x0).
  apply derivable_pt_lim_scal; assumption.
Qed.

Lemma derivable_pt_id : forall x:R, derivable_pt id x.
Proof.
  unfold derivable_pt in |- *; intro.
  exists 1.
  apply derivable_pt_lim_id.
Qed.

Lemma derivable_pt_Rsqr : forall x:R, derivable_pt Rsqr x.
Proof.
  unfold derivable_pt in |- *; intro; exists (2 * x).
  apply derivable_pt_lim_Rsqr.
Qed.

Lemma derivable_pt_comp :
  forall f1 f2 (x:R),
    derivable_pt f1 x -> derivable_pt f2 (f1 x) -> derivable_pt (f2 o f1) x.
Proof.
  unfold derivable_pt in |- *; intros f1 f2 x X X0.
  elim X; intros.
  elim X0; intros.
  exists (x1 * x0).
  apply derivable_pt_lim_comp; assumption.
Qed.

Lemma derivable_plus :
  forall f1 f2, derivable f1 -> derivable f2 -> derivable (f1 + f2).
Proof.
  unfold derivable in |- *; intros f1 f2 X X0 x.
  apply (derivable_pt_plus _ _ x (X _) (X0 _)).
Qed.

Lemma derivable_opp : forall f, derivable f -> derivable (- f).
Proof.
  unfold derivable in |- *; intros f X x.
  apply (derivable_pt_opp _ x (X _)).
Qed.

Lemma derivable_minus :
  forall f1 f2, derivable f1 -> derivable f2 -> derivable (f1 - f2).
Proof.
  unfold derivable in |- *; intros f1 f2 X X0 x.
  apply (derivable_pt_minus _ _ x (X _) (X0 _)).
Qed.

Lemma derivable_mult :
  forall f1 f2, derivable f1 -> derivable f2 -> derivable (f1 * f2).
Proof.
  unfold derivable in |- *; intros f1 f2 X X0 x.
  apply (derivable_pt_mult _ _ x (X _) (X0 _)).
Qed.

Lemma derivable_const : forall a:R, derivable (fct_cte a).
Proof.
  unfold derivable in |- *; intros.
  apply derivable_pt_const.
Qed.

Lemma derivable_scal :
  forall f (a:R), derivable f -> derivable (mult_real_fct a f).
Proof.
  unfold derivable in |- *; intros f a X x.
  apply (derivable_pt_scal _ a x (X _)).
Qed.

Lemma derivable_id : derivable id.
Proof.
  unfold derivable in |- *; intro; apply derivable_pt_id.
Qed.

Lemma derivable_Rsqr : derivable Rsqr.
Proof.
  unfold derivable in |- *; intro; apply derivable_pt_Rsqr.
Qed.

Lemma derivable_comp :
  forall f1 f2, derivable f1 -> derivable f2 -> derivable (f2 o f1).
Proof.
  unfold derivable in |- *; intros f1 f2 X X0 x.
  apply (derivable_pt_comp _ _ x (X _) (X0 _)).
Qed.

Lemma derive_pt_plus :
  forall f1 f2 (x:R) (pr1:derivable_pt f1 x) (pr2:derivable_pt f2 x),
    derive_pt (f1 + f2) x (derivable_pt_plus _ _ _ pr1 pr2) =
    derive_pt f1 x pr1 + derive_pt f2 x pr2.
Proof.
  intros.
  assert (H := derivable_derive f1 x pr1).
  assert (H0 := derivable_derive f2 x pr2).
  assert
    (H1 := derivable_derive (f1 + f2)%F x (derivable_pt_plus _ _ _ pr1 pr2)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  elim H1; clear H1; intros l H1.
  rewrite H; rewrite H0; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  assert (H4 := proj2_sig pr2).
  unfold derive_pt in H0; rewrite H0 in H4.
  apply derivable_pt_lim_plus; assumption.
Qed.

Lemma derive_pt_opp :
  forall f (x:R) (pr1:derivable_pt f x),
    derive_pt (- f) x (derivable_pt_opp _ _ pr1) = - derive_pt f x pr1.
Proof.
  intros.
  assert (H := derivable_derive f x pr1).
  assert (H0 := derivable_derive (- f)%F x (derivable_pt_opp _ _ pr1)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  rewrite H; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  apply derivable_pt_lim_opp; assumption.
Qed.

Lemma derive_pt_minus :
  forall f1 f2 (x:R) (pr1:derivable_pt f1 x) (pr2:derivable_pt f2 x),
    derive_pt (f1 - f2) x (derivable_pt_minus _ _ _ pr1 pr2) =
    derive_pt f1 x pr1 - derive_pt f2 x pr2.
Proof.
  intros.
  assert (H := derivable_derive f1 x pr1).
  assert (H0 := derivable_derive f2 x pr2).
  assert
    (H1 := derivable_derive (f1 - f2)%F x (derivable_pt_minus _ _ _ pr1 pr2)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  elim H1; clear H1; intros l H1.
  rewrite H; rewrite H0; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  assert (H4 := proj2_sig pr2).
  unfold derive_pt in H0; rewrite H0 in H4.
  apply derivable_pt_lim_minus; assumption.
Qed.

Lemma derive_pt_mult :
  forall f1 f2 (x:R) (pr1:derivable_pt f1 x) (pr2:derivable_pt f2 x),
    derive_pt (f1 * f2) x (derivable_pt_mult _ _ _ pr1 pr2) =
    derive_pt f1 x pr1 * f2 x + f1 x * derive_pt f2 x pr2.
Proof.
  intros.
  assert (H := derivable_derive f1 x pr1).
  assert (H0 := derivable_derive f2 x pr2).
  assert
    (H1 := derivable_derive (f1 * f2)%F x (derivable_pt_mult _ _ _ pr1 pr2)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  elim H1; clear H1; intros l H1.
  rewrite H; rewrite H0; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  assert (H4 := proj2_sig pr2).
  unfold derive_pt in H0; rewrite H0 in H4.
  apply derivable_pt_lim_mult; assumption.
Qed.

Lemma derive_pt_const :
  forall a x:R, derive_pt (fct_cte a) x (derivable_pt_const a x) = 0.
Proof.
  intros.
  apply derive_pt_eq_0.
  apply derivable_pt_lim_const.
Qed.

Lemma derive_pt_scal :
  forall f (a x:R) (pr:derivable_pt f x),
    derive_pt (mult_real_fct a f) x (derivable_pt_scal _ _ _ pr) =
    a * derive_pt f x pr.
Proof.
  intros.
  assert (H := derivable_derive f x pr).
  assert
    (H0 := derivable_derive (mult_real_fct a f) x (derivable_pt_scal _ _ _ pr)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  rewrite H; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr).
  unfold derive_pt in H; rewrite H in H3.
  apply derivable_pt_lim_scal; assumption.
Qed.

Lemma derive_pt_id : forall x:R, derive_pt id x (derivable_pt_id _) = 1.
Proof.
  intros.
  apply derive_pt_eq_0.
  apply derivable_pt_lim_id.
Qed.

Lemma derive_pt_Rsqr :
  forall x:R, derive_pt Rsqr x (derivable_pt_Rsqr _) = 2 * x.
Proof.
  intros.
  apply derive_pt_eq_0.
  apply derivable_pt_lim_Rsqr.
Qed.

Lemma derive_pt_comp :
  forall f1 f2 (x:R) (pr1:derivable_pt f1 x) (pr2:derivable_pt f2 (f1 x)),
    derive_pt (f2 o f1) x (derivable_pt_comp _ _ _ pr1 pr2) =
    derive_pt f2 (f1 x) pr2 * derive_pt f1 x pr1.
Proof.
  intros.
  assert (H := derivable_derive f1 x pr1).
  assert (H0 := derivable_derive f2 (f1 x) pr2).
  assert
    (H1 := derivable_derive (f2 o f1)%F x (derivable_pt_comp _ _ _ pr1 pr2)).
  elim H; clear H; intros l1 H.
  elim H0; clear H0; intros l2 H0.
  elim H1; clear H1; intros l H1.
  rewrite H; rewrite H0; apply derive_pt_eq_0.
  assert (H3 := proj2_sig pr1).
  unfold derive_pt in H; rewrite H in H3.
  assert (H4 := proj2_sig pr2).
  unfold derive_pt in H0; rewrite H0 in H4.
  apply derivable_pt_lim_comp; assumption.
Qed.

(* Pow *)
Definition pow_fct (n:nat) (y:R) : R := y ^ n.

Lemma derivable_pt_lim_pow_pos :
  forall (x:R) (n:nat),
    (0 < n)%nat -> derivable_pt_lim (fun y:R => y ^ n) x (INR n * x ^ pred n).
Proof.
  intros.
  induction  n as [| n Hrecn].
  elim (lt_irrefl _ H).
  cut (n = 0%nat \/ (0 < n)%nat).
  intro; elim H0; intro.
  rewrite H1; simpl in |- *.
  replace (fun y:R => y * 1) with (id * fct_cte 1)%F.
  replace (1 * 1) with (1 * fct_cte 1 x + id x * 0).
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  unfold fct_cte, id in |- *; ring.
  reflexivity.
  replace (fun y:R => y ^ S n) with (fun y:R => y * y ^ n).
  replace (pred (S n)) with n; [ idtac | reflexivity ].
  replace (fun y:R => y * y ^ n) with (id * (fun y:R => y ^ n))%F.
  set (f := fun y:R => y ^ n).
  replace (INR (S n) * x ^ n) with (1 * f x + id x * (INR n * x ^ pred n)).
  apply derivable_pt_lim_mult.
  apply derivable_pt_lim_id.
  unfold f in |- *; apply Hrecn; assumption.
  unfold f in |- *.
  pattern n at 1 5 in |- *; replace n with (S (pred n)).
  unfold id in |- *; rewrite S_INR; simpl in |- *.
  ring.
  symmetry  in |- *; apply S_pred with 0%nat; assumption.
  unfold mult_fct, id in |- *; reflexivity.
  reflexivity.
  inversion H.
  left; reflexivity.
  right.
  apply lt_le_trans with 1%nat.
  apply lt_O_Sn.
  assumption.
Qed.

Lemma derivable_pt_lim_pow :
  forall (x:R) (n:nat),
    derivable_pt_lim (fun y:R => y ^ n) x (INR n * x ^ pred n).
Proof.
  intros.
  induction  n as [| n Hrecn].
  simpl in |- *.
  rewrite Rmult_0_l.
  replace (fun _:R => 1) with (fct_cte 1);
  [ apply derivable_pt_lim_const | reflexivity ].
  apply derivable_pt_lim_pow_pos.
  apply lt_O_Sn.
Qed.

Lemma derivable_pt_pow :
  forall (n:nat) (x:R), derivable_pt (fun y:R => y ^ n) x.
Proof.
  intros; unfold derivable_pt in |- *.
  exists (INR n * x ^ pred n).
  apply derivable_pt_lim_pow.
Qed.

Lemma derivable_pow : forall n:nat, derivable (fun y:R => y ^ n).
Proof.
  intro; unfold derivable in |- *; intro; apply derivable_pt_pow.
Qed.

Lemma derive_pt_pow :
  forall (n:nat) (x:R),
    derive_pt (fun y:R => y ^ n) x (derivable_pt_pow n x) = INR n * x ^ pred n.
Proof.
  intros; apply derive_pt_eq_0.
  apply derivable_pt_lim_pow.
Qed.

Lemma pr_nu :
  forall f (x:R) (pr1 pr2:derivable_pt f x),
    derive_pt f x pr1 = derive_pt f x pr2.
Proof.
  intros.
  unfold derivable_pt in pr1.
  unfold derivable_pt in pr2.
  elim pr1; intros.
  elim pr2; intros.
  unfold derivable_pt_abs in p.
  unfold derivable_pt_abs in p0.
  simpl in |- *.
  apply (uniqueness_limite f x x0 x1 p p0).
Qed.


(************************************************************)
(** *           Local extremum's condition                  *)
(************************************************************)

Theorem deriv_maximum :
  forall f (a b c:R) (pr:derivable_pt f c),
    a < c ->
    c < b ->
    (forall x:R, a < x -> x < b -> f x <= f c) -> derive_pt f c pr = 0.
Proof.
  intros; case (Rtotal_order 0 (derive_pt f c pr)); intro.
  assert (H3 := derivable_derive f c pr).
  elim H3; intros l H4; rewrite H4 in H2.
  assert (H5 := derive_pt_eq_1 f c l pr H4).
  cut (0 < l / 2);
    [ intro
      | unfold Rdiv in |- *; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  elim (H5 (l / 2) H6); intros delta H7.
  cut (0 < (b - c) / 2).
  intro; cut (Rmin (delta / 2) ((b - c) / 2) <> 0).
  intro; cut (Rabs (Rmin (delta / 2) ((b - c) / 2)) < delta).
  intro.
  assert (H11 := H7 (Rmin (delta / 2) ((b - c) / 2)) H9 H10).
  cut (0 < Rmin (delta / 2) ((b - c) / 2)).
  intro; cut (a < c + Rmin (delta / 2) ((b - c) / 2)).
  intro; cut (c + Rmin (delta / 2) ((b - c) / 2) < b).
  intro; assert (H15 := H1 (c + Rmin (delta / 2) ((b - c) / 2)) H13 H14).
  cut
    ((f (c + Rmin (delta / 2) ((b - c) / 2)) - f c) /
      Rmin (delta / 2) ((b - c) / 2) <= 0).
  intro; cut (- l < 0).
  intro; unfold Rminus in H11.
  cut
    ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
      Rmin (delta / 2) ((b + - c) / 2) + - l < 0).
  intro;
    cut
      (Rabs
        ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
          Rmin (delta / 2) ((b + - c) / 2) + - l) < l / 2).
  unfold Rabs in |- *;
    case
    (Rcase_abs
      ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
        Rmin (delta / 2) ((b + - c) / 2) + - l)); intro.
  replace
  (-
    ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
      Rmin (delta / 2) ((b + - c) / 2) + - l)) with
  (l +
    -
    ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
      Rmin (delta / 2) ((b + - c) / 2))).
  intro;
    generalize
      (Rplus_lt_compat_l (- l)
        (l +
          -
          ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
            Rmin (delta / 2) ((b + - c) / 2))) (l / 2) H19);
      repeat rewrite <- Rplus_assoc; rewrite Rplus_opp_l;
        rewrite Rplus_0_l; replace (- l + l / 2) with (- (l / 2)).
  intro;
    generalize
      (Ropp_lt_gt_contravar
        (-
          ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
            Rmin (delta / 2) ((b + - c) / 2))) (- (l / 2)) H20);
      repeat rewrite Ropp_involutive; intro;
        generalize
          (Rlt_trans 0 (l / 2)
            ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
              Rmin (delta / 2) ((b + - c) / 2)) H6 H21); intro;
          elim
            (Rlt_irrefl 0
              (Rlt_le_trans 0
                ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
                  Rmin (delta / 2) ((b + - c) / 2)) 0 H22 H16)).
  pattern l at 2 in |- *; rewrite double_var.
  ring.
  ring.
  intro.
  assert
    (H20 :=
      Rge_le
      ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
        Rmin (delta / 2) ((b + - c) / 2) + - l) 0 r).
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H20 H18)).
  assumption.
  rewrite <- Ropp_0;
    replace
    ((f (c + Rmin (delta / 2) ((b + - c) / 2)) + - f c) /
      Rmin (delta / 2) ((b + - c) / 2) + - l) with
    (-
      (l +
        -
        ((f (c + Rmin (delta / 2) ((b + - c) / 2)) - f c) /
          Rmin (delta / 2) ((b + - c) / 2)))).
  apply Ropp_gt_lt_contravar;
    change
      (0 <
        l +
        -
        ((f (c + Rmin (delta / 2) ((b + - c) / 2)) - f c) /
          Rmin (delta / 2) ((b + - c) / 2))) in |- *; apply Rplus_lt_le_0_compat;
      [ assumption
        | rewrite <- Ropp_0; apply Ropp_ge_le_contravar; apply Rle_ge; assumption ].
  unfold Rminus; ring.
  rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; assumption.
  replace
  ((f (c + Rmin (delta / 2) ((b - c) / 2)) - f c) /
    Rmin (delta / 2) ((b - c) / 2)) with
  (-
    ((f c - f (c + Rmin (delta / 2) ((b - c) / 2))) /
      Rmin (delta / 2) ((b - c) / 2))).
  rewrite <- Ropp_0; apply Ropp_ge_le_contravar; apply Rle_ge;
    unfold Rdiv in |- *; apply Rmult_le_pos;
      [ generalize
        (Rplus_le_compat_r (- f (c + Rmin (delta * / 2) ((b - c) * / 2)))
          (f (c + Rmin (delta * / 2) ((b - c) * / 2))) (
            f c) H15); rewrite Rplus_opp_r; intro; assumption
        | left; apply Rinv_0_lt_compat; assumption ].
  unfold Rdiv in |- *.
  rewrite <- Ropp_mult_distr_l_reverse.
  repeat rewrite <- (Rmult_comm (/ Rmin (delta * / 2) ((b - c) * / 2))).
  apply Rmult_eq_reg_l with (Rmin (delta * / 2) ((b - c) * / 2)).
  repeat rewrite <- Rmult_assoc.
  rewrite <- Rinv_r_sym.
  repeat rewrite Rmult_1_l.
  ring.
  red in |- *; intro.
  unfold Rdiv in H12; rewrite H16 in H12; elim (Rlt_irrefl 0 H12).
  red in |- *; intro.
  unfold Rdiv in H12; rewrite H16 in H12; elim (Rlt_irrefl 0 H12).
  assert (H14 := Rmin_r (delta / 2) ((b - c) / 2)).
  assert
    (H15 :=
      Rplus_le_compat_l c (Rmin (delta / 2) ((b - c) / 2)) ((b - c) / 2) H14).
  apply Rle_lt_trans with (c + (b - c) / 2).
  assumption.
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  replace (2 * (c + (b - c) / 2)) with (c + b).
  replace (2 * b) with (b + b).
  apply Rplus_lt_compat_r; assumption.
  ring.
  unfold Rdiv in |- *; rewrite Rmult_plus_distr_l.
  repeat rewrite (Rmult_comm 2).
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r.
  ring.
  discrR.
  apply Rlt_trans with c.
  assumption.
  pattern c at 1 in |- *; rewrite <- (Rplus_0_r c); apply Rplus_lt_compat_l;
    assumption.
  cut (0 < delta / 2).
  intro;
    apply
      (Rmin_stable_in_posreal (mkposreal (delta / 2) H12)
        (mkposreal ((b - c) / 2) H8)).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply (cond_pos delta) | apply Rinv_0_lt_compat; prove_sup0 ].
  unfold Rabs in |- *; case (Rcase_abs (Rmin (delta / 2) ((b - c) / 2))).
  intro.
  cut (0 < delta / 2).
  intro.
  generalize
    (Rmin_stable_in_posreal (mkposreal (delta / 2) H10)
      (mkposreal ((b - c) / 2) H8)); simpl in |- *; intro;
    elim (Rlt_irrefl 0 (Rlt_trans 0 (Rmin (delta / 2) ((b - c) / 2)) 0 H11 r)).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply (cond_pos delta) | apply Rinv_0_lt_compat; prove_sup0 ].
  intro; apply Rle_lt_trans with (delta / 2).
  apply Rmin_l.
  unfold Rdiv in |- *; apply Rmult_lt_reg_l with 2.
  prove_sup0.
  rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l.
  replace (2 * delta) with (delta + delta).
  pattern delta at 2 in |- *; rewrite <- (Rplus_0_r delta);
    apply Rplus_lt_compat_l.
  rewrite Rplus_0_r; apply (cond_pos delta).
  symmetry  in |- *; apply double.
  discrR.
  cut (0 < delta / 2).
  intro;
    generalize
      (Rmin_stable_in_posreal (mkposreal (delta / 2) H9)
        (mkposreal ((b - c) / 2) H8)); simpl in |- *;
      intro; red in |- *; intro; rewrite H11 in H10; elim (Rlt_irrefl 0 H10).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply (cond_pos delta) | apply Rinv_0_lt_compat; prove_sup0 ].
  unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  generalize (Rplus_lt_compat_r (- c) c b H0); rewrite Rplus_opp_r; intro;
    assumption.
  apply Rinv_0_lt_compat; prove_sup0.
  elim H2; intro.
  symmetry  in |- *; assumption.
  generalize (derivable_derive f c pr); intro; elim H4; intros l H5.
  rewrite H5 in H3; generalize (derive_pt_eq_1 f c l pr H5); intro;
    cut (0 < - (l / 2)).
  intro; elim (H6 (- (l / 2)) H7); intros delta H9.
  cut (0 < (c - a) / 2).
  intro; cut (Rmax (- (delta / 2)) ((a - c) / 2) < 0).
  intro; cut (Rmax (- (delta / 2)) ((a - c) / 2) <> 0).
  intro; cut (Rabs (Rmax (- (delta / 2)) ((a - c) / 2)) < delta).
  intro; generalize (H9 (Rmax (- (delta / 2)) ((a - c) / 2)) H11 H12); intro;
    cut (a < c + Rmax (- (delta / 2)) ((a - c) / 2)).
  cut (c + Rmax (- (delta / 2)) ((a - c) / 2) < b).
  intros; generalize (H1 (c + Rmax (- (delta / 2)) ((a - c) / 2)) H15 H14);
    intro;
      cut
        (0 <=
          (f (c + Rmax (- (delta / 2)) ((a - c) / 2)) - f c) /
          Rmax (- (delta / 2)) ((a - c) / 2)).
  intro; cut (0 < - l).
  intro; unfold Rminus in H13;
    cut
      (0 <
        (f (c + Rmax (- (delta / 2)) ((a + - c) / 2)) + - f c) /
        Rmax (- (delta / 2)) ((a + - c) / 2) + - l).
  intro;
    cut
      (Rabs
        ((f (c + Rmax (- (delta / 2)) ((a + - c) / 2)) + - f c) /
          Rmax (- (delta / 2)) ((a + - c) / 2) + - l) <
        - (l / 2)).
  unfold Rabs in |- *;
    case
    (Rcase_abs
      ((f (c + Rmax (- (delta / 2)) ((a + - c) / 2)) + - f c) /
        Rmax (- (delta / 2)) ((a + - c) / 2) + - l)).
  intro;
    elim
      (Rlt_irrefl 0
        (Rlt_trans 0
          ((f (c + Rmax (- (delta / 2)) ((a + - c) / 2)) + - f c) /
            Rmax (- (delta / 2)) ((a + - c) / 2) + - l) 0 H19 r)).
  intros;
    generalize
      (Rplus_lt_compat_r l
        ((f (c + Rmax (- (delta / 2)) ((a + - c) / 2)) + - f c) /
          Rmax (- (delta / 2)) ((a + - c) / 2) + - l) (
            - (l / 2)) H20); repeat rewrite Rplus_assoc; rewrite Rplus_opp_l;
      rewrite Rplus_0_r; replace (- (l / 2) + l) with (l / 2).
  cut (l / 2 < 0).
  intros;
    generalize
      (Rlt_trans
        ((f (c + Rmax (- (delta / 2)) ((a + - c) / 2)) + - f c) /
          Rmax (- (delta / 2)) ((a + - c) / 2)) (l / 2) 0 H22 H21);
      intro;
        elim
          (Rlt_irrefl 0
            (Rle_lt_trans 0
              ((f (c + Rmax (- (delta / 2)) ((a - c) / 2)) - f c) /
                Rmax (- (delta / 2)) ((a - c) / 2)) 0 H17 H23)).
  rewrite <- (Ropp_involutive (l / 2)); rewrite <- Ropp_0;
    apply Ropp_lt_gt_contravar; assumption.
  pattern l at 3 in |- *; rewrite double_var.
  ring.
  assumption.
  apply Rplus_le_lt_0_compat; assumption.
  rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; assumption.
  unfold Rdiv in |- *;
    replace
    ((f (c + Rmax (- (delta * / 2)) ((a - c) * / 2)) - f c) *
      / Rmax (- (delta * / 2)) ((a - c) * / 2)) with
    (- (f (c + Rmax (- (delta * / 2)) ((a - c) * / 2)) - f c) *
      / - Rmax (- (delta * / 2)) ((a - c) * / 2)).
  apply Rmult_le_pos.
  generalize
    (Rplus_le_compat_l (- f (c + Rmax (- (delta * / 2)) ((a - c) * / 2)))
      (f (c + Rmax (- (delta * / 2)) ((a - c) * / 2))) (
        f c) H16); rewrite Rplus_opp_l;
    replace (- (f (c + Rmax (- (delta * / 2)) ((a - c) * / 2)) - f c)) with
    (- f (c + Rmax (- (delta * / 2)) ((a - c) * / 2)) + f c).
  intro; assumption.
  ring.
  left; apply Rinv_0_lt_compat; rewrite <- Ropp_0; apply Ropp_lt_gt_contravar;
    assumption.
  unfold Rdiv in |- *.
  rewrite <- Ropp_inv_permute.
  rewrite Rmult_opp_opp.
  reflexivity.
  unfold Rdiv in H11; assumption.
  generalize (Rplus_lt_compat_l c (Rmax (- (delta / 2)) ((a - c) / 2)) 0 H10);
    rewrite Rplus_0_r; intro; apply Rlt_trans with c;
      assumption.
  generalize (RmaxLess2 (- (delta / 2)) ((a - c) / 2)); intro;
    generalize
      (Rplus_le_compat_l c ((a - c) / 2) (Rmax (- (delta / 2)) ((a - c) / 2)) H14);
      intro; apply Rlt_le_trans with (c + (a - c) / 2).
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  replace (2 * (c + (a - c) / 2)) with (a + c).
  rewrite double.
  apply Rplus_lt_compat_l; assumption.
  field; discrR.
  assumption.
  unfold Rabs in |- *; case (Rcase_abs (Rmax (- (delta / 2)) ((a - c) / 2))).
  intro; generalize (RmaxLess1 (- (delta / 2)) ((a - c) / 2)); intro;
    generalize
      (Ropp_le_ge_contravar (- (delta / 2)) (Rmax (- (delta / 2)) ((a - c) / 2))
        H12); rewrite Ropp_involutive; intro;
      generalize (Rge_le (delta / 2) (- Rmax (- (delta / 2)) ((a - c) / 2)) H13);
        intro; apply Rle_lt_trans with (delta / 2).
  assumption.
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
    rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; rewrite double.
  pattern delta at 2 in |- *; rewrite <- (Rplus_0_r delta);
    apply Rplus_lt_compat_l; rewrite Rplus_0_r; apply (cond_pos delta).
  discrR.
  cut (- (delta / 2) < 0).
  cut ((a - c) / 2 < 0).
  intros;
    generalize
      (Rmax_stable_in_negreal (mknegreal (- (delta / 2)) H13)
        (mknegreal ((a - c) / 2) H12)); simpl in |- *;
      intro; generalize (Rge_le (Rmax (- (delta / 2)) ((a - c) / 2)) 0 r);
        intro;
          elim
            (Rlt_irrefl 0
              (Rle_lt_trans 0 (Rmax (- (delta / 2)) ((a - c) / 2)) 0 H15 H14)).
  rewrite <- Ropp_0; rewrite <- (Ropp_involutive ((a - c) / 2));
    apply Ropp_lt_gt_contravar; replace (- ((a - c) / 2)) with ((c - a) / 2).
  assumption.
  unfold Rdiv in |- *.
  rewrite <- Ropp_mult_distr_l_reverse.
  rewrite (Ropp_minus_distr a c).
  reflexivity.
  rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; unfold Rdiv in |- *;
    apply Rmult_lt_0_compat;
      [ apply (cond_pos delta)
        | assert (Hyp : 0 < 2); [ prove_sup0 | apply (Rinv_0_lt_compat 2 Hyp) ] ].
  red in |- *; intro; rewrite H11 in H10; elim (Rlt_irrefl 0 H10).
  cut ((a - c) / 2 < 0).
  intro; cut (- (delta / 2) < 0).
  intro;
    apply
      (Rmax_stable_in_negreal (mknegreal (- (delta / 2)) H11)
        (mknegreal ((a - c) / 2) H10)).
  rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; unfold Rdiv in |- *;
    apply Rmult_lt_0_compat;
      [ apply (cond_pos delta)
        | assert (Hyp : 0 < 2); [ prove_sup0 | apply (Rinv_0_lt_compat 2 Hyp) ] ].
  rewrite <- Ropp_0; rewrite <- (Ropp_involutive ((a - c) / 2));
    apply Ropp_lt_gt_contravar; replace (- ((a - c) / 2)) with ((c - a) / 2).
  assumption.
  unfold Rdiv in |- *.
  rewrite <- Ropp_mult_distr_l_reverse.
  rewrite (Ropp_minus_distr a c).
  reflexivity.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ generalize (Rplus_lt_compat_r (- a) a c H); rewrite Rplus_opp_r; intro;
      assumption
      | assert (Hyp : 0 < 2); [ prove_sup0 | apply (Rinv_0_lt_compat 2 Hyp) ] ].
  replace (- (l / 2)) with (- l / 2).
  unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; assumption.
  assert (Hyp : 0 < 2); [ prove_sup0 | apply (Rinv_0_lt_compat 2 Hyp) ].
  unfold Rdiv in |- *; apply Ropp_mult_distr_l_reverse.
Qed.

Theorem deriv_minimum :
  forall f (a b c:R) (pr:derivable_pt f c),
    a < c ->
    c < b ->
    (forall x:R, a < x -> x < b -> f c <= f x) -> derive_pt f c pr = 0.
Proof.
  intros.
  rewrite <- (Ropp_involutive (derive_pt f c pr)).
  apply Ropp_eq_0_compat.
  rewrite <- (derive_pt_opp f c pr).
  cut (forall x:R, a < x -> x < b -> (- f)%F x <= (- f)%F c).
  intro.
  apply (deriv_maximum (- f)%F a b c (derivable_pt_opp _ _ pr) H H0 H2).
  intros; unfold opp_fct in |- *; apply Ropp_ge_le_contravar; apply Rle_ge.
  apply (H1 x H2 H3).
Qed.

Theorem deriv_constant2 :
  forall f (a b c:R) (pr:derivable_pt f c),
    a < c ->
    c < b -> (forall x:R, a < x -> x < b -> f x = f c) -> derive_pt f c pr = 0.
Proof.
  intros.
  eapply deriv_maximum with a b; try assumption.
  intros; right; apply (H1 x H2 H3).
Qed.

(**********)
Lemma nonneg_derivative_0 :
  forall f (pr:derivable f),
    increasing f -> forall x:R, 0 <= derive_pt f x (pr x).
Proof.
  intros; unfold increasing in H.
  assert (H0 := derivable_derive f x (pr x)).
  elim H0; intros l H1.
  rewrite H1; case (Rtotal_order 0 l); intro.
  left; assumption.
  elim H2; intro.
  right; assumption.
  assert (H4 := derive_pt_eq_1 f x l (pr x) H1).
  cut (0 < - (l / 2)).
  intro; elim (H4 (- (l / 2)) H5); intros delta H6.
  cut (delta / 2 <> 0 /\ 0 < delta / 2 /\ Rabs (delta / 2) < delta).
  intro; decompose [and] H7; intros; generalize (H6 (delta / 2) H8 H11);
    cut (0 <= (f (x + delta / 2) - f x) / (delta / 2)).
  intro; cut (0 <= (f (x + delta / 2) - f x) / (delta / 2) - l).
  intro; unfold Rabs in |- *;
    case (Rcase_abs ((f (x + delta / 2) - f x) / (delta / 2) - l)).
  intro;
    elim
      (Rlt_irrefl 0
        (Rle_lt_trans 0 ((f (x + delta / 2) - f x) / (delta / 2) - l) 0 H12 r)).
  intros;
    generalize
      (Rplus_lt_compat_r l ((f (x + delta / 2) - f x) / (delta / 2) - l)
        (- (l / 2)) H13); unfold Rminus in |- *;
      replace (- (l / 2) + l) with (l / 2).
  rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r; intro;
    generalize
      (Rle_lt_trans 0 ((f (x + delta / 2) - f x) / (delta / 2)) (l / 2) H9 H14);
      intro; cut (l / 2 < 0).
  intro; elim (Rlt_irrefl 0 (Rlt_trans 0 (l / 2) 0 H15 H16)).
  rewrite <- Ropp_0 in H5;
    generalize (Ropp_lt_gt_contravar (-0) (- (l / 2)) H5);
      repeat rewrite Ropp_involutive; intro; assumption.
  pattern l at 3 in |- *; rewrite double_var.
  ring.
  unfold Rminus in |- *; apply Rplus_le_le_0_compat.
  unfold Rdiv in |- *; apply Rmult_le_pos.
  cut (x <= x + delta * / 2).
  intro; generalize (H x (x + delta * / 2) H12); intro;
    generalize (Rplus_le_compat_l (- f x) (f x) (f (x + delta * / 2)) H13);
      rewrite Rplus_opp_l; rewrite Rplus_comm; intro; assumption.
  pattern x at 1 in |- *; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
    left; assumption.
  left; apply Rinv_0_lt_compat; assumption.
  left; rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; assumption.
  unfold Rdiv in |- *; apply Rmult_le_pos.
  cut (x <= x + delta * / 2).
  intro; generalize (H x (x + delta * / 2) H9); intro;
    generalize (Rplus_le_compat_l (- f x) (f x) (f (x + delta * / 2)) H12);
      rewrite Rplus_opp_l; rewrite Rplus_comm; intro; assumption.
  pattern x at 1 in |- *; rewrite <- (Rplus_0_r x); apply Rplus_le_compat_l;
    left; assumption.
  left; apply Rinv_0_lt_compat; assumption.
  split.
  unfold Rdiv in |- *; apply prod_neq_R0.
  generalize (cond_pos delta); intro; red in |- *; intro H9; rewrite H9 in H7;
    elim (Rlt_irrefl 0 H7).
  apply Rinv_neq_0_compat; discrR.
  split.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply (cond_pos delta) | apply Rinv_0_lt_compat; prove_sup0 ].
  replace (Rabs (delta / 2)) with (delta / 2).
  unfold Rdiv in |- *; apply Rmult_lt_reg_l with 2.
  prove_sup0.
  rewrite (Rmult_comm 2).
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym; [ idtac | discrR ].
  rewrite Rmult_1_r.
  rewrite double.
  pattern (pos delta) at 1 in |- *; rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l; apply (cond_pos delta).
  symmetry  in |- *; apply Rabs_right.
  left; change (0 < delta / 2) in |- *; unfold Rdiv in |- *;
    apply Rmult_lt_0_compat;
      [ apply (cond_pos delta) | apply Rinv_0_lt_compat; prove_sup0 ].
  unfold Rdiv in |- *; rewrite <- Ropp_mult_distr_l_reverse;
    apply Rmult_lt_0_compat.
  apply Rplus_lt_reg_r with l.
  unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rplus_0_r; assumption.
  apply Rinv_0_lt_compat; prove_sup0.
Qed.

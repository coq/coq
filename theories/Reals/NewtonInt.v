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
Require Import Rtrigo1.
Require Import Ranalysis.
Local Open Scope R_scope.

(*******************************************)
(*            Newton's Integral            *)
(*******************************************)

Definition Newton_integrable (f:R -> R) (a b:R) : Type :=
  { g:R -> R | antiderivative f g a b \/ antiderivative f g b a }.

Definition NewtonInt (f:R -> R) (a b:R) (pr:Newton_integrable f a b) : R :=
  let (g,_) := pr in g b - g a.

(* If f is differentiable, then f' is Newton integrable (Tautology ?) *)
Lemma FTCN_step1 :
  forall (f:Differential) (a b:R),
    Newton_integrable (fun x:R => derive_pt f x (cond_diff f x)) a b.
Proof.
  intros f a b; unfold Newton_integrable; exists (d1 f);
    unfold antiderivative; intros; case (Rle_dec a b);
      intro;
        [ left; split; [ intros; exists (cond_diff f x); reflexivity | assumption ]
          | right; split;
            [ intros; exists (cond_diff f x); reflexivity | auto with real ] ].
Defined.

(* By definition, we have the Fondamental Theorem of Calculus *)
Lemma FTC_Newton :
  forall (f:Differential) (a b:R),
    NewtonInt (fun x:R => derive_pt f x (cond_diff f x)) a b
    (FTCN_step1 f a b) = f b - f a.
Proof.
  intros; unfold NewtonInt; reflexivity.
Qed.

(* $\int_a^a f$ exists forall a:R and f:R->R *)
Lemma NewtonInt_P1 : forall (f:R -> R) (a:R), Newton_integrable f a a.
Proof.
  intros f a; unfold Newton_integrable;
    exists (fct_cte (f a) * id)%F; left;
      unfold antiderivative; split.
  intros; assert (H1 : derivable_pt (fct_cte (f a) * id) x).
  apply derivable_pt_mult.
  apply derivable_pt_const.
  apply derivable_pt_id.
  exists H1; assert (H2 : x = a).
  elim H; intros; apply Rle_antisym; assumption.
  symmetry ; apply derive_pt_eq_0;
    replace (f x) with (0 * id x + fct_cte (f a) x * 1);
    [ apply (derivable_pt_lim_mult (fct_cte (f a)) id x);
      [ apply derivable_pt_lim_const | apply derivable_pt_lim_id ]
      | unfold id, fct_cte; rewrite H2; ring ].
  right; reflexivity.
Qed.

(* $\int_a^a f = 0$ *)
Lemma NewtonInt_P2 :
  forall (f:R -> R) (a:R), NewtonInt f a a (NewtonInt_P1 f a) = 0.
Proof.
  intros; unfold NewtonInt; simpl;
    unfold mult_fct, fct_cte, id.
  destruct NewtonInt_P1 as [g _].
  now apply Rminus_diag_eq.
Qed.

(* If $\int_a^b f$ exists, then $\int_b^a f$ exists too *)
Lemma NewtonInt_P3 :
  forall (f:R -> R) (a b:R) (X:Newton_integrable f a b),
    Newton_integrable f b a.
Proof.
  unfold Newton_integrable; intros; elim X; intros g H;
    exists g; tauto.
Defined.

(* $\int_a^b f = -\int_b^a f$ *)
Lemma NewtonInt_P4 :
  forall (f:R -> R) (a b:R) (pr:Newton_integrable f a b),
    NewtonInt f a b pr = - NewtonInt f b a (NewtonInt_P3 f a b pr).
Proof.
  intros f a b (x,H). unfold NewtonInt, NewtonInt_P3; simpl; ring.
Qed.

(* The set of Newton integrable functions is a vectorial space *)
Lemma NewtonInt_P5 :
  forall (f g:R -> R) (l a b:R),
    Newton_integrable f a b ->
    Newton_integrable g a b ->
    Newton_integrable (fun x:R => l * f x + g x) a b.
Proof.
  unfold Newton_integrable; intros f g l a b X X0;
    elim X; intros x p; elim X0; intros x0 p0;
      exists (fun y:R => l * x y + x0 y).
  elim p; intro.
  elim p0; intro.
  left; unfold antiderivative; unfold antiderivative in H, H0; elim H;
    clear H; intros; elim H0; clear H0; intros H0 _.
  split.
  intros; elim (H _ H2); elim (H0 _ H2); intros.
  assert (H5 : derivable_pt (fun y:R => l * x y + x0 y) x1).
  reg.
  exists H5; symmetry ; reg; rewrite <- H3; rewrite <- H4; reflexivity.
  assumption.
  unfold antiderivative in H, H0; elim H; elim H0; intros; elim H4; intro.
  elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H5 H2)).
  left; rewrite <- H5; unfold antiderivative; split.
  intros; elim H6; intros; assert (H9 : x1 = a).
  apply Rle_antisym; assumption.
  assert (H10 : a <= x1 <= b).
  split; right; [ symmetry ; assumption | rewrite <- H5; assumption ].
  assert (H11 : b <= x1 <= a).
  split; right; [ rewrite <- H5; symmetry ; assumption | assumption ].
  assert (H12 : derivable_pt x x1).
  unfold derivable_pt; exists (f x1); elim (H3 _ H10); intros;
    eapply derive_pt_eq_1; symmetry ; apply H12.
  assert (H13 : derivable_pt x0 x1).
  unfold derivable_pt; exists (g x1); elim (H1 _ H11); intros;
    eapply derive_pt_eq_1; symmetry ; apply H13.
  assert (H14 : derivable_pt (fun y:R => l * x y + x0 y) x1).
  reg.
  exists H14; symmetry ; reg.
  assert (H15 : derive_pt x0 x1 H13 = g x1).
  elim (H1 _ H11); intros; rewrite H15; apply pr_nu.
  assert (H16 : derive_pt x x1 H12 = f x1).
  elim (H3 _ H10); intros; rewrite H16; apply pr_nu.
  rewrite H15; rewrite H16; ring.
  right; reflexivity.
  elim p0; intro.
  unfold antiderivative in H, H0; elim H; elim H0; intros; elim H4; intro.
  elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H5 H2)).
  left; rewrite H5; unfold antiderivative; split.
  intros; elim H6; intros; assert (H9 : x1 = a).
  apply Rle_antisym; assumption.
  assert (H10 : a <= x1 <= b).
  split; right; [ symmetry ; assumption | rewrite H5; assumption ].
  assert (H11 : b <= x1 <= a).
  split; right; [ rewrite H5; symmetry ; assumption | assumption ].
  assert (H12 : derivable_pt x x1).
  unfold derivable_pt; exists (f x1); elim (H3 _ H11); intros;
    eapply derive_pt_eq_1; symmetry ; apply H12.
  assert (H13 : derivable_pt x0 x1).
  unfold derivable_pt; exists (g x1); elim (H1 _ H10); intros;
    eapply derive_pt_eq_1; symmetry ; apply H13.
  assert (H14 : derivable_pt (fun y:R => l * x y + x0 y) x1).
  reg.
  exists H14; symmetry ; reg.
  assert (H15 : derive_pt x0 x1 H13 = g x1).
  elim (H1 _ H10); intros; rewrite H15; apply pr_nu.
  assert (H16 : derive_pt x x1 H12 = f x1).
  elim (H3 _ H11); intros; rewrite H16; apply pr_nu.
  rewrite H15; rewrite H16; ring.
  right; reflexivity.
  right; unfold antiderivative; unfold antiderivative in H, H0; elim H;
    clear H; intros; elim H0; clear H0; intros H0 _; split.
  intros; elim (H _ H2); elim (H0 _ H2); intros.
  assert (H5 : derivable_pt (fun y:R => l * x y + x0 y) x1).
  reg.
  exists H5; symmetry ; reg; rewrite <- H3; rewrite <- H4; reflexivity.
  assumption.
Defined.

(**********)
Lemma antiderivative_P1 :
  forall (f g F G:R -> R) (l a b:R),
    antiderivative f F a b ->
    antiderivative g G a b ->
    antiderivative (fun x:R => l * f x + g x) (fun x:R => l * F x + G x) a b.
Proof.
  unfold antiderivative; intros; elim H; elim H0; clear H H0; intros;
    split.
  intros; elim (H _ H3); elim (H1 _ H3); intros.
  assert (H6 : derivable_pt (fun x:R => l * F x + G x) x).
  reg.
  exists H6; symmetry ; reg; rewrite <- H4; rewrite <- H5; ring.
  assumption.
Qed.

(* $\int_a^b \lambda f + g = \lambda \int_a^b f + \int_a^b f *)
Lemma NewtonInt_P6 :
  forall (f g:R -> R) (l a b:R) (pr1:Newton_integrable f a b)
    (pr2:Newton_integrable g a b),
    NewtonInt (fun x:R => l * f x + g x) a b (NewtonInt_P5 f g l a b pr1 pr2) =
    l * NewtonInt f a b pr1 + NewtonInt g a b pr2.
Proof.
  intros f g l a b pr1 pr2; unfold NewtonInt;
    destruct (NewtonInt_P5 f g l a b pr1 pr2) as (x,o); destruct pr1 as (x0,o0);
      destruct pr2 as (x1,o1); destruct (total_order_T a b) as [[Hlt|Heq]|Hgt].
  elim o; intro.
  elim o0; intro.
  elim o1; intro.
  assert (H2 := antiderivative_P1 f g x0 x1 l a b H0 H1);
    assert (H3 := antiderivative_Ucte _ _ _ _ _ H H2);
      elim H3; intros; assert (H5 : a <= a <= b).
  split; [ right; reflexivity | left; assumption ].
  assert (H6 : a <= b <= b).
  split; [ left; assumption | right; reflexivity ].
  assert (H7 := H4 _ H5); assert (H8 := H4 _ H6); rewrite H7; rewrite H8; ring.
  unfold antiderivative in H1; elim H1; intros;
    elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H3 Hlt)).
  unfold antiderivative in H0; elim H0; intros;
    elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H2 Hlt)).
  unfold antiderivative in H; elim H; intros;
    elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H1 Hlt)).
  rewrite Heq; ring.
  elim o; intro.
  unfold antiderivative in H; elim H; intros;
    elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H1 Hgt)).
  elim o0; intro.
  unfold antiderivative in H0; elim H0; intros;
    elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H2 Hgt)).
  elim o1; intro.
  unfold antiderivative in H1; elim H1; intros;
    elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H3 Hgt)).
  assert (H2 := antiderivative_P1 f g x0 x1 l b a H0 H1);
    assert (H3 := antiderivative_Ucte _ _ _ _ _ H H2);
      elim H3; intros; assert (H5 : b <= a <= a).
  split; [ left; assumption | right; reflexivity ].
  assert (H6 : b <= b <= a).
  split; [ right; reflexivity | left; assumption ].
  assert (H7 := H4 _ H5); assert (H8 := H4 _ H6); rewrite H7; rewrite H8; ring.
Qed.

Lemma antiderivative_P2 :
  forall (f F0 F1:R -> R) (a b c:R),
    antiderivative f F0 a b ->
    antiderivative f F1 b c ->
    antiderivative f
    (fun x:R =>
      match Rle_dec x b with
        | left _ => F0 x
        | right _ => F1 x + (F0 b - F1 b)
      end) a c.
Proof.
  intros; destruct H as (H,H1), H0 as (H0,H2); split.
  2: apply Rle_trans with b; assumption.
  intros x (H3,H4); destruct (total_order_T x b) as [[Hlt|Heq]|Hgt].
  assert (H5 : a <= x <= b).
  split; [ assumption | left; assumption ].
  destruct (H _ H5) as (x0,H6).
    assert
      (H7 :
        derivable_pt_lim
        (fun x:R =>
          match Rle_dec x b with
            | left _ => F0 x
            | right _ => F1 x + (F0 b - F1 b)
          end) x (f x)).
  unfold derivable_pt_lim. intros eps H9.
  assert (H7 : derive_pt F0 x x0 = f x) by (symmetry; assumption).
  destruct (derive_pt_eq_1 F0 x (f x) x0 H7 _ H9) as (x1,H10); set (D := Rmin x1 (b - x)).
  assert (H11 : 0 < D).
  unfold D, Rmin; case (Rle_dec x1 (b - x)); intro.
  apply (cond_pos x1).
  apply Rlt_Rminus; assumption.
  exists (mkposreal _ H11); intros h H12 H13. case (Rle_dec x b) as [|[]].
  case (Rle_dec (x + h) b) as [|[]].
  apply H10.
  assumption.
  apply Rlt_le_trans with D; [ assumption | unfold D; apply Rmin_l ].
  left; apply Rlt_le_trans with (x + D).
  apply Rplus_lt_compat_l; apply Rle_lt_trans with (Rabs h).
  apply RRle_abs.
  apply H13.
  apply Rplus_le_reg_l with (- x); rewrite <- Rplus_assoc; rewrite Rplus_opp_l;
    rewrite Rplus_0_l; rewrite Rplus_comm; unfold D;
      apply Rmin_r.
  left; assumption.
  assert
    (H8 :
      derivable_pt
      (fun x:R =>
        match Rle_dec x b with
          | left _ => F0 x
          | right _ => F1 x + (F0 b - F1 b)
        end) x).
  unfold derivable_pt; exists (f x); apply H7.
  exists H8; symmetry ; apply derive_pt_eq_0; apply H7.
  assert (H5 : a <= x <= b).
  split; [ assumption | right; assumption ].
  assert (H6 : b <= x <= c).
  split; [ right; symmetry ; assumption | assumption ].
  elim (H _ H5); elim (H0 _ H6); intros; assert (H9 : derive_pt F0 x x1 = f x).
  symmetry ; assumption.
  assert (H10 : derive_pt F1 x x0 = f x).
  symmetry ; assumption.
  assert (H11 := derive_pt_eq_1 F0 x (f x) x1 H9);
    assert (H12 := derive_pt_eq_1 F1 x (f x) x0 H10);
      assert
        (H13 :
          derivable_pt_lim
          (fun x:R =>
            match Rle_dec x b with
              | left _ => F0 x
              | right _ => F1 x + (F0 b - F1 b)
            end) x (f x)).
  unfold derivable_pt_lim; unfold derivable_pt_lim in H11, H12; intros;
    elim (H11 _ H13); elim (H12 _ H13); intros; set (D := Rmin x2 x3);
      assert (H16 : 0 < D).
  unfold D; unfold Rmin; case (Rle_dec x2 x3); intro.
  apply (cond_pos x2).
  apply (cond_pos x3).
  exists (mkposreal _ H16); intros; case (Rle_dec x b) as [|[]].
  case (Rle_dec (x + h) b); intro.
  apply H15.
  assumption.
  apply Rlt_le_trans with D; [ assumption | unfold D; apply Rmin_r ].
  replace (F1 (x + h) + (F0 b - F1 b) - F0 x) with (F1 (x + h) - F1 x).
  apply H14.
  assumption.
  apply Rlt_le_trans with D; [ assumption | unfold D; apply Rmin_l ].
  rewrite Heq; ring.
  right; assumption.
  assert
    (H14 :
      derivable_pt
      (fun x:R =>
        match Rle_dec x b with
          | left _ => F0 x
          | right _ => F1 x + (F0 b - F1 b)
        end) x).
  unfold derivable_pt; exists (f x); apply H13.
  exists H14; symmetry ; apply derive_pt_eq_0; apply H13.
  assert (H5 : b <= x <= c).
  split; [ left; assumption | assumption ].
  assert (H6 := H0 _ H5); elim H6; clear H6; intros;
    assert
      (H7 :
        derivable_pt_lim
        (fun x:R =>
          match Rle_dec x b with
            | left _ => F0 x
            | right _ => F1 x + (F0 b - F1 b)
          end) x (f x)).
  unfold derivable_pt_lim; assert (H7 : derive_pt F1 x x0 = f x).
  symmetry ; assumption.
  assert (H8 := derive_pt_eq_1 F1 x (f x) x0 H7); unfold derivable_pt_lim in H8;
    intros; elim (H8 _ H9); intros; set (D := Rmin x1 (x - b));
      assert (H11 : 0 < D).
  unfold D; unfold Rmin; case (Rle_dec x1 (x - b)); intro.
  apply (cond_pos x1).
  apply Rlt_Rminus; assumption.
  exists (mkposreal _ H11); intros; destruct (Rle_dec x b) as [Hle|Hnle].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle Hgt)).
  destruct (Rle_dec (x + h) b) as [Hle'|Hnle'].
  cut (b < x + h).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle' H14)).
  apply Rplus_lt_reg_l with (- h - b); replace (- h - b + b) with (- h);
    [ idtac | ring ]; replace (- h - b + (x + h)) with (x - b);
    [ idtac | ring ]; apply Rle_lt_trans with (Rabs h).
  rewrite <- Rabs_Ropp; apply RRle_abs.
  apply Rlt_le_trans with D.
  apply H13.
  unfold D; apply Rmin_r.
  replace (F1 (x + h) + (F0 b - F1 b) - (F1 x + (F0 b - F1 b))) with
  (F1 (x + h) - F1 x); [ idtac | ring ]; apply H10.
  assumption.
  apply Rlt_le_trans with D.
  assumption.
  unfold D; apply Rmin_l.
  assert
    (H8 :
      derivable_pt
      (fun x:R =>
        match Rle_dec x b with
          | left _ => F0 x
          | right _ => F1 x + (F0 b - F1 b)
        end) x).
  unfold derivable_pt; exists (f x); apply H7.
  exists H8; symmetry ; apply derive_pt_eq_0; apply H7.
Qed.

Lemma antiderivative_P3 :
  forall (f F0 F1:R -> R) (a b c:R),
    antiderivative f F0 a b ->
    antiderivative f F1 c b ->
    antiderivative f F1 c a \/ antiderivative f F0 a c.
Proof.
  intros; unfold antiderivative in H, H0; elim H; clear H; elim H0; clear H0;
    intros; destruct (total_order_T a c) as [[Hle|Heq]|Hgt].
  right; unfold antiderivative; split.
  intros; apply H1; elim H3; intros; split;
    [ assumption | apply Rle_trans with c; assumption ].
  left; assumption.
  right; unfold antiderivative; split.
  intros; apply H1; elim H3; intros; split;
    [ assumption | apply Rle_trans with c; assumption ].
  right; assumption.
  left; unfold antiderivative; split.
  intros; apply H; elim H3; intros; split;
    [ assumption | apply Rle_trans with a; assumption ].
  left; assumption.
Qed.

Lemma antiderivative_P4 :
  forall (f F0 F1:R -> R) (a b c:R),
    antiderivative f F0 a b ->
    antiderivative f F1 a c ->
    antiderivative f F1 b c \/ antiderivative f F0 c b.
Proof.
  intros; unfold antiderivative in H, H0; elim H; clear H; elim H0; clear H0;
    intros; destruct (total_order_T c b) as [[Hlt|Heq]|Hgt].
  right; unfold antiderivative; split.
  intros; apply H1; elim H3; intros; split;
    [ apply Rle_trans with c; assumption | assumption ].
  left; assumption.
  right; unfold antiderivative; split.
  intros; apply H1; elim H3; intros; split;
    [ apply Rle_trans with c; assumption | assumption ].
  right; assumption.
  left; unfold antiderivative; split.
  intros; apply H; elim H3; intros; split;
    [ apply Rle_trans with b; assumption | assumption ].
  left; assumption.
Qed.

Lemma NewtonInt_P7 :
  forall (f:R -> R) (a b c:R),
    a < b ->
    b < c ->
    Newton_integrable f a b ->
    Newton_integrable f b c -> Newton_integrable f a c.
Proof.
  unfold Newton_integrable; intros f a b c Hab Hbc X X0; elim X;
    clear X; intros F0 H0; elim X0; clear X0; intros F1 H1;
      set
        (g :=
          fun x:R =>
            match Rle_dec x b with
              | left _ => F0 x
              | right _ => F1 x + (F0 b - F1 b)
            end); exists g; left; unfold g;
        apply antiderivative_P2.
  elim H0; intro.
  assumption.
  unfold antiderivative in H; elim H; clear H; intros;
    elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H2 Hab)).
  elim H1; intro.
  assumption.
  unfold antiderivative in H; elim H; clear H; intros;
    elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H2 Hbc)).
Qed.

Lemma NewtonInt_P8 :
  forall (f:R -> R) (a b c:R),
    Newton_integrable f a b ->
    Newton_integrable f b c -> Newton_integrable f a c.
Proof.
  intros.
  elim X; intros F0 H0.
  elim X0; intros F1 H1.
  destruct (total_order_T a b) as [[Hlt|Heq]|Hgt].
  destruct (total_order_T b c) as [[Hlt'|Heq']|Hgt'].
(* a<b & b<c *)
  unfold Newton_integrable;
    exists
      (fun x:R =>
        match Rle_dec x b with
          | left _ => F0 x
          | right _ => F1 x + (F0 b - F1 b)
        end).
  elim H0; intro.
  elim H1; intro.
  left; apply antiderivative_P2; assumption.
  unfold antiderivative in H2; elim H2; clear H2; intros _ H2.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H2 Hlt')).
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hlt)).
(* a<b & b=c *)
  rewrite Heq' in X; apply X.
(* a<b & b>c *)
  destruct (total_order_T a c) as [[Hlt''|Heq'']|Hgt''].
  unfold Newton_integrable; exists F0.
  left.
  elim H1; intro.
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hgt')).
  elim H0; intro.
  assert (H3 := antiderivative_P3 f F0 F1 a b c H2 H).
  elim H3; intro.
  unfold antiderivative in H4; elim H4; clear H4; intros _ H4.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H4 Hlt'')).
  assumption.
  unfold antiderivative in H2; elim H2; clear H2; intros _ H2.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H2 Hlt)).
  rewrite Heq''; apply NewtonInt_P1.
  unfold Newton_integrable; exists F1.
  right.
  elim H1; intro.
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hgt')).
  elim H0; intro.
  assert (H3 := antiderivative_P3 f F0 F1 a b c H2 H).
  elim H3; intro.
  assumption.
  unfold antiderivative in H4; elim H4; clear H4; intros _ H4.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H4 Hgt'')).
  unfold antiderivative in H2; elim H2; clear H2; intros _ H2.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H2 Hlt)).
(* a=b *)
  rewrite Heq; apply X0.
  destruct (total_order_T b c) as [[Hlt'|Heq']|Hgt'].
(* a>b & b<c *)
  destruct (total_order_T a c) as [[Hlt''|Heq'']|Hgt''].
  unfold Newton_integrable; exists F1.
  left.
  elim H1; intro.
(*****************)
  elim H0; intro.
  unfold antiderivative in H2; elim H2; clear H2; intros _ H2.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H2 Hgt)).
  assert (H3 := antiderivative_P4 f F0 F1 b a c H2 H).
  elim H3; intro.
  assumption.
  unfold antiderivative in H4; elim H4; clear H4; intros _ H4.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H4 Hlt'')).
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hlt')).
  rewrite Heq''; apply NewtonInt_P1.
  unfold Newton_integrable; exists F0.
  right.
  elim H0; intro.
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hgt)).
  elim H1; intro.
  assert (H3 := antiderivative_P4 f F0 F1 b a c H H2).
  elim H3; intro.
  unfold antiderivative in H4; elim H4; clear H4; intros _ H4.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H4 Hgt'')).
  assumption.
  unfold antiderivative in H2; elim H2; clear H2; intros _ H2.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H2 Hlt')).
(* a>b & b=c *)
  rewrite Heq' in X; apply X.
(* a>b & b>c *)
  assert (X1 := NewtonInt_P3 f a b X).
  assert (X2 := NewtonInt_P3 f b c X0).
  apply NewtonInt_P3.
  apply NewtonInt_P7 with b; assumption.
Qed.

(* Chasles' relation *)
Lemma NewtonInt_P9 :
  forall (f:R -> R) (a b c:R) (pr1:Newton_integrable f a b)
    (pr2:Newton_integrable f b c),
    NewtonInt f a c (NewtonInt_P8 f a b c pr1 pr2) =
    NewtonInt f a b pr1 + NewtonInt f b c pr2.
Proof.
  intros; unfold NewtonInt.
  case (NewtonInt_P8 f a b c pr1 pr2) as (x,Hor).
  case pr1 as (x0,Hor0).
  case pr2 as (x1,Hor1).
  destruct (total_order_T a b) as [[Hlt|Heq]|Hgt].
  destruct (total_order_T b c) as [[Hlt'|Heq']|Hgt'].
(* a<b & b<c *)
  case Hor0; intro.
  case Hor1; intro.
  case Hor; intro.
  assert (H2 := antiderivative_P2 f x0 x1 a b c H H0).
  assert
    (H3 :=
      antiderivative_Ucte f x
      (fun x:R =>
        match Rle_dec x b with
          | left _ => x0 x
          | right _ => x1 x + (x0 b - x1 b)
        end) a c H1 H2).
  elim H3; intros.
  assert (H5 : a <= a <= c).
  split; [ right; reflexivity | left; apply Rlt_trans with b; assumption ].
  assert (H6 : a <= c <= c).
  split; [ left; apply Rlt_trans with b; assumption | right; reflexivity ].
  rewrite (H4 _ H5); rewrite (H4 _ H6).
  destruct (Rle_dec a b) as [Hlea|Hnlea].
  destruct (Rle_dec c b) as [Hlec|Hnlec].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hlec Hlt')).
  ring.
  elim Hnlea; left; assumption.
  unfold antiderivative in H1; elim H1; clear H1; intros _ H1.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H1 (Rlt_trans _ _ _ Hlt Hlt'))).
  unfold antiderivative in H0; elim H0; clear H0; intros _ H0.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H0 Hlt')).
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hlt)).
(* a<b & b=c *)
  rewrite <- Heq'.
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rplus_0_r.
  rewrite <- Heq' in Hor.
  elim Hor0; intro.
  elim Hor; intro.
  assert (H1 := antiderivative_Ucte f x x0 a b H0 H).
  elim H1; intros.
  rewrite (H2 b).
  rewrite (H2 a).
  ring.
  split; [ right; reflexivity | left; assumption ].
  split; [ left; assumption | right; reflexivity ].
  unfold antiderivative in H0; elim H0; clear H0; intros _ H0.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H0 Hlt)).
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hlt)).
(* a<b & b>c *)
  elim Hor1; intro.
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hgt')).
  elim Hor0; intro.
  elim Hor; intro.
  assert (H2 := antiderivative_P2 f x x1 a c b H1 H).
  assert (H3 := antiderivative_Ucte _ _ _ a b H0 H2).
  elim H3; intros.
  rewrite (H4 a).
  rewrite (H4 b).
  destruct (Rle_dec b c) as [Hle|Hnle].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle Hgt')).
  destruct (Rle_dec a c) as [Hle'|Hnle'].
  ring.
  elim Hnle'; unfold antiderivative in H1; elim H1; intros; assumption.
  split; [ left; assumption | right; reflexivity ].
  split; [ right; reflexivity | left; assumption ].
  assert (H2 := antiderivative_P2 _ _ _ _ _ _ H1 H0).
  assert (H3 := antiderivative_Ucte _ _ _ c b H H2).
  elim H3; intros.
  rewrite (H4 c).
  rewrite (H4 b).
  destruct (Rle_dec b a) as [Hle|Hnle].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle Hlt)).
  destruct (Rle_dec c a) as [Hle'|[]].
  ring.
  unfold antiderivative in H1; elim H1; intros; assumption.
  split; [ left; assumption | right; reflexivity ].
  split; [ right; reflexivity | left; assumption ].
  unfold antiderivative in H0; elim H0; clear H0; intros _ H0.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H0 Hlt)).
(* a=b *)
  rewrite Heq in Hor |- *.
  elim Hor; intro.
  elim Hor1; intro.
  assert (H1 := antiderivative_Ucte _ _ _ b c H H0).
  elim H1; intros.
  assert (H3 : b <= c).
  unfold antiderivative in H; elim H; intros; assumption.
  rewrite (H2 b).
  rewrite (H2 c).
  ring.
  split; [ assumption | right; reflexivity ].
  split; [ right; reflexivity | assumption ].
  assert (H1 : b = c).
  unfold antiderivative in H, H0; elim H; elim H0; intros; apply Rle_antisym;
    assumption.
  rewrite H1; ring.
  elim Hor1; intro.
  assert (H1 : b = c).
  unfold antiderivative in H, H0; elim H; elim H0; intros; apply Rle_antisym;
    assumption.
  rewrite H1; ring.
  assert (H1 := antiderivative_Ucte _ _ _ c b H H0).
  elim H1; intros.
  assert (H3 : c <= b).
  unfold antiderivative in H; elim H; intros; assumption.
  rewrite (H2 c).
  rewrite (H2 b).
  ring.
  split; [ assumption | right; reflexivity ].
  split; [ right; reflexivity | assumption ].
(* a>b & b<c *)
  destruct (total_order_T b c) as [[Hlt'|Heq']|Hgt'].
  elim Hor0; intro.
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hgt)).
  elim Hor1; intro.
  elim Hor; intro.
  assert (H2 := antiderivative_P2 _ _ _ _ _ _ H H1).
  assert (H3 := antiderivative_Ucte _ _ _ b c H0 H2).
  elim H3; intros.
  rewrite (H4 b).
  rewrite (H4 c).
  case (Rle_dec b a) as [|[]].
  case (Rle_dec c a) as [|].
  assert (H5 : a = c).
  unfold antiderivative in H1; elim H1; intros; apply Rle_antisym; assumption.
  rewrite H5; ring.
  ring.
  left; assumption.
  split; [ left; assumption | right; reflexivity ].
  split; [ right; reflexivity | left; assumption ].
  assert (H2 := antiderivative_P2 _ _ _ _ _ _ H0 H1).
  assert (H3 := antiderivative_Ucte _ _ _ b a H H2).
  elim H3; intros.
  rewrite (H4 a).
  rewrite (H4 b).
  case (Rle_dec b c) as [|[]].
  case (Rle_dec a c) as [|].
  assert (H5 : a = c).
  unfold antiderivative in H1; elim H1; intros; apply Rle_antisym; assumption.
  rewrite H5; ring.
  ring.
  left; assumption.
  split; [ right; reflexivity | left; assumption ].
  split; [ left; assumption | right; reflexivity ].
  unfold antiderivative in H0; elim H0; clear H0; intros _ H0.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H0 Hlt')).
(* a>b & b=c *)
  rewrite <- Heq'.
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rplus_0_r.
  rewrite <- Heq' in Hor.
  elim Hor0; intro.
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hgt)).
  elim Hor; intro.
  unfold antiderivative in H0; elim H0; clear H0; intros _ H0.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H0 Hgt)).
  assert (H1 := antiderivative_Ucte f x x0 b a H0 H).
  elim H1; intros.
  rewrite (H2 b).
  rewrite (H2 a).
  ring.
  split; [ left; assumption | right; reflexivity ].
  split; [ right; reflexivity | left; assumption ].
(* a>b & b>c *)
  elim Hor0; intro.
  unfold antiderivative in H; elim H; clear H; intros _ H.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H Hgt)).
  elim Hor1; intro.
  unfold antiderivative in H0; elim H0; clear H0; intros _ H0.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H0 Hgt')).
  elim Hor; intro.
  unfold antiderivative in H1; elim H1; clear H1; intros _ H1.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H1 (Rlt_trans _ _ _ Hgt' Hgt))).
  assert (H2 := antiderivative_P2 _ _ _ _ _ _ H0 H).
  assert (H3 := antiderivative_Ucte _ _ _ c a H1 H2).
  elim H3; intros.
  assert (H5 : c <= a).
  unfold antiderivative in H1; elim H1; intros; assumption.
  rewrite (H4 c).
  rewrite (H4 a).
  destruct (Rle_dec a b) as [Hle|Hnle].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle Hgt)).
  destruct (Rle_dec c b) as [|[]].
  ring.
  left; assumption.
  split; [ assumption | right; reflexivity ].
  split; [ right; reflexivity | assumption ].
Qed.

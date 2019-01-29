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
Require Import Ranalysis1.
Require Import RList.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.
Local Open Scope R_scope.

(** * General definitions and propositions *)

Definition included (D1 D2:R -> Prop) : Prop := forall x:R, D1 x -> D2 x.
Definition disc (x:R) (delta:posreal) (y:R) : Prop := Rabs (y - x) < delta.
Definition neighbourhood (V:R -> Prop) (x:R) : Prop :=
  exists delta : posreal, included (disc x delta) V.
Definition open_set (D:R -> Prop) : Prop :=
  forall x:R, D x -> neighbourhood D x.
Definition complementary (D:R -> Prop) (c:R) : Prop := ~ D c.
Definition closed_set (D:R -> Prop) : Prop := open_set (complementary D).
Definition intersection_domain (D1 D2:R -> Prop) (c:R) : Prop := D1 c /\ D2 c.
Definition union_domain (D1 D2:R -> Prop) (c:R) : Prop := D1 c \/ D2 c.
Definition interior (D:R -> Prop) (x:R) : Prop := neighbourhood D x.

Lemma interior_P1 : forall D:R -> Prop, included (interior D) D.
Proof.
  intros; unfold included; unfold interior; intros;
    unfold neighbourhood in H; elim H; intros; unfold included in H0;
      apply H0; unfold disc; unfold Rminus;
        rewrite Rplus_opp_r; rewrite Rabs_R0; apply (cond_pos x0).
Qed.

Lemma interior_P2 : forall D:R -> Prop, open_set D -> included D (interior D).
Proof.
  intros; unfold open_set in H; unfold included; intros;
    assert (H1 := H _ H0); unfold interior; apply H1.
Qed.

Definition point_adherent (D:R -> Prop) (x:R) : Prop :=
  forall V:R -> Prop,
    neighbourhood V x ->  exists y : R, intersection_domain V D y.
Definition adherence (D:R -> Prop) (x:R) : Prop := point_adherent D x.

Lemma adherence_P1 : forall D:R -> Prop, included D (adherence D).
Proof.
  intro; unfold included; intros; unfold adherence;
    unfold point_adherent; intros; exists x;
      unfold intersection_domain; split.
  unfold neighbourhood in H0; elim H0; intros; unfold included in H1; apply H1;
    unfold disc; unfold Rminus; rewrite Rplus_opp_r;
      rewrite Rabs_R0; apply (cond_pos x0).
  apply H.
Qed.

Lemma included_trans :
  forall D1 D2 D3:R -> Prop,
    included D1 D2 -> included D2 D3 -> included D1 D3.
Proof.
  unfold included; intros; apply H0; apply H; apply H1.
Qed.

Lemma interior_P3 : forall D:R -> Prop, open_set (interior D).
Proof.
  intro; unfold open_set, interior; unfold neighbourhood;
    intros; elim H; intros.
  exists x0; unfold included; intros.
  set (del := x0 - Rabs (x - x1)).
  cut (0 < del).
  intro; exists (mkposreal del H2); intros.
  cut (included (disc x1 (mkposreal del H2)) (disc x x0)).
  intro; assert (H5 := included_trans _ _ _ H4 H0).
  apply H5; apply H3.
  unfold included; unfold disc; intros.
  apply Rle_lt_trans with (Rabs (x3 - x1) + Rabs (x1 - x)).
  replace (x3 - x) with (x3 - x1 + (x1 - x)); [ apply Rabs_triang | ring ].
  replace (pos x0) with (del + Rabs (x1 - x)).
  do 2 rewrite <- (Rplus_comm (Rabs (x1 - x))); apply Rplus_lt_compat_l;
    apply H4.
  unfold del; rewrite <- (Rabs_Ropp (x - x1)); rewrite Ropp_minus_distr;
    ring.
  unfold del; apply Rplus_lt_reg_l with (Rabs (x - x1));
    rewrite Rplus_0_r;
      replace (Rabs (x - x1) + (x0 - Rabs (x - x1))) with (pos x0);
      [ idtac | ring ].
  unfold disc in H1; rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H1.
Qed.

Lemma complementary_P1 :
  forall D:R -> Prop,
    ~ (exists y : R, intersection_domain D (complementary D) y).
Proof.
  intro; red; intro; elim H; intros;
    unfold intersection_domain, complementary in H0; elim H0;
      intros; elim H2; assumption.
Qed.

Lemma adherence_P2 :
  forall D:R -> Prop, closed_set D -> included (adherence D) D.
Proof.
  unfold closed_set; unfold open_set, complementary; intros;
    unfold included, adherence; intros; assert (H1 := classic (D x));
      elim H1; intro.
  assumption.
  assert (H3 := H _ H2); assert (H4 := H0 _ H3); elim H4; intros;
    unfold intersection_domain in H5; elim H5; intros;
      elim H6; assumption.
Qed.

Lemma adherence_P3 : forall D:R -> Prop, closed_set (adherence D).
Proof.
  intro; unfold closed_set, adherence;
    unfold open_set, complementary, point_adherent;
      intros;
        set
          (P :=
            fun V:R -> Prop =>
              neighbourhood V x ->  exists y : R, intersection_domain V D y);
          assert (H0 := not_all_ex_not _ P H); elim H0; intros V0 H1;
            unfold P in H1; assert (H2 := imply_to_and _ _ H1);
              unfold neighbourhood; elim H2; intros; unfold neighbourhood in H3;
                elim H3; intros; exists x0; unfold included;
                  intros; red; intro.
  assert (H8 := H7 V0);
    cut (exists delta : posreal, (forall x:R, disc x1 delta x -> V0 x)).
  intro; assert (H10 := H8 H9); elim H4; assumption.
  cut (0 < x0 - Rabs (x - x1)).
  intro; set (del := mkposreal _ H9); exists del; intros;
    unfold included in H5; apply H5; unfold disc;
      apply Rle_lt_trans with (Rabs (x2 - x1) + Rabs (x1 - x)).
  replace (x2 - x) with (x2 - x1 + (x1 - x)); [ apply Rabs_triang | ring ].
  replace (pos x0) with (del + Rabs (x1 - x)).
  do 2 rewrite <- (Rplus_comm (Rabs (x1 - x))); apply Rplus_lt_compat_l;
    apply H10.
  unfold del; simpl; rewrite <- (Rabs_Ropp (x - x1));
    rewrite Ropp_minus_distr; ring.
  apply Rplus_lt_reg_l with (Rabs (x - x1)); rewrite Rplus_0_r;
    replace (Rabs (x - x1) + (x0 - Rabs (x - x1))) with (pos x0);
    [ rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H6 | ring ].
Qed.

Definition eq_Dom (D1 D2:R -> Prop) : Prop :=
  included D1 D2 /\ included D2 D1.

Infix "=_D" := eq_Dom (at level 70, no associativity).

Lemma open_set_P1 : forall D:R -> Prop, open_set D <-> D =_D interior D.
Proof.
  intro; split.
  intro; unfold eq_Dom; split.
  apply interior_P2; assumption.
  apply interior_P1.
  intro; unfold eq_Dom in H; elim H; clear H; intros; unfold open_set;
    intros; unfold included, interior in H; unfold included in H0;
      apply (H _ H1).
Qed.

Lemma closed_set_P1 : forall D:R -> Prop, closed_set D <-> D =_D adherence D.
Proof.
  intro; split.
  intro; unfold eq_Dom; split.
  apply adherence_P1.
  apply adherence_P2; assumption.
  unfold eq_Dom; unfold included; intros;
    assert (H0 := adherence_P3 D); unfold closed_set in H0;
      unfold closed_set; unfold open_set;
        unfold open_set in H0; intros; assert (H2 : complementary (adherence D) x).
  unfold complementary; unfold complementary in H1; red; intro;
    elim H; clear H; intros _ H; elim H1; apply (H _ H2).
  assert (H3 := H0 _ H2); unfold neighbourhood;
    unfold neighbourhood in H3; elim H3; intros; exists x0;
      unfold included; unfold included in H4; intros;
        assert (H6 := H4 _ H5); unfold complementary in H6;
          unfold complementary; red; intro;
            elim H; clear H; intros H _; elim H6; apply (H _ H7).
Qed.

Lemma neighbourhood_P1 :
  forall (D1 D2:R -> Prop) (x:R),
    included D1 D2 -> neighbourhood D1 x -> neighbourhood D2 x.
Proof.
  unfold included, neighbourhood; intros; elim H0; intros; exists x0;
    intros; unfold included; unfold included in H1;
      intros; apply (H _ (H1 _ H2)).
Qed.

Lemma open_set_P2 :
  forall D1 D2:R -> Prop,
    open_set D1 -> open_set D2 -> open_set (union_domain D1 D2).
Proof.
  unfold open_set; intros; unfold union_domain in H1; elim H1; intro.
  apply neighbourhood_P1 with D1.
  unfold included, union_domain; tauto.
  apply H; assumption.
  apply neighbourhood_P1 with D2.
  unfold included, union_domain; tauto.
  apply H0; assumption.
Qed.

Lemma open_set_P3 :
  forall D1 D2:R -> Prop,
    open_set D1 -> open_set D2 -> open_set (intersection_domain D1 D2).
Proof.
  unfold open_set; intros; unfold intersection_domain in H1; elim H1;
    intros.
  assert (H4 := H _ H2); assert (H5 := H0 _ H3);
    unfold intersection_domain; unfold neighbourhood in H4, H5;
      elim H4; clear H; intros del1 H; elim H5; clear H0;
        intros del2 H0; cut (0 < Rmin del1 del2).
  intro; set (del := mkposreal _ H6).
  exists del; unfold included; intros; unfold included in H, H0;
    unfold disc in H, H0, H7.
  split.
  apply H; apply Rlt_le_trans with (pos del).
  apply H7.
  unfold del; simpl; apply Rmin_l.
  apply H0; apply Rlt_le_trans with (pos del).
  apply H7.
  unfold del; simpl; apply Rmin_r.
  unfold Rmin; case (Rle_dec del1 del2); intro.
  apply (cond_pos del1).
  apply (cond_pos del2).
Qed.

Lemma open_set_P4 : open_set (fun x:R => False).
Proof.
  unfold open_set; intros; elim H.
Qed.

Lemma open_set_P5 : open_set (fun x:R => True).
Proof.
  unfold open_set; intros; unfold neighbourhood.
  exists (mkposreal 1 Rlt_0_1); unfold included; intros; trivial.
Qed.

Lemma disc_P1 : forall (x:R) (del:posreal), open_set (disc x del).
Proof.
  intros; assert (H := open_set_P1 (disc x del)).
  elim H; intros; apply H1.
  unfold eq_Dom; split.
  unfold included, interior, disc; intros;
    cut (0 < del - Rabs (x - x0)).
  intro; set (del2 := mkposreal _ H3).
  exists del2; unfold included; intros.
  apply Rle_lt_trans with (Rabs (x1 - x0) + Rabs (x0 - x)).
  replace (x1 - x) with (x1 - x0 + (x0 - x)); [ apply Rabs_triang | ring ].
  replace (pos del) with (del2 + Rabs (x0 - x)).
  do 2 rewrite <- (Rplus_comm (Rabs (x0 - x))); apply Rplus_lt_compat_l.
  apply H4.
  unfold del2; simpl; rewrite <- (Rabs_Ropp (x - x0));
    rewrite Ropp_minus_distr; ring.
  apply Rplus_lt_reg_l with (Rabs (x - x0)); rewrite Rplus_0_r;
    replace (Rabs (x - x0) + (del - Rabs (x - x0))) with (pos del);
    [ rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H2 | ring ].
  apply interior_P1.
Qed.

Lemma continuity_P1 :
  forall (f:R -> R) (x:R),
    continuity_pt f x <->
    (forall W:R -> Prop,
      neighbourhood W (f x) ->
      exists V : R -> Prop,
        neighbourhood V x /\ (forall y:R, V y -> W (f y))).
Proof.
  intros; split.
  intros; unfold neighbourhood in H0.
  elim H0; intros del1 H1.
  unfold continuity_pt in H; unfold continue_in in H; unfold limit1_in in H;
    unfold limit_in in H; simpl in H; unfold R_dist in H.
  assert (H2 := H del1 (cond_pos del1)).
  elim H2; intros del2 H3.
  elim H3; intros.
  exists (disc x (mkposreal del2 H4)).
  intros; unfold included in H1; split.
  unfold neighbourhood, disc.
  exists (mkposreal del2 H4).
  unfold included; intros; assumption.
  intros; apply H1; unfold disc; case (Req_dec y x); intro.
  rewrite H7; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    apply (cond_pos del1).
  apply H5; split.
  unfold D_x, no_cond; split.
  trivial.
  apply (not_eq_sym (A:=R)); apply H7.
  unfold disc in H6; apply H6.
  intros; unfold continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
      intros.
  assert (H1 := H (disc (f x) (mkposreal eps H0))).
  cut (neighbourhood (disc (f x) (mkposreal eps H0)) (f x)).
  intro; assert (H3 := H1 H2).
  elim H3; intros D H4; elim H4; intros; unfold neighbourhood in H5; elim H5;
    intros del1 H7.
  exists (pos del1); split.
  apply (cond_pos del1).
  intros; elim H8; intros; simpl in H10; unfold R_dist in H10; simpl;
    unfold R_dist; apply (H6 _ (H7 _ H10)).
  unfold neighbourhood, disc; exists (mkposreal eps H0);
    unfold included; intros; assumption.
Qed.

Definition image_rec (f:R -> R) (D:R -> Prop) (x:R) : Prop := D (f x).

(**********)
Lemma continuity_P2 :
  forall (f:R -> R) (D:R -> Prop),
    continuity f -> open_set D -> open_set (image_rec f D).
Proof.
  intros; unfold open_set in H0; unfold open_set; intros;
    assert (H2 := continuity_P1 f x); elim H2; intros H3 _;
      assert (H4 := H3 (H x)); unfold neighbourhood, image_rec;
        unfold image_rec in H1; assert (H5 := H4 D (H0 (f x) H1));
          elim H5; intros V0 H6; elim H6; intros; unfold neighbourhood in H7;
            elim H7; intros del H9; exists del; unfold included in H9;
              unfold included; intros; apply (H8 _ (H9 _ H10)).
Qed.

(**********)
Lemma continuity_P3 :
  forall f:R -> R,
    continuity f <->
    (forall D:R -> Prop, open_set D -> open_set (image_rec f D)).
Proof.
  intros; split.
  intros; apply continuity_P2; assumption.
  intros; unfold continuity; unfold continuity_pt;
    unfold continue_in; unfold limit1_in;
      unfold limit_in; simpl; unfold R_dist;
        intros; cut (open_set (disc (f x) (mkposreal _ H0))).
  intro; assert (H2 := H _ H1).
  unfold open_set, image_rec in H2; cut (disc (f x) (mkposreal _ H0) (f x)).
  intro; assert (H4 := H2 _ H3).
  unfold neighbourhood in H4; elim H4; intros del H5.
  exists (pos del); split.
  apply (cond_pos del).
  intros; unfold included in H5; apply H5; elim H6; intros; apply H8.
  unfold disc; unfold Rminus; rewrite Rplus_opp_r;
    rewrite Rabs_R0; apply H0.
  apply disc_P1.
Qed.

(**********)
Theorem Rsepare :
  forall x y:R,
    x <> y ->
    exists V : R -> Prop,
      (exists W : R -> Prop,
        neighbourhood V x /\
        neighbourhood W y /\ ~ (exists y : R, intersection_domain V W y)).
Proof.
  intros x y Hsep; set (D := Rabs (x - y)).
  cut (0 < D / 2).
  intro; exists (disc x (mkposreal _ H)).
  exists (disc y (mkposreal _ H)); split.
  unfold neighbourhood; exists (mkposreal _ H); unfold included;
    tauto.
  split.
  unfold neighbourhood; exists (mkposreal _ H); unfold included;
    tauto.
  red; intro; elim H0; intros; unfold intersection_domain in H1;
    elim H1; intros.
  cut (D < D).
  intro; elim (Rlt_irrefl _ H4).
  change (Rabs (x - y) < D);
    apply Rle_lt_trans with (Rabs (x - x0) + Rabs (x0 - y)).
  replace (x - y) with (x - x0 + (x0 - y)); [ apply Rabs_triang | ring ].
  rewrite (double_var D); apply Rplus_lt_compat.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H2.
  apply H3.
  unfold Rdiv; apply Rmult_lt_0_compat.
  unfold D; apply Rabs_pos_lt; apply (Rminus_eq_contra _ _ Hsep).
  apply Rinv_0_lt_compat; prove_sup0.
Qed.

Record family : Type := mkfamily
  {ind : R -> Prop;
    f :> R -> R -> Prop;
    cond_fam : forall x:R, (exists y : R, f x y) -> ind x}.

Definition family_open_set (f:family) : Prop := forall x:R, open_set (f x).

Definition domain_finite (D:R -> Prop) : Prop :=
  exists l : Rlist, (forall x:R, D x <-> In x l).

Definition family_finite (f:family) : Prop := domain_finite (ind f).

Definition covering (D:R -> Prop) (f:family) : Prop :=
  forall x:R, D x ->  exists y : R, f y x.

Definition covering_open_set (D:R -> Prop) (f:family) : Prop :=
  covering D f /\ family_open_set f.

Definition covering_finite (D:R -> Prop) (f:family) : Prop :=
  covering D f /\ family_finite f.

Lemma restriction_family :
  forall (f:family) (D:R -> Prop) (x:R),
    (exists y : R, (fun z1 z2:R => f z1 z2 /\ D z1) x y) ->
    intersection_domain (ind f) D x.
Proof.
  intros; elim H; intros; unfold intersection_domain; elim H0; intros;
    split.
  apply (cond_fam f0); exists x0; assumption.
  assumption.
Qed.

Definition subfamily (f:family) (D:R -> Prop) : family :=
  mkfamily (intersection_domain (ind f) D) (fun x y:R => f x y /\ D x)
  (restriction_family f D).

Definition compact (X:R -> Prop) : Prop :=
  forall f:family,
    covering_open_set X f ->
    exists D : R -> Prop, covering_finite X (subfamily f D).

(**********)
Lemma family_P1 :
  forall (f:family) (D:R -> Prop),
    family_open_set f -> family_open_set (subfamily f D).
Proof.
  unfold family_open_set; intros; unfold subfamily;
    simpl; assert (H0 := classic (D x)).
  elim H0; intro.
  cut (open_set (f0 x) -> open_set (fun y:R => f0 x y /\ D x)).
  intro; apply H2; apply H.
  unfold open_set; unfold neighbourhood; intros; elim H3;
    intros; assert (H6 := H2 _ H4); elim H6; intros; exists x1;
      unfold included; intros; split.
  apply (H7 _ H8).
  assumption.
  cut (open_set (fun y:R => False) -> open_set (fun y:R => f0 x y /\ D x)).
  intro; apply H2; apply open_set_P4.
  unfold open_set; unfold neighbourhood; intros; elim H3;
    intros; elim H1; assumption.
Qed.

Definition bounded (D:R -> Prop) : Prop :=
  exists m : R, (exists M : R, (forall x:R, D x -> m <= x <= M)).

Lemma open_set_P6 :
  forall D1 D2:R -> Prop, open_set D1 -> D1 =_D D2 -> open_set D2.
Proof.
  unfold open_set; unfold neighbourhood; intros.
  unfold eq_Dom in H0; elim H0; intros.
  assert (H4 := H _ (H3 _ H1)).
  elim H4; intros.
  exists x0; apply included_trans with D1; assumption.
Qed.

(**********)
Lemma compact_P1 : forall X:R -> Prop, compact X -> bounded X.
Proof.
  intros; unfold compact in H; set (D := fun x:R => True);
    set (g := fun x y:R => Rabs y < x);
      cut (forall x:R, (exists y : _, g x y) -> True);
        [ intro | intro; trivial ].
  set (f0 := mkfamily D g H0); assert (H1 := H f0);
    cut (covering_open_set X f0).
  intro; assert (H3 := H1 H2); elim H3; intros D' H4;
    unfold covering_finite in H4; elim H4; intros; unfold family_finite in H6;
      unfold domain_finite in H6; elim H6; intros l H7;
        unfold bounded; set (r := MaxRlist l).
  exists (- r); exists r; intros.
  unfold covering in H5; assert (H9 := H5 _ H8); elim H9; intros;
    unfold subfamily in H10; simpl in H10; elim H10; intros;
      assert (H13 := H7 x0); simpl in H13; cut (intersection_domain D D' x0).
  elim H13; clear H13; intros.
  assert (H16 := H13 H15); unfold g in H11; split.
  cut (x0 <= r).
  intro; cut (Rabs x < r).
  intro; assert (H19 := Rabs_def2 x r H18); elim H19; intros; left; assumption.
  apply Rlt_le_trans with x0; assumption.
  apply (MaxRlist_P1 l x0 H16).
  cut (x0 <= r).
  intro; apply Rle_trans with (Rabs x).
  apply RRle_abs.
  apply Rle_trans with x0.
  left; apply H11.
  assumption.
  apply (MaxRlist_P1 l x0 H16).
  unfold intersection_domain, D; tauto.
  unfold covering_open_set; split.
  unfold covering; intros; simpl; exists (Rabs x + 1);
    unfold g; pattern (Rabs x) at 1; rewrite <- Rplus_0_r;
      apply Rplus_lt_compat_l; apply Rlt_0_1.
  unfold family_open_set; intro; case (Rtotal_order 0 x); intro.
  apply open_set_P6 with (disc 0 (mkposreal _ H2)).
  apply disc_P1.
  unfold eq_Dom; unfold f0; simpl;
    unfold g, disc; split.
  unfold included; intros; unfold Rminus in H3; rewrite Ropp_0 in H3;
    rewrite Rplus_0_r in H3; apply H3.
  unfold included; intros; unfold Rminus; rewrite Ropp_0;
    rewrite Rplus_0_r; apply H3.
  apply open_set_P6 with (fun x:R => False).
  apply open_set_P4.
  unfold eq_Dom; split.
  unfold included; intros; elim H3.
  unfold included, f0; simpl; unfold g; intros; elim H2;
    intro;
      [ rewrite <- H4 in H3; assert (H5 := Rabs_pos x0);
        elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H5 H3))
        | assert (H6 := Rabs_pos x0); assert (H7 := Rlt_trans _ _ _ H3 H4);
          elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H6 H7)) ].
Qed.

(**********)
Lemma compact_P2 : forall X:R -> Prop, compact X -> closed_set X.
Proof.
  intros; assert (H0 := closed_set_P1 X); elim H0; clear H0; intros _ H0;
    apply H0; clear H0.
  unfold eq_Dom; split.
  apply adherence_P1.
  unfold included; unfold adherence;
    unfold point_adherent; intros; unfold compact in H;
      assert (H1 := classic (X x)); elim H1; clear H1; intro.
  assumption.
  cut (forall y:R, X y -> 0 < Rabs (y - x) / 2).
  intro; set (D := X);
    set (g := fun y z:R => Rabs (y - z) < Rabs (y - x) / 2 /\ D y);
      cut (forall x:R, (exists y : _, g x y) -> D x).
  intro; set (f0 := mkfamily D g H3); assert (H4 := H f0);
    cut (covering_open_set X f0).
  intro; assert (H6 := H4 H5); elim H6; clear H6; intros D' H6.
  unfold covering_finite in H6; decompose [and] H6;
    unfold covering, subfamily in H7; simpl in H7;
      unfold family_finite, subfamily in H8; simpl in H8;
        unfold domain_finite in H8; elim H8; clear H8; intros l H8;
          set (alp := MinRlist (AbsList l x)); cut (0 < alp).
  intro; assert (H10 := H0 (disc x (mkposreal _ H9)));
    cut (neighbourhood (disc x (mkposreal alp H9)) x).
  intro; assert (H12 := H10 H11); elim H12; clear H12; intros y H12;
    unfold intersection_domain in H12; elim H12; clear H12;
      intros; assert (H14 := H7 _ H13); elim H14; clear H14;
        intros y0 H14; elim H14; clear H14; intros; unfold g in H14;
          elim H14; clear H14; intros; unfold disc in H12; simpl in H12;
            cut (alp <= Rabs (y0 - x) / 2).
  intro; assert (H18 := Rlt_le_trans _ _ _ H12 H17);
    cut (Rabs (y0 - x) < Rabs (y0 - x)).
  intro; elim (Rlt_irrefl _ H19).
  apply Rle_lt_trans with (Rabs (y0 - y) + Rabs (y - x)).
  replace (y0 - x) with (y0 - y + (y - x)); [ apply Rabs_triang | ring ].
  rewrite (double_var (Rabs (y0 - x))); apply Rplus_lt_compat; assumption.
  apply (MinRlist_P1 (AbsList l x) (Rabs (y0 - x) / 2)); apply AbsList_P1;
    elim (H8 y0); clear H8; intros; apply H8; unfold intersection_domain;
      split; assumption.
  assert (H11 := disc_P1 x (mkposreal alp H9)); unfold open_set in H11;
    apply H11.
  unfold disc; unfold Rminus; rewrite Rplus_opp_r;
    rewrite Rabs_R0; apply H9.
  unfold alp; apply MinRlist_P2; intros;
    assert (H10 := AbsList_P2 _ _ _ H9); elim H10; clear H10;
      intros z H10; elim H10; clear H10; intros; rewrite H11;
        apply H2; elim (H8 z); clear H8; intros; assert (H13 := H12 H10);
          unfold intersection_domain, D in H13; elim H13; clear H13;
            intros; assumption.
  unfold covering_open_set; split.
  unfold covering; intros; exists x0; simpl; unfold g;
    split.
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    unfold Rminus in H2; apply (H2 _ H5).
  apply H5.
  unfold family_open_set; intro; simpl; unfold g;
    elim (classic (D x0)); intro.
  apply open_set_P6 with (disc x0 (mkposreal _ (H2 _ H5))).
  apply disc_P1.
  unfold eq_Dom; split.
  unfold included, disc; simpl; intros; split.
  rewrite <- (Rabs_Ropp (x0 - x1)); rewrite Ropp_minus_distr; apply H6.
  apply H5.
  unfold included, disc; simpl; intros; elim H6; intros;
    rewrite <- (Rabs_Ropp (x1 - x0)); rewrite Ropp_minus_distr;
      apply H7.
  apply open_set_P6 with (fun z:R => False).
  apply open_set_P4.
  unfold eq_Dom; split.
  unfold included; intros; elim H6.
  unfold included; intros; elim H6; intros; elim H5; assumption.
  intros; elim H3; intros; unfold g in H4; elim H4; clear H4; intros _ H4;
    apply H4.
  intros; unfold Rdiv; apply Rmult_lt_0_compat.
  apply Rabs_pos_lt; apply Rminus_eq_contra; red; intro;
    rewrite H3 in H2; elim H1; apply H2.
  apply Rinv_0_lt_compat; prove_sup0.
Qed.

(**********)
Lemma compact_EMP : compact (fun _:R => False).
Proof.
  unfold compact; intros; exists (fun x:R => False);
    unfold covering_finite; split.
  unfold covering; intros; elim H0.
  unfold family_finite; unfold domain_finite; exists nil; intro.
  split.
  simpl; unfold intersection_domain; intros; elim H0.
  elim H0; clear H0; intros _ H0; elim H0.
  simpl; intro; elim H0.
Qed.

Lemma compact_eqDom :
  forall X1 X2:R -> Prop, compact X1 -> X1 =_D X2 -> compact X2.
Proof.
  unfold compact; intros; unfold eq_Dom in H0; elim H0; clear H0;
    unfold included; intros; assert (H3 : covering_open_set X1 f0).
  unfold covering_open_set; unfold covering_open_set in H1; elim H1;
    clear H1; intros; split.
  unfold covering in H1; unfold covering; intros;
    apply (H1 _ (H0 _ H4)).
  apply H3.
  elim (H _ H3); intros D H4; exists D; unfold covering_finite;
    unfold covering_finite in H4; elim H4; intros; split.
  unfold covering in H5; unfold covering; intros;
    apply (H5 _ (H2 _ H7)).
  apply H6.
Qed.

(** Borel-Lebesgue's lemma *)
Lemma compact_P3 : forall a b:R, compact (fun c:R => a <= c <= b).
Proof.
  intros a b; destruct (Rle_dec a b) as [Hle|Hnle].
  unfold compact; intros f0 (H,H5);
    set
      (A :=
        fun x:R =>
          a <= x <= b /\
          (exists D : R -> Prop,
            covering_finite (fun c:R => a <= c <= x) (subfamily f0 D))).
  cut (A a); [intro H0|].
  cut (bound A); [intro H1|].
  cut (exists a0 : R, A a0); [intro H2|].
  pose proof (completeness A H1 H2) as (m,H3); unfold is_lub in H3.
  cut (a <= m <= b); [intro H4|].
  unfold covering in H; pose proof (H m H4) as (y0,H6).
  unfold family_open_set in H5; pose proof (H5 y0 m H6) as (eps,H8).
  cut (exists x : R, A x /\ m - eps < x <= m);
    [intros (x,((H9 & Dx & H12 & H13),(Hltx,_)))|].
  destruct (Req_dec m b) as [->|H11].
  set (Db := fun x:R => Dx x \/ x = y0); exists Db;
    unfold covering_finite; split.
      unfold covering; intros x0 (H14,H18);
      unfold covering in H12; destruct (Rle_dec x0 x) as [Hle'|Hnle'].
  cut (a <= x0 <= x); [intro H15|].
  pose proof (H12 x0 H15) as (x1 & H16 & H17); exists x1;
    simpl; unfold Db; split; [ apply H16 | left; apply H17 ].
  split; assumption.
  exists y0; simpl; split.
  apply H8; unfold disc;
    rewrite <- Rabs_Ropp, Ropp_minus_distr, Rabs_right.
  apply Rlt_trans with (b - x).
  unfold Rminus; apply Rplus_lt_compat_l, Ropp_lt_gt_contravar;
    auto with real.
  apply Rplus_lt_reg_l with (x - eps);
    replace (x - eps + (b - x)) with (b - eps);
    [ replace (x - eps + eps) with x; [ apply Hltx | ring ] | ring ].
  apply Rge_minus, Rle_ge, H18.
  unfold Db; right; reflexivity.
  unfold family_finite, domain_finite.
      intros; unfold family_finite in H13; unfold domain_finite in H13;
        destruct H13 as (l,H13); exists (cons y0 l);
          intro; split.
  intro H14; simpl in H14; unfold intersection_domain in H14;
    specialize H13 with x0; destruct H13 as (H13,H15);
    destruct (Req_dec x0 y0) as [H16|H16].
  simpl; left; apply H16.
  simpl; right; apply H13.
  simpl; unfold intersection_domain; unfold Db in H14;
    decompose [and or] H14.
  split; assumption.
  elim H16; assumption.
  intro H14; simpl in H14; destruct H14 as [H15|H15]; simpl;
    unfold intersection_domain.
  split.
  apply (cond_fam f0); rewrite H15; exists b; apply H6.
  unfold Db; right; assumption.
  simpl; unfold intersection_domain; elim (H13 x0).
  intros _ H16; assert (H17 := H16 H15); simpl in H17;
    unfold intersection_domain in H17; split.
  elim H17; intros; assumption.
  unfold Db; left; elim H17; intros; assumption.
  set (m' := Rmin (m + eps / 2) b).
  cut (A m'); [intro H7|].
    destruct H3 as (H14,H15); unfold is_upper_bound in H14.
    assert (H16 := H14 m' H7).
      cut (m < m'); [intro H17|].
        elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H16 H17))...
      unfold m', Rmin; destruct (Rle_dec (m + eps / 2) b) as [Hle'|Hnle'].
        pattern m at 1; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l;
          unfold Rdiv; apply Rmult_lt_0_compat;
          [ apply (cond_pos eps) | apply Rinv_0_lt_compat; prove_sup0 ].
        destruct H4 as (_,[]).
          assumption.
          elim H11; assumption.
  unfold A; split.
  split.
  apply Rle_trans with m.
  elim H4; intros; assumption.
  unfold m'; unfold Rmin; case (Rle_dec (m + eps / 2) b); intro.
  pattern m at 1; rewrite <- Rplus_0_r; apply Rplus_le_compat_l; left;
    unfold Rdiv; apply Rmult_lt_0_compat;
      [ apply (cond_pos eps) | apply Rinv_0_lt_compat; prove_sup0 ].
  destruct H4.
  assumption.
  unfold m'; apply Rmin_r.
  set (Db := fun x:R => Dx x \/ x = y0); exists Db;
    unfold covering_finite; split.
      unfold covering; intros x0 (H14,H18);
      unfold covering in H12; destruct (Rle_dec x0 x) as [Hle'|Hnle'].
  cut (a <= x0 <= x); [intro H15|].
  pose proof (H12 x0 H15) as (x1 & H16 & H17); exists x1;
    simpl; unfold Db; split; [ apply H16 | left; apply H17 ].
  split; assumption.
  exists y0; simpl; split.
  apply H8; unfold disc, Rabs; destruct (Rcase_abs (x0 - m)) as [Hlt|Hge].
  rewrite Ropp_minus_distr; apply Rlt_trans with (m - x).
  unfold Rminus; apply Rplus_lt_compat_l; apply Ropp_lt_gt_contravar;
    auto with real.
  apply Rplus_lt_reg_l with (x - eps);
    replace (x - eps + (m - x)) with (m - eps).
  replace (x - eps + eps) with x.
  assumption.
  ring.
  ring.
  apply Rle_lt_trans with (m' - m).
  unfold Rminus; do 2 rewrite <- (Rplus_comm (- m));
    apply Rplus_le_compat_l; elim H14; intros; assumption.
  apply Rplus_lt_reg_l with m; replace (m + (m' - m)) with m'.
  apply Rle_lt_trans with (m + eps / 2).
  unfold m'; apply Rmin_l.
  apply Rplus_lt_compat_l; apply Rmult_lt_reg_l with 2.
  prove_sup0.
  unfold Rdiv; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
    rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; pattern (pos eps) at 1; rewrite <- Rplus_0_r;
    rewrite double; apply Rplus_lt_compat_l; apply (cond_pos eps).
  discrR.
  ring.
  unfold Db; right; reflexivity.
  unfold family_finite, domain_finite;
    unfold family_finite, domain_finite in H13;
    destruct H13 as (l,H13); exists (cons y0 l);
          intro; split.
  intro H14; simpl in H14; unfold intersection_domain in H14;
    specialize (H13 x0); destruct H13 as (H13,H15);
    destruct (Req_dec x0 y0) as [Heq|Hneq].
  simpl; left; apply Heq.
  simpl; right; apply H13; simpl;
    unfold intersection_domain; unfold Db in H14;
      decompose [and or] H14.
  split; assumption.
  elim Hneq; assumption.
  intros [H15|H15]. split.
  apply (cond_fam f0); rewrite H15; exists m; apply H6.
  unfold Db; right; assumption.
  elim (H13 x0); intros _ H16.
  assert (H17 := H16 H15).
  simpl in H17.
  unfold intersection_domain in H17.
  split.
  elim H17; intros; assumption.
  unfold Db; left; elim H17; intros; assumption.
  elim (classic (exists x : R, A x /\ m - eps < x <= m)); intro H9.
  assumption.
  elim H3; intros H10 H11; cut (is_upper_bound A (m - eps)).
  intro H12; assert (H13 := H11 _ H12); cut (m - eps < m).
  intro H14; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H13 H14)).
  pattern m at 2; rewrite <- Rplus_0_r; unfold Rminus;
    apply Rplus_lt_compat_l; apply Ropp_lt_cancel; rewrite Ropp_involutive;
      rewrite Ropp_0; apply (cond_pos eps).
  set (P := fun n:R => A n /\ m - eps < n <= m);
    assert (H12 := not_ex_all_not _ P H9); unfold P in H12;
      unfold is_upper_bound; intros x H13;
        assert (H14 := not_and_or _ _ (H12 x)); elim H14;
          intro H15.
  elim H15; apply H13.
  destruct (not_and_or _ _ H15) as [H16|H16].
  destruct (Rle_dec x (m - eps)) as [H17|H17].
  assumption.
  elim H16; auto with real.
  unfold is_upper_bound in H10; assert (H17 := H10 x H13); elim H16; apply H17.
  elim H3; clear H3; intros.
  unfold is_upper_bound in H3.
  split.
  apply (H3 _ H0).
  clear H5.
  apply (H4 b); unfold is_upper_bound; intros x H5; unfold A in H5; elim H5;
    clear H5; intros H5 _; elim H5; clear H5; intros _ H5;
      apply H5.
  exists a; apply H0.
  unfold bound; exists b; unfold is_upper_bound; intros;
    unfold A in H1; elim H1; clear H1; intros H1 _; elim H1;
      clear H1; intros _ H1; apply H1.
  unfold A; split.
  split; [ right; reflexivity | apply Hle ].
  unfold covering in H; cut (a <= a <= b).
  intro H1; elim (H _ H1); intros y0 H2; set (D' := fun x:R => x = y0); exists D';
    unfold covering_finite; split.
  unfold covering; simpl; intros x H3; cut (x = a).
  intro H4; exists y0; split.
  rewrite H4; apply H2.
  unfold D'; reflexivity.
  elim H3; intros; apply Rle_antisym; assumption.
  unfold family_finite; unfold domain_finite;
    exists (cons y0 nil); intro; split.
  simpl; unfold intersection_domain; intros (H3,H4).
    unfold D' in H4; left; apply H4.
  simpl; unfold intersection_domain; intros [H4|[]].
  split; [ rewrite H4; apply (cond_fam f0); exists a; apply H2 | apply H4 ].
  split; [ right; reflexivity | apply Hle ].
  apply compact_eqDom with (fun c:R => False).
  apply compact_EMP.
  unfold eq_Dom; split.
  unfold included; intros; elim H.
  unfold included; intros; elim H; clear H; intros;
    assert (H1 := Rle_trans _ _ _ H H0); elim Hnle; apply H1.
Qed.

Lemma compact_P4 :
  forall X F:R -> Prop, compact X -> closed_set F -> included F X -> compact F.
Proof.
  unfold compact; intros; elim (classic (exists z : R, F z));
    intro Hyp_F_NE.
  set (D := ind f0); set (g := f f0); unfold closed_set in H0.
  set (g' := fun x y:R => f0 x y \/ complementary F y /\ D x).
  set (D' := D).
  cut (forall x:R, (exists y : R, g' x y) -> D' x).
  intro; set (f' := mkfamily D' g' H3); cut (covering_open_set X f').
  intro; elim (H _ H4); intros DX H5; exists DX.
  unfold covering_finite; unfold covering_finite in H5; elim H5;
    clear H5; intros.
  split.
  unfold covering; unfold covering in H5; intros.
  elim (H5 _ (H1 _ H7)); intros y0 H8; exists y0; simpl in H8; simpl;
    elim H8; clear H8; intros.
  split.
  unfold g' in H8; elim H8; intro.
  apply H10.
  elim H10; intros H11 _; unfold complementary in H11; elim H11; apply H7.
  apply H9.
  unfold family_finite; unfold domain_finite;
    unfold family_finite in H6; unfold domain_finite in H6;
      elim H6; clear H6; intros l H6; exists l; intro; assert (H7 := H6 x);
        elim H7; clear H7; intros.
  split.
  intro; apply H7; simpl; unfold intersection_domain;
    simpl in H9; unfold intersection_domain in H9; unfold D';
      apply H9.
  intro; assert (H10 := H8 H9); simpl in H10; unfold intersection_domain in H10;
    simpl; unfold intersection_domain;
      unfold D' in H10; apply H10.
  unfold covering_open_set; unfold covering_open_set in H2; elim H2;
    clear H2; intros.
  split.
  unfold covering; unfold covering in H2; intros.
  elim (classic (F x)); intro.
  elim (H2 _ H6); intros y0 H7; exists y0; simpl; unfold g';
    left; assumption.
  cut (exists z : R, D z).
  intro; elim H7; clear H7; intros x0 H7; exists x0; simpl;
    unfold g'; right.
  split.
  unfold complementary; apply H6.
  apply H7.
  elim Hyp_F_NE; intros z0 H7.
  assert (H8 := H2 _ H7).
  elim H8; clear H8; intros t H8; exists t; apply (cond_fam f0); exists z0;
    apply H8.
  unfold family_open_set; intro; simpl; unfold g';
    elim (classic (D x)); intro.
  apply open_set_P6 with (union_domain (f0 x) (complementary F)).
  apply open_set_P2.
  unfold family_open_set in H4; apply H4.
  apply H0.
  unfold eq_Dom; split.
  unfold included, union_domain, complementary; intros.
  elim H6; intro; [ left; apply H7 | right; split; assumption ].
  unfold included, union_domain, complementary; intros.
  elim H6; intro; [ left; apply H7 | right; elim H7; intros; apply H8 ].
  apply open_set_P6 with (f0 x).
  unfold family_open_set in H4; apply H4.
  unfold eq_Dom; split.
  unfold included, complementary; intros; left; apply H6.
  unfold included, complementary; intros.
  elim H6; intro.
  apply H7.
  elim H7; intros _ H8; elim H5; apply H8.
  intros; elim H3; intros y0 H4; unfold g' in H4; elim H4; intro.
  apply (cond_fam f0); exists y0; apply H5.
  elim H5; clear H5; intros _ H5; apply H5.
(* Cas ou F est l'ensemble vide *)
  cut (compact F).
  intro; apply (H3 f0 H2).
  apply compact_eqDom with (fun _:R => False).
  apply compact_EMP.
  unfold eq_Dom; split.
  unfold included; intros; elim H3.
  assert (H3 := not_ex_all_not _ _ Hyp_F_NE); unfold included; intros;
    elim (H3 x); apply H4.
Qed.

(**********)
Lemma compact_P5 : forall X:R -> Prop, closed_set X -> bounded X -> compact X.
Proof.
  intros; unfold bounded in H0.
  elim H0; clear H0; intros m H0.
  elim H0; clear H0; intros M H0.
  assert (H1 := compact_P3 m M).
  apply (compact_P4 (fun c:R => m <= c <= M) X H1 H H0).
Qed.

(**********)
Lemma compact_carac :
  forall X:R -> Prop, compact X <-> closed_set X /\ bounded X.
Proof.
  intro; split.
  intro; split; [ apply (compact_P2 _ H) | apply (compact_P1 _ H) ].
  intro; elim H; clear H; intros; apply (compact_P5 _ H H0).
Qed.

Definition image_dir (f:R -> R) (D:R -> Prop) (x:R) : Prop :=
  exists y : R, x = f y /\ D y.

(**********)
Lemma continuity_compact :
  forall (f:R -> R) (X:R -> Prop),
    (forall x:R, continuity_pt f x) -> compact X -> compact (image_dir f X).
Proof.
  unfold compact; intros; unfold covering_open_set in H1.
  elim H1; clear H1; intros.
  set (D := ind f1).
  set (g := fun x y:R => image_rec f0 (f1 x) y).
  cut (forall x:R, (exists y : R, g x y) -> D x).
  intro; set (f' := mkfamily D g H3).
  cut (covering_open_set X f').
  intro; elim (H0 f' H4); intros D' H5; exists D'.
  unfold covering_finite in H5; elim H5; clear H5; intros;
    unfold covering_finite; split.
  unfold covering, image_dir; simpl; unfold covering in H5;
    intros; elim H7; intros y H8; elim H8; intros; assert (H11 := H5 _ H10);
      simpl in H11; elim H11; intros z H12; exists z; unfold g in H12;
        unfold image_rec in H12; rewrite H9; apply H12.
  unfold family_finite in H6; unfold domain_finite in H6;
    unfold family_finite; unfold domain_finite;
      elim H6; intros l H7; exists l; intro; elim (H7 x);
        intros; split; intro.
  apply H8; simpl in H10; simpl; apply H10.
  apply (H9 H10).
  unfold covering_open_set; split.
  unfold covering; intros; simpl; unfold covering in H1;
    unfold image_dir in H1; unfold g; unfold image_rec;
      apply H1.
  exists x; split; [ reflexivity | apply H4 ].
  unfold family_open_set; unfold family_open_set in H2; intro;
    simpl; unfold g;
      cut ((fun y:R => image_rec f0 (f1 x) y) = image_rec f0 (f1 x)).
  intro; rewrite H4.
  apply (continuity_P2 f0 (f1 x) H (H2 x)).
  reflexivity.
  intros; apply (cond_fam f1); unfold g in H3; unfold image_rec in H3; elim H3;
    intros; exists (f0 x0); apply H4.
Qed.

Lemma prolongement_C0 :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall c:R, a <= c <= b -> continuity_pt f c) ->
    exists g : R -> R,
      continuity g /\ (forall c:R, a <= c <= b -> g c = f c).
Proof.
  intros; elim H; intro.
  set
    (h :=
      fun x:R =>
        match Rle_dec x a with
          | left _ => f0 a
          | right _ =>
            match Rle_dec x b with
              | left _ => f0 x
              | right _ => f0 b
            end
        end).
  assert (H2 : 0 < b - a).
  apply Rlt_Rminus; assumption.
  exists h; split.
  unfold continuity; intro; case (Rtotal_order x a); intro.
  unfold continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
      simpl; unfold R_dist; intros; exists (a - x);
        split.
  change (0 < a - x); apply Rlt_Rminus; assumption.
  intros; elim H5; clear H5; intros _ H5; unfold h.
  case (Rle_dec x a) as [|[]].
  case (Rle_dec x0 a) as [|[]].
  unfold Rminus; rewrite Rplus_opp_r, Rabs_R0; assumption.
  left; apply Rplus_lt_reg_l with (- x);
    do 2 rewrite (Rplus_comm (- x)); apply Rle_lt_trans with (Rabs (x0 - x)).
  apply RRle_abs.
  assumption.
  left; assumption.
  elim H3; intro.
  assert (H5 : a <= a <= b).
  split; [ right; reflexivity | left; assumption ].
  assert (H6 := H0 _ H5); unfold continuity_pt in H6; unfold continue_in in H6;
    unfold limit1_in in H6; unfold limit_in in H6; simpl in H6;
      unfold R_dist in H6; unfold continuity_pt;
        unfold continue_in; unfold limit1_in;
          unfold limit_in; simpl; unfold R_dist;
            intros; elim (H6 _ H7); intros; exists (Rmin x0 (b - a));
              split.
  unfold Rmin; case (Rle_dec x0 (b - a)); intro.
  elim H8; intros; assumption.
  change (0 < b - a); apply Rlt_Rminus; assumption.
  intros; elim H9; clear H9; intros _ H9; cut (x1 < b).
  intro; unfold h; case (Rle_dec x a) as [|[]].
  case (Rle_dec x1 a) as [Hlta|Hnlea].
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
  case (Rle_dec x1 b) as [Hleb|[]].
  elim H8; intros; apply H12; split.
  unfold D_x, no_cond; split.
  trivial.
  red; intro; elim Hnlea; right; symmetry ; assumption.
  apply Rlt_le_trans with (Rmin x0 (b - a)).
  rewrite H4 in H9; apply H9.
  apply Rmin_l.
  left; assumption.
  right; assumption.
  apply Rplus_lt_reg_l with (- a); do 2 rewrite (Rplus_comm (- a));
    rewrite H4 in H9; apply Rle_lt_trans with (Rabs (x1 - a)).
  apply RRle_abs.
  apply Rlt_le_trans with (Rmin x0 (b - a)).
  assumption.
  apply Rmin_r.
  case (Rtotal_order x b); intro.
  assert (H6 : a <= x <= b).
  split; left; assumption.
  assert (H7 := H0 _ H6); unfold continuity_pt in H7; unfold continue_in in H7;
    unfold limit1_in in H7; unfold limit_in in H7; simpl in H7;
      unfold R_dist in H7; unfold continuity_pt;
        unfold continue_in; unfold limit1_in;
          unfold limit_in; simpl; unfold R_dist;
            intros; elim (H7 _ H8); intros; elim H9; clear H9;
              intros.
  assert (H11 : 0 < x - a).
  apply Rlt_Rminus; assumption.
  assert (H12 : 0 < b - x).
  apply Rlt_Rminus; assumption.
  exists (Rmin x0 (Rmin (x - a) (b - x))); split.
  unfold Rmin; case (Rle_dec (x - a) (b - x)) as [Hle|Hnle].
  case (Rle_dec x0 (x - a)) as [Hlea|Hnlea].
  assumption.
  assumption.
  case (Rle_dec x0 (b - x)) as [Hleb|Hnleb].
  assumption.
  assumption.
  intros x1 (H13,H14); cut (a < x1 < b).
  intro; elim H15; clear H15; intros; unfold h; case (Rle_dec x a) as [Hle|Hnle].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle H4)).
  case (Rle_dec x b) as [|[]].
  case (Rle_dec x1 a) as [Hle0|].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle0 H15)).
  case (Rle_dec x1 b) as [|[]].
  apply H10; split.
  assumption.
  apply Rlt_le_trans with (Rmin x0 (Rmin (x - a) (b - x))).
  assumption.
  apply Rmin_l.
  left; assumption.
  left; assumption.
  split.
  apply Ropp_lt_cancel; apply Rplus_lt_reg_l with x;
    apply Rle_lt_trans with (Rabs (x1 - x)).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply RRle_abs.
  apply Rlt_le_trans with (Rmin x0 (Rmin (x - a) (b - x))).
  assumption.
  apply Rle_trans with (Rmin (x - a) (b - x)).
  apply Rmin_r.
  apply Rmin_l.
  apply Rplus_lt_reg_l with (- x); do 2 rewrite (Rplus_comm (- x));
    apply Rle_lt_trans with (Rabs (x1 - x)).
  apply RRle_abs.
  apply Rlt_le_trans with (Rmin x0 (Rmin (x - a) (b - x))).
  assumption.
  apply Rle_trans with (Rmin (x - a) (b - x)); apply Rmin_r.
  elim H5; intro.
  assert (H7 : a <= b <= b).
  split; [ left; assumption | right; reflexivity ].
  assert (H8 := H0 _ H7); unfold continuity_pt in H8; unfold continue_in in H8;
    unfold limit1_in in H8; unfold limit_in in H8; simpl in H8;
      unfold R_dist in H8; unfold continuity_pt;
        unfold continue_in; unfold limit1_in;
          unfold limit_in; simpl; unfold R_dist;
            intros; elim (H8 _ H9); intros; exists (Rmin x0 (b - a));
              split.
  unfold Rmin; case (Rle_dec x0 (b - a)); intro.
  elim H10; intros; assumption.
  change (0 < b - a); apply Rlt_Rminus; assumption.
  intros; elim H11; clear H11; intros _ H11; cut (a < x1).
  intro; unfold h; case (Rle_dec x a) as [Hlea|Hnlea].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hlea H4)).
  case (Rle_dec x1 a) as [Hlea'|Hnlea'].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hlea' H12)).
  case (Rle_dec x b) as [Hleb|Hnleb].
  case (Rle_dec x1 b) as [Hleb'|Hnleb'].
  rewrite H6; elim H10; intros; destruct Hleb'.
  apply H14; split.
  unfold D_x, no_cond; split.
  trivial.
  red; intro; rewrite <- H16 in H15; elim (Rlt_irrefl _ H15).
  rewrite H6 in H11; apply Rlt_le_trans with (Rmin x0 (b - a)).
  apply H11.
  apply Rmin_l.
  rewrite H15; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    assumption.
  rewrite H6; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    assumption.
  elim Hnleb; right; assumption.
  rewrite H6 in H11; apply Ropp_lt_cancel; apply Rplus_lt_reg_l with b;
    apply Rle_lt_trans with (Rabs (x1 - b)).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply RRle_abs.
  apply Rlt_le_trans with (Rmin x0 (b - a)).
  assumption.
  apply Rmin_r.
  unfold continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
      simpl; unfold R_dist; intros; exists (x - b);
        split.
  change (0 < x - b); apply Rlt_Rminus; assumption.
  intros; elim H8; clear H8; intros.
  assert (H10 : b < x0).
  apply Ropp_lt_cancel; apply Rplus_lt_reg_l with x;
    apply Rle_lt_trans with (Rabs (x0 - x)).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply RRle_abs.
  assumption.
  unfold h; case (Rle_dec x a) as [Hle|Hnle].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle H4)).
  case (Rle_dec x b) as [Hleb|Hnleb].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hleb H6)).
  case (Rle_dec x0 a) as [Hlea'|Hnlea'].
  elim (Rlt_irrefl _ (Rlt_trans _ _ _ H1 (Rlt_le_trans _ _ _ H10 Hlea'))).
  case (Rle_dec x0 b) as [Hleb'|Hnleb'].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hleb' H10)).
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
  intros; elim H3; intros; unfold h; case (Rle_dec c a) as [[|]|].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H4 H6)).
  rewrite H6; reflexivity.
  case (Rle_dec c b) as [|[]].
  reflexivity.
  assumption.
  exists (fun _:R => f0 a); split.
  apply derivable_continuous; apply (derivable_const (f0 a)).
  intros; elim H2; intros; rewrite H1 in H3; cut (b = c).
  intro; rewrite <- H5; rewrite H1; reflexivity.
  apply Rle_antisym; assumption.
Qed.

(**********)
Lemma continuity_ab_maj :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall c:R, a <= c <= b -> continuity_pt f c) ->
    exists Mx : R, (forall c:R, a <= c <= b -> f c <= f Mx) /\ a <= Mx <= b.
Proof.
  intros;
    cut
      (exists g : R -> R,
        continuity g /\ (forall c:R, a <= c <= b -> g c = f0 c)).
  intro HypProl.
  elim HypProl; intros g Hcont_eq.
  elim Hcont_eq; clear Hcont_eq; intros Hcont Heq.
  assert (H1 := compact_P3 a b).
  assert (H2 := continuity_compact g (fun c:R => a <= c <= b) Hcont H1).
  assert (H3 := compact_P2 _ H2).
  assert (H4 := compact_P1 _ H2).
  cut (bound (image_dir g (fun c:R => a <= c <= b))).
  cut (exists x : R, image_dir g (fun c:R => a <= c <= b) x).
  intros; assert (H7 := completeness _ H6 H5).
  elim H7; clear H7; intros M H7; cut (image_dir g (fun c:R => a <= c <= b) M).
  intro; unfold image_dir in H8; elim H8; clear H8; intros Mxx H8; elim H8;
    clear H8; intros; exists Mxx; split.
  intros; rewrite <- (Heq c H10); rewrite <- (Heq Mxx H9); intros;
    rewrite <- H8; unfold is_lub in H7; elim H7; clear H7;
      intros H7 _; unfold is_upper_bound in H7; apply H7;
        unfold image_dir; exists c; split; [ reflexivity | apply H10 ].
  apply H9.
  elim (classic (image_dir g (fun c:R => a <= c <= b) M)); intro.
  assumption.
  cut
    (exists eps : posreal,
      (forall y:R,
        ~
        intersection_domain (disc M eps)
        (image_dir g (fun c:R => a <= c <= b)) y)).
  intro; elim H9; clear H9; intros eps H9; unfold is_lub in H7; elim H7;
    clear H7; intros;
      cut (is_upper_bound (image_dir g (fun c:R => a <= c <= b)) (M - eps)).
  intro; assert (H12 := H10 _ H11); cut (M - eps < M).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H12 H13)).
  pattern M at 2; rewrite <- Rplus_0_r; unfold Rminus;
    apply Rplus_lt_compat_l; apply Ropp_lt_cancel; rewrite Ropp_0;
      rewrite Ropp_involutive; apply (cond_pos eps).
  unfold is_upper_bound, image_dir; intros; cut (x <= M).
  intro; destruct (Rle_dec x (M - eps)) as [H13|].
  apply H13.
  elim (H9 x); unfold intersection_domain, disc, image_dir; split.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; rewrite Rabs_right.
  apply Rplus_lt_reg_l with (x - eps);
    replace (x - eps + (M - x)) with (M - eps).
  replace (x - eps + eps) with x.
  auto with real.
  ring.
  ring.
  apply Rge_minus; apply Rle_ge; apply H12.
  apply H11.
  apply H7; apply H11.
  cut
    (exists V : R -> Prop,
      neighbourhood V M /\
      (forall y:R,
        ~ intersection_domain V (image_dir g (fun c:R => a <= c <= b)) y)).
  intro; elim H9; intros V H10; elim H10; clear H10; intros.
  unfold neighbourhood in H10; elim H10; intros del H12; exists del; intros;
    red; intro; elim (H11 y).
  unfold intersection_domain; unfold intersection_domain in H13;
    elim H13; clear H13; intros; split.
  apply (H12 _ H13).
  apply H14.
  cut (~ point_adherent (image_dir g (fun c:R => a <= c <= b)) M).
  intro; unfold point_adherent in H9.
  assert
    (H10 :=
      not_all_ex_not _
      (fun V:R -> Prop =>
        neighbourhood V M ->
        exists y : R,
          intersection_domain V (image_dir g (fun c:R => a <= c <= b)) y) H9).
  elim H10; intros V0 H11; exists V0; assert (H12 := imply_to_and _ _ H11);
    elim H12; clear H12; intros.
  split.
  apply H12.
  apply (not_ex_all_not _ _ H13).
  red; intro; cut (adherence (image_dir g (fun c:R => a <= c <= b)) M).
  intro; elim (closed_set_P1 (image_dir g (fun c:R => a <= c <= b)));
    intros H11 _; assert (H12 := H11 H3).
  elim H8.
  unfold eq_Dom in H12; elim H12; clear H12; intros.
  apply (H13 _ H10).
  apply H9.
  exists (g a); unfold image_dir; exists a; split.
  reflexivity.
  split; [ right; reflexivity | apply H ].
  unfold bound; unfold bounded in H4; elim H4; clear H4; intros m H4;
    elim H4; clear H4; intros M H4; exists M; unfold is_upper_bound;
      intros; elim (H4 _ H5); intros _ H6; apply H6.
  apply prolongement_C0; assumption.
Qed.

(**********)
Lemma continuity_ab_min :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall c:R, a <= c <= b -> continuity_pt f c) ->
    exists mx : R, (forall c:R, a <= c <= b -> f mx <= f c) /\ a <= mx <= b.
Proof.
  intros.
  cut (forall c:R, a <= c <= b -> continuity_pt (- f0) c).
  intro; assert (H2 := continuity_ab_maj (- f0)%F a b H H1); elim H2;
    intros x0 H3; exists x0; intros; split.
  intros; rewrite <- (Ropp_involutive (f0 x0));
    rewrite <- (Ropp_involutive (f0 c)); apply Ropp_le_contravar;
      elim H3; intros; unfold opp_fct in H5; apply H5; apply H4.
  elim H3; intros; assumption.
  intros.
  assert (H2 := H0 _ H1).
  apply (continuity_pt_opp _ _ H2).
Qed.


(********************************************************)
(** *      Proof of Bolzano-Weierstrass theorem         *)
(********************************************************)

Definition ValAdh (un:nat -> R) (x:R) : Prop :=
  forall (V:R -> Prop) (N:nat),
    neighbourhood V x ->  exists p : nat, (N <= p)%nat /\ V (un p).

Definition intersection_family (f:family) (x:R) : Prop :=
  forall y:R, ind f y -> f y x.

Lemma ValAdh_un_exists :
  forall (un:nat -> R) (D:=fun x:R =>  exists n : nat, x = INR n)
    (f:=
      fun x:R =>
        adherence
        (fun y:R => (exists p : nat, y = un p /\ x <= INR p) /\ D x))
    (x:R), (exists y : R, f x y) -> D x.
Proof.
  intros; elim H; intros; unfold f in H0; unfold adherence in H0;
    unfold point_adherent in H0;
      assert (H1 : neighbourhood (disc x0 (mkposreal _ Rlt_0_1)) x0).
  unfold neighbourhood, disc; exists (mkposreal _ Rlt_0_1);
    unfold included; trivial.
  elim (H0 _ H1); intros; unfold intersection_domain in H2; elim H2; intros;
    elim H4; intros; apply H6.
Qed.

Definition ValAdh_un (un:nat -> R) : R -> Prop :=
  let D := fun x:R =>  exists n : nat, x = INR n in
    let f :=
      fun x:R =>
        adherence
        (fun y:R => (exists p : nat, y = un p /\ x <= INR p) /\ D x) in
        intersection_family (mkfamily D f (ValAdh_un_exists un)).

Lemma ValAdh_un_prop :
  forall (un:nat -> R) (x:R), ValAdh un x <-> ValAdh_un un x.
Proof.
  intros; split; intro.
  unfold ValAdh in H; unfold ValAdh_un;
    unfold intersection_family; simpl;
      intros; elim H0; intros N H1; unfold adherence;
        unfold point_adherent; intros; elim (H V N H2);
          intros; exists (un x0); unfold intersection_domain;
            elim H3; clear H3; intros; split.
  assumption.
  split.
  exists x0; split; [ reflexivity | rewrite H1; apply (le_INR _ _ H3) ].
  exists N; assumption.
  unfold ValAdh; intros; unfold ValAdh_un in H;
    unfold intersection_family in H; simpl in H;
      assert
        (H1 :
          adherence
          (fun y0:R =>
            (exists p : nat, y0 = un p /\ INR N <= INR p) /\
            (exists n : nat, INR N = INR n)) x).
  apply H; exists N; reflexivity.
  unfold adherence in H1; unfold point_adherent in H1; assert (H2 := H1 _ H0);
    elim H2; intros; unfold intersection_domain in H3;
      elim H3; clear H3; intros; elim H4; clear H4; intros;
        elim H4; clear H4; intros; elim H4; clear H4; intros;
          exists x1; split.
  apply (INR_le _ _ H6).
  rewrite H4 in H3; apply H3.
Qed.

Lemma adherence_P4 :
  forall F G:R -> Prop, included F G -> included (adherence F) (adherence G).
Proof.
  unfold adherence, included; unfold point_adherent; intros;
    elim (H0 _ H1); unfold intersection_domain;
      intros; elim H2; clear H2; intros; exists x0; split;
        [ assumption | apply (H _ H3) ].
Qed.

Definition family_closed_set (f:family) : Prop :=
  forall x:R, closed_set (f x).

Definition intersection_vide_in (D:R -> Prop) (f:family) : Prop :=
  forall x:R,
    (ind f x -> included (f x) D) /\
    ~ (exists y : R, intersection_family f y).

Definition intersection_vide_finite_in (D:R -> Prop)
  (f:family) : Prop := intersection_vide_in D f /\ family_finite f.

(**********)
Lemma compact_P6 :
  forall X:R -> Prop,
    compact X ->
    (exists z : R, X z) ->
    forall g:family,
      family_closed_set g ->
      intersection_vide_in X g ->
      exists D : R -> Prop, intersection_vide_finite_in X (subfamily g D).
Proof.
  intros X H Hyp g H0 H1.
  set (D' := ind g).
  set (f' := fun x y:R => complementary (g x) y /\ D' x).
  assert (H2 : forall x:R, (exists y : R, f' x y) -> D' x).
  intros; elim H2; intros; unfold f' in H3; elim H3; intros; assumption.
  set (f0 := mkfamily D' f' H2).
  unfold compact in H; assert (H3 : covering_open_set X f0).
  unfold covering_open_set; split.
  unfold covering; intros; unfold intersection_vide_in in H1;
    elim (H1 x); intros; unfold intersection_family in H5;
      assert
        (H6 := not_ex_all_not _ (fun y:R => forall y0:R, ind g y0 -> g y0 y) H5 x);
        assert (H7 := not_all_ex_not _ (fun y0:R => ind g y0 -> g y0 x) H6);
          elim H7; intros; exists x0; elim (imply_to_and _ _ H8);
            intros; unfold f0; simpl; unfold f';
              split; [ apply H10 | apply H9 ].
  unfold family_open_set; intro; elim (classic (D' x)); intro.
  apply open_set_P6 with (complementary (g x)).
  unfold family_closed_set in H0; unfold closed_set in H0; apply H0.
  unfold f0; simpl; unfold f'; unfold eq_Dom;
    split.
  unfold included; intros; split; [ apply H4 | apply H3 ].
  unfold included; intros; elim H4; intros; assumption.
  apply open_set_P6 with (fun _:R => False).
  apply open_set_P4.
  unfold eq_Dom; unfold included; split; intros;
    [ elim H4
      | simpl in H4; unfold f' in H4; elim H4; intros; elim H3; assumption ].
  elim (H _ H3); intros SF H4; exists SF;
    unfold intersection_vide_finite_in; split.
  unfold intersection_vide_in; simpl; intros; split.
  intros; unfold included; intros; unfold intersection_vide_in in H1;
    elim (H1 x); intros; elim H6; intros; apply H7.
  unfold intersection_domain in H5; elim H5; intros; assumption.
  assumption.
  elim (classic (exists y : R, intersection_domain (ind g) SF y)); intro Hyp'.
  red; intro; elim H5; intros; unfold intersection_family in H6;
    simpl in H6.
  cut (X x0).
  intro; unfold covering_finite in H4; elim H4; clear H4; intros H4 _;
    unfold covering in H4; elim (H4 x0 H7); intros; simpl in H8;
      unfold intersection_domain in H6; cut (ind g x1 /\ SF x1).
  intro; assert (H10 := H6 x1 H9); elim H10; clear H10; intros H10 _; elim H8;
    clear H8; intros H8 _; unfold f' in H8; unfold complementary in H8;
      elim H8; clear H8; intros H8 _; elim H8; assumption.
  split.
  apply (cond_fam f0).
  exists x0; elim H8; intros; assumption.
  elim H8; intros; assumption.
  unfold intersection_vide_in in H1; elim Hyp'; intros; assert (H8 := H6 _ H7);
    elim H8; intros; cut (ind g x1).
  intro; elim (H1 x1); intros; apply H12.
  apply H11.
  apply H9.
  apply (cond_fam g); exists x0; assumption.
  unfold covering_finite in H4; elim H4; clear H4; intros H4 _;
    cut (exists z : R, X z).
  intro; elim H5; clear H5; intros; unfold covering in H4; elim (H4 x0 H5);
    intros; simpl in H6; elim Hyp'; exists x1; elim H6;
      intros; unfold intersection_domain; split.
  apply (cond_fam f0); exists x0; apply H7.
  apply H8.
  apply Hyp.
  unfold covering_finite in H4; elim H4; clear H4; intros;
    unfold family_finite in H5; unfold domain_finite in H5;
      unfold family_finite; unfold domain_finite;
        elim H5; clear H5; intros l H5; exists l; intro; elim (H5 x);
          intros; split; intro;
            [ apply H6; simpl; simpl in H8; apply H8 | apply (H7 H8) ].
Qed.

Theorem Bolzano_Weierstrass :
  forall (un:nat -> R) (X:R -> Prop),
    compact X -> (forall n:nat, X (un n)) ->  exists l : R, ValAdh un l.
Proof.
  intros; cut (exists l : R, ValAdh_un un l).
  intro; elim H1; intros; exists x; elim (ValAdh_un_prop un x); intros;
    apply (H4 H2).
  assert (H1 :  exists z : R, X z).
  exists (un 0%nat); apply H0.
  set (D := fun x:R =>  exists n : nat, x = INR n).
  set
    (g :=
      fun x:R =>
        adherence (fun y:R => (exists p : nat, y = un p /\ x <= INR p) /\ D x)).
  assert (H2 : forall x:R, (exists y : R, g x y) -> D x).
  intros; elim H2; intros; unfold g in H3; unfold adherence in H3;
    unfold point_adherent in H3.
  assert (H4 : neighbourhood (disc x0 (mkposreal _ Rlt_0_1)) x0).
  unfold neighbourhood; exists (mkposreal _ Rlt_0_1);
    unfold included; trivial.
  elim (H3 _ H4); intros; unfold intersection_domain in H5; decompose [and] H5;
    assumption.
  set (f0 := mkfamily D g H2).
  assert (H3 := compact_P6 X H H1 f0).
  elim (classic (exists l : R, ValAdh_un un l)); intro.
  assumption.
  cut (family_closed_set f0).
  intro; cut (intersection_vide_in X f0).
  intro; assert (H7 := H3 H5 H6).
  elim H7; intros SF H8; unfold intersection_vide_finite_in in H8; elim H8;
    clear H8; intros; unfold intersection_vide_in in H8;
      elim (H8 0); intros _ H10; elim H10; unfold family_finite in H9;
        unfold domain_finite in H9; elim H9; clear H9; intros l H9;
          set (r := MaxRlist l); cut (D r).
  intro; unfold D in H11; elim H11; intros; exists (un x);
    unfold intersection_family; simpl;
      unfold intersection_domain; intros; split.
  unfold g; apply adherence_P1; split.
  exists x; split;
    [ reflexivity
      | rewrite <- H12; unfold r; apply MaxRlist_P1; elim (H9 y); intros;
        apply H14; simpl; apply H13 ].
  elim H13; intros; assumption.
  elim H13; intros; assumption.
  elim (H9 r); intros.
  simpl in H12; unfold intersection_domain in H12; cut (In r l).
  intro; elim (H12 H13); intros; assumption.
  unfold r; apply MaxRlist_P2;
    cut (exists z : R, intersection_domain (ind f0) SF z).
  intro; elim H13; intros; elim (H9 x); intros; simpl in H15;
    assert (H17 := H15 H14); exists x; apply H17.
  elim (classic (exists z : R, intersection_domain (ind f0) SF z)); intro.
  assumption.
  elim (H8 0); intros _ H14; elim H1; intros;
    assert
      (H16 :=
        not_ex_all_not _ (fun y:R => intersection_family (subfamily f0 SF) y) H14);
      assert
        (H17 :=
          not_ex_all_not _ (fun z:R => intersection_domain (ind f0) SF z) H13);
        assert (H18 := H16 x); unfold intersection_family in H18;
          simpl in H18;
            assert
              (H19 :=
                not_all_ex_not _ (fun y:R => intersection_domain D SF y -> g y x /\ SF y)
                H18); elim H19; intros; assert (H21 := imply_to_and _ _ H20);
              elim (H17 x0); elim H21; intros; assumption.
  unfold intersection_vide_in; intros; split.
  intro; simpl in H6; unfold f0; simpl; unfold g;
    apply included_trans with (adherence X).
  apply adherence_P4.
  unfold included; intros; elim H7; intros; elim H8; intros; elim H10;
    intros; rewrite H11; apply H0.
  apply adherence_P2; apply compact_P2; assumption.
  apply H4.
  unfold family_closed_set; unfold f0; simpl;
    unfold g; intro; apply adherence_P3.
Qed.

(********************************************************)
(** *            Proof of Heine's theorem               *)
(********************************************************)

Definition uniform_continuity (f:R -> R) (X:R -> Prop) : Prop :=
  forall eps:posreal,
    exists delta : posreal,
      (forall x y:R,
        X x -> X y -> Rabs (x - y) < delta -> Rabs (f x - f y) < eps).

Lemma is_lub_u :
  forall (E:R -> Prop) (x y:R), is_lub E x -> is_lub E y -> x = y.
Proof.
  unfold is_lub; intros; elim H; elim H0; intros; apply Rle_antisym;
    [ apply (H4 _ H1) | apply (H2 _ H3) ].
Qed.

Lemma domain_P1 :
  forall X:R -> Prop,
    ~ (exists y : R, X y) \/
    (exists y : R, X y /\ (forall x:R, X x -> x = y)) \/
    (exists x : R, (exists y : R, X x /\ X y /\ x <> y)).
Proof.
  intro; elim (classic (exists y : R, X y)); intro.
  right; elim H; intros; elim (classic (exists y : R, X y /\ y <> x)); intro.
  right; elim H1; intros; elim H2; intros; exists x; exists x0; intros.
  split;
    [ assumption
      | split; [ assumption | apply (not_eq_sym (A:=R)); assumption ] ].
  left; exists x; split.
  assumption.
  intros; case (Req_dec x0 x); intro.
  assumption.
  elim H1; exists x0; split; assumption.
  left; assumption.
Qed.

Theorem Heine :
  forall (f:R -> R) (X:R -> Prop),
    compact X ->
    (forall x:R, X x -> continuity_pt f x) -> uniform_continuity f X.
Proof.
  intros f0 X H0 H; elim (domain_P1 X); intro Hyp.
(* X is empty *)
  unfold uniform_continuity; intros; exists (mkposreal _ Rlt_0_1);
    intros; elim Hyp; exists x; assumption.
  elim Hyp; clear Hyp; intro Hyp.
(* X has only one element *)
  unfold uniform_continuity; intros; exists (mkposreal _ Rlt_0_1);
    intros; elim Hyp; clear Hyp; intros; elim H4; clear H4;
      intros; assert (H6 := H5 _ H1); assert (H7 := H5 _ H2);
        rewrite H6; rewrite H7; unfold Rminus; rewrite Rplus_opp_r;
          rewrite Rabs_R0; apply (cond_pos eps).
(* X has at least two distinct elements *)
  assert
    (X_enc :
      exists m : R, (exists M : R, (forall x:R, X x -> m <= x <= M) /\ m < M)).
  assert (H1 := compact_P1 X H0); unfold bounded in H1; elim H1; intros;
    elim H2; intros; exists x; exists x0; split.
  apply H3.
  elim Hyp; intros; elim H4; intros; decompose [and] H5;
    assert (H10 := H3 _ H6); assert (H11 := H3 _ H8);
      elim H10; intros; elim H11; intros;
      destruct (total_order_T x x0) as [[|H15]|H15].
  assumption.
  rewrite H15 in H13, H7; elim H9; apply Rle_antisym;
    apply Rle_trans with x0; assumption.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ (Rle_trans _ _ _ H13 H14) H15)).
  elim X_enc; clear X_enc; intros m X_enc; elim X_enc; clear X_enc;
    intros M X_enc; elim X_enc; clear X_enc Hyp; intros X_enc Hyp;
      unfold uniform_continuity; intro;
        assert (H1 : forall t:posreal, 0 < t / 2).
  intro; unfold Rdiv; apply Rmult_lt_0_compat;
    [ apply (cond_pos t) | apply Rinv_0_lt_compat; prove_sup0 ].
  set
    (g :=
      fun x y:R =>
        X x /\
        (exists del : posreal,
          (forall z:R, Rabs (z - x) < del -> Rabs (f0 z - f0 x) < eps / 2) /\
          is_lub
          (fun zeta:R =>
            0 < zeta <= M - m /\
            (forall z:R, Rabs (z - x) < zeta -> Rabs (f0 z - f0 x) < eps / 2))
          del /\ disc x (mkposreal (del / 2) (H1 del)) y)).
  assert (H2 : forall x:R, (exists y : R, g x y) -> X x).
  intros; elim H2; intros; unfold g in H3; elim H3; clear H3; intros H3 _;
    apply H3.
  set (f' := mkfamily X g H2); unfold compact in H0;
    assert (H3 : covering_open_set X f').
  unfold covering_open_set; split.
  unfold covering; intros; exists x; simpl; unfold g;
    split.
  assumption.
  assert (H4 := H _ H3); unfold continuity_pt in H4; unfold continue_in in H4;
    unfold limit1_in in H4; unfold limit_in in H4; simpl in H4;
      unfold R_dist in H4; elim (H4 (eps / 2) (H1 eps));
        intros;
          set
            (E :=
              fun zeta:R =>
                0 < zeta <= M - m /\
                (forall z:R, Rabs (z - x) < zeta -> Rabs (f0 z - f0 x) < eps / 2));
            assert (H6 : bound E).
  unfold bound; exists (M - m); unfold is_upper_bound;
    unfold E; intros; elim H6; clear H6; intros H6 _;
      elim H6; clear H6; intros _ H6; apply H6.
  assert (H7 :  exists x : R, E x).
  elim H5; clear H5; intros; exists (Rmin x0 (M - m)); unfold E; intros;
    split.
  split.
  unfold Rmin; case (Rle_dec x0 (M - m)); intro.
  apply H5.
  apply Rlt_Rminus; apply Hyp.
  apply Rmin_r.
  intros; case (Req_dec x z); intro.
  rewrite H9; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    apply (H1 eps).
  apply H7; split.
  unfold D_x, no_cond; split; [ trivial | assumption ].
  apply Rlt_le_trans with (Rmin x0 (M - m)); [ apply H8 | apply Rmin_l ].
  destruct (completeness _ H6 H7) as (x1,p).
    cut (0 < x1 <= M - m).
  intros (H8,H9); exists (mkposreal _ H8); split.
  intros; cut (exists alp : R, Rabs (z - x) < alp <= x1 /\ E alp).
  intros; elim H11; intros; elim H12; clear H12; intros; unfold E in H13;
    elim H13; intros; apply H15.
  elim H12; intros; assumption.
  elim (classic (exists alp : R, Rabs (z - x) < alp <= x1 /\ E alp)); intro.
  assumption.
  assert
    (H12 :=
      not_ex_all_not _ (fun alp:R => Rabs (z - x) < alp <= x1 /\ E alp) H11);
    unfold is_lub in p; elim p; intros; cut (is_upper_bound E (Rabs (z - x))).
  intro; assert (H16 := H14 _ H15);
    elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H10 H16)).
  unfold is_upper_bound; intros; unfold is_upper_bound in H13;
    assert (H16 := H13 _ H15); case (Rle_dec x2 (Rabs (z - x)));
      intro.
  assumption.
  elim (H12 x2); split; [ split; [ auto with real | assumption ] | assumption ].
  split.
  apply p.
  unfold disc; unfold Rminus; rewrite Rplus_opp_r;
    rewrite Rabs_R0; simpl; unfold Rdiv;
      apply Rmult_lt_0_compat; [ apply H8 | apply Rinv_0_lt_compat; prove_sup0 ].
  elim H7; intros; unfold E in H8; elim H8; intros H9 _; elim H9; intros H10 _;
    unfold is_lub in p; elim p; intros; unfold is_upper_bound in H12;
      unfold is_upper_bound in H11; split.
  apply Rlt_le_trans with x2; [ assumption | apply (H11 _ H8) ].
  apply H12; intros; unfold E in H13; elim H13; intros; elim H14; intros;
    assumption.
  unfold family_open_set; intro; simpl; elim (classic (X x));
    intro.
  unfold g; unfold open_set; intros; elim H4; clear H4;
    intros _ H4; elim H4; clear H4; intros; elim H4; clear H4;
      intros; unfold neighbourhood; case (Req_dec x x0);
        intro.
  exists (mkposreal _ (H1 x1)); rewrite <- H6; unfold included; intros;
    split.
  assumption.
  exists x1; split.
  apply H4.
  split.
  elim H5; intros; apply H8.
  apply H7.
  set (d := x1 / 2 - Rabs (x0 - x)); assert (H7 : 0 < d).
  unfold d; apply Rlt_Rminus; elim H5; clear H5; intros;
    unfold disc in H7; apply H7.
  exists (mkposreal _ H7); unfold included; intros; split.
  assumption.
  exists x1; split.
  apply H4.
  elim H5; intros; split.
  assumption.
  unfold disc in H8; simpl in H8; unfold disc; simpl;
    unfold disc in H10; simpl in H10;
      apply Rle_lt_trans with (Rabs (x2 - x0) + Rabs (x0 - x)).
  replace (x2 - x) with (x2 - x0 + (x0 - x)); [ apply Rabs_triang | ring ].
  replace (x1 / 2) with (d + Rabs (x0 - x)); [ idtac | unfold d; ring ].
  do 2 rewrite <- (Rplus_comm (Rabs (x0 - x))); apply Rplus_lt_compat_l;
    apply H8.
  apply open_set_P6 with (fun _:R => False).
  apply open_set_P4.
  unfold eq_Dom; unfold included; intros; split.
  intros; elim H4.
  intros; unfold g in H4; elim H4; clear H4; intros H4 _; elim H3; apply H4.
  elim (H0 _ H3); intros DF H4; unfold covering_finite in H4; elim H4; clear H4;
    intros; unfold family_finite in H5; unfold domain_finite in H5;
      unfold covering in H4; simpl in H4; simpl in H5; elim H5;
        clear H5; intros l H5; unfold intersection_domain in H5;
          cut
            (forall x:R,
              In x l ->
              exists del : R,
                0 < del /\
                (forall z:R, Rabs (z - x) < del -> Rabs (f0 z - f0 x) < eps / 2) /\
                included (g x) (fun z:R => Rabs (z - x) < del / 2)).
  intros;
    assert
      (H7 :=
        Rlist_P1 l
        (fun x del:R =>
          0 < del /\
          (forall z:R, Rabs (z - x) < del -> Rabs (f0 z - f0 x) < eps / 2) /\
          included (g x) (fun z:R => Rabs (z - x) < del / 2)) H6);
      elim H7; clear H7; intros l' H7; elim H7; clear H7;
        intros; set (D := MinRlist l'); cut (0 < D / 2).
  intro; exists (mkposreal _ H9); intros; assert (H13 := H4 _ H10); elim H13;
    clear H13; intros xi H13; assert (H14 : In xi l).
  unfold g in H13; decompose [and] H13; elim (H5 xi); intros; apply H14; split;
    assumption.
  elim (pos_Rl_P2 l xi); intros H15 _; elim (H15 H14); intros i H16; elim H16;
    intros; apply Rle_lt_trans with (Rabs (f0 x - f0 xi) + Rabs (f0 xi - f0 y)).
  replace (f0 x - f0 y) with (f0 x - f0 xi + (f0 xi - f0 y));
  [ apply Rabs_triang | ring ].
  rewrite (double_var eps); apply Rplus_lt_compat.
  assert (H19 := H8 i H17); elim H19; clear H19; intros; rewrite <- H18 in H20;
    elim H20; clear H20; intros; apply H20; unfold included in H21;
      apply Rlt_trans with (pos_Rl l' i / 2).
  apply H21.
  elim H13; clear H13; intros; assumption.
  unfold Rdiv; apply Rmult_lt_reg_l with 2.
  prove_sup0.
  rewrite Rmult_comm; rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; pattern (pos_Rl l' i) at 1; rewrite <- Rplus_0_r;
    rewrite double; apply Rplus_lt_compat_l; apply H19.
  discrR.
  assert (H19 := H8 i H17); elim H19; clear H19; intros; rewrite <- H18 in H20;
    elim H20; clear H20; intros; rewrite <- Rabs_Ropp;
      rewrite Ropp_minus_distr; apply H20; unfold included in H21;
        elim H13; intros; assert (H24 := H21 x H22);
          apply Rle_lt_trans with (Rabs (y - x) + Rabs (x - xi)).
  replace (y - xi) with (y - x + (x - xi)); [ apply Rabs_triang | ring ].
  rewrite (double_var (pos_Rl l' i)); apply Rplus_lt_compat.
  apply Rlt_le_trans with (D / 2).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H12.
  unfold Rdiv; do 2 rewrite <- (Rmult_comm (/ 2));
    apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; prove_sup0.
  unfold D; apply MinRlist_P1; elim (pos_Rl_P2 l' (pos_Rl l' i));
    intros; apply H26; exists i; split;
      [ rewrite <- H7; assumption | reflexivity ].
  assumption.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ unfold D; apply MinRlist_P2; intros; elim (pos_Rl_P2 l' y); intros;
      elim (H10 H9); intros; elim H12; intros; rewrite H14;
        rewrite <- H7 in H13; elim (H8 x H13); intros;
          apply H15
      | apply Rinv_0_lt_compat; prove_sup0 ].
  intros; elim (H5 x); intros; elim (H8 H6); intros;
    set
      (E :=
        fun zeta:R =>
          0 < zeta <= M - m /\
          (forall z:R, Rabs (z - x) < zeta -> Rabs (f0 z - f0 x) < eps / 2));
      assert (H11 : bound E).
  unfold bound; exists (M - m); unfold is_upper_bound;
    unfold E; intros; elim H11; clear H11; intros H11 _;
      elim H11; clear H11; intros _ H11; apply H11.
  assert (H12 :  exists x : R, E x).
  assert (H13 := H _ H9); unfold continuity_pt in H13;
    unfold continue_in in H13; unfold limit1_in in H13;
      unfold limit_in in H13; simpl in H13; unfold R_dist in H13;
        elim (H13 _ (H1 eps)); intros; elim H12; clear H12;
          intros; exists (Rmin x0 (M - m)); unfold E;
            intros; split.
  split;
    [ unfold Rmin; case (Rle_dec x0 (M - m)); intro;
      [ apply H12 | apply Rlt_Rminus; apply Hyp ]
      | apply Rmin_r ].
  intros; case (Req_dec x z); intro.
  rewrite H16; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    apply (H1 eps).
  apply H14; split;
    [ unfold D_x, no_cond; split; [ trivial | assumption ]
      | apply Rlt_le_trans with (Rmin x0 (M - m)); [ apply H15 | apply Rmin_l ] ].
  destruct (completeness _ H11 H12) as (x0,p).
    cut (0 < x0 <= M - m).
  intro; elim H13; clear H13; intros; exists x0; split.
  assumption.
  split.
  intros; cut (exists alp : R, Rabs (z - x) < alp <= x0 /\ E alp).
  intros; elim H16; intros; elim H17; clear H17; intros; unfold E in H18;
    elim H18; intros; apply H20; elim H17; intros; assumption.
  elim (classic (exists alp : R, Rabs (z - x) < alp <= x0 /\ E alp)); intro.
  assumption.
  assert
    (H17 :=
      not_ex_all_not _ (fun alp:R => Rabs (z - x) < alp <= x0 /\ E alp) H16);
    unfold is_lub in p; elim p; intros; cut (is_upper_bound E (Rabs (z - x))).
  intro; assert (H21 := H19 _ H20);
    elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H15 H21)).
  unfold is_upper_bound; intros; unfold is_upper_bound in H18;
    assert (H21 := H18 _ H20); case (Rle_dec x1 (Rabs (z - x)));
      intro.
  assumption.
  elim (H17 x1); split.
  split; [ auto with real | assumption ].
  assumption.
  unfold included, g; intros; elim H15; intros; elim H17; intros;
    decompose [and] H18; cut (x0 = x2).
  intro; rewrite H20; apply H22.
  unfold E in p; eapply is_lub_u.
  apply p.
  apply H21.
  elim H12; intros; unfold E in H13; elim H13; intros H14 _; elim H14;
    intros H15 _; unfold is_lub in p; elim p; intros;
      unfold is_upper_bound in H16; unfold is_upper_bound in H17;
        split.
  apply Rlt_le_trans with x1; [ assumption | apply (H16 _ H13) ].
  apply H17; intros; unfold E in H18; elim H18; intros; elim H19; intros;
    assumption.
Qed.

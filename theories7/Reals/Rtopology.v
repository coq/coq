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
Require Ranalysis1.
Require RList.
Require Classical_Prop.
Require Classical_Pred_Type.
V7only [Import R_scope.]. Open Local Scope R_scope.

Definition included [D1,D2:R->Prop] : Prop := (x:R)(D1 x)->(D2 x).
Definition disc [x:R;delta:posreal] : R->Prop := [y:R]``(Rabsolu (y-x))<delta``.
Definition neighbourhood [V:R->Prop;x:R] : Prop := (EXT delta:posreal | (included (disc x delta) V)).
Definition open_set [D:R->Prop] : Prop := (x:R) (D x)->(neighbourhood D x).
Definition complementary [D:R->Prop] : R->Prop := [c:R]~(D c).
Definition closed_set [D:R->Prop] : Prop := (open_set (complementary D)).
Definition intersection_domain [D1,D2:R->Prop] : R->Prop := [c:R](D1 c)/\(D2 c).
Definition union_domain [D1,D2:R->Prop] : R->Prop := [c:R](D1 c)\/(D2 c).
Definition interior [D:R->Prop] : R->Prop := [x:R](neighbourhood D x).

Lemma interior_P1 : (D:R->Prop) (included (interior D) D).
Intros; Unfold included; Unfold interior; Intros; Unfold neighbourhood in H; Elim H; Intros; Unfold included in H0; Apply H0; Unfold disc; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply (cond_pos x0).
Qed.

Lemma interior_P2 : (D:R->Prop) (open_set D) -> (included D (interior D)).
Intros; Unfold open_set in H; Unfold included; Intros; Assert H1 := (H ? H0); Unfold interior; Apply H1.
Qed.

Definition point_adherent [D:R->Prop;x:R] : Prop := (V:R->Prop) (neighbourhood V x) -> (EXT y:R | (intersection_domain V D y)).
Definition adherence [D:R->Prop] : R->Prop := [x:R](point_adherent D x).

Lemma adherence_P1 : (D:R->Prop) (included D (adherence D)).
Intro; Unfold included; Intros; Unfold adherence; Unfold point_adherent; Intros; Exists x; Unfold intersection_domain; Split.
Unfold neighbourhood in H0; Elim H0; Intros; Unfold included in H1; Apply H1; Unfold disc; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply (cond_pos x0).
Apply H.
Qed.

Lemma included_trans : (D1,D2,D3:R->Prop) (included D1 D2) -> (included D2 D3) -> (included D1 D3).
Unfold included; Intros; Apply H0; Apply H; Apply H1.
Qed.

Lemma interior_P3 : (D:R->Prop) (open_set (interior D)).
Intro; Unfold open_set interior; Unfold neighbourhood; Intros; Elim H; Intros.
Exists x0; Unfold included; Intros.
Pose del := ``x0-(Rabsolu (x-x1))``.
Cut ``0<del``.
Intro; Exists (mkposreal del H2); Intros.
Cut (included (disc x1 (mkposreal del H2)) (disc x x0)).
Intro; Assert H5 := (included_trans ? ? ? H4 H0).
Apply H5; Apply H3.
Unfold included; Unfold disc; Intros.
Apply Rle_lt_trans with ``(Rabsolu (x3-x1))+(Rabsolu (x1-x))``.
Replace ``x3-x`` with ``(x3-x1)+(x1-x)``; [Apply Rabsolu_triang | Ring].
Replace (pos x0) with ``del+(Rabsolu (x1-x))``.
Do 2 Rewrite <- (Rplus_sym (Rabsolu ``x1-x``)); Apply Rlt_compatibility; Apply H4.
Unfold del; Rewrite <- (Rabsolu_Ropp ``x-x1``); Rewrite Ropp_distr2; Ring.
Unfold del; Apply Rlt_anti_compatibility with ``(Rabsolu (x-x1))``; Rewrite Rplus_Or; Replace ``(Rabsolu (x-x1))+(x0-(Rabsolu (x-x1)))`` with (pos x0); [Idtac | Ring].
Unfold disc in H1; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H1.
Qed.

Lemma complementary_P1 : (D:R->Prop) ~(EXT y:R | (intersection_domain D (complementary D) y)).
Intro; Red; Intro; Elim H; Intros; Unfold intersection_domain complementary in H0; Elim H0; Intros; Elim H2; Assumption.
Qed.

Lemma adherence_P2 : (D:R->Prop) (closed_set D) -> (included (adherence D) D).
Unfold closed_set; Unfold open_set complementary; Intros; Unfold included adherence; Intros; Assert H1 := (classic (D x)); Elim H1; Intro.
Assumption.
Assert H3 := (H ? H2); Assert H4 := (H0 ? H3); Elim H4; Intros; Unfold intersection_domain in H5; Elim H5; Intros; Elim H6; Assumption.
Qed.

Lemma adherence_P3 : (D:R->Prop) (closed_set (adherence D)).
Intro; Unfold closed_set adherence; Unfold open_set complementary point_adherent; Intros; Pose P := [V:R->Prop](neighbourhood V x)->(EXT y:R | (intersection_domain V D y)); Assert H0 := (not_all_ex_not ? P H); Elim H0; Intros V0 H1; Unfold P in H1; Assert H2 := (imply_to_and ? ? H1); Unfold neighbourhood; Elim H2; Intros; Unfold neighbourhood in H3; Elim H3; Intros; Exists x0; Unfold included; Intros; Red; Intro.
Assert H8 := (H7 V0); Cut (EXT delta:posreal | (x:R)(disc x1 delta x)->(V0 x)).
Intro; Assert H10 := (H8 H9); Elim H4; Assumption.
Cut ``0<x0-(Rabsolu (x-x1))``.
Intro; Pose del := (mkposreal ? H9); Exists del; Intros; Unfold included in H5; Apply H5; Unfold disc; Apply Rle_lt_trans with ``(Rabsolu (x2-x1))+(Rabsolu (x1-x))``.
Replace ``x2-x`` with ``(x2-x1)+(x1-x)``; [Apply Rabsolu_triang | Ring].
Replace (pos x0) with ``del+(Rabsolu (x1-x))``.
Do 2 Rewrite <- (Rplus_sym ``(Rabsolu (x1-x))``); Apply Rlt_compatibility; Apply H10.
Unfold del; Simpl; Rewrite <- (Rabsolu_Ropp ``x-x1``); Rewrite Ropp_distr2; Ring.
Apply Rlt_anti_compatibility with ``(Rabsolu (x-x1))``; Rewrite Rplus_Or; Replace ``(Rabsolu (x-x1))+(x0-(Rabsolu (x-x1)))`` with (pos x0); [Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H6 | Ring].
Qed.

Definition eq_Dom [D1,D2:R->Prop] : Prop := (included D1 D2)/\(included D2 D1).

Infix "=_D" eq_Dom (at level 5, no associativity).

Lemma open_set_P1 : (D:R->Prop) (open_set D) <-> D =_D (interior D).
Intro; Split.
Intro; Unfold eq_Dom; Split.
Apply interior_P2; Assumption.
Apply interior_P1.
Intro; Unfold eq_Dom in H; Elim H; Clear H; Intros; Unfold open_set; Intros; Unfold included interior in H; Unfold included in H0; Apply (H ? H1).
Qed.

Lemma closed_set_P1 : (D:R->Prop) (closed_set D) <-> D =_D (adherence D).
Intro; Split.
Intro; Unfold eq_Dom; Split.
Apply adherence_P1.
Apply adherence_P2; Assumption.
Unfold eq_Dom; Unfold included; Intros; Assert H0 := (adherence_P3 D); Unfold closed_set in H0; Unfold closed_set; Unfold open_set; Unfold open_set in H0; Intros; Assert H2 : (complementary (adherence D) x).
Unfold complementary; Unfold complementary in H1; Red; Intro; Elim H; Clear H; Intros _ H; Elim H1; Apply (H ? H2).
Assert H3 := (H0 ? H2); Unfold neighbourhood; Unfold neighbourhood in H3; Elim H3; Intros; Exists x0; Unfold included; Unfold included in H4; Intros; Assert H6 := (H4 ? H5); Unfold complementary in H6; Unfold complementary; Red; Intro; Elim H; Clear H; Intros H _; Elim H6; Apply (H ? H7).
Qed.

Lemma neighbourhood_P1 : (D1,D2:R->Prop;x:R) (included D1 D2) -> (neighbourhood D1 x) -> (neighbourhood D2 x).
Unfold included neighbourhood; Intros; Elim H0; Intros; Exists x0; Intros; Unfold included; Unfold included in H1; Intros; Apply (H ? (H1 ? H2)).
Qed.

Lemma open_set_P2 : (D1,D2:R->Prop) (open_set D1) -> (open_set D2) -> (open_set (union_domain D1 D2)).
Unfold open_set; Intros; Unfold union_domain in H1; Elim H1; Intro.
Apply neighbourhood_P1 with D1.
Unfold included union_domain; Tauto.
Apply H; Assumption.
Apply neighbourhood_P1 with D2.
Unfold included union_domain; Tauto.
Apply H0; Assumption.
Qed.

Lemma open_set_P3 : (D1,D2:R->Prop) (open_set D1) -> (open_set D2) -> (open_set (intersection_domain D1 D2)).
Unfold open_set; Intros; Unfold intersection_domain in H1; Elim H1; Intros.
Assert H4 := (H ? H2); Assert H5 := (H0 ? H3); Unfold intersection_domain; Unfold neighbourhood in H4 H5; Elim H4; Clear H; Intros del1 H; Elim H5; Clear H0; Intros del2 H0; Cut ``0<(Rmin del1 del2)``.
Intro; Pose del := (mkposreal ? H6).
Exists del; Unfold included; Intros; Unfold included in H H0; Unfold disc in H H0 H7.
Split.
Apply H; Apply Rlt_le_trans with (pos del).
Apply H7.
Unfold del; Simpl; Apply Rmin_l.
Apply H0; Apply Rlt_le_trans with (pos del).
Apply H7.
Unfold del; Simpl; Apply Rmin_r.
Unfold Rmin; Case (total_order_Rle del1 del2); Intro.
Apply (cond_pos del1).
Apply (cond_pos del2).
Qed.

Lemma open_set_P4 : (open_set [x:R]False).
Unfold open_set; Intros; Elim H.
Qed.

Lemma open_set_P5 : (open_set [x:R]True).
Unfold open_set; Intros; Unfold neighbourhood.
Exists (mkposreal R1 Rlt_R0_R1); Unfold included; Intros; Trivial.
Qed.

Lemma disc_P1 : (x:R;del:posreal) (open_set (disc x del)).
Intros; Assert H := (open_set_P1 (disc x del)).
Elim H; Intros; Apply H1.
Unfold eq_Dom; Split.
Unfold included interior disc; Intros; Cut ``0<del-(Rabsolu (x-x0))``.
Intro; Pose del2 := (mkposreal ? H3).
Exists del2; Unfold included; Intros.
Apply Rle_lt_trans with ``(Rabsolu (x1-x0))+(Rabsolu (x0 -x))``.
Replace ``x1-x`` with ``(x1-x0)+(x0-x)``; [Apply Rabsolu_triang | Ring].
Replace (pos del) with ``del2 + (Rabsolu (x0-x))``.
Do 2 Rewrite <- (Rplus_sym ``(Rabsolu (x0-x))``); Apply Rlt_compatibility.
Apply H4.
Unfold del2; Simpl; Rewrite <- (Rabsolu_Ropp ``x-x0``); Rewrite Ropp_distr2; Ring.
Apply Rlt_anti_compatibility with ``(Rabsolu (x-x0))``; Rewrite Rplus_Or; Replace ``(Rabsolu (x-x0))+(del-(Rabsolu (x-x0)))`` with (pos del); [Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H2 | Ring].
Apply interior_P1.
Qed.

Lemma continuity_P1 : (f:R->R;x:R) (continuity_pt f x) <-> (W:R->Prop)(neighbourhood W (f x)) -> (EXT V:R->Prop | (neighbourhood V x) /\ ((y:R)(V y)->(W (f y)))).
Intros; Split.
Intros; Unfold neighbourhood in H0.
Elim H0; Intros del1 H1.
Unfold continuity_pt in H; Unfold continue_in in H; Unfold limit1_in in H; Unfold limit_in in H; Simpl in H; Unfold R_dist in H.
Assert H2 := (H del1 (cond_pos del1)).
Elim H2; Intros del2 H3.
Elim H3; Intros.
Exists (disc x (mkposreal del2 H4)).
Intros; Unfold included in H1; Split.
Unfold neighbourhood disc.
Exists (mkposreal del2 H4).
Unfold included; Intros; Assumption.
Intros; Apply H1; Unfold disc; Case (Req_EM y x); Intro.
Rewrite H7; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply (cond_pos del1).
Apply H5; Split.
Unfold D_x no_cond; Split.
Trivial.
Apply not_sym; Apply H7.
Unfold disc in H6; Apply H6.
Intros; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Intros.
Assert H1 := (H (disc (f x) (mkposreal eps H0))).
Cut (neighbourhood (disc (f x) (mkposreal eps H0)) (f x)).
Intro; Assert H3 := (H1 H2).
Elim H3; Intros D H4; Elim H4; Intros; Unfold neighbourhood in H5; Elim H5; Intros del1 H7.
Exists (pos del1); Split.
Apply (cond_pos del1).
Intros; Elim H8; Intros; Simpl in H10; Unfold R_dist in H10; Simpl; Unfold R_dist; Apply (H6 ? (H7 ? H10)).
Unfold neighbourhood disc; Exists (mkposreal eps H0); Unfold included; Intros; Assumption.
Qed.

Definition image_rec [f:R->R;D:R->Prop] : R->Prop := [x:R](D (f x)).

(**********)
Lemma continuity_P2 : (f:R->R;D:R->Prop) (continuity f) -> (open_set D) -> (open_set (image_rec f D)).
Intros; Unfold open_set in H0; Unfold open_set; Intros; Assert H2 := (continuity_P1 f x); Elim H2; Intros H3 _; Assert H4 := (H3 (H x)); Unfold neighbourhood image_rec; Unfold image_rec in H1; Assert H5 := (H4 D (H0 (f x) H1)); Elim H5; Intros V0 H6; Elim H6; Intros; Unfold neighbourhood in H7; Elim H7; Intros del H9; Exists del; Unfold included in H9; Unfold included; Intros; Apply (H8 ? (H9 ? H10)).
Qed.

(**********)
Lemma continuity_P3 : (f:R->R) (continuity f) <-> (D:R->Prop) (open_set D)->(open_set (image_rec f D)).
Intros; Split.
Intros; Apply continuity_P2; Assumption.
Intros; Unfold continuity; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros; Cut (open_set (disc (f x) (mkposreal ? H0))).
Intro; Assert H2 := (H ? H1).
Unfold open_set image_rec in H2; Cut (disc (f x) (mkposreal ? H0) (f x)).
Intro; Assert H4 := (H2 ? H3).
Unfold neighbourhood in H4; Elim H4; Intros del H5.
Exists (pos del); Split.
Apply (cond_pos del).
Intros; Unfold included in H5; Apply H5; Elim H6; Intros; Apply H8.
Unfold disc; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply H0.
Apply disc_P1.
Qed.

(**********)
Theorem Rsepare : (x,y:R) ``x<>y``->(EXT V:R->Prop | (EXT W:R->Prop | (neighbourhood V x)/\(neighbourhood W y)/\~(EXT y:R | (intersection_domain V W y)))).
Intros x y Hsep; Pose D := ``(Rabsolu (x-y))``.
Cut ``0<D/2``.
Intro; Exists (disc x (mkposreal ? H)).
Exists (disc y (mkposreal ? H)); Split.
Unfold neighbourhood; Exists (mkposreal ? H); Unfold included; Tauto.
Split.
Unfold neighbourhood; Exists (mkposreal ? H); Unfold included; Tauto.
Red; Intro; Elim H0; Intros; Unfold intersection_domain in H1; Elim H1; Intros.
Cut ``D<D``.
Intro; Elim (Rlt_antirefl ? H4).
Change ``(Rabsolu (x-y))<D``; Apply Rle_lt_trans with ``(Rabsolu (x-x0))+(Rabsolu (x0-y))``.
Replace ``x-y`` with ``(x-x0)+(x0-y)``; [Apply Rabsolu_triang | Ring].
Rewrite (double_var D); Apply Rplus_lt.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H2.
Apply H3.
Unfold Rdiv; Apply Rmult_lt_pos.
Unfold D; Apply Rabsolu_pos_lt; Apply (Rminus_eq_contra ? ? Hsep).
Apply Rlt_Rinv; Sup0.
Qed.

Record family : Type := mkfamily {
  ind : R->Prop;
  f :> R->R->Prop;
  cond_fam : (x:R)(EXT y:R|(f x y))->(ind x) }.

Definition family_open_set [f:family] : Prop := (x:R) (open_set (f x)).

Definition domain_finite [D:R->Prop] : Prop := (EXT l:Rlist | (x:R)(D x)<->(In x l)).

Definition family_finite [f:family] : Prop := (domain_finite (ind f)).

Definition covering [D:R->Prop;f:family] : Prop := (x:R) (D x)->(EXT y:R | (f y x)).

Definition covering_open_set [D:R->Prop;f:family] : Prop := (covering D f)/\(family_open_set f).

Definition covering_finite [D:R->Prop;f:family] : Prop := (covering D f)/\(family_finite f).

Lemma restriction_family : (f:family;D:R->Prop) (x:R)(EXT y:R|([z1:R][z2:R](f z1 z2)/\(D z1) x y))->(intersection_domain (ind f) D x).
Intros; Elim H; Intros; Unfold intersection_domain; Elim H0; Intros; Split.
Apply (cond_fam f0); Exists x0; Assumption.
Assumption.
Qed.

Definition subfamily [f:family;D:R->Prop] : family := (mkfamily (intersection_domain (ind f) D) [x:R][y:R](f x y)/\(D x) (restriction_family f D)).

Definition compact [X:R->Prop] : Prop := (f:family) (covering_open_set X f) -> (EXT D:R->Prop | (covering_finite X (subfamily f D))).

(**********)
Lemma family_P1 : (f:family;D:R->Prop) (family_open_set f) -> (family_open_set (subfamily f D)).
Unfold family_open_set; Intros; Unfold subfamily; Simpl; Assert H0 := (classic (D x)).
Elim H0; Intro.
Cut (open_set (f0 x))->(open_set [y:R](f0 x y)/\(D x)).
Intro; Apply H2; Apply H.
Unfold open_set; Unfold neighbourhood; Intros; Elim H3; Intros; Assert H6 := (H2 ? H4); Elim H6; Intros; Exists x1; Unfold included; Intros; Split.
Apply (H7 ? H8).
Assumption.
Cut (open_set [y:R]False) -> (open_set [y:R](f0 x y)/\(D x)).
Intro; Apply H2; Apply open_set_P4.
Unfold open_set; Unfold neighbourhood; Intros; Elim H3; Intros; Elim H1; Assumption.
Qed.

Definition bounded [D:R->Prop] : Prop := (EXT m:R | (EXT M:R | (x:R)(D x)->``m<=x<=M``)).

Lemma open_set_P6 : (D1,D2:R->Prop) (open_set D1) -> D1 =_D D2 -> (open_set D2).
Unfold open_set; Unfold neighbourhood; Intros.
Unfold eq_Dom in H0; Elim H0; Intros.
Assert H4 := (H ? (H3 ? H1)).
Elim H4; Intros.
Exists x0; Apply included_trans with D1; Assumption.
Qed.

(**********)
Lemma compact_P1 : (X:R->Prop) (compact X) -> (bounded X).
Intros; Unfold compact in H; Pose D := [x:R]True; Pose g := [x:R][y:R]``(Rabsolu y)<x``; Cut (x:R)(EXT y|(g x y))->True; [Intro | Intro; Trivial].
Pose f0 := (mkfamily D g H0); Assert H1 := (H f0); Cut (covering_open_set X f0).
Intro; Assert H3 := (H1 H2); Elim H3; Intros D' H4; Unfold covering_finite in H4; Elim H4; Intros; Unfold family_finite in H6; Unfold domain_finite in H6; Elim H6; Intros l H7; Unfold bounded; Pose r := (MaxRlist l).
Exists ``-r``; Exists r; Intros.
Unfold covering in H5; Assert H9 := (H5 ? H8); Elim H9; Intros; Unfold subfamily in H10; Simpl in H10; Elim H10; Intros; Assert H13 := (H7 x0); Simpl in H13; Cut (intersection_domain D D' x0).
Elim H13; Clear H13; Intros.
Assert H16 := (H13 H15); Unfold g in H11; Split.
Cut ``x0<=r``.
Intro; Cut ``(Rabsolu x)<r``.
Intro; Assert H19 := (Rabsolu_def2 x r H18); Elim H19; Intros; Left; Assumption.
Apply Rlt_le_trans with x0; Assumption.
Apply (MaxRlist_P1 l x0 H16).
Cut ``x0<=r``.
Intro; Apply Rle_trans with (Rabsolu x).
Apply Rle_Rabsolu.
Apply Rle_trans with x0.
Left; Apply H11.
Assumption.
Apply (MaxRlist_P1 l x0 H16).
Unfold intersection_domain D; Tauto.
Unfold covering_open_set; Split.
Unfold covering; Intros; Simpl; Exists ``(Rabsolu x)+1``; Unfold g; Pattern 1 (Rabsolu x); Rewrite <- Rplus_Or; Apply Rlt_compatibility; Apply Rlt_R0_R1.
Unfold family_open_set; Intro; Case (total_order R0 x); Intro.
Apply open_set_P6 with (disc R0 (mkposreal ? H2)).
Apply disc_P1.
Unfold eq_Dom; Unfold f0; Simpl; Unfold g disc; Split.
Unfold included; Intros; Unfold Rminus in H3; Rewrite Ropp_O in H3; Rewrite Rplus_Or in H3; Apply H3.
Unfold included; Intros; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply H3.
Apply open_set_P6 with [x:R]False.
Apply open_set_P4.
Unfold eq_Dom; Split.
Unfold included; Intros; Elim H3.
Unfold included f0; Simpl; Unfold g; Intros; Elim H2; Intro; [Rewrite <- H4 in H3; Assert H5 := (Rabsolu_pos x0); Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H5 H3)) | Assert H6 := (Rabsolu_pos x0); Assert H7 := (Rlt_trans ? ? ? H3 H4); Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H6 H7))].
Qed.

(**********)
Lemma compact_P2 : (X:R->Prop) (compact X) -> (closed_set X).
Intros; Assert H0 := (closed_set_P1 X); Elim H0; Clear H0; Intros _ H0; Apply H0; Clear H0.
Unfold eq_Dom; Split.
Apply adherence_P1.
Unfold included; Unfold adherence; Unfold point_adherent; Intros; Unfold compact in H; Assert H1 := (classic (X x)); Elim H1; Clear H1; Intro.
Assumption.
Cut (y:R)(X y)->``0<(Rabsolu (y-x))/2``.
Intro; Pose D := X; Pose g := [y:R][z:R]``(Rabsolu (y-z))<(Rabsolu (y-x))/2``/\(D y); Cut (x:R)(EXT y|(g x y))->(D x).
Intro; Pose f0 := (mkfamily D g H3); Assert H4 := (H f0); Cut (covering_open_set X f0).
Intro; Assert H6 := (H4 H5); Elim H6; Clear H6; Intros D' H6.
Unfold covering_finite in H6; Decompose [and] H6; Unfold covering subfamily in H7; Simpl in H7; Unfold family_finite subfamily in H8; Simpl in H8; Unfold domain_finite in H8; Elim H8; Clear H8; Intros l H8; Pose alp := (MinRlist (AbsList l x)); Cut ``0<alp``.
Intro; Assert H10 := (H0 (disc x (mkposreal ? H9))); Cut (neighbourhood (disc x (mkposreal alp H9)) x).
Intro; Assert H12 := (H10 H11); Elim H12; Clear H12; Intros y H12; Unfold intersection_domain in H12; Elim H12; Clear H12; Intros; Assert H14 := (H7 ? H13); Elim H14; Clear H14; Intros y0 H14; Elim H14; Clear H14; Intros; Unfold g in H14; Elim H14; Clear H14; Intros; Unfold disc in H12; Simpl in H12; Cut ``alp<=(Rabsolu (y0-x))/2``.
Intro; Assert H18 := (Rlt_le_trans ? ? ? H12 H17); Cut ``(Rabsolu (y0-x))<(Rabsolu (y0-x))``.
Intro; Elim (Rlt_antirefl ? H19).
Apply Rle_lt_trans with ``(Rabsolu (y0-y))+(Rabsolu (y-x))``.
Replace ``y0-x`` with ``(y0-y)+(y-x)``; [Apply Rabsolu_triang | Ring].
Rewrite (double_var ``(Rabsolu (y0-x))``); Apply Rplus_lt; Assumption.
Apply (MinRlist_P1 (AbsList l x) ``(Rabsolu (y0-x))/2``); Apply AbsList_P1; Elim (H8 y0); Clear H8; Intros; Apply H8; Unfold intersection_domain; Split; Assumption.
Assert H11 := (disc_P1 x (mkposreal alp H9)); Unfold open_set in H11; Apply H11.
Unfold disc; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply H9.
Unfold alp; Apply MinRlist_P2; Intros; Assert H10 := (AbsList_P2 ? ? ? H9); Elim H10; Clear H10; Intros z H10; Elim H10; Clear H10; Intros; Rewrite H11; Apply H2; Elim (H8 z); Clear H8; Intros; Assert H13 := (H12 H10); Unfold intersection_domain D in H13; Elim H13; Clear H13; Intros; Assumption.
Unfold covering_open_set; Split.
Unfold covering; Intros; Exists x0; Simpl; Unfold g; Split.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Unfold Rminus in H2; Apply (H2 ? H5).
Apply H5.
Unfold family_open_set; Intro; Simpl; Unfold g; Elim (classic (D x0)); Intro.
Apply open_set_P6 with (disc x0 (mkposreal ? (H2 ? H5))).
Apply disc_P1.
Unfold eq_Dom; Split.
Unfold included disc; Simpl; Intros; Split.
Rewrite <- (Rabsolu_Ropp ``x0-x1``); Rewrite Ropp_distr2; Apply H6.
Apply H5.
Unfold included disc; Simpl; Intros; Elim H6; Intros; Rewrite <- (Rabsolu_Ropp ``x1-x0``); Rewrite Ropp_distr2; Apply H7.
Apply open_set_P6 with [z:R]False.
Apply open_set_P4.
Unfold eq_Dom; Split.
Unfold included; Intros; Elim H6.
Unfold included; Intros; Elim H6; Intros; Elim H5; Assumption.
Intros; Elim H3; Intros; Unfold g in H4; Elim H4; Clear H4; Intros _ H4; Apply H4.
Intros; Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rabsolu_pos_lt; Apply Rminus_eq_contra; Red; Intro; Rewrite H3 in H2; Elim H1; Apply H2.
Apply Rlt_Rinv; Sup0.
Qed.

(**********)
Lemma compact_EMP : (compact [_:R]False).
Unfold compact; Intros; Exists [x:R]False; Unfold covering_finite; Split.
Unfold covering; Intros; Elim H0.
Unfold family_finite; Unfold domain_finite; Exists nil; Intro.
Split.
Simpl; Unfold intersection_domain; Intros; Elim H0.
Elim H0; Clear H0; Intros _ H0; Elim H0.
Simpl; Intro; Elim H0.
Qed.

Lemma compact_eqDom : (X1,X2:R->Prop) (compact X1) -> X1 =_D X2 -> (compact X2).
Unfold compact; Intros; Unfold eq_Dom in H0; Elim H0; Clear H0; Unfold included; Intros; Assert H3 : (covering_open_set X1 f0).
Unfold covering_open_set; Unfold covering_open_set in H1; Elim H1; Clear H1; Intros; Split.
Unfold covering in H1; Unfold covering; Intros; Apply (H1 ? (H0 ? H4)).
Apply H3.
Elim (H ? H3); Intros D H4; Exists D; Unfold covering_finite; Unfold covering_finite in H4; Elim H4; Intros; Split.
Unfold covering in H5; Unfold covering; Intros; Apply (H5 ? (H2 ? H7)).
Apply H6.
Qed.

(* Borel-Lebesgue's lemma *)
Lemma compact_P3 : (a,b:R) (compact [c:R]``a<=c<=b``).
Intros; Case (total_order_Rle a b); Intro.
Unfold compact; Intros; Pose A := [x:R]``a<=x<=b``/\(EXT D:R->Prop | (covering_finite [c:R]``a <= c <= x`` (subfamily f0 D))); Cut (A a).
Intro; Cut (bound A).
Intro; Cut (EXT a0:R | (A a0)).
Intro; Assert H3 := (complet A H1 H2); Elim H3; Clear H3; Intros m H3; Unfold is_lub in H3; Cut ``a<=m<=b``.
Intro; Unfold covering_open_set in H; Elim H; Clear H; Intros; Unfold covering in H; Assert H6 := (H m H4); Elim H6; Clear H6; Intros y0 H6; Unfold family_open_set in H5; Assert H7 := (H5 y0); Unfold open_set in H7; Assert H8 := (H7 m H6); Unfold neighbourhood in H8; Elim H8; Clear H8; Intros eps H8; Cut (EXT x:R | (A x)/\``m-eps<x<=m``).
Intro; Elim H9; Clear H9; Intros x H9; Elim H9; Clear H9; Intros; Case (Req_EM m b); Intro.
Rewrite H11 in H10; Rewrite H11 in H8; Unfold A in H9; Elim H9; Clear H9; Intros; Elim H12; Clear H12; Intros Dx H12; Pose Db := [x:R](Dx x)\/x==y0; Exists Db; Unfold covering_finite; Split.
Unfold covering; Unfold covering_finite in H12; Elim H12; Clear H12; Intros; Unfold covering in H12; Case (total_order_Rle x0 x); Intro.
Cut ``a<=x0<=x``.
Intro; Assert H16 := (H12 x0 H15); Elim H16; Clear H16; Intros; Exists x1; Simpl in H16; Simpl; Unfold Db; Elim H16; Clear H16; Intros; Split; [Apply H16 | Left; Apply H17].
Split.
Elim H14; Intros; Assumption.
Assumption.
Exists y0; Simpl; Split.
Apply H8; Unfold disc; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Rewrite Rabsolu_right.
Apply Rlt_trans with ``b-x``.
Unfold Rminus; Apply Rlt_compatibility; Apply Rlt_Ropp; Auto with real.
Elim H10; Intros H15 _; Apply Rlt_anti_compatibility with ``x-eps``; Replace ``x-eps+(b-x)`` with ``b-eps``; [Replace ``x-eps+eps`` with x; [Apply H15 | Ring] | Ring].
Apply Rge_minus; Apply Rle_sym1; Elim H14; Intros _ H15; Apply H15.
Unfold Db; Right; Reflexivity.
Unfold family_finite; Unfold domain_finite; Unfold covering_finite in H12; Elim H12; Clear H12; Intros; Unfold family_finite in H13; Unfold domain_finite in H13; Elim H13; Clear H13; Intros l H13; Exists (cons y0 l); Intro; Split.
Intro; Simpl in H14; Unfold intersection_domain in H14; Elim (H13 x0); Clear H13; Intros; Case (Req_EM x0 y0); Intro.
Simpl; Left; Apply H16.
Simpl; Right; Apply H13.
Simpl; Unfold intersection_domain; Unfold Db in H14; Decompose [and or] H14.
Split; Assumption.
Elim H16; Assumption.
Intro; Simpl in H14; Elim H14; Intro; Simpl; Unfold intersection_domain.
Split.
Apply (cond_fam f0); Rewrite H15; Exists m; Apply H6.
Unfold Db; Right; Assumption.
Simpl; Unfold intersection_domain; Elim (H13 x0).
Intros _ H16; Assert H17 := (H16 H15); Simpl in H17; Unfold intersection_domain in H17; Split.
Elim H17; Intros; Assumption.
Unfold Db; Left; Elim H17; Intros; Assumption.
Pose m' := (Rmin ``m+eps/2`` b); Cut (A m').
Intro; Elim H3; Intros; Unfold is_upper_bound in H13; Assert H15 := (H13 m' H12); Cut ``m<m'``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H15 H16)).
Unfold m'; Unfold Rmin; Case (total_order_Rle ``m+eps/2`` b); Intro.
Pattern 1 m; Rewrite <- Rplus_Or; Apply Rlt_compatibility; Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos eps) | Apply Rlt_Rinv; Sup0].
Elim H4; Intros.
Elim H17; Intro.
Assumption.
Elim H11; Assumption.
Unfold A; Split.
Split.
Apply Rle_trans with m.
Elim H4; Intros; Assumption.
Unfold m'; Unfold Rmin; Case (total_order_Rle ``m+eps/2`` b); Intro.
Pattern 1 m; Rewrite <- Rplus_Or; Apply Rle_compatibility; Left; Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos eps) | Apply Rlt_Rinv; Sup0].
Elim H4; Intros.
Elim H13; Intro.
Assumption.
Elim H11; Assumption.
Unfold m'; Apply Rmin_r.
Unfold A in H9; Elim H9; Clear H9; Intros; Elim H12; Clear H12; Intros Dx H12; Pose Db := [x:R](Dx x)\/x==y0; Exists Db; Unfold covering_finite; Split.
Unfold covering; Unfold covering_finite in H12; Elim H12; Clear H12; Intros; Unfold covering in H12; Case (total_order_Rle x0 x); Intro.
Cut ``a<=x0<=x``.
Intro; Assert H16 := (H12 x0 H15); Elim H16; Clear H16; Intros; Exists x1; Simpl in H16; Simpl; Unfold Db.
Elim H16; Clear H16; Intros; Split; [Apply H16 | Left; Apply H17].
Elim H14; Intros; Split; Assumption.
Exists y0; Simpl; Split.
Apply H8; Unfold disc; Unfold Rabsolu; Case (case_Rabsolu ``x0-m``); Intro.
Rewrite Ropp_distr2; Apply Rlt_trans with ``m-x``.
Unfold Rminus; Apply Rlt_compatibility; Apply Rlt_Ropp; Auto with real.
Apply Rlt_anti_compatibility with ``x-eps``; Replace ``x-eps+(m-x)`` with ``m-eps``.
Replace ``x-eps+eps`` with x.
Elim H10; Intros; Assumption.
Ring.
Ring.
Apply Rle_lt_trans with ``m'-m``.
Unfold Rminus; Do 2 Rewrite <- (Rplus_sym ``-m``); Apply Rle_compatibility; Elim H14; Intros; Assumption.
Apply Rlt_anti_compatibility with m; Replace ``m+(m'-m)`` with m'.
Apply Rle_lt_trans with ``m+eps/2``.
Unfold m'; Apply Rmin_l.
Apply Rlt_compatibility; Apply Rlt_monotony_contra with ``2``.
Sup0.
Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l; Pattern 1 (pos eps); Rewrite <- Rplus_Or; Rewrite double; Apply Rlt_compatibility; Apply (cond_pos eps).
DiscrR.
Ring.
Unfold Db; Right; Reflexivity.
Unfold family_finite; Unfold domain_finite; Unfold covering_finite in H12; Elim H12; Clear H12; Intros; Unfold family_finite in H13; Unfold domain_finite in H13; Elim H13; Clear H13; Intros l H13; Exists (cons y0 l); Intro; Split.
Intro; Simpl in H14; Unfold intersection_domain in H14; Elim (H13 x0); Clear H13; Intros; Case (Req_EM x0 y0); Intro.
Simpl; Left; Apply H16.
Simpl; Right; Apply H13; Simpl; Unfold intersection_domain; Unfold Db in H14; Decompose [and or] H14.
Split; Assumption.
Elim H16; Assumption.
Intro; Simpl in H14; Elim H14; Intro; Simpl; Unfold intersection_domain.
Split.
Apply (cond_fam f0); Rewrite H15; Exists m; Apply H6.
Unfold Db; Right; Assumption.
Elim (H13 x0); Intros _ H16.
Assert H17 := (H16 H15).
Simpl in H17.
Unfold intersection_domain in H17.
Split.
Elim H17; Intros; Assumption.
Unfold Db; Left; Elim H17; Intros; Assumption.
Elim (classic (EXT x:R | (A x)/\``m-eps < x <= m``)); Intro.
Assumption.
Elim H3; Intros; Cut (is_upper_bound A ``m-eps``).
Intro; Assert H13 := (H11 ? H12); Cut ``m-eps<m``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H13 H14)).
Pattern 2 m; Rewrite <- Rplus_Or; Unfold Rminus; Apply Rlt_compatibility; Apply Ropp_Rlt; Rewrite Ropp_Ropp; Rewrite Ropp_O; Apply (cond_pos eps).
Pose P := [n:R](A n)/\``m-eps<n<=m``; Assert H12 := (not_ex_all_not ? P H9); Unfold P in H12; Unfold is_upper_bound; Intros; Assert H14 := (not_and_or ? ? (H12 x)); Elim H14; Intro.
Elim H15; Apply H13.
Elim (not_and_or ? ? H15); Intro.
Case (total_order_Rle x ``m-eps``); Intro.
Assumption.
Elim H16; Auto with real.
Unfold is_upper_bound in H10; Assert H17 := (H10 x H13); Elim H16; Apply H17.
Elim H3; Clear H3; Intros.
Unfold is_upper_bound in H3.
Split.
Apply (H3 ? H0).
Apply (H4 b); Unfold is_upper_bound; Intros; Unfold A in H5; Elim H5; Clear H5; Intros H5 _; Elim H5; Clear H5; Intros _ H5; Apply H5.
Exists a; Apply H0.
Unfold bound; Exists b; Unfold is_upper_bound; Intros; Unfold A in H1; Elim H1; Clear H1; Intros H1 _; Elim H1; Clear H1; Intros _ H1; Apply H1.
Unfold A; Split.
Split; [Right; Reflexivity | Apply r].
Unfold covering_open_set in H; Elim H; Clear H; Intros; Unfold covering in H; Cut ``a<=a<=b``.
Intro; Elim (H ? H1); Intros y0 H2; Pose D':=[x:R]x==y0; Exists D'; Unfold covering_finite; Split.
Unfold covering; Simpl; Intros; Cut x==a.
Intro; Exists y0; Split.
Rewrite H4; Apply H2.
Unfold D'; Reflexivity.
Elim H3; Intros; Apply Rle_antisym; Assumption.
Unfold family_finite; Unfold domain_finite; Exists (cons y0 nil); Intro; Split.
Simpl; Unfold intersection_domain; Intro; Elim H3; Clear H3; Intros; Unfold D' in H4; Left; Apply H4.
Simpl; Unfold intersection_domain; Intro; Elim H3; Intro.
Split; [Rewrite H4; Apply (cond_fam f0); Exists a; Apply H2 | Apply H4].
Elim H4.
Split; [Right; Reflexivity | Apply r].
Apply compact_eqDom with [c:R]False.
Apply compact_EMP.
Unfold eq_Dom; Split.
Unfold included; Intros; Elim H.
Unfold included; Intros; Elim H; Clear H; Intros; Assert H1 := (Rle_trans ? ? ? H H0); Elim n; Apply H1.
Qed.

Lemma compact_P4 : (X,F:R->Prop) (compact X) -> (closed_set F) -> (included F X) -> (compact F).
Unfold compact; Intros; Elim (classic (EXT z:R | (F z))); Intro Hyp_F_NE.
Pose D := (ind f0); Pose g := (f f0); Unfold closed_set in H0.
Pose g' := [x:R][y:R](f0 x y)\/((complementary F y)/\(D x)).
Pose D' := D.
Cut (x:R)(EXT y:R | (g' x y))->(D' x).
Intro; Pose f' := (mkfamily D' g' H3); Cut (covering_open_set X f').
Intro; Elim (H ? H4); Intros DX H5; Exists DX.
Unfold covering_finite; Unfold covering_finite in H5; Elim H5; Clear H5; Intros.
Split.
Unfold covering; Unfold covering in H5; Intros.
Elim (H5 ? (H1 ? H7)); Intros y0 H8; Exists y0; Simpl in H8; Simpl; Elim H8; Clear H8; Intros.
Split.
Unfold g' in H8; Elim H8; Intro.
Apply H10.
Elim H10; Intros H11 _; Unfold complementary in H11; Elim H11; Apply H7.
Apply H9.
Unfold family_finite; Unfold domain_finite; Unfold family_finite in H6; Unfold domain_finite in H6; Elim H6; Clear H6; Intros l H6; Exists l; Intro; Assert H7 := (H6 x); Elim H7; Clear H7; Intros.
Split.
Intro; Apply H7; Simpl; Unfold intersection_domain; Simpl in H9; Unfold intersection_domain in H9; Unfold D'; Apply H9.
Intro; Assert H10 := (H8 H9); Simpl in H10; Unfold intersection_domain in H10; Simpl; Unfold intersection_domain; Unfold D' in H10; Apply H10.
Unfold covering_open_set; Unfold covering_open_set in H2; Elim H2; Clear H2; Intros.
Split.
Unfold covering; Unfold covering in H2; Intros.
Elim (classic (F x)); Intro.
Elim (H2 ? H6); Intros y0 H7; Exists y0; Simpl; Unfold g'; Left; Assumption.
Cut (EXT z:R | (D z)).
Intro; Elim H7; Clear H7; Intros x0 H7; Exists x0; Simpl; Unfold g'; Right.
Split.
Unfold complementary; Apply H6.
Apply H7.
Elim Hyp_F_NE; Intros z0 H7.
Assert H8 := (H2 ? H7).
Elim H8; Clear H8; Intros t H8; Exists t; Apply (cond_fam f0); Exists z0; Apply H8.
Unfold family_open_set; Intro; Simpl; Unfold g'; Elim (classic (D x)); Intro.
Apply open_set_P6 with (union_domain (f0 x) (complementary F)).
Apply open_set_P2.
Unfold family_open_set in H4; Apply H4.
Apply H0.
Unfold eq_Dom; Split.
Unfold included union_domain complementary; Intros.
Elim H6; Intro; [Left; Apply H7 | Right; Split; Assumption].
Unfold included union_domain complementary; Intros.
Elim H6; Intro; [Left; Apply H7 | Right; Elim H7; Intros; Apply H8].
Apply open_set_P6 with (f0 x).
Unfold family_open_set in H4; Apply H4.
Unfold eq_Dom; Split.
Unfold included complementary; Intros; Left; Apply H6.
Unfold included complementary; Intros.
Elim H6; Intro.
Apply H7.
Elim H7; Intros _ H8; Elim H5; Apply H8.
Intros; Elim H3; Intros y0 H4; Unfold g' in H4; Elim H4; Intro.
Apply (cond_fam f0); Exists y0; Apply H5.
Elim H5; Clear H5; Intros _ H5; Apply H5.
(* Cas ou F est l'ensemble vide *)
Cut (compact F).
Intro; Apply (H3 f0 H2).
Apply compact_eqDom with [_:R]False.
Apply compact_EMP.
Unfold eq_Dom; Split.
Unfold included; Intros; Elim H3.
Assert H3 := (not_ex_all_not ? ? Hyp_F_NE); Unfold included; Intros; Elim (H3 x); Apply H4.
Qed.

(**********)
Lemma compact_P5 : (X:R->Prop) (closed_set X)->(bounded X)->(compact X).
Intros; Unfold bounded in H0.
Elim H0; Clear H0; Intros m H0.
Elim H0; Clear H0; Intros M H0.
Assert H1 := (compact_P3 m M).
Apply (compact_P4 [c:R]``m<=c<=M`` X H1 H H0).
Qed.

(**********)
Lemma compact_carac : (X:R->Prop) (compact X)<->(closed_set X)/\(bounded X).
Intro; Split.
Intro; Split; [Apply (compact_P2 ? H) | Apply (compact_P1 ? H)].
Intro; Elim H; Clear H; Intros; Apply (compact_P5 ? H H0).
Qed.

Definition image_dir [f:R->R;D:R->Prop] : R->Prop := [x:R](EXT y:R | x==(f y)/\(D y)).

(**********)
Lemma continuity_compact : (f:R->R;X:R->Prop) ((x:R)(continuity_pt f x)) -> (compact X) -> (compact (image_dir f X)).
Unfold compact; Intros; Unfold covering_open_set in H1.
Elim H1; Clear H1; Intros.
Pose D := (ind f1).
Pose g := [x:R][y:R](image_rec f0 (f1 x) y).
Cut (x:R)(EXT y:R | (g x y))->(D x).
Intro; Pose f' := (mkfamily D g H3).
Cut (covering_open_set X f').
Intro; Elim (H0 f' H4); Intros D' H5; Exists D'.
Unfold covering_finite in H5; Elim H5; Clear H5; Intros; Unfold covering_finite; Split.
Unfold covering image_dir; Simpl; Unfold covering in H5; Intros; Elim H7; Intros y H8; Elim H8; Intros; Assert H11 := (H5 ? H10); Simpl in H11; Elim H11; Intros z H12; Exists z; Unfold g in H12; Unfold image_rec in H12; Rewrite H9; Apply H12.
Unfold family_finite in H6; Unfold domain_finite in H6; Unfold family_finite; Unfold domain_finite; Elim H6; Intros l H7; Exists l; Intro; Elim (H7 x); Intros; Split; Intro.
Apply H8; Simpl in H10; Simpl; Apply H10.
Apply (H9 H10).
Unfold covering_open_set; Split.
Unfold covering; Intros; Simpl; Unfold covering in H1; Unfold image_dir in H1; Unfold g; Unfold image_rec; Apply H1.
Exists x; Split; [Reflexivity | Apply H4].
Unfold family_open_set; Unfold family_open_set in H2; Intro; Simpl; Unfold g; Cut ([y:R](image_rec f0 (f1 x) y))==(image_rec f0 (f1 x)).
Intro; Rewrite H4.
Apply (continuity_P2 f0 (f1 x) H (H2 x)).
Reflexivity.
Intros; Apply (cond_fam f1); Unfold g in H3; Unfold image_rec in H3; Elim H3; Intros; Exists (f0 x0); Apply H4.
Qed.

Lemma Rlt_Rminus : (a,b:R) ``a<b`` -> ``0<b-a``.
Intros; Apply Rlt_anti_compatibility with a; Rewrite Rplus_Or; Replace ``a+(b-a)`` with b; [Assumption | Ring].
Qed.

Lemma prolongement_C0 : (f:R->R;a,b:R) ``a<=b`` -> ((c:R)``a<=c<=b``->(continuity_pt f c)) -> (EXT g:R->R | (continuity g)/\((c:R)``a<=c<=b``->(g c)==(f c))).
Intros; Elim H; Intro.
Pose h := [x:R](Cases (total_order_Rle x a) of
  (leftT _) => (f0 a)
| (rightT _) => (Cases (total_order_Rle x b) of
       (leftT _) => (f0 x)
     | (rightT _) => (f0 b) end) end).
Assert H2 : ``0<b-a``.
Apply Rlt_Rminus; Assumption.
Exists h; Split.
Unfold continuity; Intro; Case (total_order x a); Intro.
Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros; Exists ``a-x``; Split.
Change ``0<a-x``; Apply Rlt_Rminus; Assumption.
Intros; Elim H5; Clear H5; Intros _ H5; Unfold h.
Case (total_order_Rle x a); Intro.
Case (total_order_Rle x0 a); Intro.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Elim n; Left; Apply Rlt_anti_compatibility with ``-x``; Do 2 Rewrite (Rplus_sym ``-x``); Apply Rle_lt_trans with ``(Rabsolu (x0-x))``.
Apply Rle_Rabsolu.
Assumption.
Elim n; Left; Assumption.
Elim H3; Intro.
Assert H5 : ``a<=a<=b``.
Split; [Right; Reflexivity | Left; Assumption].
Assert H6 := (H0 ? H5); Unfold continuity_pt in H6; Unfold continue_in in H6; Unfold limit1_in in H6; Unfold limit_in in H6; Simpl in H6; Unfold R_dist in H6; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros; Elim (H6 ? H7); Intros; Exists (Rmin x0 ``b-a``); Split.
Unfold Rmin; Case (total_order_Rle x0 ``b-a``); Intro.
Elim H8; Intros; Assumption.
Change ``0<b-a``; Apply Rlt_Rminus; Assumption.
Intros; Elim H9; Clear H9; Intros _ H9; Cut ``x1<b``.
Intro; Unfold h; Case (total_order_Rle x a); Intro.
Case (total_order_Rle x1 a); Intro.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Case (total_order_Rle x1 b); Intro.
Elim H8; Intros; Apply H12; Split.
Unfold D_x no_cond; Split.
Trivial.
Red; Intro; Elim n; Right; Symmetry; Assumption.
Apply Rlt_le_trans with (Rmin x0 ``b-a``).
Rewrite H4 in H9; Apply H9.
Apply Rmin_l.
Elim n0; Left; Assumption.
Elim n; Right; Assumption.
Apply Rlt_anti_compatibility with ``-a``; Do 2 Rewrite (Rplus_sym ``-a``); Rewrite H4 in H9; Apply Rle_lt_trans with ``(Rabsolu (x1-a))``.
Apply Rle_Rabsolu.
Apply Rlt_le_trans with ``(Rmin x0 (b-a))``.
Assumption.
Apply Rmin_r.
Case (total_order x b); Intro.
Assert H6 : ``a<=x<=b``.
Split; Left; Assumption.
Assert H7 := (H0 ? H6); Unfold continuity_pt in H7; Unfold continue_in in H7; Unfold limit1_in in H7; Unfold limit_in in H7; Simpl in H7; Unfold R_dist in H7; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros; Elim (H7 ? H8); Intros; Elim H9; Clear H9; Intros.
Assert H11 : ``0<x-a``.
Apply Rlt_Rminus; Assumption.
Assert H12 : ``0<b-x``.
Apply Rlt_Rminus; Assumption.
Exists (Rmin x0 (Rmin ``x-a`` ``b-x``)); Split.
Unfold Rmin; Case (total_order_Rle ``x-a`` ``b-x``); Intro.
Case (total_order_Rle x0 ``x-a``); Intro.
Assumption.
Assumption.
Case (total_order_Rle x0 ``b-x``); Intro.
Assumption.
Assumption.
Intros; Elim H13; Clear H13; Intros; Cut ``a<x1<b``.
Intro; Elim H15; Clear H15; Intros; Unfold h; Case (total_order_Rle x a); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H4)).
Case (total_order_Rle x b); Intro.
Case (total_order_Rle x1 a); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r0 H15)).
Case (total_order_Rle x1 b); Intro.
Apply H10; Split.
Assumption.
Apply Rlt_le_trans with ``(Rmin x0 (Rmin (x-a) (b-x)))``.
Assumption.
Apply Rmin_l.
Elim n1; Left; Assumption.
Elim n0; Left; Assumption.
Split.
Apply Ropp_Rlt; Apply Rlt_anti_compatibility with x; Apply Rle_lt_trans with ``(Rabsolu (x1-x))``.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply Rle_Rabsolu.
Apply Rlt_le_trans with ``(Rmin x0 (Rmin (x-a) (b-x)))``.
Assumption.
Apply Rle_trans with ``(Rmin (x-a) (b-x))``.
Apply Rmin_r.
Apply Rmin_l.
Apply Rlt_anti_compatibility with ``-x``; Do 2 Rewrite (Rplus_sym ``-x``); Apply Rle_lt_trans with ``(Rabsolu (x1-x))``.
Apply Rle_Rabsolu.
Apply Rlt_le_trans with ``(Rmin x0 (Rmin (x-a) (b-x)))``.
Assumption.
Apply Rle_trans with ``(Rmin (x-a) (b-x))``; Apply Rmin_r.
Elim H5; Intro.
Assert H7 : ``a<=b<=b``.
Split; [Left; Assumption | Right; Reflexivity].
Assert H8 := (H0 ? H7); Unfold continuity_pt in H8; Unfold continue_in in H8; Unfold limit1_in in H8; Unfold limit_in in H8; Simpl in H8; Unfold R_dist in H8; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros; Elim (H8 ? H9); Intros; Exists (Rmin x0 ``b-a``); Split.
Unfold Rmin; Case (total_order_Rle x0 ``b-a``); Intro.
Elim H10; Intros; Assumption.
Change ``0<b-a``; Apply Rlt_Rminus; Assumption.
Intros; Elim H11; Clear H11; Intros _ H11; Cut ``a<x1``.
Intro; Unfold h; Case (total_order_Rle x a); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H4)).
Case (total_order_Rle x1 a); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H12)).
Case (total_order_Rle x b); Intro.
Case (total_order_Rle x1 b); Intro.
Rewrite H6; Elim H10; Intros; Elim r0; Intro.
Apply H14; Split.
Unfold D_x no_cond; Split.
Trivial.
Red; Intro; Rewrite <- H16 in H15; Elim (Rlt_antirefl ? H15).
Rewrite H6 in H11; Apply Rlt_le_trans with ``(Rmin x0 (b-a))``.
Apply H11.
Apply Rmin_l.
Rewrite H15; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Rewrite H6; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Elim n1; Right; Assumption.
Rewrite H6 in H11; Apply Ropp_Rlt; Apply Rlt_anti_compatibility with b; Apply Rle_lt_trans with ``(Rabsolu (x1-b))``.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply Rle_Rabsolu.
Apply Rlt_le_trans with ``(Rmin x0 (b-a))``.
Assumption.
Apply Rmin_r.
Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros; Exists ``x-b``; Split.
Change ``0<x-b``; Apply Rlt_Rminus; Assumption.
Intros; Elim H8; Clear H8; Intros.
Assert H10 : ``b<x0``.
Apply Ropp_Rlt; Apply Rlt_anti_compatibility with x; Apply Rle_lt_trans with ``(Rabsolu (x0-x))``.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply Rle_Rabsolu.
Assumption.
Unfold h; Case (total_order_Rle x a); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H4)).
Case (total_order_Rle x b); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H6)).
Case (total_order_Rle x0 a); Intro.
Elim (Rlt_antirefl ? (Rlt_trans ? ? ? H1 (Rlt_le_trans ? ? ? H10 r))).
Case (total_order_Rle x0 b); Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? r H10)).
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Intros; Elim H3; Intros; Unfold h; Case (total_order_Rle c a); Intro.
Elim r; Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H4 H6)).
Rewrite H6; Reflexivity.
Case (total_order_Rle c b); Intro.
Reflexivity.
Elim n0; Assumption.
Exists [_:R](f0 a); Split.
Apply derivable_continuous; Apply (derivable_const (f0 a)).
Intros; Elim H2; Intros; Rewrite H1 in H3; Cut b==c.
Intro; Rewrite <- H5; Rewrite H1; Reflexivity.
Apply Rle_antisym; Assumption.
Qed.

(**********)
Lemma continuity_ab_maj : (f:R->R;a,b:R) ``a<=b`` -> ((c:R)``a<=c<=b``->(continuity_pt f c)) -> (EXT Mx : R |  ((c:R)``a<=c<=b``->``(f c)<=(f Mx)``)/\``a<=Mx<=b``).
Intros; Cut (EXT g:R->R | (continuity g)/\((c:R)``a<=c<=b``->(g c)==(f0 c))).
Intro HypProl.
Elim HypProl; Intros g Hcont_eq.
Elim Hcont_eq; Clear Hcont_eq; Intros Hcont Heq.
Assert H1 := (compact_P3 a b).
Assert H2 := (continuity_compact g [c:R]``a<=c<=b`` Hcont H1).
Assert H3 := (compact_P2 ? H2).
Assert H4 := (compact_P1 ? H2).
Cut (bound (image_dir g [c:R]``a <= c <= b``)).
Cut (ExT [x:R] ((image_dir g [c:R]``a <= c <= b``) x)).
Intros; Assert H7 := (complet ? H6 H5).
Elim H7; Clear H7; Intros M H7; Cut (image_dir g [c:R]``a <= c <= b`` M).
Intro; Unfold image_dir in H8; Elim H8; Clear H8; Intros Mxx H8; Elim H8; Clear H8; Intros; Exists Mxx; Split.
Intros; Rewrite <- (Heq c H10); Rewrite <- (Heq Mxx H9); Intros; Rewrite <- H8; Unfold is_lub in H7; Elim H7; Clear H7; Intros H7 _; Unfold is_upper_bound in H7; Apply H7; Unfold image_dir; Exists c; Split; [Reflexivity | Apply H10].
Apply H9.
Elim (classic (image_dir g [c:R]``a <= c <= b`` M)); Intro.
Assumption.
Cut (EXT eps:posreal | (y:R)~(intersection_domain (disc M eps) (image_dir g [c:R]``a <= c <= b``) y)).
Intro; Elim H9; Clear H9; Intros eps H9; Unfold is_lub in H7; Elim H7; Clear H7; Intros; Cut (is_upper_bound (image_dir g [c:R]``a <= c <= b``) ``M-eps``).
Intro; Assert H12 := (H10 ? H11); Cut ``M-eps<M``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H12 H13)).
Pattern 2 M; Rewrite <- Rplus_Or; Unfold Rminus; Apply Rlt_compatibility; Apply Ropp_Rlt; Rewrite Ropp_O; Rewrite Ropp_Ropp; Apply (cond_pos eps).
Unfold is_upper_bound image_dir; Intros; Cut ``x<=M``.
Intro; Case (total_order_Rle x ``M-eps``); Intro.
Apply r.
Elim (H9 x); Unfold intersection_domain disc image_dir; Split.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Rewrite Rabsolu_right.
Apply Rlt_anti_compatibility with ``x-eps``; Replace ``x-eps+(M-x)`` with ``M-eps``.
Replace ``x-eps+eps`` with x.
Auto with real.
Ring.
Ring.
Apply Rge_minus; Apply Rle_sym1; Apply H12.
Apply H11.
Apply H7; Apply H11.
Cut (EXT V:R->Prop | (neighbourhood V M)/\((y:R)~(intersection_domain V (image_dir g [c:R]``a <= c <= b``) y))).
Intro; Elim H9; Intros V H10; Elim H10; Clear H10; Intros.
Unfold neighbourhood in H10; Elim H10; Intros del H12; Exists del; Intros; Red; Intro; Elim (H11 y).
Unfold intersection_domain; Unfold intersection_domain in H13; Elim H13; Clear H13; Intros; Split.
Apply (H12 ? H13).
Apply H14.
Cut ~(point_adherent (image_dir g [c:R]``a <= c <= b``) M).
Intro; Unfold point_adherent in H9.
Assert H10 := (not_all_ex_not ? [V:R->Prop](neighbourhood V M)
            ->(EXT y:R |
                   (intersection_domain V
                     (image_dir g [c:R]``a <= c <= b``) y)) H9).
Elim H10; Intros V0 H11; Exists V0; Assert H12 := (imply_to_and ? ? H11); Elim H12; Clear H12; Intros.
Split.
Apply H12.
Apply (not_ex_all_not ? ? H13).
Red; Intro; Cut (adherence (image_dir g [c:R]``a <= c <= b``) M).
Intro; Elim (closed_set_P1 (image_dir g [c:R]``a <= c <= b``)); Intros H11 _; Assert H12 := (H11 H3).
Elim H8.
Unfold eq_Dom in H12; Elim H12; Clear H12; Intros.
Apply (H13 ? H10).
Apply H9.
Exists (g a); Unfold image_dir; Exists a; Split.
Reflexivity.
Split; [Right; Reflexivity | Apply H].
Unfold bound; Unfold bounded in H4; Elim H4; Clear H4; Intros m H4; Elim H4; Clear H4; Intros M H4; Exists M; Unfold is_upper_bound; Intros; Elim (H4 ? H5); Intros _ H6; Apply H6.
Apply prolongement_C0; Assumption.
Qed.

(**********)
Lemma continuity_ab_min : (f:(R->R); a,b:R) ``a <= b``->((c:R)``a<=c<=b``->(continuity_pt f c))->(EXT mx:R | ((c:R)``a <= c <= b``->``(f mx) <= (f c)``)/\``a <= mx <= b``).
Intros.
Cut ((c:R)``a<=c<=b``->(continuity_pt (opp_fct f0) c)).
Intro; Assert H2 := (continuity_ab_maj (opp_fct f0) a b H H1); Elim H2; Intros x0 H3; Exists x0; Intros; Split.
Intros; Rewrite <- (Ropp_Ropp (f0 x0)); Rewrite <- (Ropp_Ropp (f0 c)); Apply Rle_Ropp1; Elim H3; Intros; Unfold opp_fct in H5; Apply H5; Apply H4.
Elim H3; Intros; Assumption.
Intros.
Assert H2 := (H0 ? H1).
Apply (continuity_pt_opp ? ? H2).
Qed.


(********************************************************)
(*         Proof of Bolzano-Weierstrass theorem         *)
(********************************************************)

Definition ValAdh [un:nat->R;x:R] : Prop := (V:R->Prop;N:nat) (neighbourhood V x) -> (EX p:nat | (le N p)/\(V (un p))).

Definition intersection_family [f:family] : R->Prop := [x:R](y:R)(ind f y)->(f y x).

Lemma ValAdh_un_exists : (un:nat->R) let D=[x:R](EX n:nat | x==(INR n)) in let f=[x:R](adherence [y:R](EX p:nat | y==(un p)/\``x<=(INR p)``)/\(D x)) in ((x:R)(EXT y:R | (f x y))->(D x)).
Intros; Elim H; Intros; Unfold f in H0; Unfold adherence in H0; Unfold point_adherent in H0; Assert H1 : (neighbourhood (disc x0 (mkposreal ? Rlt_R0_R1)) x0).
Unfold neighbourhood disc; Exists (mkposreal ? Rlt_R0_R1); Unfold included; Trivial.
Elim (H0 ? H1); Intros; Unfold intersection_domain in H2; Elim H2; Intros; Elim H4; Intros; Apply H6.
Qed.

Definition ValAdh_un [un:nat->R] : R->Prop := let D=[x:R](EX n:nat | x==(INR n)) in let f=[x:R](adherence [y:R](EX p:nat | y==(un p)/\``x<=(INR p)``)/\(D x)) in (intersection_family (mkfamily D f (ValAdh_un_exists un))).

Lemma ValAdh_un_prop : (un:nat->R;x:R) (ValAdh un x) <-> (ValAdh_un un x).
Intros; Split; Intro.
Unfold ValAdh in H; Unfold ValAdh_un; Unfold intersection_family; Simpl; Intros; Elim H0; Intros N H1; Unfold adherence; Unfold point_adherent; Intros; Elim (H V N H2); Intros; Exists (un x0); Unfold intersection_domain; Elim H3; Clear H3; Intros; Split.
Assumption.
Split.
Exists x0; Split; [Reflexivity | Rewrite H1; Apply (le_INR ? ? H3)].
Exists N; Assumption.
Unfold ValAdh; Intros; Unfold ValAdh_un in H; Unfold intersection_family in H; Simpl in H; Assert H1 : (adherence [y0:R](EX p:nat | ``y0 == (un p)``/\``(INR N) <= (INR p)``)/\(EX n:nat | ``(INR N) == (INR n)``) x).
Apply H; Exists N; Reflexivity.
Unfold adherence in H1; Unfold point_adherent in H1; Assert H2 := (H1 ? H0); Elim H2; Intros; Unfold intersection_domain in H3; Elim H3; Clear H3; Intros; Elim H4; Clear H4; Intros; Elim H4; Clear H4; Intros; Elim H4; Clear H4; Intros; Exists x1; Split.
Apply (INR_le ? ? H6).
Rewrite H4 in H3; Apply H3.
Qed.

Lemma adherence_P4 : (F,G:R->Prop) (included F G) -> (included (adherence F) (adherence G)).
Unfold adherence included; Unfold point_adherent; Intros; Elim (H0 ? H1); Unfold intersection_domain; Intros; Elim H2; Clear H2; Intros; Exists x0; Split; [Assumption | Apply (H ? H3)].
Qed.

Definition family_closed_set [f:family] : Prop := (x:R) (closed_set (f x)).

Definition intersection_vide_in [D:R->Prop;f:family] : Prop := ((x:R)((ind f x)->(included (f x) D))/\~(EXT y:R | (intersection_family f y))).

Definition intersection_vide_finite_in [D:R->Prop;f:family] : Prop := (intersection_vide_in D f)/\(family_finite f).

(**********)
Lemma compact_P6 : (X:R->Prop) (compact X) -> (EXT z:R | (X z)) -> ((g:family) (family_closed_set g) -> (intersection_vide_in X g) -> (EXT D:R->Prop | (intersection_vide_finite_in X (subfamily g D)))).
Intros X H Hyp g H0 H1.
Pose D' := (ind g).
Pose f' := [x:R][y:R](complementary (g x) y)/\(D' x).
Assert H2 : (x:R)(EXT y:R|(f' x y))->(D' x).
Intros; Elim H2; Intros; Unfold f' in H3; Elim H3; Intros; Assumption.
Pose f0 := (mkfamily D' f' H2).
Unfold compact in H; Assert H3 : (covering_open_set X f0).
Unfold covering_open_set; Split.
Unfold covering; Intros; Unfold intersection_vide_in in H1; Elim (H1 x); Intros; Unfold intersection_family in H5; Assert H6 := (not_ex_all_not ? [y:R](y0:R)(ind g y0)->(g y0 y) H5 x); Assert H7 := (not_all_ex_not ? [y0:R](ind g y0)->(g y0 x) H6); Elim H7; Intros; Exists x0; Elim (imply_to_and ? ? H8); Intros; Unfold f0; Simpl; Unfold f'; Split; [Apply H10 | Apply H9].
Unfold family_open_set; Intro; Elim (classic (D' x)); Intro.
Apply open_set_P6 with (complementary (g x)).
Unfold family_closed_set in H0; Unfold closed_set in H0; Apply H0.
Unfold f0; Simpl; Unfold f'; Unfold eq_Dom; Split.
Unfold included; Intros; Split; [Apply H4 | Apply H3].
Unfold included; Intros; Elim H4; Intros; Assumption.
Apply open_set_P6 with [_:R]False.
Apply open_set_P4.
Unfold eq_Dom; Unfold included; Split; Intros; [Elim H4 | Simpl in H4; Unfold f' in H4; Elim H4; Intros; Elim H3; Assumption].
Elim (H ? H3); Intros SF H4; Exists SF; Unfold intersection_vide_finite_in; Split.
Unfold intersection_vide_in; Simpl; Intros; Split.
Intros; Unfold included; Intros; Unfold intersection_vide_in in H1; Elim (H1 x); Intros; Elim H6; Intros; Apply H7.
Unfold intersection_domain in H5; Elim H5; Intros; Assumption.
Assumption.
Elim (classic (EXT y:R | (intersection_domain (ind g) SF y))); Intro Hyp'.
Red; Intro; Elim H5; Intros; Unfold intersection_family in H6; Simpl in H6.
Cut (X x0).
Intro; Unfold covering_finite in H4; Elim H4; Clear H4; Intros H4 _; Unfold covering in H4; Elim (H4 x0 H7); Intros; Simpl in H8; Unfold intersection_domain in H6; Cut (ind g x1)/\(SF x1).
Intro; Assert H10 := (H6 x1 H9); Elim H10; Clear H10; Intros H10 _; Elim H8; Clear H8; Intros H8 _; Unfold f' in H8; Unfold complementary in H8; Elim H8; Clear H8; Intros H8 _; Elim H8; Assumption.
Split.
Apply (cond_fam f0).
Exists x0; Elim H8; Intros; Assumption.
Elim H8; Intros; Assumption.
Unfold intersection_vide_in in H1; Elim Hyp'; Intros; Assert H8 := (H6 ? H7); Elim H8; Intros; Cut (ind g x1).
Intro; Elim (H1 x1); Intros; Apply H12.
Apply H11.
Apply H9.
Apply (cond_fam g); Exists x0; Assumption.
Unfold covering_finite in H4; Elim H4; Clear H4; Intros H4 _; Cut (EXT z:R | (X z)).
Intro; Elim H5; Clear H5; Intros; Unfold covering in H4; Elim (H4 x0 H5); Intros; Simpl in H6; Elim Hyp'; Exists x1; Elim H6; Intros; Unfold intersection_domain; Split.
Apply (cond_fam f0); Exists x0; Apply H7.
Apply H8.
Apply Hyp.
Unfold covering_finite in H4; Elim H4; Clear H4; Intros; Unfold family_finite in H5; Unfold domain_finite in H5; Unfold family_finite; Unfold domain_finite; Elim H5; Clear H5; Intros l H5; Exists l; Intro; Elim (H5 x); Intros; Split; Intro; [Apply H6; Simpl; Simpl in H8; Apply H8 | Apply (H7 H8)].
Qed.

Theorem Bolzano_Weierstrass : (un:nat->R;X:R->Prop) (compact X) -> ((n:nat)(X (un n))) -> (EXT l:R | (ValAdh un l)).
Intros; Cut (EXT l:R | (ValAdh_un un l)).
Intro; Elim H1; Intros; Exists x; Elim (ValAdh_un_prop un x); Intros; Apply (H4 H2).
Assert H1 : (EXT z:R | (X z)).
Exists (un O); Apply H0.
Pose D:=[x:R](EX n:nat | x==(INR n)).
Pose g:=[x:R](adherence [y:R](EX p:nat | y==(un p)/\``x<=(INR p)``)/\(D x)).
Assert H2 : (x:R)(EXT y:R | (g x y))->(D x).
Intros; Elim H2; Intros; Unfold g in H3; Unfold adherence in H3; Unfold point_adherent in H3.
Assert H4 : (neighbourhood (disc x0 (mkposreal ? Rlt_R0_R1)) x0).
Unfold neighbourhood; Exists (mkposreal ? Rlt_R0_R1); Unfold included; Trivial.
Elim (H3 ? H4); Intros; Unfold intersection_domain in H5; Decompose [and] H5; Assumption.
Pose f0 := (mkfamily D g H2).
Assert H3 := (compact_P6 X H H1 f0).
Elim (classic (EXT l:R | (ValAdh_un un l))); Intro.
Assumption.
Cut (family_closed_set f0).
Intro; Cut (intersection_vide_in X f0).
Intro; Assert H7 := (H3 H5 H6).
Elim H7; Intros SF H8; Unfold intersection_vide_finite_in in H8; Elim H8; Clear H8; Intros; Unfold intersection_vide_in in H8; Elim (H8 R0); Intros _ H10; Elim H10; Unfold family_finite in H9; Unfold domain_finite in H9; Elim H9; Clear H9; Intros l H9; Pose r := (MaxRlist l); Cut (D r).
Intro; Unfold D in H11; Elim H11; Intros; Exists (un x); Unfold intersection_family; Simpl; Unfold intersection_domain; Intros; Split.
Unfold g; Apply adherence_P1; Split.
Exists x; Split; [Reflexivity | Rewrite <- H12; Unfold r; Apply MaxRlist_P1; Elim (H9 y); Intros; Apply H14; Simpl; Apply H13].
Elim H13; Intros; Assumption.
Elim H13; Intros; Assumption.
Elim (H9 r); Intros.
Simpl in H12; Unfold intersection_domain in H12; Cut (In r l).
Intro; Elim (H12 H13); Intros; Assumption.
Unfold r; Apply MaxRlist_P2; Cut (EXT z:R | (intersection_domain (ind f0) SF z)).
Intro; Elim H13; Intros; Elim (H9 x); Intros; Simpl in H15; Assert H17 := (H15 H14); Exists x; Apply H17.
Elim (classic (EXT z:R | (intersection_domain (ind f0) SF z))); Intro.
Assumption.
Elim (H8 R0); Intros _ H14; Elim H1; Intros; Assert H16 := (not_ex_all_not ? [y:R](intersection_family (subfamily f0 SF) y) H14); Assert H17 := (not_ex_all_not ? [z:R](intersection_domain (ind f0) SF z) H13); Assert H18 := (H16 x); Unfold intersection_family in H18; Simpl in H18; Assert H19 := (not_all_ex_not ? [y:R](intersection_domain D SF y)->(g y x)/\(SF y) H18); Elim H19; Intros; Assert H21 := (imply_to_and ? ? H20); Elim (H17 x0); Elim H21; Intros; Assumption.
Unfold intersection_vide_in; Intros; Split.
Intro; Simpl in H6; Unfold f0; Simpl; Unfold g; Apply included_trans with (adherence X).
Apply adherence_P4.
Unfold included; Intros; Elim H7; Intros; Elim H8; Intros; Elim H10; Intros; Rewrite H11; Apply H0.
Apply adherence_P2; Apply compact_P2; Assumption.
Apply H4.
Unfold family_closed_set; Unfold f0; Simpl; Unfold g; Intro; Apply adherence_P3.
Qed.

(********************************************************)
(*               Proof of Heine's theorem               *)
(********************************************************)

Definition uniform_continuity [f:R->R;X:R->Prop] : Prop := (eps:posreal)(EXT delta:posreal | (x,y:R) (X x)->(X y)->``(Rabsolu (x-y))<delta`` ->``(Rabsolu ((f x)-(f y)))<eps``).

Lemma is_lub_u : (E:R->Prop;x,y:R) (is_lub E x) -> (is_lub E y) -> x==y.
Unfold is_lub; Intros; Elim H; Elim H0; Intros; Apply Rle_antisym; [Apply (H4 ? H1) | Apply (H2 ? H3)].
Qed.

Lemma domain_P1 : (X:R->Prop) ~(EXT y:R | (X y))\/(EXT y:R | (X y)/\((x:R)(X x)->x==y))\/(EXT x:R | (EXT y:R | (X x)/\(X y)/\``x<>y``)).
Intro; Elim (classic (EXT y:R | (X y))); Intro.
Right; Elim H; Intros; Elim (classic (EXT y:R | (X y)/\``y<>x``)); Intro.
Right; Elim H1; Intros; Elim H2; Intros; Exists x; Exists x0; Intros.
Split; [Assumption | Split; [Assumption | Apply not_sym; Assumption]].
Left; Exists x; Split.
Assumption.
Intros; Case (Req_EM x0 x); Intro.
Assumption.
Elim H1; Exists x0; Split; Assumption.
Left; Assumption.
Qed.

Theorem Heine : (f:R->R;X:R->Prop) (compact X) -> ((x:R)(X x)->(continuity_pt f x)) -> (uniform_continuity f X).
Intros f0 X H0 H; Elim (domain_P1 X); Intro Hyp.
(* X est vide *)
Unfold uniform_continuity; Intros; Exists (mkposreal ? Rlt_R0_R1); Intros; Elim Hyp; Exists x; Assumption.
Elim Hyp; Clear Hyp; Intro Hyp.
(* X possède un seul élément *)
Unfold uniform_continuity; Intros; Exists (mkposreal ? Rlt_R0_R1); Intros; Elim Hyp; Clear Hyp; Intros; Elim H4; Clear H4; Intros; Assert H6 := (H5 ? H1); Assert H7 := (H5 ? H2); Rewrite H6; Rewrite H7; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply (cond_pos eps).
(* X possède au moins deux éléments distincts *)
Assert X_enc : (EXT m:R | (EXT M:R | ((x:R)(X x)->``m<=x<=M``)/\``m<M``)).
Assert H1 := (compact_P1 X H0); Unfold bounded in H1; Elim H1; Intros; Elim H2; Intros; Exists x; Exists x0; Split.
Apply H3.
Elim Hyp; Intros; Elim H4; Intros; Decompose [and] H5; Assert H10 := (H3 ? H6); Assert H11 := (H3 ? H8); Elim H10; Intros; Elim H11; Intros; Case (total_order_T x x0); Intro.
Elim s; Intro.
Assumption.
Rewrite b in H13; Rewrite b in H7; Elim H9; Apply Rle_antisym; Apply Rle_trans with x0; Assumption.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? (Rle_trans ? ? ? H13 H14) r)).
Elim X_enc; Clear X_enc; Intros m X_enc; Elim X_enc; Clear X_enc; Intros M X_enc; Elim X_enc; Clear X_enc Hyp; Intros X_enc Hyp; Unfold uniform_continuity; Intro; Assert H1 : (t:posreal)``0<t/2``.
Intro; Unfold Rdiv; Apply Rmult_lt_pos; [Apply (cond_pos t) | Apply Rlt_Rinv; Sup0].
Pose g := [x:R][y:R](X x)/\(EXT del:posreal | ((z:R) ``(Rabsolu (z-x))<del``->``(Rabsolu ((f0 z)-(f0 x)))<eps/2``)/\(is_lub [zeta:R]``0<zeta<=M-m``/\((z:R) ``(Rabsolu (z-x))<zeta``->``(Rabsolu ((f0 z)-(f0 x)))<eps/2``) del)/\(disc x (mkposreal ``del/2`` (H1 del)) y)).
Assert H2 : (x:R)(EXT y:R | (g x y))->(X x).
Intros; Elim H2; Intros; Unfold g in H3; Elim H3; Clear H3; Intros H3 _; Apply H3.
Pose f' := (mkfamily X g H2); Unfold compact in H0; Assert H3 : (covering_open_set X f').
Unfold covering_open_set; Split.
Unfold covering; Intros; Exists x; Simpl; Unfold g; Split.
Assumption.
Assert H4 := (H ? H3); Unfold continuity_pt in H4; Unfold continue_in in H4; Unfold limit1_in in H4; Unfold limit_in in H4; Simpl in H4; Unfold R_dist in H4; Elim (H4 ``eps/2`` (H1 eps)); Intros; Pose E:=[zeta:R]``0<zeta <= M-m``/\((z:R)``(Rabsolu (z-x)) < zeta``->``(Rabsolu ((f0 z)-(f0 x))) < eps/2``); Assert H6 : (bound E).
Unfold bound; Exists ``M-m``; Unfold is_upper_bound; Unfold E; Intros; Elim H6; Clear H6; Intros H6 _; Elim H6; Clear H6; Intros _ H6; Apply H6.
Assert H7 : (EXT x:R | (E x)).
Elim H5; Clear H5; Intros; Exists (Rmin x0 ``M-m``); Unfold E; Intros; Split.
Split.
Unfold Rmin; Case (total_order_Rle x0 ``M-m``); Intro.
Apply H5.
Apply Rlt_Rminus; Apply Hyp.
Apply Rmin_r.
Intros; Case (Req_EM x z); Intro.
Rewrite H9; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply (H1 eps).
Apply H7; Split.
Unfold D_x no_cond; Split; [Trivial | Assumption].
Apply Rlt_le_trans with (Rmin x0 ``M-m``); [Apply H8 | Apply Rmin_l].
Assert H8 := (complet ? H6 H7); Elim H8; Clear H8; Intros; Cut ``0<x1<=(M-m)``.
Intro; Elim H8; Clear H8; Intros; Exists (mkposreal ? H8); Split.
Intros; Cut (EXT alp:R | ``(Rabsolu (z-x))<alp<=x1``/\(E alp)).
Intros; Elim H11; Intros; Elim H12; Clear H12; Intros; Unfold E in H13; Elim H13; Intros; Apply H15.
Elim H12; Intros; Assumption.
Elim (classic (EXT alp:R | ``(Rabsolu (z-x)) < alp <= x1``/\(E alp))); Intro.
Assumption.
Assert H12 := (not_ex_all_not ? [alp:R]``(Rabsolu (z-x)) < alp <= x1``/\(E alp) H11); Unfold is_lub in p; Elim p; Intros; Cut (is_upper_bound E ``(Rabsolu (z-x))``).
Intro; Assert H16 := (H14 ? H15); Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H10 H16)).
Unfold is_upper_bound; Intros; Unfold is_upper_bound in H13; Assert H16 := (H13 ? H15); Case (total_order_Rle x2 ``(Rabsolu (z-x))``); Intro.
Assumption.
Elim (H12 x2); Split; [Split; [Auto with real | Assumption] | Assumption].
Split.
Apply p.
Unfold disc; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Simpl; Unfold Rdiv; Apply Rmult_lt_pos; [Apply H8 | Apply Rlt_Rinv; Sup0].
Elim H7; Intros; Unfold E in H8; Elim H8; Intros H9 _; Elim H9; Intros H10 _; Unfold is_lub in p; Elim p; Intros; Unfold is_upper_bound in H12; Unfold is_upper_bound in H11; Split.
Apply Rlt_le_trans with x2; [Assumption | Apply (H11 ? H8)].
Apply H12; Intros; Unfold E in H13; Elim H13; Intros; Elim H14; Intros; Assumption.
Unfold family_open_set; Intro; Simpl; Elim (classic (X x)); Intro.
Unfold g; Unfold open_set; Intros; Elim H4; Clear H4; Intros _ H4; Elim H4; Clear H4; Intros; Elim H4; Clear H4; Intros; Unfold neighbourhood; Case (Req_EM x x0); Intro.
Exists (mkposreal ? (H1 x1)); Rewrite <- H6; Unfold included; Intros; Split.
Assumption.
Exists x1; Split.
Apply H4.
Split.
Elim H5; Intros; Apply H8.
Apply H7.
Pose d := ``x1/2-(Rabsolu (x0-x))``; Assert H7 : ``0<d``.
Unfold d; Apply Rlt_Rminus; Elim H5; Clear H5; Intros; Unfold disc in H7; Apply H7.
Exists (mkposreal ? H7); Unfold included; Intros; Split.
Assumption.
Exists x1; Split.
Apply H4.
Elim H5; Intros; Split.
Assumption.
Unfold disc in H8; Simpl in H8; Unfold disc; Simpl; Unfold disc in H10; Simpl in H10; Apply Rle_lt_trans with ``(Rabsolu (x2-x0))+(Rabsolu (x0-x))``.
Replace ``x2-x`` with ``(x2-x0)+(x0-x)``; [Apply Rabsolu_triang | Ring].
Replace ``x1/2`` with ``d+(Rabsolu (x0-x))``; [Idtac | Unfold d; Ring].
Do 2 Rewrite <- (Rplus_sym ``(Rabsolu (x0-x))``); Apply Rlt_compatibility; Apply H8.
Apply open_set_P6 with [_:R]False.
Apply open_set_P4.
Unfold eq_Dom; Unfold included; Intros; Split.
Intros; Elim H4.
Intros; Unfold g in H4; Elim H4; Clear H4; Intros H4 _; Elim H3; Apply H4.
Elim (H0 ? H3); Intros DF H4; Unfold covering_finite in H4; Elim H4; Clear H4; Intros; Unfold family_finite in H5; Unfold domain_finite in H5; Unfold covering in H4; Simpl in H4; Simpl in H5; Elim H5; Clear H5; Intros l H5; Unfold intersection_domain in H5; Cut (x:R)(In x l)->(EXT del:R | ``0<del``/\((z:R)``(Rabsolu (z-x)) < del``->``(Rabsolu ((f0 z)-(f0 x))) < eps/2``)/\(included (g x) [z:R]``(Rabsolu (z-x))<del/2``)).
Intros; Assert H7 := (Rlist_P1 l [x:R][del:R]``0<del``/\((z:R)``(Rabsolu (z-x)) < del``->``(Rabsolu ((f0 z)-(f0 x))) < eps/2``)/\(included (g x) [z:R]``(Rabsolu (z-x))<del/2``) H6); Elim H7; Clear H7; Intros l' H7; Elim H7; Clear H7; Intros; Pose D := (MinRlist l'); Cut ``0<D/2``.
Intro; Exists (mkposreal ? H9); Intros; Assert H13 := (H4 ? H10); Elim H13; Clear H13; Intros xi H13; Assert H14 : (In xi l).
Unfold g in H13; Decompose [and] H13; Elim (H5 xi); Intros; Apply H14; Split; Assumption.
Elim (pos_Rl_P2 l xi); Intros H15 _; Elim (H15 H14); Intros i H16; Elim H16; Intros; Apply Rle_lt_trans with ``(Rabsolu ((f0 x)-(f0 xi)))+(Rabsolu ((f0 xi)-(f0 y)))``.
Replace ``(f0 x)-(f0 y)`` with ``((f0 x)-(f0 xi))+((f0 xi)-(f0 y))``; [Apply Rabsolu_triang | Ring].
Rewrite (double_var eps); Apply Rplus_lt.
Assert H19 := (H8 i H17); Elim H19; Clear H19; Intros; Rewrite <- H18 in H20; Elim H20; Clear H20; Intros; Apply H20; Unfold included in H21; Apply Rlt_trans with ``(pos_Rl l' i)/2``.
Apply H21.
Elim H13; Clear H13; Intros; Assumption.
Unfold Rdiv; Apply Rlt_monotony_contra with ``2``.
Sup0.
Rewrite Rmult_sym; Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Pattern 1 (pos_Rl l' i); Rewrite <- Rplus_Or; Rewrite double; Apply Rlt_compatibility; Apply H19.
DiscrR.
Assert H19 := (H8 i H17); Elim H19; Clear H19; Intros; Rewrite <- H18 in H20; Elim H20; Clear H20; Intros; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H20; Unfold included in H21; Elim H13; Intros; Assert H24 := (H21 x H22); Apply Rle_lt_trans with ``(Rabsolu (y-x))+(Rabsolu (x-xi))``.
Replace ``y-xi`` with ``(y-x)+(x-xi)``; [Apply Rabsolu_triang | Ring].
Rewrite (double_var (pos_Rl l' i)); Apply Rplus_lt.
Apply Rlt_le_trans with ``D/2``.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H12.
Unfold Rdiv; Do 2 Rewrite <- (Rmult_sym ``/2``); Apply Rle_monotony.
Left; Apply Rlt_Rinv; Sup0.
Unfold D; Apply MinRlist_P1; Elim (pos_Rl_P2 l' (pos_Rl l' i)); Intros; Apply H26; Exists i; Split; [Rewrite <- H7; Assumption | Reflexivity].
Assumption.
Unfold Rdiv; Apply Rmult_lt_pos; [Unfold D; Apply MinRlist_P2; Intros; Elim (pos_Rl_P2 l' y); Intros; Elim (H10 H9); Intros; Elim H12; Intros; Rewrite H14; Rewrite <- H7 in H13; Elim (H8 x H13); Intros; Apply H15 | Apply Rlt_Rinv; Sup0].
Intros; Elim (H5 x); Intros; Elim (H8 H6); Intros; Pose E:=[zeta:R]``0<zeta <= M-m``/\((z:R)``(Rabsolu (z-x)) < zeta``->``(Rabsolu ((f0 z)-(f0 x))) < eps/2``); Assert H11 : (bound E).
Unfold bound; Exists ``M-m``; Unfold is_upper_bound; Unfold E; Intros; Elim H11; Clear H11; Intros H11 _; Elim H11; Clear H11; Intros _ H11; Apply H11.
Assert H12 : (EXT x:R | (E x)).
Assert H13 := (H ? H9); Unfold continuity_pt in H13; Unfold continue_in in H13; Unfold limit1_in in H13; Unfold limit_in in H13; Simpl in H13; Unfold R_dist in H13; Elim (H13 ? (H1 eps)); Intros; Elim H12; Clear H12; Intros; Exists (Rmin x0 ``M-m``); Unfold E; Intros; Split.
Split; [Unfold Rmin; Case (total_order_Rle x0 ``M-m``); Intro; [Apply H12 | Apply Rlt_Rminus; Apply Hyp] | Apply Rmin_r].
Intros; Case (Req_EM x z); Intro.
Rewrite H16; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply (H1 eps).
Apply H14; Split; [Unfold D_x no_cond; Split; [Trivial | Assumption] | Apply Rlt_le_trans with (Rmin x0 ``M-m``); [Apply H15 | Apply Rmin_l]].
Assert H13 := (complet ? H11 H12); Elim H13; Clear H13; Intros; Cut ``0<x0<=M-m``.
Intro; Elim H13; Clear H13; Intros; Exists x0; Split.
Assumption.
Split.
Intros; Cut (EXT alp:R | ``(Rabsolu (z-x))<alp<=x0``/\(E alp)).
Intros; Elim H16; Intros; Elim H17; Clear H17; Intros; Unfold E in H18; Elim H18; Intros; Apply H20; Elim H17; Intros; Assumption.
Elim (classic (EXT alp:R | ``(Rabsolu (z-x)) < alp <= x0``/\(E alp))); Intro.
Assumption.
Assert H17 := (not_ex_all_not ? [alp:R]``(Rabsolu (z-x)) < alp <= x0``/\(E alp) H16); Unfold is_lub in p; Elim p; Intros; Cut (is_upper_bound E ``(Rabsolu (z-x))``).
Intro; Assert H21 := (H19 ? H20); Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H15 H21)).
Unfold is_upper_bound; Intros; Unfold is_upper_bound in H18; Assert H21 := (H18 ? H20); Case (total_order_Rle x1 ``(Rabsolu (z-x))``); Intro.
Assumption.
Elim (H17 x1); Split.
Split; [Auto with real | Assumption].
Assumption.
Unfold included g; Intros; Elim H15; Intros; Elim H17; Intros; Decompose [and] H18; Cut x0==x2.
Intro; Rewrite H20; Apply H22.
Unfold E in p; EApply is_lub_u.
Apply p.
Apply H21.
Elim H12; Intros; Unfold E in H13; Elim H13; Intros H14 _; Elim H14; Intros H15 _; Unfold is_lub in p; Elim p; Intros; Unfold is_upper_bound in H16; Unfold is_upper_bound in H17; Split.
Apply Rlt_le_trans with x1; [Assumption | Apply (H16 ? H13)].
Apply H17; Intros; Unfold E in H18; Elim H18; Intros; Elim H19; Intros; Assumption.
Qed.

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
Require DiscrR.
Require Rderiv.
Require Alembert.
Require Ranalysis1.
Require Classical_Prop.
Require Classical_Pred_Type.

Definition inclus [D1,D2:R->Prop] : Prop := (x:R)(D1 x)->(D2 x).
Definition Disque [x:R;delta:posreal] : R->Prop := [y:R]``(Rabsolu (y-x))<delta``.
Definition voisinage [V:R->Prop;x:R] : Prop := (EXT delta:posreal | (inclus (Disque x delta) V)).
(* Une partie est ouverte ssi c'est un voisinage de chacun de ses points *)
Definition ouvert [D:R->Prop] : Prop := (x:R) (D x)->(voisinage D x).
Definition complementaire [D:R->Prop] : R->Prop := [c:R]~(D c).
Definition ferme [D:R->Prop] : Prop := (ouvert (complementaire D)).
Definition intersection_domaine [D1,D2:R->Prop] : R->Prop := [c:R](D1 c)/\(D2 c).
Definition union_domaine [D1,D2:R->Prop] : R->Prop := [c:R](D1 c)\/(D2 c).
Definition interieur [D:R->Prop] : R->Prop := [x:R](voisinage D x).

(* D° est inclus dans D *)
Lemma interieur_P1 : (D:R->Prop) (inclus (interieur D) D).
Intros; Unfold inclus; Unfold interieur; Intros; Unfold voisinage in H; Elim H; Intros; Unfold inclus in H0; Apply H0; Unfold Disque; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply (cond_pos x0).
Qed.

Lemma interieur_P2 : (D:R->Prop) (ouvert D) -> (inclus D (interieur D)).
Intros; Unfold ouvert in H; Unfold inclus; Intros; Assert H1 := (H ? H0); Unfold interieur; Apply H1.
Qed.

Definition point_adherent [D:R->Prop;x:R] : Prop := (V:R->Prop) (voisinage V x) -> (EXT y:R | (intersection_domaine V D y)).
Definition adherence [D:R->Prop] : R->Prop := [x:R](point_adherent D x).

Lemma adherence_P1 : (D:R->Prop) (inclus D (adherence D)).
Intro; Unfold inclus; Intros; Unfold adherence; Unfold point_adherent; Intros; Exists x; Unfold intersection_domaine; Split.
Unfold voisinage in H0; Elim H0; Intros; Unfold inclus in H1; Apply H1; Unfold Disque; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply (cond_pos x0).
Apply H.
Qed.

Lemma inclus_trans : (D1,D2,D3:R->Prop) (inclus D1 D2) -> (inclus D2 D3) -> (inclus D1 D3).
Unfold inclus; Intros; Apply H0; Apply H; Apply H1.
Qed.

(* D° est ouvert *)
Lemma interieur_P3 : (D:R->Prop) (ouvert (interieur D)).
Intro; Unfold ouvert interieur; Unfold voisinage; Intros; Elim H; Intros.
Exists x0; Unfold inclus; Intros.
Pose del := ``x0-(Rabsolu (x-x1))``.
Cut ``0<del``.
Intro; Exists (mkposreal del H2); Intros.
Cut (inclus (Disque x1 (mkposreal del H2)) (Disque x x0)).
Intro; Assert H5 := (inclus_trans ? ? ? H4 H0).
Apply H5; Apply H3.
Unfold inclus; Unfold Disque; Intros.
Apply Rle_lt_trans with ``(Rabsolu (x3-x1))+(Rabsolu (x1-x))``.
Replace ``x3-x`` with ``(x3-x1)+(x1-x)``; [Apply Rabsolu_triang | Ring].
Replace (pos x0) with ``del+(Rabsolu (x1-x))``.
Do 2 Rewrite <- (Rplus_sym (Rabsolu ``x1-x``)); Apply Rlt_compatibility; Apply H4.
Unfold del; Rewrite <- (Rabsolu_Ropp ``x-x1``); Rewrite Ropp_distr2; Ring.
Unfold del; Apply Rlt_anti_compatibility with ``(Rabsolu (x-x1))``; Rewrite Rplus_Or; Replace ``(Rabsolu (x-x1))+(x0-(Rabsolu (x-x1)))`` with (pos x0); [Idtac | Ring].
Unfold Disque in H1; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H1.
Qed.

Lemma complementaire_P1 : (D:R->Prop) ~(EXT y:R | (intersection_domaine D (complementaire D) y)).
Intro; Red; Intro; Elim H; Intros; Unfold intersection_domaine complementaire in H0; Elim H0; Intros; Elim H2; Assumption.
Qed.

(* Schéma d'induction de l'égalité entre domaines de R *)
Axiom eqDom : (P:(R->Prop)->Prop)(x:R->Prop)(P x)->((y:R->Prop)(inclus x y)->(inclus y x)->(P y)).

Lemma eqDD : (D1,D2:R->Prop) ((x:R)(D1 x)<->(D2 x)) -> D1==D2.
Intros; Cut (x:R)(D1 x)->(D2 x).
Cut (x:R)(D2 x)->(D1 x).
Intros; Cut (inclus D1 D2); [Intro | Assumption]; Cut (inclus D2 D1); [Intro | Assumption]; Pose P := [X:R->Prop]D1==X.
Cut D1==D1; [Intro; Apply (eqDom P D1 H4 D2 H2 H3) | Reflexivity].
Intros; Elim (H x); Intros; Apply (H2 H0).
Intros; Elim (H x); Intros; Apply (H1 H0).
Qed.

Lemma adherence_P2 : (D:R->Prop) (ferme D) -> (inclus (adherence D) D).
Unfold ferme; Unfold ouvert complementaire; Intros; Unfold inclus adherence; Intros; Assert H1 := (classic (D x)); Elim H1; Intro.
Assumption.
Assert H3 := (H ? H2); Assert H4 := (H0 ? H3); Elim H4; Intros; Unfold intersection_domaine in H5; Elim H5; Intros; Elim H6; Assumption.
Qed.

Lemma adherence_P3 : (D:R->Prop) (ferme (adherence D)).
Intro; Unfold ferme adherence; Unfold ouvert complementaire point_adherent; Intros; Pose P := [V:R->Prop](voisinage V x)->(EXT y:R | (intersection_domaine V D y)); Assert H0 := (not_all_ex_not ? P H); Elim H0; Intros V0 H1; Unfold P in H1; Assert H2 := (imply_to_and ? ? H1); Unfold voisinage; Elim H2; Intros; Unfold voisinage in H3; Elim H3; Intros; Exists x0; Unfold inclus; Intros; Red; Intro.
Assert H8 := (H7 V0); Cut (EXT delta:posreal | (x:R)(Disque x1 delta x)->(V0 x)).
Intro; Assert H10 := (H8 H9); Elim H4; Assumption.
Cut ``0<x0-(Rabsolu (x-x1))``.
Intro; Pose del := (mkposreal ? H9); Exists del; Intros; Unfold inclus in H5; Apply H5; Unfold Disque; Apply Rle_lt_trans with ``(Rabsolu (x2-x1))+(Rabsolu (x1-x))``.
Replace ``x2-x`` with ``(x2-x1)+(x1-x)``; [Apply Rabsolu_triang | Ring].
Replace (pos x0) with ``del+(Rabsolu (x1-x))``.
Do 2 Rewrite <- (Rplus_sym ``(Rabsolu (x1-x))``); Apply Rlt_compatibility; Apply H10.
Unfold del; Simpl; Rewrite <- (Rabsolu_Ropp ``x-x1``); Rewrite Ropp_distr2; Ring.
Apply Rlt_anti_compatibility with ``(Rabsolu (x-x1))``; Rewrite Rplus_Or; Replace ``(Rabsolu (x-x1))+(x0-(Rabsolu (x-x1)))`` with (pos x0); [Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H6 | Ring].
Qed.

Lemma ouvert_P1 : (D:R->Prop) (ouvert D) <-> D==(interieur D).
Intro; Split.
Intro; Apply eqDom with D.
Reflexivity.
Apply interieur_P2; Assumption.
Apply interieur_P1.
Intro; Rewrite H; Apply interieur_P3.
Qed.

Lemma ferme_P1 : (D:R->Prop) (ferme D) <-> D==(adherence D).
Intro; Split.
Intro; Apply eqDom with D.
Reflexivity.
Apply adherence_P1.
Apply adherence_P2; Assumption.
Intro; Rewrite H; Apply adherence_P3.
Qed.

Lemma union_sym : (D1,D2:R->Prop) (union_domaine D1 D2)==(union_domaine D2 D1).
Intros; Apply eqDD; Intro; Unfold union_domaine; Tauto.
Qed.

Lemma intersection_sym : (D1,D2:R->Prop) (intersection_domaine D1 D2)==(intersection_domaine D2 D1).
Intros; Apply eqDD; Intro; Unfold intersection_domaine; Tauto.
Qed.

Lemma voisinage_P1 : (D1,D2:R->Prop;x:R) (inclus D1 D2) -> (voisinage D1 x) -> (voisinage D2 x).
Unfold inclus voisinage; Intros; Elim H0; Intros; Exists x0; Intros; Unfold inclus; Unfold inclus in H1; Intros; Apply (H ? (H1 ? H2)).
Qed.

Lemma ouvert_P2 : (D1,D2:R->Prop) (ouvert D1) -> (ouvert D2) -> (ouvert (union_domaine D1 D2)).
Unfold ouvert; Intros; Unfold union_domaine in H1; Elim H1; Intro.
Apply voisinage_P1 with D1.
Unfold inclus union_domaine; Tauto.
Apply H; Assumption.
Apply voisinage_P1 with D2.
Unfold inclus union_domaine; Tauto.
Apply H0; Assumption.
Qed.

Lemma ouvert_P3 : (D1,D2:R->Prop) (ouvert D1) -> (ouvert D2) -> (ouvert (intersection_domaine D1 D2)).
Unfold ouvert; Intros; Unfold intersection_domaine in H1; Elim H1; Intros.
Assert H4 := (H ? H2); Assert H5 := (H0 ? H3); Unfold intersection_domaine; Unfold voisinage in H4 H5; Elim H4; Clear H; Intros del1 H; Elim H5; Clear H0; Intros del2 H0; Cut ``0<(Rmin del1 del2)``.
Intro; Pose del := (mkposreal ? H6).
Exists del; Unfold inclus; Intros; Unfold inclus in H H0; Unfold Disque in H H0 H7.
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

Lemma ouvert_P4 : (ouvert [x:R]False).
Unfold ouvert; Intros; Elim H.
Qed.

Lemma ouvert_P5 : (ouvert [x:R]True).
Unfold ouvert; Intros; Unfold voisinage.
Exists (mkposreal R1 Rlt_R0_R1); Unfold inclus; Intros; Trivial.
Qed.

Lemma disque_P1 : (x:R;del:posreal) (ouvert (Disque x del)).
Intros; Assert H := (ouvert_P1 (Disque x del)).
Elim H; Intros; Apply H1.
Apply eqDom with (Disque x del).
Reflexivity.
Unfold inclus interieur Disque; Intros; Cut ``0<del-(Rabsolu (x-x0))``.
Intro; Pose del2 := (mkposreal ? H3).
Exists del2; Unfold inclus; Intros.
Apply Rle_lt_trans with ``(Rabsolu (x1-x0))+(Rabsolu (x0 -x))``.
Replace ``x1-x`` with ``(x1-x0)+(x0-x)``; [Apply Rabsolu_triang | Ring].
Replace (pos del) with ``del2 + (Rabsolu (x0-x))``.
Do 2 Rewrite <- (Rplus_sym ``(Rabsolu (x0-x))``); Apply Rlt_compatibility.
Apply H4.
Unfold del2; Simpl; Rewrite <- (Rabsolu_Ropp ``x-x0``); Rewrite Ropp_distr2; Ring.
Apply Rlt_anti_compatibility with ``(Rabsolu (x-x0))``; Rewrite Rplus_Or; Replace ``(Rabsolu (x-x0))+(del-(Rabsolu (x-x0)))`` with (pos del); [Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Apply H2 | Ring].
Apply interieur_P1.
Qed.

Lemma continuity_P1 : (f:R->R;x:R) (continuity_pt f x) <-> (W:R->Prop)(voisinage W (f x)) -> (EXT V:R->Prop | (voisinage V x) /\ ((y:R)(V y)->(W (f y)))).
Intros; Split.
Intros; Unfold voisinage in H0.
Elim H0; Intros del1 H1.
Unfold continuity_pt in H; Unfold continue_in in H; Unfold limit1_in in H; Unfold limit_in in H; Simpl in H; Unfold R_dist in H.
Assert H2 := (H del1 (cond_pos del1)).
Elim H2; Intros del2 H3.
Elim H3; Intros.
Exists (Disque x (mkposreal del2 H4)).
Intros; Unfold inclus in H1; Split.
Unfold voisinage Disque.
Exists (mkposreal del2 H4).
Unfold inclus; Intros; Assumption.
Intros; Apply H1; Unfold Disque; Case (Req_EM y x); Intro.
Rewrite H7; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply (cond_pos del1).
Apply H5; Split.
Unfold D_x no_cond; Split.
Trivial.
Apply not_sym; Apply H7.
Unfold Disque in H6; Apply H6.
Intros; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Intros.
Assert H1 := (H (Disque (f x) (mkposreal eps H0))).
Cut (voisinage (Disque (f x) (mkposreal eps H0)) (f x)).
Intro; Assert H3 := (H1 H2).
Elim H3; Intros D H4; Elim H4; Intros; Unfold voisinage in H5; Elim H5; Intros del1 H7.
Exists (pos del1); Split.
Apply (cond_pos del1).
Intros; Elim H8; Intros; Simpl in H10; Unfold R_dist in H10; Simpl; Unfold R_dist; Apply (H6 ? (H7 ? H10)).
Unfold voisinage Disque; Exists (mkposreal eps H0); Unfold inclus; Intros; Assumption.
Qed.

Definition image_rec [f:R->R;D:R->Prop] : R->Prop := [x:R](D (f x)).

(* L'image réciproque d'un ouvert par une fonction continue est un ouvert *)
Lemma continuity_P2 : (f:R->R;D:R->Prop) (continuity f) -> (ouvert D) -> (ouvert (image_rec f D)).
Intros; Unfold ouvert in H0; Unfold ouvert; Intros; Assert H2 := (continuity_P1 f x); Elim H2; Intros H3 _; Assert H4 := (H3 (H x)); Unfold voisinage image_rec; Unfold image_rec in H1; Assert H5 := (H4 D (H0 (f x) H1)); Elim H5; Intros V0 H6; Elim H6; Intros; Unfold voisinage in H7; Elim H7; Intros del H9; Exists del; Unfold inclus in H9; Unfold inclus; Intros; Apply (H8 ? (H9 ? H10)).
Qed.

(* Caractérisation complète des fonctions continues : *)
(* une fonction est continue ssi l'image réciproque de tout ouvert est un ouvert *)
Lemma continuity_P3 : (f:R->R) (continuity f) <-> (D:R->Prop) (ouvert D)->(ouvert (image_rec f D)).
Intros; Split.
Intros; Apply continuity_P2; Assumption.
Intros; Unfold continuity; Unfold continuity_pt; Unfold continue_in; Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros; Cut (ouvert (Disque (f x) (mkposreal ? H0))).
Intro; Assert H2 := (H ? H1).
Unfold ouvert image_rec in H2; Cut (Disque (f x) (mkposreal ? H0) (f x)).
Intro; Assert H4 := (H2 ? H3).
Unfold voisinage in H4; Elim H4; Intros del H5.
Exists (pos del); Split.
Apply (cond_pos del).
Intros; Unfold inclus in H5; Apply H5; Elim H6; Intros; Apply H8.
Unfold Disque; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply H0.
Apply disque_P1.
Qed.

(* R est séparé *)
Theorem Rsepare : (x,y:R) ``x<>y``->(EXT V:R->Prop | (EXT W:R->Prop | (voisinage V x)/\(voisinage W y)/\~(EXT y:R | (intersection_domaine V W y)))).
Intros x y Hsep; Pose D := ``(Rabsolu (x-y))``.
Cut ``0<D/2``.
Intro; Exists (Disque x (mkposreal ? H)).
Exists (Disque y (mkposreal ? H)); Split.
Unfold voisinage; Exists (mkposreal ? H); Unfold inclus; Tauto.
Split.
Unfold voisinage; Exists (mkposreal ? H); Unfold inclus; Tauto.
Red; Intro; Elim H0; Intros; Unfold intersection_domaine in H1; Elim H1; Intros.
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

(* Ce type décrit les familles de domaines indexées par un domaine *)
Record famille : Type := mkfamille {
  ind : R->Prop;
  f :> R->R->Prop;
  cond_fam : (x:R)(EXT y:R|(f x y))->(ind x) }.

Definition famille_ouvert [f:famille] : Prop := (x:R) (ouvert (f x)).

(* Liste de réels *)
Inductive Rlist : Type :=
| nil : Rlist
| cons : R -> Rlist -> Rlist.

Fixpoint In [x:R;l:Rlist] : Prop :=
Cases l of
| nil => False
| (cons a l') => ``x==a``\/(In x l') end.

Definition domaine_fini [D:R->Prop] : Prop := (EXT l:Rlist | (x:R)(D x)<->(In x l)).

Fixpoint longueur [l:Rlist] : nat :=
Cases l of
| nil => O
| (cons a l') => (S (longueur l')) end.

(* Cette fonction renvoie le maximum des éléments d'une liste non vide *)
Fixpoint MaxRlist [l:Rlist] : R :=
 Cases l of
 | nil => R0 (* valeur de retour si la liste de départ est vide *)
 | (cons a l1) => 
   Cases l1 of
   | nil => a
   | (cons a' l2) => (Rmax a (MaxRlist l1)) 
   end
end.

Fixpoint MinRlist [l:Rlist] : R :=
Cases l of
 | nil => R1 (* valeur de retour si la liste de départ est vide *)
 | (cons a l1) => 
   Cases l1 of
   | nil => a
   | (cons a' l2) => (Rmin a (MinRlist l1)) 
   end
end.

Definition famille_finie [f:famille] : Prop := (domaine_fini (ind f)).

Definition recouvrement [D:R->Prop;f:famille] : Prop := (x:R) (D x)->(EXT y:R | (f y x)).

Definition recouvrement_ouvert [D:R->Prop;f:famille] : Prop := (recouvrement D f)/\(famille_ouvert f).

Definition recouvrement_fini [D:R->Prop;f:famille] : Prop := (recouvrement D f)/\(famille_finie f).

Lemma restriction_famille : (f:famille;D:R->Prop) (x:R)(EXT y:R|([z1:R][z2:R](f z1 z2)/\(D z1) x y))->(intersection_domaine (ind f) D x).
Intros; Elim H; Intros; Unfold intersection_domaine; Elim H0; Intros; Split.
Apply (cond_fam f0); Exists x0; Assumption.
Assumption.
Qed.

Definition famille_restreinte [f:famille;D:R->Prop] : famille := (mkfamille (intersection_domaine (ind f) D) [x:R][y:R](f x y)/\(D x) (restriction_famille f D)).

Definition compact [X:R->Prop] : Prop := (f:famille) (recouvrement_ouvert X f) -> (EXT D:R->Prop | (recouvrement_fini X (famille_restreinte f D))).

(* Un sous-ensemble d'une famille d'ouverts est une famille d'ouverts *)
Lemma famille_P1 : (f:famille;D:R->Prop) (famille_ouvert f) -> (famille_ouvert (famille_restreinte f D)).
Unfold famille_ouvert; Intros; Unfold famille_restreinte; Simpl; Assert H0 := (classic (D x)).
Elim H0; Intro.
Cut (ouvert (f0 x))->(ouvert [y:R](f0 x y)/\(D x)).
Intro; Apply H2; Apply H.
Unfold ouvert; Unfold voisinage; Intros; Elim H3; Intros; Assert H6 := (H2 ? H4); Elim H6; Intros; Exists x1; Unfold inclus; Intros; Split.
Apply (H7 ? H8).
Assumption.
Cut (ouvert [y:R]False) -> (ouvert [y:R](f0 x y)/\(D x)).
Intro; Apply H2; Apply ouvert_P4.
Unfold ouvert; Unfold voisinage; Intros; Elim H3; Intros; Elim H1; Assumption.
Qed.

Definition bornee [D:R->Prop] : Prop := (EXT m:R | (EXT M:R | (x:R)(D x)->``m<=x<=M``)).

Lemma MaxRlist_P1 : (l:Rlist;x:R) (In x l)->``x<=(MaxRlist l)``.
Intros; Induction l.
Simpl in H; Elim H.
Induction l.
Simpl in H; Elim H; Intro.
Simpl; Right; Assumption.
Elim H0.
Replace (MaxRlist (cons r (cons r0 l))) with (Rmax r (MaxRlist (cons r0 l))).
Simpl in H; Decompose [or] H.
Rewrite H0; Apply RmaxLess1.
Unfold Rmax; Case (total_order_Rle r (MaxRlist (cons r0 l))); Intro.
Apply Hrecl; Simpl; Tauto.
Apply Rle_trans with (MaxRlist (cons r0 l)); [Apply Hrecl; Simpl; Tauto | Left; Auto with real].
Unfold Rmax; Case (total_order_Rle r (MaxRlist (cons r0 l))); Intro.
Apply Hrecl; Simpl; Tauto.
Apply Rle_trans with (MaxRlist (cons r0 l)); [Apply Hrecl; Simpl; Tauto | Left; Auto with real].
Reflexivity.
Qed.

(* Les parties compactes de R sont bornées *)
Lemma compact_P1 : (X:R->Prop) (compact X) -> (bornee X).
Intros; Unfold compact in H; Pose D := [x:R]True; Pose g := [x:R][y:R]``(Rabsolu y)<x``; Cut (x:R)(EXT y|(g x y))->True; [Intro | Intro; Trivial].
Pose f0 := (mkfamille D g H0); Assert H1 := (H f0); Cut (recouvrement_ouvert X f0).
Intro; Assert H3 := (H1 H2); Elim H3; Intros D' H4; Unfold recouvrement_fini in H4; Elim H4; Intros; Unfold famille_finie in H6; Unfold domaine_fini in H6; Elim H6; Intros l H7; Unfold bornee; Pose r := (MaxRlist l).
Exists ``-r``; Exists r; Intros.
Unfold recouvrement in H5; Assert H9 := (H5 ? H8); Elim H9; Intros; Unfold famille_restreinte in H10; Simpl in H10; Elim H10; Intros; Assert H13 := (H7 x0); Simpl in H13; Cut (intersection_domaine D D' x0).
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
Unfold intersection_domaine D; Tauto.
Unfold recouvrement_ouvert; Split.
Unfold recouvrement; Intros; Simpl; Exists ``(Rabsolu x)+1``; Unfold g; Pattern 1 (Rabsolu x); Rewrite <- Rplus_Or; Apply Rlt_compatibility; Apply Rlt_R0_R1.
Unfold famille_ouvert; Intro; Case (total_order R0 x); Intro.
Cut (f0 x)==(Disque R0 (mkposreal ? H2)).
Intro; Rewrite H3; Apply disque_P1.
Unfold f0; Simpl; Unfold g Disque; Apply eqDom with [y:R]``(Rabsolu y) < x``; [Reflexivity | Unfold inclus; Intros; Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Apply H3 | Unfold inclus; Intros; Unfold Rminus in H3; Rewrite Ropp_O in H3; Rewrite Rplus_Or in H3; Apply H3].
Cut (f0 x)==[x:R]False.
Intro; Rewrite H3; Apply ouvert_P4.
Apply eqDom with (f0 x); [Reflexivity | Unfold inclus f0; Simpl; Unfold g; Intros; Elim H2; Intro; [Rewrite <- H4 in H3; Assert H5 := (Rabsolu_pos x0); Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H5 H3)) | Assert H6 := (Rabsolu_pos x0); Assert H7 := (Rlt_trans ? ? ? H3 H4); Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H6 H7))] | Unfold inclus; Intros; Elim H3].
Qed.

Fixpoint AbsList [l:Rlist] : R->Rlist :=
[x:R] Cases l of
| nil => nil
| (cons a l') => (cons ``(Rabsolu (a-x))/2`` (AbsList l' x))
end.

Lemma MinRlist_P1 : (l:Rlist;x:R) (In x l)->``(MinRlist l)<=x``.
Intros; Induction l.
Simpl in H; Elim H.
Induction l.
Simpl in H; Elim H; Intro.
Simpl; Right; Symmetry; Assumption.
Elim H0.
Replace (MinRlist (cons r (cons r0 l))) with (Rmin r (MinRlist (cons r0 l))).
Simpl in H; Decompose [or] H.
Rewrite H0; Apply Rmin_l.
Unfold Rmin; Case (total_order_Rle r (MinRlist (cons r0 l))); Intro.
Apply Rle_trans with (MinRlist (cons r0 l)).
Assumption.
Apply Hrecl; Simpl; Tauto.
Apply Hrecl; Simpl; Tauto.
Apply Rle_trans with (MinRlist (cons r0 l)).
Apply Rmin_r.
Apply Hrecl; Simpl; Tauto.
Reflexivity.
Qed.

Lemma AbsList_P1 : (l:Rlist;x,y:R) (In y l) -> (In ``(Rabsolu (y-x))/2`` (AbsList l x)).
Intros; Induction l.
Elim H.
Simpl; Simpl in H; Elim H; Intro.
Left; Rewrite H0; Reflexivity.
Right; Apply Hrecl; Assumption.
Qed.

Lemma MinRlist_P2 : (l:Rlist) ((y:R)(In y l)->``0<y``)->``0<(MinRlist l)``.
Intros; Induction l.
Apply Rlt_R0_R1.
Induction l.
Simpl; Apply H; Simpl; Tauto.
Replace (MinRlist (cons r (cons r0 l))) with (Rmin r (MinRlist (cons r0 l))).
Unfold Rmin; Case (total_order_Rle r (MinRlist (cons r0 l))); Intro.
Apply H; Simpl; Tauto.
Apply Hrecl; Intros; Apply H; Simpl; Simpl in H0; Tauto.
Reflexivity.
Qed.

Lemma AbsList_P2 : (l:Rlist;x,y:R) (In y (AbsList l x)) -> (EXT z : R | (In z l)/\``y==(Rabsolu (z-x))/2``).
Intros; Induction l.
Elim H.
Elim H; Intro.
Exists r; Split.
Simpl; Tauto.
Assumption.
Assert H1 := (Hrecl H0); Elim H1; Intros; Elim H2; Clear H2; Intros; Exists x0; Simpl; Simpl in H2; Tauto.
Qed.

(* Les parties compactes de R sont fermées *)
Lemma compact_P2 : (X:R->Prop) (compact X) -> (ferme X).
Intros; Assert H0 := (ferme_P1 X); Elim H0; Clear H0; Intros _ H0; Apply H0; Clear H0; Apply eqDom with X.
Reflexivity.
Apply adherence_P1.
Unfold inclus; Unfold adherence; Unfold point_adherent; Intros; Unfold compact in H; Assert H1 := (classic (X x)); Elim H1; Clear H1; Intro.
Assumption.
Cut (y:R)(X y)->``0<(Rabsolu (y-x))/2``.
Intro; Pose D := X; Pose g := [y:R][z:R]``(Rabsolu (y-z))<(Rabsolu (y-x))/2``/\(D y); Cut (x:R)(EXT y|(g x y))->(D x).
Intro; Pose f0 := (mkfamille D g H3); Assert H4 := (H f0); Cut (recouvrement_ouvert X f0).
Intro; Assert H6 := (H4 H5); Elim H6; Clear H6; Intros D' H6.
Unfold recouvrement_fini in H6; Decompose [and] H6; Unfold recouvrement famille_restreinte in H7; Simpl in H7; Unfold famille_finie famille_restreinte in H8; Simpl in H8; Unfold domaine_fini in H8; Elim H8; Clear H8; Intros l H8; Pose alp := (MinRlist (AbsList l x)); Cut ``0<alp``.
Intro; Assert H10 := (H0 (Disque x (mkposreal ? H9))); Cut (voisinage (Disque x (mkposreal alp H9)) x).
Intro; Assert H12 := (H10 H11); Elim H12; Clear H12; Intros y H12; Unfold intersection_domaine in H12; Elim H12; Clear H12; Intros; Assert H14 := (H7 ? H13); Elim H14; Clear H14; Intros y0 H14; Elim H14; Clear H14; Intros; Unfold g in H14; Elim H14; Clear H14; Intros; Unfold Disque in H12; Simpl in H12; Cut ``alp<=(Rabsolu (y0-x))/2``.
Intro; Assert H18 := (Rlt_le_trans ? ? ? H12 H17); Cut ``(Rabsolu (y0-x))<(Rabsolu (y0-x))``.
Intro; Elim (Rlt_antirefl ? H19).
Apply Rle_lt_trans with ``(Rabsolu (y0-y))+(Rabsolu (y-x))``.
Replace ``y0-x`` with ``(y0-y)+(y-x)``; [Apply Rabsolu_triang | Ring].
Rewrite (double_var ``(Rabsolu (y0-x))``); Apply Rplus_lt; Assumption.
Apply (MinRlist_P1 (AbsList l x) ``(Rabsolu (y0-x))/2``); Apply AbsList_P1; Elim (H8 y0); Clear H8; Intros; Apply H8; Unfold intersection_domaine; Split; Assumption.
Assert H11 := (disque_P1 x (mkposreal alp H9)); Unfold ouvert in H11; Apply H11.
Unfold Disque; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Apply H9.
Unfold alp; Apply MinRlist_P2; Intros; Assert H10 := (AbsList_P2 ? ? ? H9); Elim H10; Clear H10; Intros z H10; Elim H10; Clear H10; Intros; Rewrite H11; Apply H2; Elim (H8 z); Clear H8; Intros; Assert H13 := (H12 H10); Unfold intersection_domaine D in H13; Elim H13; Clear H13; Intros; Assumption.
Unfold recouvrement_ouvert; Split.
Unfold recouvrement; Intros; Exists x0; Simpl; Unfold g; Split.
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Unfold Rminus in H2; Apply (H2 ? H5).
Apply H5.
Unfold famille_ouvert; Intro; Simpl; Unfold g; Elim (classic (D x0)); Intro.
Cut ([z:R]``(Rabsolu (x0-z)) < (Rabsolu (x0-x))/2``/\(D x0))==(Disque x0 (mkposreal ? (H2 ? H5))).
Intro; Rewrite H6; Apply disque_P1.
Apply eqDom with [z:R]``(Rabsolu (x0-z)) < (Rabsolu (x0-x))/2``/\(D x0).
Reflexivity.
Unfold inclus Disque; Simpl; Intros; Elim H6; Intros; Rewrite <- (Rabsolu_Ropp ``x1-x0``); Rewrite Ropp_distr2; Apply H7.
Unfold inclus Disque; Simpl; Intros; Split.
Rewrite <- (Rabsolu_Ropp ``x0-x1``); Rewrite Ropp_distr2; Apply H6.
Apply H5.
Cut ([z:R]``(Rabsolu (x0-z)) < (Rabsolu (x0-x))/2``/\(D x0))==[z:R]False.
Intro; Rewrite H6; Apply ouvert_P4.
Apply eqDom with [z:R]``(Rabsolu (x0-z)) < (Rabsolu (x0-x))/2``/\(D x0).
Reflexivity.
Unfold inclus; Intros; Elim H6; Intros; Elim H5; Assumption.
Unfold inclus; Intros; Elim H6.
Intros; Elim H3; Intros; Unfold g in H4; Elim H4; Clear H4; Intros _ H4; Apply H4.
Intros; Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rabsolu_pos_lt; Apply Rminus_eq_contra; Red; Intro; Rewrite H3 in H2; Elim H1; Apply H2.
Apply Rlt_Rinv; Sup0.
Qed.

(* La partie vide est compacte *)
Lemma compact_EMP : (compact [_:R]False).
Unfold compact; Intros; Exists [x:R]False; Unfold recouvrement_fini; Split.
Unfold recouvrement; Intros; Elim H0.
Unfold famille_finie; Unfold domaine_fini; Exists nil; Intro.
Split.
Simpl; Unfold intersection_domaine; Intros; Elim H0.
Elim H0; Clear H0; Intros _ H0; Elim H0.
Simpl; Intro; Elim H0.
Qed.

(* Lemme de Borel-Lebesgue *)
Lemma compact_P3 : (a,b:R) (compact [c:R]``a<=c<=b``).
Intros; Case (total_order_Rle a b); Intro.
Unfold compact; Intros; Pose A := [x:R]``a<=x<=b``/\(EXT D:R->Prop | (recouvrement_fini [c:R]``a <= c <= x`` (famille_restreinte f0 D))); Cut (A a).
Intro; Cut (bound A).
Intro; Cut (EXT a0:R | (A a0)).
Intro; Assert H3 := (complet A H1 H2); Elim H3; Clear H3; Intros m H3; Unfold is_lub in H3; Cut ``a<=m<=b``.
Intro; Unfold recouvrement_ouvert in H; Elim H; Clear H; Intros; Unfold recouvrement in H; Assert H6 := (H m H4); Elim H6; Clear H6; Intros y0 H6; Unfold famille_ouvert in H5; Assert H7 := (H5 y0); Unfold ouvert in H7; Assert H8 := (H7 m H6); Unfold voisinage in H8; Elim H8; Clear H8; Intros eps H8; Cut (EXT x:R | (A x)/\``m-eps<x<=m``).
Intro; Elim H9; Clear H9; Intros x H9; Elim H9; Clear H9; Intros; Case (Req_EM m b); Intro.
Rewrite H11 in H10; Rewrite H11 in H8; Unfold A in H9; Elim H9; Clear H9; Intros; Elim H12; Clear H12; Intros Dx H12; Pose Db := [x:R](Dx x)\/x==y0; Exists Db; Unfold recouvrement_fini; Split.
Unfold recouvrement; Unfold recouvrement_fini in H12; Elim H12; Clear H12; Intros; Unfold recouvrement in H12; Case (total_order_Rle x0 x); Intro.
Cut ``a<=x0<=x``.
Intro; Assert H16 := (H12 x0 H15); Elim H16; Clear H16; Intros; Exists x1; Simpl in H16; Simpl; Unfold Db; Elim H16; Clear H16; Intros; Split; [Apply H16 | Left; Apply H17].
Split.
Elim H14; Intros; Assumption.
Assumption.
Exists y0; Simpl; Split.
Apply H8; Unfold Disque; Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Rewrite Rabsolu_right.
Apply Rlt_trans with ``b-x``.
Unfold Rminus; Apply Rlt_compatibility; Apply Rlt_Ropp; Auto with real.
Elim H10; Intros H15 _; Apply Rlt_anti_compatibility with ``x-eps``; Replace ``x-eps+(b-x)`` with ``b-eps``; [Replace ``x-eps+eps`` with x; [Apply H15 | Ring] | Ring].
Apply Rge_minus; Apply Rle_sym1; Elim H14; Intros _ H15; Apply H15.
Unfold Db; Right; Reflexivity.
Unfold famille_finie; Unfold domaine_fini; Unfold recouvrement_fini in H12; Elim H12; Clear H12; Intros; Unfold famille_finie in H13; Unfold domaine_fini in H13; Elim H13; Clear H13; Intros l H13; Exists (cons y0 l); Intro; Split.
Intro; Simpl in H14; Unfold intersection_domaine in H14; Elim (H13 x0); Clear H13; Intros; Case (Req_EM x0 y0); Intro.
Simpl; Left; Apply H16.
Simpl; Right; Apply H13.
Simpl; Unfold intersection_domaine; Unfold Db in H14; Decompose [and or] H14.
Split; Assumption.
Elim H16; Assumption.
Intro; Simpl in H14; Elim H14; Intro; Simpl; Unfold intersection_domaine.
Split.
Apply (cond_fam f0); Rewrite H15; Exists m; Apply H6.
Unfold Db; Right; Assumption.
Simpl; Unfold intersection_domaine; Elim (H13 x0).
Intros _ H16; Assert H17 := (H16 H15); Simpl in H17; Unfold intersection_domaine in H17; Split.
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
Unfold A in H9; Elim H9; Clear H9; Intros; Elim H12; Clear H12; Intros Dx H12; Pose Db := [x:R](Dx x)\/x==y0; Exists Db; Unfold recouvrement_fini; Split.
Unfold recouvrement; Unfold recouvrement_fini in H12; Elim H12; Clear H12; Intros; Unfold recouvrement in H12; Case (total_order_Rle x0 x); Intro.
Cut ``a<=x0<=x``.
Intro; Assert H16 := (H12 x0 H15); Elim H16; Clear H16; Intros; Exists x1; Simpl in H16; Simpl; Unfold Db.
Elim H16; Clear H16; Intros; Split; [Apply H16 | Left; Apply H17].
Elim H14; Intros; Split; Assumption.
Exists y0; Simpl; Split.
Apply H8; Unfold Disque; Unfold Rabsolu; Case (case_Rabsolu ``x0-m``); Intro.
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
Unfold famille_finie; Unfold domaine_fini; Unfold recouvrement_fini in H12; Elim H12; Clear H12; Intros; Unfold famille_finie in H13; Unfold domaine_fini in H13; Elim H13; Clear H13; Intros l H13; Exists (cons y0 l); Intro; Split.
Intro; Simpl in H14; Unfold intersection_domaine in H14; Elim (H13 x0); Clear H13; Intros; Case (Req_EM x0 y0); Intro.
Simpl; Left; Apply H16.
Simpl; Right; Apply H13; Simpl; Unfold intersection_domaine; Unfold Db in H14; Decompose [and or] H14.
Split; Assumption.
Elim H16; Assumption.
Intro; Simpl in H14; Elim H14; Intro; Simpl; Unfold intersection_domaine.
Split.
Apply (cond_fam f0); Rewrite H15; Exists m; Apply H6.
Unfold Db; Right; Assumption.
Elim (H13 x0); Intros _ H16.
Assert H17 := (H16 H15).
Simpl in H17.
Unfold intersection_domaine in H17.
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
Unfold recouvrement_ouvert in H; Elim H; Clear H; Intros; Unfold recouvrement in H; Cut ``a<=a<=b``.
Intro; Elim (H ? H1); Intros y0 H2; Pose D':=[x:R]x==y0; Exists D'; Unfold recouvrement_fini; Split.
Unfold recouvrement; Simpl; Intros; Cut x==a.
Intro; Exists y0; Split.
Rewrite H4; Apply H2.
Unfold D'; Reflexivity.
Elim H3; Intros; Apply Rle_antisym; Assumption.
Unfold famille_finie; Unfold domaine_fini; Exists (cons y0 nil); Intro; Split.
Simpl; Unfold intersection_domaine; Intro; Elim H3; Clear H3; Intros; Unfold D' in H4; Left; Apply H4.
Simpl; Unfold intersection_domaine; Intro; Elim H3; Intro.
Split; [Rewrite H4; Apply (cond_fam f0); Exists a; Apply H2 | Apply H4].
Elim H4.
Split; [Right; Reflexivity | Apply r].
Cut ([c:R]``a<=c<=b``)==[c:R]False.
Intro; Rewrite H.
Apply compact_EMP.
Apply eqDom with [c:R]``a <= c <= b``.
Reflexivity.
Unfold inclus; Intros; Elim H; Clear H; Intros; Assert H1 := (Rle_trans ? ? ? H H0); Elim n; Apply H1.
Unfold inclus; Intros; Elim H.
Qed.

Lemma compact_P4 : (X,F:R->Prop) (compact X) -> (ferme F) -> (inclus F X) -> (compact F).
Unfold compact; Intros; Elim (classic (EXT z:R | (F z))); Intro Hyp_F_NE.
Pose D := (ind f0); Pose g := (f f0); Unfold ferme in H0.
Pose g' := [x:R][y:R](f0 x y)\/((complementaire F y)/\(D x)).
Pose D' := D.
Cut (x:R)(EXT y:R | (g' x y))->(D' x).
Intro; Pose f' := (mkfamille D' g' H3); Cut (recouvrement_ouvert X f').
Intro; Elim (H ? H4); Intros DX H5; Exists DX.
Unfold recouvrement_fini; Unfold recouvrement_fini in H5; Elim H5; Clear H5; Intros.
Split.
Unfold recouvrement; Unfold recouvrement in H5; Intros.
Elim (H5 ? (H1 ? H7)); Intros y0 H8; Exists y0; Simpl in H8; Simpl; Elim H8; Clear H8; Intros.
Split.
Unfold g' in H8; Elim H8; Intro.
Apply H10.
Elim H10; Intros H11 _; Unfold complementaire in H11; Elim H11; Apply H7.
Apply H9.
Unfold famille_finie; Unfold domaine_fini; Unfold famille_finie in H6; Unfold domaine_fini in H6; Elim H6; Clear H6; Intros l H6; Exists l; Intro; Assert H7 := (H6 x); Elim H7; Clear H7; Intros.
Split.
Intro; Apply H7; Simpl; Unfold intersection_domaine; Simpl in H9; Unfold intersection_domaine in H9; Unfold D'; Apply H9.
Intro; Assert H10 := (H8 H9); Simpl in H10; Unfold intersection_domaine in H10; Simpl; Unfold intersection_domaine; Unfold D' in H10; Apply H10.
Unfold recouvrement_ouvert; Unfold recouvrement_ouvert in H2; Elim H2; Clear H2; Intros.
Split.
Unfold recouvrement; Unfold recouvrement in H2; Intros.
Elim (classic (F x)); Intro.
Elim (H2 ? H6); Intros y0 H7; Exists y0; Simpl; Unfold g'; Left; Assumption.
Cut (EXT z:R | (D z)).
Intro; Elim H7; Clear H7; Intros x0 H7; Exists x0; Simpl; Unfold g'; Right.
Split.
Unfold complementaire; Apply H6.
Apply H7.
Elim Hyp_F_NE; Intros z0 H7.
Assert H8 := (H2 ? H7).
Elim H8; Clear H8; Intros t H8; Exists t; Apply (cond_fam f0); Exists z0; Apply H8.
Unfold famille_ouvert; Intro; Simpl; Unfold g'; Elim (classic (D x)); Intro.
Cut ([y:R](f0 x y)\/(complementaire F y)/\(D x))==(union_domaine (f0 x) (complementaire F)).
Intro; Rewrite H6; Apply ouvert_P2.
Unfold famille_ouvert in H4; Apply H4.
Apply H0.
Apply eqDom with [y:R](f0 x y)\/(complementaire F y)/\(D x).
Reflexivity.
Unfold inclus union_domaine complementaire; Intros.
Elim H6; Intro; [Left; Apply H7 | Right; Elim H7; Intros; Apply H8].
Unfold inclus union_domaine complementaire; Intros.
Elim H6; Intro; [Left; Apply H7 | Right; Split; Assumption].
Cut ([y:R](f0 x y)\/(complementaire F y)/\(D x))==(f0 x).
Intro; Rewrite H6; Unfold famille_ouvert in H4; Apply H4.
Apply eqDom with [y:R](f0 x y)\/(complementaire F y)/\(D x).
Reflexivity.
Unfold inclus complementaire; Intros.
Elim H6; Intro.
Apply H7.
Elim H7; Intros _ H8; Elim H5; Apply H8.
Unfold inclus complementaire; Intros; Left; Apply H6.
Intros; Elim H3; Intros y0 H4; Unfold g' in H4; Elim H4; Intro.
Apply (cond_fam f0); Exists y0; Apply H5.
Elim H5; Clear H5; Intros _ H5; Apply H5.
(* Cas ou F est l'ensemble vide *)
Cut F==[x:R]False.
Intro; Cut (compact F).
Intro; Apply (H4 f0 H2).
Rewrite H3; Apply compact_EMP.
Apply eqDom with F.
Reflexivity.
Assert H3 := (not_ex_all_not ? ? Hyp_F_NE); Unfold inclus; Intros; Elim (H3 x); Apply H4.
Unfold inclus; Intros; Elim H3.
Qed.

(* Les parties fermées et bornées sont compactes *)
Lemma compact_P5 : (X:R->Prop) (ferme X)->(bornee X)->(compact X).
Intros; Unfold bornee in H0.
Elim H0; Clear H0; Intros m H0.
Elim H0; Clear H0; Intros M H0.
Assert H1 := (compact_P3 m M).
Apply (compact_P4 [c:R]``m<=c<=M`` X H1 H H0).
Qed.

(* Les compacts de R sont les fermés bornés *)
Lemma compact_carac : (X:R->Prop) (compact X)<->(ferme X)/\(bornee X).
Intro; Split.
Intro; Split; [Apply (compact_P2 ? H) | Apply (compact_P1 ? H)].
Intro; Elim H; Clear H; Intros; Apply (compact_P5 ? H H0).
Qed.

Definition image_dir [f:R->R;D:R->Prop] : R->Prop := [x:R](EXT y:R | x==(f y)/\(D y)).

(* L'image d'un compact par une application continue est un compact *)
Lemma continuity_compact : (f:R->R;X:R->Prop) (continuity f) -> (compact X) -> (compact (image_dir f X)).
Unfold compact; Intros; Unfold recouvrement_ouvert in H1.
Elim H1; Clear H1; Intros.
Pose D := (ind f1).
Pose g := [x:R][y:R](image_rec f0 (f1 x) y).
Cut (x:R)(EXT y:R | (g x y))->(D x).
Intro; Pose f' := (mkfamille D g H3).
Cut (recouvrement_ouvert X f').
Intro; Elim (H0 f' H4); Intros D' H5; Exists D'.
Unfold recouvrement_fini in H5; Elim H5; Clear H5; Intros; Unfold recouvrement_fini; Split.
Unfold recouvrement image_dir; Simpl; Unfold recouvrement in H5; Intros; Elim H7; Intros y H8; Elim H8; Intros; Assert H11 := (H5 ? H10); Simpl in H11; Elim H11; Intros z H12; Exists z; Unfold g in H12; Unfold image_rec in H12; Rewrite H9; Apply H12.
Unfold famille_finie in H6; Unfold domaine_fini in H6; Unfold famille_finie; Unfold domaine_fini; Elim H6; Intros l H7; Exists l; Intro; Elim (H7 x); Intros; Split; Intro.
Apply H8; Simpl in H10; Simpl; Apply H10.
Apply (H9 H10).
Unfold recouvrement_ouvert; Split.
Unfold recouvrement; Intros; Simpl; Unfold recouvrement in H1; Unfold image_dir in H1; Unfold g; Unfold image_rec; Apply H1.
Exists x; Split; [Reflexivity | Apply H4].
Unfold famille_ouvert; Unfold famille_ouvert in H2; Intro; Simpl; Unfold g; Cut ([y:R](image_rec f0 (f1 x) y))==(image_rec f0 (f1 x)).
Intro; Rewrite H4; Apply (continuity_P2 f0 (f1 x) H (H2 x)).
Reflexivity.
Intros; Apply (cond_fam f1); Unfold g in H3; Unfold image_rec in H3; Elim H3; Intros; Exists (f0 x0); Apply H4.
Qed.

(* f continue sur [a,b] est majorée et atteint sa borne supérieure *)
Lemma continuity_ab_maj : (f:R->R;a,b:R) ``a<=b`` -> (continuity f) -> (EXT Mx : R |  ((c:R)``a<=c<=b``->``(f c)<=(f Mx)``)/\``a<=Mx<=b``).
Intros.
Assert H1 := (compact_P3 a b).
Assert H2 := (continuity_compact f0 [c:R]``a<=c<=b`` H0 H1).
Assert H3 := (compact_P2 ? H2).
Assert H4 := (compact_P1 ? H2).
Cut (bound (image_dir f0 [c:R]``a <= c <= b``)).
Cut (ExT [x:R] ((image_dir f0 [c:R]``a <= c <= b``) x)).
Intros; Assert H7 := (complet ? H6 H5).
Elim H7; Clear H7; Intros M H7; Cut (image_dir f0 [c:R]``a <= c <= b`` M).
Intro; Unfold image_dir in H8; Elim H8; Clear H8; Intros Mxx H8; Elim H8; Clear H8; Intros; Exists Mxx; Split.
Intros; Rewrite <- H8; Unfold is_lub in H7; Elim H7; Clear H7; Intros H7 _; Unfold is_upper_bound in H7; Apply H7; Unfold image_dir; Exists c; Split; [Reflexivity | Apply H10].
Apply H9.
Elim (classic (image_dir f0 [c:R]``a <= c <= b`` M)); Intro.
Assumption.
Cut (EXT eps:posreal | (y:R)~(intersection_domaine (Disque M eps) (image_dir f0 [c:R]``a <= c <= b``) y)).
Intro; Elim H9; Clear H9; Intros eps H9.
Unfold is_lub in H7; Elim H7; Clear H7; Intros; Cut (is_upper_bound (image_dir f0 [c:R]``a <= c <= b``) ``M-eps``).
Intro; Assert H12 := (H10 ? H11); Cut ``M-eps<M``.
Intro; Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H12 H13)).
Pattern 2 M; Rewrite <- Rplus_Or; Unfold Rminus; Apply Rlt_compatibility; Apply Ropp_Rlt; Rewrite Ropp_O; Rewrite Ropp_Ropp; Apply (cond_pos eps).
Unfold is_upper_bound image_dir; Intros; Cut ``x<=M``.
Intro; Case (total_order_Rle x ``M-eps``); Intro.
Apply r.
Elim (H9 x); Unfold intersection_domaine Disque image_dir; Split.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr2; Rewrite Rabsolu_right.
Apply Rlt_anti_compatibility with ``x-eps``; Replace ``x-eps+(M-x)`` with ``M-eps``.
Replace ``x-eps+eps`` with x.
Auto with real.
Ring.
Ring.
Apply Rge_minus; Apply Rle_sym1; Apply H12.
Apply H11.
Apply H7; Apply H11.
Cut (EXT V:R->Prop | (voisinage V M)/\((y:R)~(intersection_domaine V (image_dir f0 [c:R]``a <= c <= b``) y))).
Intro; Elim H9; Intros V H10; Elim H10; Clear H10; Intros.
Unfold voisinage in H10; Elim H10; Intros del H12; Exists del; Intros; Red; Intro; Elim (H11 y).
Unfold intersection_domaine; Unfold intersection_domaine in H13; Elim H13; Clear H13; Intros; Split.
Apply (H12 ? H13).
Apply H14.
Cut ~(point_adherent (image_dir f0 [c:R]``a <= c <= b``) M).
Intro; Unfold point_adherent in H9.
Assert H10 := (not_all_ex_not ? [V:R->Prop](voisinage V M)
            ->(EXT y:R |
                   (intersection_domaine V
                     (image_dir f0 [c:R]``a <= c <= b``) y)) H9).
Elim H10; Intros V0 H11; Exists V0; Assert H12 := (imply_to_and ? ? H11); Elim H12; Clear H12; Intros.
Split.
Apply H12.
Apply (not_ex_all_not ? ? H13).
Red; Intro; Cut (adherence (image_dir f0 [c:R]``a <= c <= b``) M).
Intro; Elim (ferme_P1 (image_dir f0 [c:R]``a <= c <= b``)); Intros H11 _; Assert H12 := (H11 H3).
Rewrite <- H12 in H10; Elim H8; Apply H10.
Apply H9.
Exists (f0 a); Unfold image_dir; Exists a; Split.
Reflexivity.
Split; [Right; Reflexivity | Apply H].
Unfold bound; Unfold bornee in H4; Elim H4; Clear H4; Intros m H4; Elim H4; Clear H4; Intros M H4; Exists M; Unfold is_upper_bound; Intros; Elim (H4 ? H5); Intros _ H6; Apply H6.
Qed.

(* f continue sur [a,b] est minorée et atteint sa borne inférieure *)
Lemma continuity_ab_min : (f:(R->R); a,b:R) ``a <= b``->(continuity f)->(EXT mx:R | ((c:R)``a <= c <= b``->``(f mx) <= (f c)``)/\``a <= mx <= b``).
Intros; Cut (continuity (opp_fct f0)).
Intro; Assert H2 := (continuity_ab_maj (opp_fct f0) a b H H1); Elim H2; Intros x0 H3; Exists x0; Intros; Split.
Intros; Rewrite <- (Ropp_Ropp (f0 x0)); Rewrite <- (Ropp_Ropp (f0 c)); Apply Rle_Ropp1; Elim H3; Intros; Unfold opp_fct in H5; Apply H5; Apply H4.
Elim H3; Intros; Assumption.
Apply (continuity_opp ? H0).
Qed.
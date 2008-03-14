(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

Require Import Bool.
Require Import Sumbool.
Require Import Arith.
Require Import NArith.
Require Import Ndigits.
Require Import Ndec.
Require Import Map.
Require Import Mapaxioms.
Require Import Mapiter.
Require Import Fset.
Require Import List.
Require Import Lsort.
Require Import Mapsubset.
Require Import Mapcard.

Section MapCanon.

  Variable A : Set.

  Inductive mapcanon : Map A -> Prop :=
    | M0_canon : mapcanon (M0 A)
    | M1_canon : forall (a:ad) (y:A), mapcanon (M1 A a y)
    | M2_canon :
        forall m1 m2:Map A,
          mapcanon m1 ->
          mapcanon m2 -> 2 <= MapCard A (M2 A m1 m2) -> mapcanon (M2 A m1 m2).

  Lemma mapcanon_M2 :
   forall m1 m2:Map A, mapcanon (M2 A m1 m2) -> 2 <= MapCard A (M2 A m1 m2).
  Proof.
    intros. inversion H. assumption.
  Qed.

  Lemma mapcanon_M2_1 :
   forall m1 m2:Map A, mapcanon (M2 A m1 m2) -> mapcanon m1.
  Proof.
    intros. inversion H. assumption.
  Qed.

  Lemma mapcanon_M2_2 :
   forall m1 m2:Map A, mapcanon (M2 A m1 m2) -> mapcanon m2.
  Proof.
    intros. inversion H. assumption.
  Qed.

  Lemma M2_eqmap_1 :
   forall m0 m1 m2 m3:Map A,
     eqmap A (M2 A m0 m1) (M2 A m2 m3) -> eqmap A m0 m2.
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite <- (Ndouble_div2 a).
    rewrite <- (MapGet_M2_bit_0_0 A _ (Ndouble_bit0 a) m0 m1).
    rewrite <- (MapGet_M2_bit_0_0 A _ (Ndouble_bit0 a) m2 m3).
    exact (H (Ndouble a)).
  Qed.

  Lemma M2_eqmap_2 :
   forall m0 m1 m2 m3:Map A,
     eqmap A (M2 A m0 m1) (M2 A m2 m3) -> eqmap A m1 m3.
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite <- (Ndouble_plus_one_div2 a).
    rewrite <- (MapGet_M2_bit_0_1 A _ (Ndouble_plus_one_bit0 a) m0 m1).
    rewrite <- (MapGet_M2_bit_0_1 A _ (Ndouble_plus_one_bit0 a) m2 m3).
    exact (H (Ndouble_plus_one a)).
  Qed.

  Lemma mapcanon_unique :
   forall m m':Map A, mapcanon m -> mapcanon m' -> eqmap A m m' -> m = m'.
  Proof.
    simple induction m. simple induction m'. trivial.
    intros a y H H0 H1. cut (None = MapGet A (M1 A a y) a). simpl in |- *. rewrite (Neqb_correct a).
    intro. discriminate H2.
    exact (H1 a).
    intros. cut (2 <= MapCard A (M0 A)). intro. elim (le_Sn_O _ H4).
    rewrite (MapCard_ext A _ _ H3). exact (mapcanon_M2 _ _ H2).
    intros a y. simple induction m'. intros. cut (MapGet A (M1 A a y) a = None). simpl in |- *.
    rewrite (Neqb_correct a). intro. discriminate H2.
    exact (H1 a).
    intros a0 y0 H H0 H1. cut (MapGet A (M1 A a y) a = MapGet A (M1 A a0 y0) a). simpl in |- *.
    rewrite (Neqb_correct a). intro. elim (sumbool_of_bool (Neqb a0 a)). intro H3.
    rewrite H3 in H2. inversion H2. rewrite (Neqb_complete _ _ H3). reflexivity.
    intro H3. rewrite H3 in H2. discriminate H2.
    exact (H1 a).
    intros. cut (2 <= MapCard A (M1 A a y)). intro. elim (le_Sn_O _ (le_S_n _ _ H4)).
    rewrite (MapCard_ext A _ _ H3). exact (mapcanon_M2 _ _ H2).
    simple induction m'. intros. cut (2 <= MapCard A (M0 A)). intro. elim (le_Sn_O _ H4).
    rewrite <- (MapCard_ext A _ _ H3). exact (mapcanon_M2 _ _ H1).
    intros a y H1 H2 H3. cut (2 <= MapCard A (M1 A a y)). intro.
    elim (le_Sn_O _ (le_S_n _ _ H4)).
    rewrite <- (MapCard_ext A _ _ H3). exact (mapcanon_M2 _ _ H1).
    intros. rewrite (H m2). rewrite (H0 m3). reflexivity.
    exact (mapcanon_M2_2 _ _ H3).
    exact (mapcanon_M2_2 _ _ H4).
    exact (M2_eqmap_2 _ _ _ _ H5).
    exact (mapcanon_M2_1 _ _ H3).
    exact (mapcanon_M2_1 _ _ H4).
    exact (M2_eqmap_1 _ _ _ _ H5).
  Qed.

  Lemma MapPut1_canon :
   forall (p:positive) (a a':ad) (y y':A), mapcanon (MapPut1 A a y a' y' p).
  Proof.
    simple induction p. simpl in |- *. intros. case (Nbit0 a). apply M2_canon. apply M1_canon.
    apply M1_canon.
    apply le_n.
    apply M2_canon. apply M1_canon.
    apply M1_canon.
    apply le_n.
    simpl in |- *. intros. case (Nbit0 a). apply M2_canon. apply M0_canon.
    apply H.
    simpl in |- *. rewrite MapCard_Put1_equals_2. apply le_n.
    apply M2_canon. apply H.
    apply M0_canon.
    simpl in |- *. rewrite MapCard_Put1_equals_2. apply le_n.
    simpl in |- *. simpl in |- *. intros. case (Nbit0 a). apply M2_canon. apply M1_canon.
    apply M1_canon.
    simpl in |- *. apply le_n.
    apply M2_canon. apply M1_canon.
    apply M1_canon.
    simpl in |- *. apply le_n.
  Qed.

  Lemma MapPut_canon :
   forall m:Map A,
     mapcanon m -> forall (a:ad) (y:A), mapcanon (MapPut A m a y).
  Proof.
    simple induction m. intros. simpl in |- *. apply M1_canon.
    intros a0 y0 H a y. simpl in |- *. case (Nxor a0 a). apply M1_canon.
    intro. apply MapPut1_canon.
    intros. simpl in |- *. elim a. apply M2_canon. apply H. exact (mapcanon_M2_1 m0 m1 H1).
    exact (mapcanon_M2_2 m0 m1 H1).
    simpl in |- *. apply le_trans with (m := MapCard A m0 + MapCard A m1). exact (mapcanon_M2 _ _ H1).
    apply plus_le_compat. exact (MapCard_Put_lb A m0 N0 y).
    apply le_n.
    intro. case p. intro. apply M2_canon. exact (mapcanon_M2_1 m0 m1 H1).
    apply H0. exact (mapcanon_M2_2 m0 m1 H1).
    simpl in |- *. apply le_trans with (m := MapCard A m0 + MapCard A m1).
    exact (mapcanon_M2 m0 m1 H1).
    apply plus_le_compat_l. exact (MapCard_Put_lb A m1 (Npos p0) y).
    intro. apply M2_canon. apply H. exact (mapcanon_M2_1 m0 m1 H1).
    exact (mapcanon_M2_2 m0 m1 H1).
    simpl in |- *. apply le_trans with (m := MapCard A m0 + MapCard A m1).
    exact (mapcanon_M2 m0 m1 H1).
    apply plus_le_compat_r. exact (MapCard_Put_lb A m0 (Npos p0) y).
    apply M2_canon. apply (mapcanon_M2_1 m0 m1 H1).
    apply H0. apply (mapcanon_M2_2 m0 m1 H1).
    simpl in |- *. apply le_trans with (m := MapCard A m0 + MapCard A m1).
    exact (mapcanon_M2 m0 m1 H1).
    apply plus_le_compat_l. exact (MapCard_Put_lb A m1 N0 y).
  Qed.

  Lemma MapPut_behind_canon :
   forall m:Map A,
     mapcanon m -> forall (a:ad) (y:A), mapcanon (MapPut_behind A m a y).
  Proof.
    simple induction m. intros. simpl in |- *. apply M1_canon.
    intros a0 y0 H a y. simpl in |- *. case (Nxor a0 a). apply M1_canon.
    intro. apply MapPut1_canon.
    intros. simpl in |- *. elim a. apply M2_canon. apply H. exact (mapcanon_M2_1 m0 m1 H1).
    exact (mapcanon_M2_2 m0 m1 H1).
    simpl in |- *. apply le_trans with (m := MapCard A m0 + MapCard A m1). exact (mapcanon_M2 _ _ H1).
    apply plus_le_compat. rewrite MapCard_Put_behind_Put. exact (MapCard_Put_lb A m0 N0 y).
    apply le_n.
    intro. case p. intro. apply M2_canon. exact (mapcanon_M2_1 m0 m1 H1).
    apply H0. exact (mapcanon_M2_2 m0 m1 H1).
    simpl in |- *. apply le_trans with (m := MapCard A m0 + MapCard A m1).
    exact (mapcanon_M2 m0 m1 H1).
    apply plus_le_compat_l. rewrite MapCard_Put_behind_Put. exact (MapCard_Put_lb A m1 (Npos p0) y).
    intro. apply M2_canon. apply H. exact (mapcanon_M2_1 m0 m1 H1).
    exact (mapcanon_M2_2 m0 m1 H1).
    simpl in |- *. apply le_trans with (m := MapCard A m0 + MapCard A m1).
    exact (mapcanon_M2 m0 m1 H1).
    apply plus_le_compat_r. rewrite MapCard_Put_behind_Put. exact (MapCard_Put_lb A m0 (Npos p0) y).
    apply M2_canon. apply (mapcanon_M2_1 m0 m1 H1).
    apply H0. apply (mapcanon_M2_2 m0 m1 H1).
    simpl in |- *. apply le_trans with (m := MapCard A m0 + MapCard A m1).
    exact (mapcanon_M2 m0 m1 H1).
    apply plus_le_compat_l. rewrite MapCard_Put_behind_Put. exact (MapCard_Put_lb A m1 N0 y).
  Qed.

  Lemma makeM2_canon :
   forall m m':Map A, mapcanon m -> mapcanon m' -> mapcanon (makeM2 A m m').
  Proof.
    intro. case m. intro. case m'. intros. exact M0_canon.
    intros a y H H0. exact (M1_canon (Ndouble_plus_one a) y).
    intros. simpl in |- *. apply M2_canon; try assumption. exact (mapcanon_M2 m0 m1 H0).
    intros a y m'. case m'. intros. exact (M1_canon (Ndouble a) y).
    intros a0 y0 H H0. simpl in |- *. apply M2_canon; try assumption. apply le_n.
    intros. simpl in |- *. apply M2_canon; try assumption.
    apply le_trans with (m := MapCard A (M2 A m0 m1)). exact (mapcanon_M2 _ _ H0).
    exact (le_plus_r (MapCard A (M1 A a y)) (MapCard A (M2 A m0 m1))).
    simpl in |- *. intros. apply M2_canon; try assumption.
    apply le_trans with (m := MapCard A (M2 A m0 m1)). exact (mapcanon_M2 _ _ H).
    exact (le_plus_l (MapCard A (M2 A m0 m1)) (MapCard A m')).
  Qed.

  Fixpoint MapCanonicalize (m:Map A) : Map A :=
    match m with
    | M2 m0 m1 => makeM2 A (MapCanonicalize m0) (MapCanonicalize m1)
    | _ => m
    end.

  Lemma mapcanon_exists_1 : forall m:Map A, eqmap A m (MapCanonicalize m).
  Proof.
    simple induction m. apply eqmap_refl.
    intros. apply eqmap_refl.
    intros. simpl in |- *. unfold eqmap, eqm in |- *. intro.
    rewrite (makeM2_M2 A (MapCanonicalize m0) (MapCanonicalize m1) a).
    rewrite MapGet_M2_bit_0_if. rewrite MapGet_M2_bit_0_if.
    rewrite <- (H (Ndiv2 a)). rewrite <- (H0 (Ndiv2 a)). reflexivity.
  Qed.

  Lemma mapcanon_exists_2 : forall m:Map A, mapcanon (MapCanonicalize m).
  Proof.
    simple induction m. apply M0_canon.
    intros. simpl in |- *. apply M1_canon.
    intros. simpl in |- *. apply makeM2_canon; assumption.
  Qed.

  Lemma mapcanon_exists :
   forall m:Map A, {m' : Map A | eqmap A m m' /\ mapcanon m'}.
  Proof.
    intro. split with (MapCanonicalize m). split. apply mapcanon_exists_1.
    apply mapcanon_exists_2.
  Qed.

  Lemma MapRemove_canon :
   forall m:Map A, mapcanon m -> forall a:ad, mapcanon (MapRemove A m a).
  Proof.
    simple induction m. intros. exact M0_canon.
    intros a y H a0. simpl in |- *. case (Neqb a a0). exact M0_canon.
    assumption.
    intros. simpl in |- *. case (Nbit0 a). apply makeM2_canon. exact (mapcanon_M2_1 _ _ H1).
    apply H0. exact (mapcanon_M2_2 _ _ H1).
    apply makeM2_canon. apply H. exact (mapcanon_M2_1 _ _ H1).
    exact (mapcanon_M2_2 _ _ H1).
  Qed.

  Lemma MapMerge_canon :
   forall m m':Map A, mapcanon m -> mapcanon m' -> mapcanon (MapMerge A m m').
  Proof.
    simple induction m. intros. exact H0.
    simpl in |- *. intros a y m' H H0. exact (MapPut_behind_canon m' H0 a y).
    simple induction m'. intros. exact H1.
    intros a y H1 H2. unfold MapMerge in |- *. exact (MapPut_canon _ H1 a y).
    intros. simpl in |- *. apply M2_canon. apply H. exact (mapcanon_M2_1 _ _ H3).
    exact (mapcanon_M2_1 _ _ H4).
    apply H0. exact (mapcanon_M2_2 _ _ H3).
    exact (mapcanon_M2_2 _ _ H4).
    change (2 <= MapCard A (MapMerge A (M2 A m0 m1) (M2 A m2 m3))) in |- *.
    apply le_trans with (m := MapCard A (M2 A m0 m1)). exact (mapcanon_M2 _ _ H3).
    exact (MapMerge_Card_lb_l A (M2 A m0 m1) (M2 A m2 m3)).
  Qed.

  Lemma MapDelta_canon :
   forall m m':Map A, mapcanon m -> mapcanon m' -> mapcanon (MapDelta A m m').
  Proof.
    simple induction m. intros. exact H0.
    simpl in |- *. intros a y m' H H0. case (MapGet A m' a).
    intro. exact (MapRemove_canon m' H0 a).
    exact (MapPut_canon m' H0 a y).
    simple induction m'. intros. exact H1.
    unfold MapDelta in |- *. intros a y H1 H2. case (MapGet A (M2 A m0 m1) a). 
    intro. exact (MapRemove_canon _ H1 a).
    exact (MapPut_canon _ H1 a y).
    intros. simpl in |- *. apply makeM2_canon. apply H. exact (mapcanon_M2_1 _ _ H3).
    exact (mapcanon_M2_1 _ _ H4).
    apply H0. exact (mapcanon_M2_2 _ _ H3).
    exact (mapcanon_M2_2 _ _ H4).
  Qed.

  Variable B : Set.

  Lemma MapDomRestrTo_canon :
   forall m:Map A,
     mapcanon m -> forall m':Map B, mapcanon (MapDomRestrTo A B m m').
  Proof.
    simple induction m. intros. exact M0_canon.
    simpl in |- *. intros a y H m'. case (MapGet B m' a). 
    intro. apply M1_canon.
    exact M0_canon.
    simple induction m'. exact M0_canon.
    unfold MapDomRestrTo in |- *. intros a y. case (MapGet A (M2 A m0 m1) a). 
    intro. apply M1_canon.
    exact M0_canon.
    intros. simpl in |- *. apply makeM2_canon. apply H. exact (mapcanon_M2_1 m0 m1 H1).
    apply H0. exact (mapcanon_M2_2 m0 m1 H1).
  Qed.

  Lemma MapDomRestrBy_canon :
   forall m:Map A,
     mapcanon m -> forall m':Map B, mapcanon (MapDomRestrBy A B m m').
  Proof.
    simple induction m. intros. exact M0_canon.
    simpl in |- *. intros a y H m'. case (MapGet B m' a); try assumption.
    intro. exact M0_canon.
    simple induction m'. exact H1.
    intros a y. simpl in |- *. case (Nbit0 a). apply makeM2_canon. exact (mapcanon_M2_1 _ _ H1).
    apply MapRemove_canon. exact (mapcanon_M2_2 _ _ H1).
    apply makeM2_canon. apply MapRemove_canon. exact (mapcanon_M2_1 _ _ H1).
    exact (mapcanon_M2_2 _ _ H1).
    intros. simpl in |- *. apply makeM2_canon. apply H. exact (mapcanon_M2_1 _ _ H1).
    apply H0. exact (mapcanon_M2_2 _ _ H1).
  Qed.

  Lemma Map_of_alist_canon : forall l:alist A, mapcanon (Map_of_alist A l).
  Proof.
    simple induction l. exact M0_canon.
    intro r. elim r. intros a y l0 H. simpl in |- *. apply MapPut_canon. assumption.
  Qed.

  Lemma MapSubset_c_1 :
   forall (m:Map A) (m':Map B),
     mapcanon m -> MapSubset A B m m' -> MapDomRestrBy A B m m' = M0 A.
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrBy_canon. assumption.
    apply M0_canon.
    exact (MapSubset_imp_2 _ _ m m' H0).
  Qed.

  Lemma MapSubset_c_2 :
   forall (m:Map A) (m':Map B),
     MapDomRestrBy A B m m' = M0 A -> MapSubset A B m m'.
  Proof.
    intros. apply MapSubset_2_imp. unfold MapSubset_2 in |- *. rewrite H. apply eqmap_refl.
  Qed.

End MapCanon.

Section FSetCanon.

  Variable A : Set.

  Lemma MapDom_canon :
   forall m:Map A, mapcanon A m -> mapcanon unit (MapDom A m).
  Proof.
    simple induction m. intro. exact (M0_canon unit).
    intros a y H. exact (M1_canon unit a _).
    intros. simpl in |- *. apply M2_canon. apply H. exact (mapcanon_M2_1 A _ _ H1).
    apply H0. exact (mapcanon_M2_2 A _ _ H1).
    change (2 <= MapCard unit (MapDom A (M2 A m0 m1))) in |- *. rewrite <- MapCard_Dom.
    exact (mapcanon_M2 A _ _ H1).
  Qed.

End FSetCanon.

Section MapFoldCanon.

  Variables A B : Set.

  Lemma MapFold_canon_1 :
   forall m0:Map B,
     mapcanon B m0 ->
     forall op:Map B -> Map B -> Map B,
       (forall m1:Map B,
          mapcanon B m1 ->
          forall m2:Map B, mapcanon B m2 -> mapcanon B (op m1 m2)) ->
       forall f:ad -> A -> Map B,
         (forall (a:ad) (y:A), mapcanon B (f a y)) ->
         forall (m:Map A) (pf:ad -> ad),
           mapcanon B (MapFold1 A (Map B) m0 op f pf m).
  Proof.
    simple induction m. intro. exact H.
    intros a y pf. simpl in |- *. apply H1.
    intros. simpl in |- *. apply H0. apply H2.
    apply H3.
  Qed.

  Lemma MapFold_canon :
   forall m0:Map B,
     mapcanon B m0 ->
     forall op:Map B -> Map B -> Map B,
       (forall m1:Map B,
          mapcanon B m1 ->
          forall m2:Map B, mapcanon B m2 -> mapcanon B (op m1 m2)) ->
       forall f:ad -> A -> Map B,
         (forall (a:ad) (y:A), mapcanon B (f a y)) ->
         forall m:Map A, mapcanon B (MapFold A (Map B) m0 op f m).
  Proof.
    intros. exact (MapFold_canon_1 m0 H op H0 f H1 m (fun a:ad => a)).
  Qed.

  Lemma MapCollect_canon :
   forall f:ad -> A -> Map B,
     (forall (a:ad) (y:A), mapcanon B (f a y)) ->
     forall m:Map A, mapcanon B (MapCollect A B f m).
  Proof.
    intros. rewrite MapCollect_as_Fold. apply MapFold_canon. apply M0_canon.
    intros. exact (MapMerge_canon B m1 m2 H0 H1).
    assumption.
  Qed.

End MapFoldCanon.
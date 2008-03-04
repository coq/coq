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
Require Import Fset.
Require Import Mapaxioms.
Require Import Mapiter.

Section MapSubsetDef.

  Variables A B : Type.

  Definition MapSubset (m:Map A) (m':Map B) :=
    forall a:ad, in_dom A a m = true -> in_dom B a m' = true.

  Definition MapSubset_1 (m:Map A) (m':Map B) :=
    match MapSweep A (fun (a:ad) (_:A) => negb (in_dom B a m')) m with
    | None => true
    | _ => false
    end.

  Definition MapSubset_2 (m:Map A) (m':Map B) :=
    eqmap A (MapDomRestrBy A B m m') (M0 A).

  Lemma MapSubset_imp_1 :
   forall (m:Map A) (m':Map B), MapSubset m m' -> MapSubset_1 m m' = true.
  Proof.
    unfold MapSubset, MapSubset_1 in |- *. intros.
    elim
     (option_sum _ (MapSweep A (fun (a:ad) (_:A) => negb (in_dom B a m')) m)).
    intro H0. elim H0. intro r. elim r. intros a y H1. cut (negb (in_dom B a m') = true).
    intro. cut (in_dom A a m = false). intro. unfold in_dom in H3.
    rewrite (MapSweep_semantics_2 _ _ m a y H1) in H3. discriminate H3.
    elim (sumbool_of_bool (in_dom A a m)). intro H3. rewrite (H a H3) in H2. discriminate H2.
    trivial.
    exact (MapSweep_semantics_1 _ _ m a y H1).
    intro H0. rewrite H0. reflexivity.
  Qed.

  Lemma MapSubset_1_imp :
   forall (m:Map A) (m':Map B), MapSubset_1 m m' = true -> MapSubset m m'.
  Proof.
    unfold MapSubset, MapSubset_1 in |- *. unfold in_dom at 2 in |- *. intros. elim (option_sum _ (MapGet A m a)).
    intro H1. elim H1. intros y H2.
    elim
     (option_sum _ (MapSweep A (fun (a:ad) (_:A) => negb (in_dom B a m')) m)). intro H3.
    elim H3. intro r. elim r. intros a' y' H4. rewrite H4 in H. discriminate H.
    intro H3. cut (negb (in_dom B a m') = false). intro. rewrite (negb_intro (in_dom B a m')).
    rewrite H4. reflexivity.
    exact (MapSweep_semantics_3 _ _ m H3 a y H2).
    intro H1. rewrite H1 in H0. discriminate H0.
  Qed.

  Lemma map_dom_empty_1 :
   forall m:Map A, eqmap A m (M0 A) -> forall a:ad, in_dom _ a m = false.
  Proof.
    unfold eqmap, eqm, in_dom in |- *. intros. rewrite (H a). reflexivity.
  Qed.

  Lemma map_dom_empty_2 :
   forall m:Map A, (forall a:ad, in_dom _ a m = false) -> eqmap A m (M0 A).
  Proof.
    unfold eqmap, eqm, in_dom in |- *. intros.
    cut
     (match MapGet A m a with
      | None => false
      | Some _ => true
      end = false).
    case (MapGet A m a); trivial.
    intros. discriminate H0.
    exact (H a).
  Qed.

  Lemma MapSubset_imp_2 :
   forall (m:Map A) (m':Map B), MapSubset m m' -> MapSubset_2 m m'.
  Proof.
    unfold MapSubset, MapSubset_2 in |- *. intros. apply map_dom_empty_2. intro. rewrite in_dom_restrby.
    elim (sumbool_of_bool (in_dom A a m)). intro H0. rewrite H0. rewrite (H a H0). reflexivity.
    intro H0. rewrite H0. reflexivity.
  Qed.

  Lemma MapSubset_2_imp :
   forall (m:Map A) (m':Map B), MapSubset_2 m m' -> MapSubset m m'.
  Proof.
    unfold MapSubset, MapSubset_2 in |- *. intros. cut (in_dom _ a (MapDomRestrBy A B m m') = false).
    rewrite in_dom_restrby. intro. elim (andb_false_elim _ _ H1). rewrite H0.
    intro H2. discriminate H2.
    intro H2. rewrite (negb_intro (in_dom B a m')). rewrite H2. reflexivity.
    exact (map_dom_empty_1 _ H a).
  Qed.

End MapSubsetDef.

Section MapSubsetOrder.

  Variables A B C : Type.

  Lemma MapSubset_refl : forall m:Map A, MapSubset A A m m.
  Proof.
      unfold MapSubset in |- *. trivial.
  Qed.

  Lemma MapSubset_antisym :
   forall (m:Map A) (m':Map B),
     MapSubset A B m m' ->
     MapSubset B A m' m -> eqmap unit (MapDom A m) (MapDom B m').
  Proof.
    unfold MapSubset, eqmap, eqm in |- *. intros. elim (option_sum _ (MapGet _ (MapDom A m) a)).
    intro H1. elim H1. intro t. elim t. intro H2. elim (option_sum _ (MapGet _ (MapDom B m') a)).
    intro H3. elim H3. intro t'. elim t'. intro H4. rewrite H4. exact H2. 
    intro H3. cut (in_dom B a m' = true). intro. rewrite (MapDom_Dom B m' a) in H4.
    unfold in_FSet, in_dom in H4. rewrite H3 in H4. discriminate H4.
    apply H. rewrite (MapDom_Dom A m a). unfold in_FSet, in_dom in |- *. rewrite H2. reflexivity.
    intro H1. elim (option_sum _ (MapGet _ (MapDom B m') a)). intro H2. elim H2. intros t H3.
    cut (in_dom A a m = true). intro. rewrite (MapDom_Dom A m a) in H4. unfold in_FSet, in_dom in H4.
    rewrite H1 in H4. discriminate H4.
    apply H0. rewrite (MapDom_Dom B m' a). unfold in_FSet, in_dom in |- *. rewrite H3. reflexivity.
    intro H2. rewrite H2. exact H1.
  Qed.

  Lemma MapSubset_trans :
   forall (m:Map A) (m':Map B) (m'':Map C),
     MapSubset A B m m' -> MapSubset B C m' m'' -> MapSubset A C m m''.
  Proof.
    unfold MapSubset in |- *. intros. apply H0. apply H. assumption.
  Qed.

End MapSubsetOrder.

Section FSubsetOrder.

  Lemma FSubset_refl : forall s:FSet, MapSubset _ _ s s.
  Proof.
    exact (MapSubset_refl unit).
  Qed.

  Lemma FSubset_antisym :
   forall s s':FSet,
     MapSubset _ _ s s' -> MapSubset _ _ s' s -> eqmap unit s s'.
  Proof.
    intros. rewrite <- (FSet_Dom s). rewrite <- (FSet_Dom s').
    exact (MapSubset_antisym _ _ s s' H H0).
  Qed.

  Lemma FSubset_trans :
   forall s s' s'':FSet,
     MapSubset _ _ s s' -> MapSubset _ _ s' s'' -> MapSubset _ _ s s''.
  Proof.
    exact (MapSubset_trans unit unit unit).
  Qed.

End FSubsetOrder.

Section MapSubsetExtra.

  Variables A B : Type.

  Lemma MapSubset_Dom_1 :
   forall (m:Map A) (m':Map B),
     MapSubset A B m m' -> MapSubset unit unit (MapDom A m) (MapDom B m').
  Proof.
    unfold MapSubset in |- *. intros. elim (MapDom_semantics_2 _ m a H0). intros y H1.
    cut (in_dom A a m = true -> in_dom B a m' = true). intro. unfold in_dom in H2.
    rewrite H1 in H2. elim (option_sum _ (MapGet B m' a)). intro H3. elim H3.
    intros y' H4. exact (MapDom_semantics_1 _ m' a y' H4).
    intro H3. rewrite H3 in H2. cut (false = true). intro. discriminate H4.
    apply H2. reflexivity.
    exact (H a).
  Qed.

  Lemma MapSubset_Dom_2 :
   forall (m:Map A) (m':Map B),
     MapSubset unit unit (MapDom A m) (MapDom B m') -> MapSubset A B m m'.
  Proof.
    unfold MapSubset in |- *. intros. unfold in_dom in H0. elim (option_sum _ (MapGet A m a)).
    intro H1. elim H1. intros y H2.
    elim (MapDom_semantics_2 _ _ _ (H a (MapDom_semantics_1 _ _ _ _ H2))). intros y' H3.
    unfold in_dom in |- *. rewrite H3. reflexivity.
    intro H1. rewrite H1 in H0. discriminate H0.
  Qed.

  Lemma MapSubset_1_Dom :
   forall (m:Map A) (m':Map B),
     MapSubset_1 A B m m' = MapSubset_1 unit unit (MapDom A m) (MapDom B m').
  Proof.
    intros. elim (sumbool_of_bool (MapSubset_1 A B m m')). intro H. rewrite H.
    apply sym_eq. apply MapSubset_imp_1. apply MapSubset_Dom_1. exact (MapSubset_1_imp _ _ _ _ H).
    intro H. rewrite H. elim (sumbool_of_bool (MapSubset_1 unit unit (MapDom A m) (MapDom B m'))).
    intro H0.
    rewrite
     (MapSubset_imp_1 _ _ _ _
        (MapSubset_Dom_2 _ _ (MapSubset_1_imp _ _ _ _ H0)))
      in H.
    discriminate H.
    intro. apply sym_eq. assumption.
  Qed.

  Lemma MapSubset_Put :
   forall (m:Map A) (a:ad) (y:A), MapSubset A A m (MapPut A m a y).
  Proof.
    unfold MapSubset in |- *. intros. rewrite in_dom_put. rewrite H. apply orb_b_true.
  Qed.

  Lemma MapSubset_Put_mono :
   forall (m:Map A) (m':Map B) (a:ad) (y:A) (y':B),
     MapSubset A B m m' -> MapSubset A B (MapPut A m a y) (MapPut B m' a y').
  Proof.
    unfold MapSubset in |- *. intros. rewrite in_dom_put. rewrite (in_dom_put A m a y a0) in H0.
    elim (orb_true_elim _ _ H0). intro H1. rewrite H1. reflexivity.
    intro H1. rewrite (H _ H1). apply orb_b_true.
  Qed.

  Lemma MapSubset_Put_behind :
   forall (m:Map A) (a:ad) (y:A), MapSubset A A m (MapPut_behind A m a y).
  Proof.
    unfold MapSubset in |- *. intros. rewrite in_dom_put_behind. rewrite H. apply orb_b_true.
  Qed.

  Lemma MapSubset_Put_behind_mono :
   forall (m:Map A) (m':Map B) (a:ad) (y:A) (y':B),
     MapSubset A B m m' ->
     MapSubset A B (MapPut_behind A m a y) (MapPut_behind B m' a y').
  Proof.
    unfold MapSubset in |- *. intros. rewrite in_dom_put_behind.
    rewrite (in_dom_put_behind A m a y a0) in H0.
    elim (orb_true_elim _ _ H0). intro H1. rewrite H1. reflexivity.
    intro H1. rewrite (H _ H1). apply orb_b_true.
  Qed.

  Lemma MapSubset_Remove :
   forall (m:Map A) (a:ad), MapSubset A A (MapRemove A m a) m.
  Proof.
    unfold MapSubset in |- *. intros. unfold MapSubset in |- *. intros. rewrite (in_dom_remove _ m a a0) in H.
    elim (andb_prop _ _ H). trivial.
  Qed.

  Lemma MapSubset_Remove_mono :
   forall (m:Map A) (m':Map B) (a:ad),
     MapSubset A B m m' -> MapSubset A B (MapRemove A m a) (MapRemove B m' a).
  Proof.
    unfold MapSubset in |- *. intros. rewrite in_dom_remove. rewrite (in_dom_remove A m a a0) in H0.
    elim (andb_prop _ _ H0). intros. rewrite H1. rewrite (H _ H2). reflexivity.
  Qed.

  Lemma MapSubset_Merge_l :
   forall m m':Map A, MapSubset A A m (MapMerge A m m').
  Proof.
    unfold MapSubset in |- *. intros. rewrite in_dom_merge. rewrite H. reflexivity.
  Qed.

  Lemma MapSubset_Merge_r :
   forall m m':Map A, MapSubset A A m' (MapMerge A m m').
  Proof.
    unfold MapSubset in |- *. intros. rewrite in_dom_merge. rewrite H. apply orb_b_true.
  Qed.

  Lemma MapSubset_Merge_mono :
   forall (m m':Map A) (m'' m''':Map B),
     MapSubset A B m m'' ->
     MapSubset A B m' m''' ->
     MapSubset A B (MapMerge A m m') (MapMerge B m'' m''').
  Proof.
    unfold MapSubset in |- *. intros. rewrite in_dom_merge. rewrite (in_dom_merge A m m' a) in H1.
    elim (orb_true_elim _ _ H1). intro H2. rewrite (H _ H2). reflexivity.
    intro H2. rewrite (H0 _ H2). apply orb_b_true.
  Qed.

  Lemma MapSubset_DomRestrTo_l :
   forall (m:Map A) (m':Map B), MapSubset A A (MapDomRestrTo A B m m') m.
  Proof.
    unfold MapSubset in |- *. intros. rewrite (in_dom_restrto _ _ m m' a) in H. elim (andb_prop _ _ H).
    trivial.
  Qed.

  Lemma MapSubset_DomRestrTo_r :
   forall (m:Map A) (m':Map B), MapSubset A B (MapDomRestrTo A B m m') m'.
  Proof.
    unfold MapSubset in |- *. intros. rewrite (in_dom_restrto _ _ m m' a) in H. elim (andb_prop _ _ H).
    trivial.
  Qed.

  Lemma MapSubset_ext :
   forall (m0 m1:Map A) (m2 m3:Map B),
     eqmap A m0 m1 ->
     eqmap B m2 m3 -> MapSubset A B m0 m2 -> MapSubset A B m1 m3.
  Proof.
    intros. apply MapSubset_2_imp. unfold MapSubset_2 in |- *.
    apply eqmap_trans with (m' := MapDomRestrBy A B m0 m2). apply MapDomRestrBy_ext. apply eqmap_sym.
    assumption.
    apply eqmap_sym. assumption.
    exact (MapSubset_imp_2 _ _ _ _ H1).
  Qed.

  Variables C D : Type.

  Lemma MapSubset_DomRestrTo_mono :
   forall (m:Map A) (m':Map B) (m'':Map C) (m''':Map D),
     MapSubset _ _ m m'' ->
     MapSubset _ _ m' m''' ->
     MapSubset _ _ (MapDomRestrTo _ _ m m') (MapDomRestrTo _ _ m'' m''').
  Proof.
    unfold MapSubset in |- *. intros. rewrite in_dom_restrto. rewrite (in_dom_restrto A B m m' a) in H1.
    elim (andb_prop _ _ H1). intros. rewrite (H _ H2). rewrite (H0 _ H3). reflexivity.
  Qed.

  Lemma MapSubset_DomRestrBy_l :
   forall (m:Map A) (m':Map B), MapSubset A A (MapDomRestrBy A B m m') m.
  Proof.
    unfold MapSubset in |- *. intros. rewrite (in_dom_restrby _ _ m m' a) in H. elim (andb_prop _ _ H).
    trivial.
  Qed.

  Lemma MapSubset_DomRestrBy_mono :
   forall (m:Map A) (m':Map B) (m'':Map C) (m''':Map D),
     MapSubset _ _ m m'' ->
     MapSubset _ _ m''' m' ->
     MapSubset _ _ (MapDomRestrBy _ _ m m') (MapDomRestrBy _ _ m'' m''').
  Proof.
    unfold MapSubset in |- *. intros. rewrite in_dom_restrby. rewrite (in_dom_restrby A B m m' a) in H1.
    elim (andb_prop _ _ H1). intros. rewrite (H _ H2). elim (sumbool_of_bool (in_dom D a m''')).
    intro H4. rewrite (H0 _ H4) in H3. discriminate H3.
    intro H4. rewrite H4. reflexivity.
  Qed.
  
End MapSubsetExtra.

Section MapDisjointDef.

  Variables A B : Type.

  Definition MapDisjoint (m:Map A) (m':Map B) :=
    forall a:ad, in_dom A a m = true -> in_dom B a m' = true -> False.

  Definition MapDisjoint_1 (m:Map A) (m':Map B) :=
    match MapSweep A (fun (a:ad) (_:A) => in_dom B a m') m with
    | None => true
    | _ => false
    end.

  Definition MapDisjoint_2 (m:Map A) (m':Map B) :=
    eqmap A (MapDomRestrTo A B m m') (M0 A).

  Lemma MapDisjoint_imp_1 :
   forall (m:Map A) (m':Map B), MapDisjoint m m' -> MapDisjoint_1 m m' = true.
  Proof.
    unfold MapDisjoint, MapDisjoint_1 in |- *. intros.
    elim (option_sum _ (MapSweep A (fun (a:ad) (_:A) => in_dom B a m') m)). intro H0. elim H0.
    intro r. elim r. intros a y H1. cut (in_dom A a m = true -> in_dom B a m' = true -> False).
    intro. unfold in_dom at 1 in H2. rewrite (MapSweep_semantics_2 _ _ _ _ _ H1) in H2.
    rewrite (MapSweep_semantics_1 _ _ _ _ _ H1) in H2. elim (H2 (refl_equal _) (refl_equal _)).
    exact (H a).
    intro H0. rewrite H0. reflexivity.
  Qed.

  Lemma MapDisjoint_1_imp :
   forall (m:Map A) (m':Map B), MapDisjoint_1 m m' = true -> MapDisjoint m m'.
  Proof.
    unfold MapDisjoint, MapDisjoint_1 in |- *. intros.
    elim (option_sum _ (MapSweep A (fun (a:ad) (_:A) => in_dom B a m') m)). intro H2. elim H2.
    intro r. elim r. intros a' y' H3. rewrite H3 in H. discriminate H.
    intro H2. unfold in_dom in H0. elim (option_sum _ (MapGet A m a)). intro H3. elim H3.
    intros y H4. rewrite (MapSweep_semantics_3 _ _ _ H2 a y H4) in H1. discriminate H1.
    intro H3. rewrite H3 in H0. discriminate H0.
  Qed.

  Lemma MapDisjoint_imp_2 :
   forall (m:Map A) (m':Map B), MapDisjoint m m' -> MapDisjoint_2 m m'.
  Proof.
    unfold MapDisjoint, MapDisjoint_2 in |- *. unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrTo_semantics A B m m' a).
    cut (in_dom A a m = true -> in_dom B a m' = true -> False). intro.
    elim (option_sum _ (MapGet A m a)). intro H1. elim H1. intros y H2. unfold in_dom at 1 in H0.
    elim (option_sum _ (MapGet B m' a)). intro H3. elim H3. intros y' H4. unfold in_dom at 1 in H0.
    rewrite H4 in H0. rewrite H2 in H0. elim (H0 (refl_equal _) (refl_equal _)).
    intro H3. rewrite H3. reflexivity.
    intro H1. rewrite H1. case (MapGet B m' a); reflexivity.
    exact (H a).
  Qed.

  Lemma MapDisjoint_2_imp :
   forall (m:Map A) (m':Map B), MapDisjoint_2 m m' -> MapDisjoint m m'.
  Proof.
    unfold MapDisjoint, MapDisjoint_2 in |- *. unfold eqmap, eqm in |- *. intros. elim (in_dom_some _ _ _ H0).
    intros y H2. elim (in_dom_some _ _ _ H1). intros y' H3.
    cut (MapGet A (MapDomRestrTo A B m m') a = None). intro.
    rewrite (MapDomRestrTo_semantics _ _ m m' a) in H4. rewrite H3 in H4. rewrite H2 in H4.
    discriminate H4.
    exact (H a).
  Qed.

  Lemma Map_M0_disjoint : forall m:Map B, MapDisjoint (M0 A) m.
  Proof.
    unfold MapDisjoint, in_dom in |- *. intros. discriminate H.
  Qed.

  Lemma Map_disjoint_M0 : forall m:Map A, MapDisjoint m (M0 B).
  Proof.
    unfold MapDisjoint, in_dom in |- *. intros. discriminate H0.
  Qed.

End MapDisjointDef.

Section MapDisjointExtra.

  Variables A B : Type.

  Lemma MapDisjoint_ext :
   forall (m0 m1:Map A) (m2 m3:Map B),
     eqmap A m0 m1 ->
     eqmap B m2 m3 -> MapDisjoint A B m0 m2 -> MapDisjoint A B m1 m3.
  Proof.
    intros. apply MapDisjoint_2_imp. unfold MapDisjoint_2 in |- *.
    apply eqmap_trans with (m' := MapDomRestrTo A B m0 m2). apply eqmap_sym. apply MapDomRestrTo_ext.
    assumption.
    assumption.
    exact (MapDisjoint_imp_2 _ _ _ _ H1).
  Qed.

  Lemma MapMerge_disjoint :
   forall m m':Map A,
     MapDisjoint A A m m' ->
     forall a:ad,
       in_dom A a (MapMerge A m m') =
       orb (andb (in_dom A a m) (negb (in_dom A a m')))
         (andb (in_dom A a m') (negb (in_dom A a m))).
  Proof.
    unfold MapDisjoint in |- *. intros. rewrite in_dom_merge. elim (sumbool_of_bool (in_dom A a m)).
    intro H0. rewrite H0. elim (sumbool_of_bool (in_dom A a m')). intro H1. elim (H a H0 H1).
    intro H1. rewrite H1. reflexivity.
    intro H0. rewrite H0. simpl in |- *. rewrite andb_b_true. reflexivity.
  Qed.

  Lemma MapDisjoint_M2_l :
   forall (m0 m1:Map A) (m2 m3:Map B),
     MapDisjoint A B (M2 A m0 m1) (M2 B m2 m3) -> MapDisjoint A B m0 m2.
  Proof.
    unfold MapDisjoint, in_dom in |- *. intros. elim (option_sum _ (MapGet A m0 a)). intro H2.
    elim H2. intros y H3. elim (option_sum _ (MapGet B m2 a)). intro H4. elim H4.
    intros y' H5. apply (H (Ndouble a)).
    rewrite (MapGet_M2_bit_0_0 _ (Ndouble a) (Ndouble_bit0 a) m0 m1).
    rewrite (Ndouble_div2 a). rewrite H3. reflexivity.
    rewrite (MapGet_M2_bit_0_0 _ (Ndouble a) (Ndouble_bit0 a) m2 m3).
    rewrite (Ndouble_div2 a). rewrite H5. reflexivity.
    intro H4. rewrite H4 in H1. discriminate H1.
    intro H2. rewrite H2 in H0. discriminate H0.
  Qed.

  Lemma MapDisjoint_M2_r :
   forall (m0 m1:Map A) (m2 m3:Map B),
     MapDisjoint A B (M2 A m0 m1) (M2 B m2 m3) -> MapDisjoint A B m1 m3.
  Proof.
    unfold MapDisjoint, in_dom in |- *. intros. elim (option_sum _ (MapGet A m1 a)). intro H2.
    elim H2. intros y H3. elim (option_sum _ (MapGet B m3 a)). intro H4. elim H4.
    intros y' H5. apply (H (Ndouble_plus_one a)).
    rewrite
     (MapGet_M2_bit_0_1 _ (Ndouble_plus_one a) (Ndouble_plus_one_bit0 a)
        m0 m1).
    rewrite (Ndouble_plus_one_div2 a). rewrite H3. reflexivity.
    rewrite
     (MapGet_M2_bit_0_1 _ (Ndouble_plus_one a) (Ndouble_plus_one_bit0 a)
        m2 m3).
    rewrite (Ndouble_plus_one_div2 a). rewrite H5. reflexivity.
    intro H4. rewrite H4 in H1. discriminate H1.
    intro H2. rewrite H2 in H0. discriminate H0.
  Qed.

  Lemma MapDisjoint_M2 :
   forall (m0 m1:Map A) (m2 m3:Map B),
     MapDisjoint A B m0 m2 ->
     MapDisjoint A B m1 m3 -> MapDisjoint A B (M2 A m0 m1) (M2 B m2 m3).
  Proof.
    unfold MapDisjoint, in_dom in |- *. intros. elim (sumbool_of_bool (Nbit0 a)). intro H3.
    rewrite (MapGet_M2_bit_0_1 A a H3 m0 m1) in H1.
    rewrite (MapGet_M2_bit_0_1 B a H3 m2 m3) in H2. exact (H0 (Ndiv2 a) H1 H2).
    intro H3. rewrite (MapGet_M2_bit_0_0 A a H3 m0 m1) in H1.
    rewrite (MapGet_M2_bit_0_0 B a H3 m2 m3) in H2. exact (H (Ndiv2 a) H1 H2).
  Qed.

  Lemma MapDisjoint_M1_l :
   forall (m:Map A) (a:ad) (y:B),
     MapDisjoint B A (M1 B a y) m -> in_dom A a m = false.
  Proof.
    unfold MapDisjoint in |- *. intros. elim (sumbool_of_bool (in_dom A a m)). intro H0.
    elim (H a (in_dom_M1_1 B a y) H0).
    trivial.
  Qed.

  Lemma MapDisjoint_M1_r :
   forall (m:Map A) (a:ad) (y:B),
     MapDisjoint A B m (M1 B a y) -> in_dom A a m = false.
  Proof.
    unfold MapDisjoint in |- *. intros. elim (sumbool_of_bool (in_dom A a m)). intro H0.
    elim (H a H0 (in_dom_M1_1 B a y)).
    trivial.
  Qed.

  Lemma MapDisjoint_M1_conv_l :
   forall (m:Map A) (a:ad) (y:B),
     in_dom A a m = false -> MapDisjoint B A (M1 B a y) m.
  Proof.
    unfold MapDisjoint in |- *. intros. rewrite (in_dom_M1_2 B a a0 y H0) in H. rewrite H1 in H.
    discriminate H.
  Qed.

  Lemma MapDisjoint_M1_conv_r :
   forall (m:Map A) (a:ad) (y:B),
     in_dom A a m = false -> MapDisjoint A B m (M1 B a y).
  Proof.
    unfold MapDisjoint in |- *. intros. rewrite (in_dom_M1_2 B a a0 y H1) in H. rewrite H0 in H.
    discriminate H.
  Qed.
 
  Lemma MapDisjoint_sym :
   forall (m:Map A) (m':Map B), MapDisjoint A B m m' -> MapDisjoint B A m' m.
  Proof.
    unfold MapDisjoint in |- *. intros. exact (H _ H1 H0).
  Qed.

  Lemma MapDisjoint_empty :
   forall m:Map A, MapDisjoint A A m m -> eqmap A m (M0 A).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite <- (MapDomRestrTo_idempotent A m a).
    exact (MapDisjoint_imp_2 A A m m H a).
  Qed.

  Lemma MapDelta_disjoint :
   forall m m':Map A,
     MapDisjoint A A m m' -> eqmap A (MapDelta A m m') (MapMerge A m m').
  Proof.
    intros.
    apply eqmap_trans with
     (m' := MapDomRestrBy A A (MapMerge A m m') (MapDomRestrTo A A m m')).
    apply MapDelta_as_DomRestrBy.
    apply eqmap_trans with (m' := MapDomRestrBy A A (MapMerge A m m') (M0 A)).
    apply MapDomRestrBy_ext. apply eqmap_refl.
    exact (MapDisjoint_imp_2 A A m m' H).
    apply MapDomRestrBy_m_empty.
  Qed.

  Variable C : Type.

  Lemma MapDomRestr_disjoint :
   forall (m:Map A) (m':Map B) (m'':Map C),
     MapDisjoint A B (MapDomRestrTo A C m m'') (MapDomRestrBy B C m' m'').
  Proof.
    unfold MapDisjoint in |- *. intros m m' m'' a. rewrite in_dom_restrto. rewrite in_dom_restrby.
    intros. elim (andb_prop _ _ H). elim (andb_prop _ _ H0). intros. rewrite H4 in H2.
    discriminate H2.
  Qed.

  Lemma MapDelta_RestrTo_disjoint :
   forall m m':Map A,
     MapDisjoint A A (MapDelta A m m') (MapDomRestrTo A A m m').
  Proof.
    unfold MapDisjoint in |- *. intros m m' a. rewrite in_dom_delta. rewrite in_dom_restrto.
    intros. elim (andb_prop _ _ H0). intros. rewrite H1 in H. rewrite H2 in H. discriminate H.
  Qed.

  Lemma MapDelta_RestrTo_disjoint_2 :
   forall m m':Map A,
     MapDisjoint A A (MapDelta A m m') (MapDomRestrTo A A m' m).
  Proof.
    unfold MapDisjoint in |- *. intros m m' a. rewrite in_dom_delta. rewrite in_dom_restrto.
    intros. elim (andb_prop _ _ H0). intros. rewrite H1 in H. rewrite H2 in H. discriminate H.
  Qed.

  Variable D : Type.

  Lemma MapSubset_Disjoint :
   forall (m:Map A) (m':Map B) (m'':Map C) (m''':Map D),
     MapSubset _ _ m m' ->
     MapSubset _ _ m'' m''' ->
     MapDisjoint _ _ m' m''' -> MapDisjoint _ _ m m''.
  Proof.
    unfold MapSubset, MapDisjoint in |- *. intros. exact (H1 _ (H _ H2) (H0 _ H3)).
  Qed.

  Lemma MapSubset_Disjoint_l :
   forall (m:Map A) (m':Map B) (m'':Map C),
     MapSubset _ _ m m' -> MapDisjoint _ _ m' m'' -> MapDisjoint _ _ m m''.
  Proof.
    unfold MapSubset, MapDisjoint in |- *. intros. exact (H0 _ (H _ H1) H2).
  Qed.

  Lemma MapSubset_Disjoint_r :
   forall (m:Map A) (m'':Map C) (m''':Map D),
     MapSubset _ _ m'' m''' ->
     MapDisjoint _ _ m m''' -> MapDisjoint _ _ m m''.
  Proof.
    unfold MapSubset, MapDisjoint in |- *. intros. exact (H0 _ H1 (H _ H2)).
  Qed.

End MapDisjointExtra.
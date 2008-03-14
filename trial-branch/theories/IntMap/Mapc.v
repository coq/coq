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
Require Import Map.
Require Import Mapaxioms.
Require Import Fset.
Require Import Mapiter.
Require Import Mapsubset.
Require Import List.
Require Import Lsort.
Require Import Mapcard.
Require Import Mapcanon.

Section MapC.

  Variables A B C : Set.

  Lemma MapPut_as_Merge_c :
   forall m:Map A,
     mapcanon A m ->
     forall (a:ad) (y:A), MapPut A m a y = MapMerge A m (M1 A a y).
  Proof.
    intros. apply mapcanon_unique. exact (MapPut_canon A m H a y).
    apply MapMerge_canon. assumption.
    apply M1_canon.
    apply MapPut_as_Merge.
  Qed.

  Lemma MapPut_behind_as_Merge_c :
   forall m:Map A,
     mapcanon A m ->
     forall (a:ad) (y:A), MapPut_behind A m a y = MapMerge A (M1 A a y) m.
  Proof.
    intros. apply mapcanon_unique. exact (MapPut_behind_canon A m H a y).
    apply MapMerge_canon. apply M1_canon.
    assumption.
    apply MapPut_behind_as_Merge.
  Qed.

  Lemma MapMerge_empty_m_c : forall m:Map A, MapMerge A (M0 A) m = m.
  Proof.
    trivial.
  Qed.

  Lemma MapMerge_assoc_c :
   forall m m' m'':Map A,
     mapcanon A m ->
     mapcanon A m' ->
     mapcanon A m'' ->
     MapMerge A (MapMerge A m m') m'' = MapMerge A m (MapMerge A m' m'').
  Proof.
    intros. apply mapcanon_unique.
    apply MapMerge_canon; try assumption. apply MapMerge_canon; try assumption.
    apply MapMerge_canon; try assumption. apply MapMerge_canon; try assumption.
    apply MapMerge_assoc.
  Qed.

  Lemma MapMerge_idempotent_c :
   forall m:Map A, mapcanon A m -> MapMerge A m m = m.
  Proof.
    intros. apply mapcanon_unique. apply MapMerge_canon; assumption.
    assumption.
    apply MapMerge_idempotent.
  Qed.

  Lemma MapMerge_RestrTo_l_c :
   forall m m' m'':Map A,
     mapcanon A m ->
     mapcanon A m'' ->
     MapMerge A (MapDomRestrTo A A m m') m'' =
     MapDomRestrTo A A (MapMerge A m m'') (MapMerge A m' m'').
  Proof.
    intros. apply mapcanon_unique. apply MapMerge_canon. apply MapDomRestrTo_canon; assumption.
    assumption.
    apply MapDomRestrTo_canon; apply MapMerge_canon; assumption.
    apply MapMerge_RestrTo_l.
  Qed.

  Lemma MapRemove_as_RestrBy_c :
   forall m:Map A,
     mapcanon A m ->
     forall (a:ad) (y:B), MapRemove A m a = MapDomRestrBy A B m (M1 B a y).
  Proof.
    intros. apply mapcanon_unique. apply MapRemove_canon; assumption.
    apply MapDomRestrBy_canon; assumption.
    apply MapRemove_as_RestrBy.
  Qed.

  Lemma MapDomRestrTo_assoc_c :
   forall (m:Map A) (m':Map B) (m'':Map C),
     mapcanon A m ->
     MapDomRestrTo A C (MapDomRestrTo A B m m') m'' =
     MapDomRestrTo A B m (MapDomRestrTo B C m' m'').
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrTo_canon; try assumption.
    apply MapDomRestrTo_canon; try assumption.
    apply MapDomRestrTo_canon; try assumption.
    apply MapDomRestrTo_assoc.
  Qed.

  Lemma MapDomRestrTo_idempotent_c :
   forall m:Map A, mapcanon A m -> MapDomRestrTo A A m m = m.
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrTo_canon; assumption.
    assumption.
    apply MapDomRestrTo_idempotent.
  Qed.

  Lemma MapDomRestrTo_Dom_c :
   forall (m:Map A) (m':Map B),
     mapcanon A m ->
     MapDomRestrTo A B m m' = MapDomRestrTo A unit m (MapDom B m').
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrTo_Dom.
  Qed.

  Lemma MapDomRestrBy_Dom_c :
   forall (m:Map A) (m':Map B),
     mapcanon A m ->
     MapDomRestrBy A B m m' = MapDomRestrBy A unit m (MapDom B m').
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrBy_canon; assumption.
    apply MapDomRestrBy_canon; assumption.
    apply MapDomRestrBy_Dom.
  Qed.

  Lemma MapDomRestrBy_By_c :
   forall (m:Map A) (m' m'':Map B),
     mapcanon A m ->
     MapDomRestrBy A B (MapDomRestrBy A B m m') m'' =
     MapDomRestrBy A B m (MapMerge B m' m'').
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrBy_canon; try assumption.
    apply MapDomRestrBy_canon; try assumption.
    apply MapDomRestrBy_canon; try assumption.
    apply MapDomRestrBy_By.
  Qed.

  Lemma MapDomRestrBy_By_comm_c :
   forall (m:Map A) (m':Map B) (m'':Map C),
     mapcanon A m ->
     MapDomRestrBy A C (MapDomRestrBy A B m m') m'' =
     MapDomRestrBy A B (MapDomRestrBy A C m m'') m'.
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrBy_canon.
    apply MapDomRestrBy_canon; assumption.
    apply MapDomRestrBy_canon. apply MapDomRestrBy_canon; assumption.
    apply MapDomRestrBy_By_comm.
  Qed.

  Lemma MapDomRestrBy_To_c :
   forall (m:Map A) (m':Map B) (m'':Map C),
     mapcanon A m ->
     MapDomRestrBy A C (MapDomRestrTo A B m m') m'' =
     MapDomRestrTo A B m (MapDomRestrBy B C m' m'').
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrBy_canon.
    apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrBy_To.
  Qed.

  Lemma MapDomRestrBy_To_comm_c :
   forall (m:Map A) (m':Map B) (m'':Map C),
     mapcanon A m ->
     MapDomRestrBy A C (MapDomRestrTo A B m m') m'' =
     MapDomRestrTo A B (MapDomRestrBy A C m m'') m'.
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrBy_canon.
    apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrTo_canon. apply MapDomRestrBy_canon; assumption.
    apply MapDomRestrBy_To_comm.
  Qed.

  Lemma MapDomRestrTo_By_c :
   forall (m:Map A) (m':Map B) (m'':Map C),
     mapcanon A m ->
     MapDomRestrTo A C (MapDomRestrBy A B m m') m'' =
     MapDomRestrTo A C m (MapDomRestrBy C B m'' m').
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrTo_canon.
    apply MapDomRestrBy_canon; assumption.
    apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrTo_By.
  Qed.

  Lemma MapDomRestrTo_By_comm_c :
   forall (m:Map A) (m':Map B) (m'':Map C),
     mapcanon A m ->
     MapDomRestrTo A C (MapDomRestrBy A B m m') m'' =
     MapDomRestrBy A B (MapDomRestrTo A C m m'') m'.
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrTo_canon.
    apply MapDomRestrBy_canon; assumption.
    apply MapDomRestrBy_canon. apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrTo_By_comm.
  Qed.

  Lemma MapDomRestrTo_To_comm_c :
   forall (m:Map A) (m':Map B) (m'':Map C),
     mapcanon A m ->
     MapDomRestrTo A C (MapDomRestrTo A B m m') m'' =
     MapDomRestrTo A B (MapDomRestrTo A C m m'') m'.
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrTo_canon.
    apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrTo_canon. apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrTo_To_comm.
  Qed.

  Lemma MapMerge_DomRestrTo_c :
   forall (m m':Map A) (m'':Map B),
     mapcanon A m ->
     mapcanon A m' ->
     MapDomRestrTo A B (MapMerge A m m') m'' =
     MapMerge A (MapDomRestrTo A B m m'') (MapDomRestrTo A B m' m'').
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrTo_canon.
    apply MapMerge_canon; assumption.
    apply MapMerge_canon. apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrTo_canon; assumption.
    apply MapMerge_DomRestrTo.
  Qed.

  Lemma MapMerge_DomRestrBy_c :
   forall (m m':Map A) (m'':Map B),
     mapcanon A m ->
     mapcanon A m' ->
     MapDomRestrBy A B (MapMerge A m m') m'' =
     MapMerge A (MapDomRestrBy A B m m'') (MapDomRestrBy A B m' m'').
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrBy_canon. apply MapMerge_canon; assumption.
    apply MapMerge_canon. apply MapDomRestrBy_canon; assumption.
    apply MapDomRestrBy_canon; assumption.
    apply MapMerge_DomRestrBy.
  Qed.

  Lemma MapDelta_nilpotent_c :
   forall m:Map A, mapcanon A m -> MapDelta A m m = M0 A.
  Proof.
    intros. apply mapcanon_unique. apply MapDelta_canon; assumption.
    apply M0_canon.
    apply MapDelta_nilpotent.
  Qed.

  Lemma MapDelta_as_Merge_c :
   forall m m':Map A,
     mapcanon A m ->
     mapcanon A m' ->
     MapDelta A m m' =
     MapMerge A (MapDomRestrBy A A m m') (MapDomRestrBy A A m' m).
  Proof.
    intros. apply mapcanon_unique. apply MapDelta_canon; assumption.
    apply MapMerge_canon; apply MapDomRestrBy_canon; assumption.
    apply MapDelta_as_Merge.
  Qed.

  Lemma MapDelta_as_DomRestrBy_c :
   forall m m':Map A,
     mapcanon A m ->
     mapcanon A m' ->
     MapDelta A m m' =
     MapDomRestrBy A A (MapMerge A m m') (MapDomRestrTo A A m m').
  Proof.
    intros. apply mapcanon_unique. apply MapDelta_canon; assumption.
    apply MapDomRestrBy_canon. apply MapMerge_canon; assumption.
    apply MapDelta_as_DomRestrBy.
  Qed.

  Lemma MapDelta_as_DomRestrBy_2_c :
   forall m m':Map A,
     mapcanon A m ->
     mapcanon A m' ->
     MapDelta A m m' =
     MapDomRestrBy A A (MapMerge A m m') (MapDomRestrTo A A m' m).
  Proof.
    intros. apply mapcanon_unique. apply MapDelta_canon; assumption.
    apply MapDomRestrBy_canon. apply MapMerge_canon; assumption.
    apply MapDelta_as_DomRestrBy_2.
  Qed.

  Lemma MapDelta_sym_c :
   forall m m':Map A,
     mapcanon A m -> mapcanon A m' -> MapDelta A m m' = MapDelta A m' m.
  Proof.
    intros. apply mapcanon_unique. apply MapDelta_canon; assumption.
    apply MapDelta_canon; assumption. apply MapDelta_sym.
  Qed.

  Lemma MapDom_Split_1_c :
   forall (m:Map A) (m':Map B),
     mapcanon A m ->
     m = MapMerge A (MapDomRestrTo A B m m') (MapDomRestrBy A B m m').
  Proof.
    intros. apply mapcanon_unique. assumption.
    apply MapMerge_canon. apply MapDomRestrTo_canon; assumption.
    apply MapDomRestrBy_canon; assumption.
    apply MapDom_Split_1.
  Qed.

  Lemma MapDom_Split_2_c :
   forall (m:Map A) (m':Map B),
     mapcanon A m ->
     m = MapMerge A (MapDomRestrBy A B m m') (MapDomRestrTo A B m m').
  Proof.
    intros. apply mapcanon_unique. assumption.
    apply MapMerge_canon. apply MapDomRestrBy_canon; assumption.
    apply MapDomRestrTo_canon; assumption.
    apply MapDom_Split_2.
  Qed.

  Lemma MapDom_Split_3_c :
   forall (m:Map A) (m':Map B),
     mapcanon A m ->
     MapDomRestrTo A A (MapDomRestrTo A B m m') (MapDomRestrBy A B m m') =
     M0 A.
  Proof.
    intros. apply mapcanon_unique. apply MapDomRestrTo_canon.
    apply MapDomRestrTo_canon; assumption.
    apply M0_canon.
    apply MapDom_Split_3.
  Qed.

  Lemma Map_of_alist_of_Map_c :
   forall m:Map A, mapcanon A m -> Map_of_alist A (alist_of_Map A m) = m.
  Proof.
    intros. apply mapcanon_unique; try assumption. apply Map_of_alist_canon.
    apply Map_of_alist_of_Map.
  Qed.

  Lemma alist_of_Map_of_alist_c :
   forall l:alist A,
     alist_sorted_2 A l -> alist_of_Map A (Map_of_alist A l) = l.
  Proof.
    intros. apply alist_canonical. apply alist_of_Map_of_alist.
    apply alist_of_Map_sorts2.
    assumption.
  Qed.

  Lemma MapSubset_antisym_c :
   forall (m:Map A) (m':Map B),
     mapcanon A m ->
     mapcanon B m' ->
     MapSubset A B m m' -> MapSubset B A m' m -> MapDom A m = MapDom B m'.
  Proof.
    intros. apply (mapcanon_unique unit). apply MapDom_canon; assumption.
    apply MapDom_canon; assumption.
    apply MapSubset_antisym; assumption.
  Qed.

  Lemma FSubset_antisym_c :
   forall s s':FSet,
     mapcanon unit s ->
     mapcanon unit s' -> MapSubset _ _ s s' -> MapSubset _ _ s' s -> s = s'.
  Proof.
    intros. apply (mapcanon_unique unit); try assumption. apply FSubset_antisym; assumption.
  Qed.

  Lemma MapDisjoint_empty_c :
   forall m:Map A, mapcanon A m -> MapDisjoint A A m m -> m = M0 A.
  Proof.
    intros. apply mapcanon_unique; try assumption; try apply M0_canon.
    apply MapDisjoint_empty; assumption.
  Qed.

  Lemma MapDelta_disjoint_c :
   forall m m':Map A,
     mapcanon A m ->
     mapcanon A m' ->
     MapDisjoint A A m m' -> MapDelta A m m' = MapMerge A m m'.
  Proof.
    intros. apply mapcanon_unique. apply MapDelta_canon; assumption.
    apply MapMerge_canon; assumption. apply MapDelta_disjoint; assumption.
  Qed.

End MapC.

Lemma FSetDelta_assoc_c :
 forall s s' s'':FSet,
   mapcanon unit s ->
   mapcanon unit s' ->
   mapcanon unit s'' ->
   MapDelta _ (MapDelta _ s s') s'' = MapDelta _ s (MapDelta _ s' s'').
Proof.
  intros. apply (mapcanon_unique unit). apply MapDelta_canon. apply MapDelta_canon; assumption.
  assumption.
  apply MapDelta_canon. assumption.
  apply MapDelta_canon; assumption.
  apply FSetDelta_assoc; assumption.
Qed.

Lemma FSet_ext_c :
 forall s s':FSet,
   mapcanon unit s ->
   mapcanon unit s' -> (forall a:ad, in_FSet a s = in_FSet a s') -> s = s'.
Proof.
  intros. apply (mapcanon_unique unit); try assumption. apply FSet_ext. assumption.
Qed.

Lemma FSetUnion_comm_c :
 forall s s':FSet,
   mapcanon unit s -> mapcanon unit s' -> FSetUnion s s' = FSetUnion s' s.
Proof.
  intros.
  apply (mapcanon_unique unit);
   try (unfold FSetUnion in |- *; apply MapMerge_canon; assumption).
  apply FSetUnion_comm.
Qed.

Lemma FSetUnion_assoc_c :
 forall s s' s'':FSet,
   mapcanon unit s ->
   mapcanon unit s' ->
   mapcanon unit s'' ->
   FSetUnion (FSetUnion s s') s'' = FSetUnion s (FSetUnion s' s'').
Proof.
  exact (MapMerge_assoc_c unit).
Qed.

Lemma FSetUnion_M0_s_c : forall s:FSet, FSetUnion (M0 unit) s = s.
Proof.
  exact (MapMerge_empty_m_c unit).
Qed.

Lemma FSetUnion_s_M0_c : forall s:FSet, FSetUnion s (M0 unit) = s.
Proof.
  exact (MapMerge_m_empty_1 unit).
Qed.

Lemma FSetUnion_idempotent :
 forall s:FSet, mapcanon unit s -> FSetUnion s s = s.
Proof.
  exact (MapMerge_idempotent_c unit).
Qed.

Lemma FSetInter_comm_c :
 forall s s':FSet,
   mapcanon unit s -> mapcanon unit s' -> FSetInter s s' = FSetInter s' s.
Proof.
  intros.
  apply (mapcanon_unique unit);
   try (unfold FSetInter in |- *; apply MapDomRestrTo_canon; assumption).
  apply FSetInter_comm.
Qed.

Lemma FSetInter_assoc_c :
 forall s s' s'':FSet,
   mapcanon unit s ->
   FSetInter (FSetInter s s') s'' = FSetInter s (FSetInter s' s'').
Proof.
  exact (MapDomRestrTo_assoc_c unit unit unit).
Qed.

Lemma FSetInter_M0_s_c : forall s:FSet, FSetInter (M0 unit) s = M0 unit.
Proof.
  trivial.
Qed.

Lemma FSetInter_s_M0_c : forall s:FSet, FSetInter s (M0 unit) = M0 unit.
Proof.
  exact (MapDomRestrTo_m_empty_1 unit unit).
Qed.

Lemma FSetInter_idempotent :
 forall s:FSet, mapcanon unit s -> FSetInter s s = s.
Proof.
  exact (MapDomRestrTo_idempotent_c unit).
Qed.

Lemma FSetUnion_Inter_l_c :
 forall s s' s'':FSet,
   mapcanon unit s ->
   mapcanon unit s'' ->
   FSetUnion (FSetInter s s') s'' =
   FSetInter (FSetUnion s s'') (FSetUnion s' s'').
Proof.
  intros. apply (mapcanon_unique unit). unfold FSetUnion in |- *. apply MapMerge_canon; try assumption.
  unfold FSetInter in |- *. apply MapDomRestrTo_canon; assumption.
  unfold FSetInter in |- *; unfold FSetUnion in |- *;
   apply MapDomRestrTo_canon; apply MapMerge_canon; 
   assumption.
  apply FSetUnion_Inter_l.
Qed.

Lemma FSetUnion_Inter_r :
 forall s s' s'':FSet,
   mapcanon unit s ->
   mapcanon unit s' ->
   FSetUnion s (FSetInter s' s'') =
   FSetInter (FSetUnion s s') (FSetUnion s s'').
Proof.
  intros. apply (mapcanon_unique unit). unfold FSetUnion in |- *. apply MapMerge_canon; try assumption.
  unfold FSetInter in |- *. apply MapDomRestrTo_canon; assumption.
  unfold FSetInter in |- *; unfold FSetUnion in |- *;
   apply MapDomRestrTo_canon; apply MapMerge_canon; 
   assumption.
  apply FSetUnion_Inter_r.
Qed.

Lemma FSetInter_Union_l_c :
 forall s s' s'':FSet,
   mapcanon unit s ->
   mapcanon unit s' ->
   FSetInter (FSetUnion s s') s'' =
   FSetUnion (FSetInter s s'') (FSetInter s' s'').
Proof.
  intros. apply (mapcanon_unique unit). unfold FSetInter in |- *.
  apply MapDomRestrTo_canon; try assumption. unfold FSetUnion in |- *.
  apply MapMerge_canon; assumption.
  unfold FSetUnion in |- *; unfold FSetInter in |- *; apply MapMerge_canon;
   apply MapDomRestrTo_canon; assumption.
  apply FSetInter_Union_l.
Qed.

Lemma FSetInter_Union_r :
 forall s s' s'':FSet,
   mapcanon unit s ->
   mapcanon unit s' ->
   FSetInter s (FSetUnion s' s'') =
   FSetUnion (FSetInter s s') (FSetInter s s'').
Proof.
  intros. apply (mapcanon_unique unit). unfold FSetInter in |- *.
  apply MapDomRestrTo_canon; try assumption.
  unfold FSetUnion in |- *. apply MapMerge_canon; unfold FSetInter in |- *; apply MapDomRestrTo_canon;
  assumption.
  apply FSetInter_Union_r.
Qed.
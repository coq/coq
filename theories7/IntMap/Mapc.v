(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

Require Bool.
Require Sumbool.
Require Arith.
Require ZArith.
Require Addr.
Require Adist.
Require Addec.
Require Map.
Require Mapaxioms.
Require Fset.
Require Mapiter.
Require Mapsubset.
Require PolyList.
Require Lsort.
Require Mapcard.
Require Mapcanon.

Section MapC.

  Variable A, B, C : Set.

  Lemma MapPut_as_Merge_c : (m:(Map A)) (mapcanon A m) ->
      (a:ad) (y:A) (MapPut A m a y)=(MapMerge A m (M1 A a y)).
  Proof.
    Intros. Apply mapcanon_unique. Exact (MapPut_canon A m H a y).
    Apply MapMerge_canon. Assumption.
    Apply M1_canon.
    Apply MapPut_as_Merge.
  Qed.

  Lemma MapPut_behind_as_Merge_c : (m:(Map A)) (mapcanon A m) ->
      (a:ad) (y:A) (MapPut_behind A m a y)=(MapMerge A (M1 A a y) m).
  Proof.
    Intros. Apply mapcanon_unique. Exact (MapPut_behind_canon A m H a y).
    Apply MapMerge_canon. Apply M1_canon.
    Assumption.
    Apply MapPut_behind_as_Merge.
  Qed.

  Lemma MapMerge_empty_m_c : (m:(Map A)) (MapMerge A (M0 A) m)=m.
  Proof.
    Trivial.
  Qed.

  Lemma MapMerge_assoc_c : (m,m',m'':(Map A))
      (mapcanon A m) -> (mapcanon A m') -> (mapcanon A m'') ->
        (MapMerge A (MapMerge A m m') m'')=(MapMerge A m (MapMerge A m' m'')).
  Proof.
    Intros. Apply mapcanon_unique.
    (Apply MapMerge_canon; Try Assumption). (Apply MapMerge_canon; Try Assumption).
    (Apply MapMerge_canon; Try Assumption). (Apply MapMerge_canon; Try Assumption).
    Apply MapMerge_assoc.
  Qed.

  Lemma MapMerge_idempotent_c : (m:(Map A)) (mapcanon A m) -> (MapMerge A m m)=m.
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapMerge_canon; Assumption).
    Assumption.
    Apply MapMerge_idempotent.
  Qed.

  Lemma MapMerge_RestrTo_l_c : (m,m',m'':(Map A)) 
      (mapcanon A m) -> (mapcanon A m'') -> 
        (MapMerge A (MapDomRestrTo A A m m') m'')=
        (MapDomRestrTo A A (MapMerge A m m'') (MapMerge A m' m'')).
  Proof.
    Intros. Apply mapcanon_unique. Apply MapMerge_canon. Apply MapDomRestrTo_canon; Assumption.
    Assumption.
    Apply MapDomRestrTo_canon; Apply MapMerge_canon; Assumption.
    Apply MapMerge_RestrTo_l.
  Qed.

  Lemma MapRemove_as_RestrBy_c : (m:(Map A)) (mapcanon A m) ->
      (a:ad) (y:B) (MapRemove A m a)=(MapDomRestrBy A B m (M1 B a y)).
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapRemove_canon; Assumption).
    (Apply MapDomRestrBy_canon; Assumption).
    Apply MapRemove_as_RestrBy.
  Qed.

  Lemma MapDomRestrTo_assoc_c : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (mapcanon A m) ->
        (MapDomRestrTo A C (MapDomRestrTo A B m m') m'')=
        (MapDomRestrTo A B m (MapDomRestrTo B C m' m'')).
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapDomRestrTo_canon; Try Assumption).
    (Apply MapDomRestrTo_canon; Try Assumption).
    (Apply MapDomRestrTo_canon; Try Assumption).
    Apply MapDomRestrTo_assoc.
  Qed.

  Lemma MapDomRestrTo_idempotent_c : (m:(Map A)) (mapcanon A m) -> 
      (MapDomRestrTo A A m m)=m.
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapDomRestrTo_canon; Assumption).
    Assumption.
    Apply MapDomRestrTo_idempotent.
  Qed.

  Lemma MapDomRestrTo_Dom_c : (m:(Map A)) (m':(Map B)) (mapcanon A m) ->
      (MapDomRestrTo A B m m')=(MapDomRestrTo A unit m (MapDom B m')).
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapDomRestrTo_canon; Assumption).
    (Apply MapDomRestrTo_canon; Assumption).
    Apply MapDomRestrTo_Dom.
  Qed.

  Lemma MapDomRestrBy_Dom_c : (m:(Map A)) (m':(Map B)) (mapcanon A m) ->
      (MapDomRestrBy A B m m')=(MapDomRestrBy A unit m (MapDom B m')).
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrBy_canon; Assumption.
    Apply MapDomRestrBy_canon; Assumption.
    Apply MapDomRestrBy_Dom.
  Qed.

  Lemma MapDomRestrBy_By_c : (m:(Map A)) (m':(Map B)) (m'':(Map B)) 
      (mapcanon A m) -> 
        (MapDomRestrBy A B (MapDomRestrBy A B m m') m'')=
        (MapDomRestrBy A B m (MapMerge B m' m'')).
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapDomRestrBy_canon; Try Assumption).
    (Apply MapDomRestrBy_canon; Try Assumption).
    (Apply MapDomRestrBy_canon; Try Assumption).
    Apply MapDomRestrBy_By.
  Qed.

  Lemma MapDomRestrBy_By_comm_c : (m:(Map A)) (m':(Map B)) (m'':(Map C)) 
      (mapcanon A m) ->
        (MapDomRestrBy A C (MapDomRestrBy A B m m') m'')=
        (MapDomRestrBy A B (MapDomRestrBy A C m m'') m').
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrBy_canon.
    (Apply MapDomRestrBy_canon; Assumption).
    Apply MapDomRestrBy_canon. (Apply MapDomRestrBy_canon; Assumption).
    Apply MapDomRestrBy_By_comm.
  Qed.

  Lemma MapDomRestrBy_To_c : (m:(Map A)) (m':(Map B)) (m'':(Map C)) 
      (mapcanon A m) ->
        (MapDomRestrBy A C (MapDomRestrTo A B m m') m'')=
        (MapDomRestrTo A B m (MapDomRestrBy B C m' m'')).
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrBy_canon.
    (Apply MapDomRestrTo_canon; Assumption).
    (Apply MapDomRestrTo_canon; Assumption).
    Apply MapDomRestrBy_To.
  Qed.

  Lemma MapDomRestrBy_To_comm_c : (m:(Map A)) (m':(Map B)) (m'':(Map C)) 
      (mapcanon A m) ->
        (MapDomRestrBy A C (MapDomRestrTo A B m m') m'')=
        (MapDomRestrTo A B (MapDomRestrBy A C m m'') m').
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrBy_canon.
    Apply MapDomRestrTo_canon; Assumption.
    Apply MapDomRestrTo_canon. Apply MapDomRestrBy_canon; Assumption.
    Apply MapDomRestrBy_To_comm.
  Qed.

  Lemma MapDomRestrTo_By_c : (m:(Map A)) (m':(Map B)) (m'':(Map C)) 
      (mapcanon A m) ->
        (MapDomRestrTo A C (MapDomRestrBy A B m m') m'')=
        (MapDomRestrTo A C m (MapDomRestrBy C B m'' m')).
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrTo_canon.
    Apply MapDomRestrBy_canon; Assumption.
    Apply MapDomRestrTo_canon; Assumption.
    Apply MapDomRestrTo_By.
  Qed.

  Lemma MapDomRestrTo_By_comm_c : (m:(Map A)) (m':(Map B)) (m'':(Map C)) 
      (mapcanon A m) ->
        (MapDomRestrTo A C (MapDomRestrBy A B m m') m'')=
        (MapDomRestrBy A B (MapDomRestrTo A C m m'') m').
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrTo_canon.
    (Apply MapDomRestrBy_canon; Assumption).
    Apply MapDomRestrBy_canon. (Apply MapDomRestrTo_canon; Assumption).
    Apply MapDomRestrTo_By_comm.
  Qed.

  Lemma MapDomRestrTo_To_comm_c : (m:(Map A)) (m':(Map B)) (m'':(Map C)) 
      (mapcanon A m) ->
        (MapDomRestrTo A C (MapDomRestrTo A B m m') m'')=
        (MapDomRestrTo A B (MapDomRestrTo A C m m'') m').
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrTo_canon.
    Apply MapDomRestrTo_canon; Assumption.
    Apply MapDomRestrTo_canon. Apply MapDomRestrTo_canon; Assumption.
    Apply MapDomRestrTo_To_comm.
  Qed.

  Lemma MapMerge_DomRestrTo_c : (m,m':(Map A)) (m'':(Map B))
      (mapcanon A m) -> (mapcanon A m') ->
        (MapDomRestrTo A B (MapMerge A m m') m'')=
        (MapMerge A (MapDomRestrTo A B m m'') (MapDomRestrTo A B m' m'')).
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrTo_canon.
    (Apply MapMerge_canon; Assumption).
    Apply MapMerge_canon. (Apply MapDomRestrTo_canon; Assumption).
    (Apply MapDomRestrTo_canon; Assumption).
    Apply MapMerge_DomRestrTo.
  Qed.

  Lemma MapMerge_DomRestrBy_c : (m,m':(Map A)) (m'':(Map B))
      (mapcanon A m) -> (mapcanon A m') ->
        (MapDomRestrBy A B (MapMerge A m m') m'')=
        (MapMerge A (MapDomRestrBy A B m m'') (MapDomRestrBy A B m' m'')).
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrBy_canon. Apply MapMerge_canon; Assumption.
    Apply MapMerge_canon. Apply MapDomRestrBy_canon; Assumption.
    Apply MapDomRestrBy_canon; Assumption.
    Apply MapMerge_DomRestrBy.
  Qed.

  Lemma MapDelta_nilpotent_c : (m:(Map A)) (mapcanon A m) -> 
      (MapDelta A m m)=(M0 A).
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapDelta_canon; Assumption).
    Apply M0_canon.
    Apply MapDelta_nilpotent.
  Qed.

  Lemma MapDelta_as_Merge_c : (m,m':(Map A))
      (mapcanon A m) -> (mapcanon A m') ->
        (MapDelta A m m')=
	(MapMerge A (MapDomRestrBy A A m m') (MapDomRestrBy A A m' m)).
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapDelta_canon; Assumption).
    (Apply MapMerge_canon; Apply MapDomRestrBy_canon; Assumption).
    Apply MapDelta_as_Merge.
  Qed.

  Lemma MapDelta_as_DomRestrBy_c : (m,m':(Map A))
      (mapcanon A m) -> (mapcanon A m') ->
        (MapDelta A m m')=
	(MapDomRestrBy A A (MapMerge A m m') (MapDomRestrTo A A m m')).
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDelta_canon; Assumption.
    Apply MapDomRestrBy_canon. (Apply MapMerge_canon; Assumption).
    Apply MapDelta_as_DomRestrBy.
  Qed.

  Lemma MapDelta_as_DomRestrBy_2_c : (m,m':(Map A))
      (mapcanon A m) -> (mapcanon A m') ->
        (MapDelta A m m')=
	(MapDomRestrBy A A (MapMerge A m m') (MapDomRestrTo A A m' m)).
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapDelta_canon; Assumption).
    Apply MapDomRestrBy_canon. Apply MapMerge_canon; Assumption.
    Apply MapDelta_as_DomRestrBy_2.
  Qed.

  Lemma MapDelta_sym_c : (m,m':(Map A))
      (mapcanon A m) -> (mapcanon A m') -> (MapDelta A m m')=(MapDelta A m' m).
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapDelta_canon; Assumption).
    (Apply MapDelta_canon; Assumption). Apply MapDelta_sym.
  Qed.

  Lemma MapDom_Split_1_c : (m:(Map A)) (m':(Map B)) (mapcanon A m) ->
      m=(MapMerge A (MapDomRestrTo A B m m') (MapDomRestrBy A B m m')).
  Proof.
    Intros. Apply mapcanon_unique. Assumption.
    Apply MapMerge_canon. Apply MapDomRestrTo_canon; Assumption.
    Apply MapDomRestrBy_canon; Assumption.
    Apply MapDom_Split_1.
  Qed.

  Lemma MapDom_Split_2_c : (m:(Map A)) (m':(Map B)) (mapcanon A m) ->
      m=(MapMerge A (MapDomRestrBy A B m m') (MapDomRestrTo A B m m')).
  Proof.
    Intros. Apply mapcanon_unique. Assumption.
    Apply MapMerge_canon. (Apply MapDomRestrBy_canon; Assumption).
    (Apply MapDomRestrTo_canon; Assumption).
    Apply MapDom_Split_2.
  Qed.

  Lemma MapDom_Split_3_c : (m:(Map A)) (m':(Map B)) (mapcanon A m) ->
      (MapDomRestrTo A A (MapDomRestrTo A B m m') (MapDomRestrBy A B m m'))=
      (M0 A).
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrTo_canon.
    Apply MapDomRestrTo_canon; Assumption.
    Apply M0_canon.
    Apply MapDom_Split_3.
  Qed.

  Lemma Map_of_alist_of_Map_c : (m:(Map A)) (mapcanon A m) ->
      (Map_of_alist A (alist_of_Map A m))=m.
  Proof.
    Intros. (Apply mapcanon_unique; Try Assumption). Apply Map_of_alist_canon.
    Apply Map_of_alist_of_Map.
  Qed.

  Lemma alist_of_Map_of_alist_c : (l:(alist A)) (alist_sorted_2 A l) ->
      (alist_of_Map A (Map_of_alist A l))=l.
  Proof.
    Intros. Apply alist_canonical. Apply alist_of_Map_of_alist.
    Apply alist_of_Map_sorts2.
    Assumption.
  Qed.

  Lemma MapSubset_antisym_c : (m:(Map A)) (m':(Map B))
      (mapcanon A m) -> (mapcanon B m') ->
      (MapSubset A B m m') -> (MapSubset B A m' m) -> (MapDom A m)=(MapDom B m').
  Proof.
    Intros. Apply (mapcanon_unique unit). (Apply MapDom_canon; Assumption).
    (Apply MapDom_canon; Assumption).
    (Apply MapSubset_antisym; Assumption).
  Qed.

  Lemma FSubset_antisym_c : (s,s':FSet) (mapcanon unit s) -> (mapcanon unit s') ->
      (MapSubset ? ? s s') -> (MapSubset ? ? s' s) -> s=s'.
  Proof.
    Intros. Apply (mapcanon_unique unit); Try Assumption. Apply FSubset_antisym; Assumption.
  Qed.

  Lemma MapDisjoint_empty_c : (m:(Map A)) (mapcanon A m) ->
      (MapDisjoint A A m m) -> m=(M0 A).
  Proof.
    Intros. Apply mapcanon_unique; Try Assumption; Try Apply M0_canon.
    Apply MapDisjoint_empty; Assumption.
  Qed.

  Lemma MapDelta_disjoint_c : (m,m':(Map A)) (mapcanon A m) -> (mapcanon A m') ->
      (MapDisjoint A A m m') -> (MapDelta A m m')=(MapMerge A m m').
  Proof.
    Intros. Apply mapcanon_unique. (Apply MapDelta_canon; Assumption).
    (Apply MapMerge_canon; Assumption). Apply MapDelta_disjoint; Assumption.
  Qed.

End MapC.

Lemma FSetDelta_assoc_c : (s,s',s'':FSet)
    (mapcanon unit s) -> (mapcanon unit s') -> (mapcanon unit s'') ->
      (MapDelta ? (MapDelta ? s s') s'')=(MapDelta ? s (MapDelta ? s' s'')).
Proof.
  Intros. Apply (mapcanon_unique unit). Apply MapDelta_canon. (Apply MapDelta_canon; Assumption).
  Assumption.
  Apply MapDelta_canon. Assumption.
  (Apply MapDelta_canon; Assumption).
  Apply FSetDelta_assoc; Assumption.
Qed.

Lemma FSet_ext_c : (s,s':FSet) (mapcanon unit s) -> (mapcanon unit s') ->
      ((a:ad) (in_FSet a s)=(in_FSet a s')) -> s=s'.
Proof.
  Intros. (Apply (mapcanon_unique unit); Try Assumption). Apply FSet_ext. Assumption.
Qed.

Lemma FSetUnion_comm_c : (s,s':FSet) (mapcanon unit s) -> (mapcanon unit s') ->
      (FSetUnion s s')=(FSetUnion s' s).
Proof.
  Intros.
  Apply (mapcanon_unique unit); Try (Unfold FSetUnion; Apply MapMerge_canon; Assumption).
  Apply FSetUnion_comm.
Qed.

Lemma FSetUnion_assoc_c : (s,s',s'':FSet)
      (mapcanon unit s) -> (mapcanon unit s') -> (mapcanon unit s'') ->
        (FSetUnion (FSetUnion s s') s'')=(FSetUnion s (FSetUnion s' s'')).
Proof.
  Exact (MapMerge_assoc_c unit).
Qed.

Lemma FSetUnion_M0_s_c : (s:FSet) (FSetUnion (M0 unit) s)=s.
Proof.
  Exact (MapMerge_empty_m_c unit).
Qed.

Lemma FSetUnion_s_M0_c : (s:FSet) (FSetUnion s (M0 unit))=s.
Proof.
  Exact (MapMerge_m_empty_1 unit).
Qed.

Lemma FSetUnion_idempotent : (s:FSet) (mapcanon unit s) -> (FSetUnion s s)=s.
Proof.
  Exact (MapMerge_idempotent_c unit).
Qed.

Lemma FSetInter_comm_c : (s,s':FSet) (mapcanon unit s) -> (mapcanon unit s') ->
      (FSetInter s s')=(FSetInter s' s).
Proof.
  Intros.
  Apply (mapcanon_unique unit); Try (Unfold FSetInter; Apply MapDomRestrTo_canon; Assumption).
  Apply FSetInter_comm.
Qed.

Lemma FSetInter_assoc_c : (s,s',s'':FSet)
      (mapcanon unit s) ->
        (FSetInter (FSetInter s s') s'')=(FSetInter s (FSetInter s' s'')).
Proof.
  Exact (MapDomRestrTo_assoc_c unit unit unit).
Qed.

Lemma FSetInter_M0_s_c : (s:FSet) (FSetInter (M0 unit) s)=(M0 unit).
Proof.
  Trivial.
Qed.

Lemma FSetInter_s_M0_c : (s:FSet) (FSetInter s (M0 unit))=(M0 unit).
Proof.
  Exact (MapDomRestrTo_m_empty_1 unit unit).
Qed.

Lemma FSetInter_idempotent : (s:FSet) (mapcanon unit s) -> (FSetInter s s)=s.
Proof.
  Exact (MapDomRestrTo_idempotent_c unit).
Qed.

Lemma FSetUnion_Inter_l_c : (s,s',s'':FSet) (mapcanon unit s) -> (mapcanon unit s'') ->
      (FSetUnion (FSetInter s s') s'')=(FSetInter (FSetUnion s s'') (FSetUnion s' s'')).
Proof.
  Intros. Apply (mapcanon_unique unit). Unfold FSetUnion. (Apply MapMerge_canon; Try Assumption).
  Unfold FSetInter. (Apply MapDomRestrTo_canon; Assumption).
  Unfold FSetInter; Unfold FSetUnion; Apply MapDomRestrTo_canon; Apply MapMerge_canon; Assumption.
  Apply FSetUnion_Inter_l.
Qed.

Lemma FSetUnion_Inter_r : (s,s',s'':FSet) (mapcanon unit s) -> (mapcanon unit s') ->
      (FSetUnion s (FSetInter s' s''))=(FSetInter (FSetUnion s s') (FSetUnion s s'')).
Proof.
  Intros. Apply (mapcanon_unique unit). Unfold FSetUnion. (Apply MapMerge_canon; Try Assumption).
  Unfold FSetInter. (Apply MapDomRestrTo_canon; Assumption).
  Unfold FSetInter; Unfold FSetUnion; Apply MapDomRestrTo_canon; Apply MapMerge_canon; Assumption.
  Apply FSetUnion_Inter_r.
Qed.

Lemma FSetInter_Union_l_c : (s,s',s'':FSet) (mapcanon unit s) -> (mapcanon unit s') ->
      (FSetInter (FSetUnion s s') s'')=(FSetUnion (FSetInter s s'') (FSetInter s' s'')).
Proof.
  Intros. Apply (mapcanon_unique unit). Unfold FSetInter.
  Apply MapDomRestrTo_canon; Try Assumption. Unfold FSetUnion.
  Apply MapMerge_canon; Assumption.
  Unfold FSetUnion; Unfold FSetInter; Apply MapMerge_canon; Apply MapDomRestrTo_canon;
  Assumption.
  Apply FSetInter_Union_l.
Qed.

Lemma FSetInter_Union_r : (s,s',s'':FSet) (mapcanon unit s) -> (mapcanon unit s') ->
      (FSetInter s (FSetUnion s' s''))=(FSetUnion (FSetInter s s') (FSetInter s s'')).
Proof.
  Intros. Apply (mapcanon_unique unit). Unfold FSetInter.
  Apply MapDomRestrTo_canon; Try Assumption.
  Unfold FSetUnion. Apply MapMerge_canon; Unfold FSetInter; Apply MapDomRestrTo_canon; Assumption.
  Apply FSetInter_Union_r.
Qed.

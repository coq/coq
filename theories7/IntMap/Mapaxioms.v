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
Require ZArith.
Require Addr.
Require Adist.
Require Addec.
Require Map.
Require Fset.

Section MapAxioms.

  Variable A, B, C : Set.

  Lemma eqm_sym : (f,f':ad->(option A)) (eqm A f f') -> (eqm A f' f).
  Proof.
    Unfold eqm. Intros. Rewrite H. Reflexivity.
  Qed.

  Lemma eqm_refl :  (f:ad->(option A)) (eqm A f f).
  Proof.
    Unfold eqm. Trivial.
  Qed.

  Lemma eqm_trans : (f,f',f'':ad->(option A)) (eqm A f f') -> (eqm A f' f'') -> (eqm A f f'').
  Proof.
    Unfold eqm. Intros. Rewrite H. Exact (H0 a).
  Qed.

  Definition eqmap := [m,m':(Map A)] (eqm A (MapGet A m) (MapGet A m')).

  Lemma eqmap_sym : (m,m':(Map A)) (eqmap m m') -> (eqmap m' m).
  Proof.
    Intros. Unfold eqmap. Apply eqm_sym. Assumption.
  Qed.

  Lemma eqmap_refl :  (m:(Map A)) (eqmap m m).
  Proof.
    Intros. Unfold eqmap. Apply eqm_refl.
  Qed.

  Lemma eqmap_trans : (m,m',m'':(Map A)) (eqmap m m') -> (eqmap m' m'') -> (eqmap m m'').
  Proof.
    Intros. Exact (eqm_trans (MapGet A m) (MapGet A m') (MapGet A m'') H H0).
  Qed.

  Lemma MapPut_as_Merge : (m:(Map A)) (a:ad) (y:A)
      (eqmap (MapPut A m a y) (MapMerge A m (M1 A a y))).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapPut_semantics A m a y a0).
    Rewrite (MapMerge_semantics A m (M1 A a y) a0). Unfold 2 MapGet.
    Elim (sumbool_of_bool (ad_eq a a0)); Intro H; Rewrite H; Reflexivity.
  Qed.

  Lemma MapPut_ext : (m,m':(Map A)) (eqmap m m') ->
      (a:ad) (y:A) (eqmap (MapPut A m a y) (MapPut A m' a y)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapPut_semantics A m' a y a0).
    Rewrite (MapPut_semantics A m a y a0). 
    Case (ad_eq a a0); [ Reflexivity | Apply H ].
  Qed.

  Lemma MapPut_behind_as_Merge : (m:(Map A)) (a:ad) (y:A)
      (eqmap (MapPut_behind A m a y) (MapMerge A (M1 A a y) m)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapPut_behind_semantics A m a y a0).
    Rewrite (MapMerge_semantics A (M1 A a y) m a0). Reflexivity.
  Qed.

  Lemma MapPut_behind_ext : (m,m':(Map A)) (eqmap m m') ->
      (a:ad) (y:A) (eqmap (MapPut_behind A m a y) (MapPut_behind A m' a y)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapPut_behind_semantics A m' a y a0).
    Rewrite (MapPut_behind_semantics A m a y a0). Rewrite (H a0). Reflexivity.
  Qed.

  Lemma MapMerge_empty_m_1 : (m:(Map A)) (MapMerge A (M0 A) m)=m.
  Proof.
    Trivial.
  Qed.

  Lemma MapMerge_empty_m : (m:(Map A)) (eqmap (MapMerge A (M0 A) m) m).
  Proof.
    Unfold eqmap eqm. Trivial.
  Qed.

  Lemma MapMerge_m_empty_1 : (m:(Map A)) (MapMerge A m (M0 A))=m.
  Proof.
    Induction m;Trivial.
  Qed.

  Lemma MapMerge_m_empty : (m:(Map A)) (eqmap (MapMerge A m (M0 A)) m).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite MapMerge_m_empty_1. Reflexivity.
  Qed.

  Lemma MapMerge_empty_l : (m,m':(Map A)) (eqmap (MapMerge A m m') (M0 A)) ->
      (eqmap m (M0 A)).
  Proof.
    Unfold eqmap eqm. Intros. Cut (MapGet A (MapMerge A m m') a)=(MapGet A (M0 A) a).
    Rewrite (MapMerge_semantics A m m' a). Case (MapGet A m' a). Trivial.
    Intros. Discriminate H0.
    Exact (H a).
  Qed.

  Lemma MapMerge_empty_r : (m,m':(Map A)) (eqmap (MapMerge A m m') (M0 A)) ->
      (eqmap m' (M0 A)).
  Proof.
    Unfold eqmap eqm. Intros. Cut (MapGet A (MapMerge A m m') a)=(MapGet A (M0 A) a).
    Rewrite (MapMerge_semantics A m m' a). Case (MapGet A m' a). Trivial.
    Intros. Discriminate H0.
    Exact (H a).
  Qed.

  Lemma MapMerge_assoc : (m,m',m'':(Map A)) (eqmap
      (MapMerge A (MapMerge A m m') m'')
      (MapMerge A m (MapMerge A m' m''))).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapMerge_semantics A (MapMerge A m m') m'' a).
    Rewrite (MapMerge_semantics A m (MapMerge A m' m'') a). Rewrite (MapMerge_semantics A m m' a).
    Rewrite (MapMerge_semantics A m' m'' a).
    Case (MapGet A m'' a); Case (MapGet A m' a); Trivial.
  Qed.

  Lemma MapMerge_idempotent : (m:(Map A)) (eqmap (MapMerge A m m) m).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapMerge_semantics A m m a).
    Case (MapGet A m a); Trivial.
  Qed.

  Lemma MapMerge_ext : (m1,m2,m'1,m'2:(Map A))
      (eqmap m1 m'1) -> (eqmap m2 m'2) -> 
        (eqmap (MapMerge A m1 m2) (MapMerge A m'1 m'2)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapMerge_semantics A m1 m2 a).
    Rewrite (MapMerge_semantics A m'1 m'2 a). Rewrite (H a). Rewrite (H0 a). Reflexivity.
  Qed.

  Lemma MapMerge_ext_l : (m1,m'1,m2:(Map A))
      (eqmap m1 m'1) -> (eqmap (MapMerge A m1 m2) (MapMerge A m'1 m2)).
  Proof.
    Intros. Apply MapMerge_ext. Assumption.
    Apply eqmap_refl.
  Qed.

  Lemma MapMerge_ext_r : (m1,m2,m'2:(Map A))
      (eqmap m2 m'2) -> (eqmap (MapMerge A m1 m2) (MapMerge A m1 m'2)).
  Proof.
    Intros. Apply MapMerge_ext. Apply eqmap_refl.
    Assumption.
  Qed.

  Lemma MapMerge_RestrTo_l : (m,m',m'':(Map A))
      (eqmap (MapMerge A (MapDomRestrTo A A m m') m'')
             (MapDomRestrTo A A (MapMerge A m m'') (MapMerge A m' m''))).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapMerge_semantics A (MapDomRestrTo A A m m') m'' a).
    Rewrite (MapDomRestrTo_semantics A A m m' a).
    Rewrite (MapDomRestrTo_semantics A A (MapMerge A m m'') (MapMerge A m' m'') a).
    Rewrite (MapMerge_semantics A m' m'' a). Rewrite (MapMerge_semantics A m m'' a).
    Case (MapGet A m'' a); Case (MapGet A m' a); Reflexivity.
  Qed.

  Lemma MapRemove_as_RestrBy : (m:(Map A)) (a:ad) (y:B)
      (eqmap (MapRemove A m a) (MapDomRestrBy A B m (M1 B a y))).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapRemove_semantics A m a a0).
    Rewrite (MapDomRestrBy_semantics A B m (M1 B a y) a0). Elim (sumbool_of_bool (ad_eq a a0)).
    Intro H. Rewrite H. Rewrite (ad_eq_complete a a0 H). Rewrite (M1_semantics_1 B a0 y).
    Reflexivity.
    Intro H. Rewrite H. Rewrite (M1_semantics_2 B a a0 y H). Reflexivity.
  Qed.

  Lemma MapRemove_ext : (m,m':(Map A)) (eqmap m m') ->
      (a:ad) (eqmap (MapRemove A m a) (MapRemove A m' a)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapRemove_semantics A m' a a0).
    Rewrite (MapRemove_semantics A m a a0). 
    Case (ad_eq a a0); [ Reflexivity | Apply H ].
  Qed.

  Lemma MapDomRestrTo_empty_m_1 : 
      (m:(Map B)) (MapDomRestrTo A B (M0 A) m)=(M0 A).
  Proof.
    Trivial.
  Qed.

  Lemma MapDomRestrTo_empty_m : 
      (m:(Map B)) (eqmap (MapDomRestrTo A B (M0 A) m) (M0 A)).
  Proof.
    Unfold eqmap eqm. Trivial.
  Qed.

  Lemma MapDomRestrTo_m_empty_1 : 
      (m:(Map A)) (MapDomRestrTo A B m (M0 B))=(M0 A).
  Proof.
    Induction m;Trivial.
  Qed.

  Lemma MapDomRestrTo_m_empty : 
      (m:(Map A)) (eqmap (MapDomRestrTo A B m (M0 B)) (M0 A)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDomRestrTo_m_empty_1 m). Reflexivity.
  Qed.

  Lemma MapDomRestrTo_assoc : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (eqmap (MapDomRestrTo A C (MapDomRestrTo A B m m') m'')
             (MapDomRestrTo A B m (MapDomRestrTo B C m' m''))).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrTo_semantics A C (MapDomRestrTo A B m m') m'' a).
    Rewrite (MapDomRestrTo_semantics A B m m' a).
    Rewrite (MapDomRestrTo_semantics A B m (MapDomRestrTo B C m' m'') a).
    Rewrite (MapDomRestrTo_semantics B C m' m'' a).
    Case (MapGet C m'' a); Case (MapGet B m' a); Trivial.
  Qed.

  Lemma MapDomRestrTo_idempotent : (m:(Map A)) (eqmap (MapDomRestrTo A A m m) m).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDomRestrTo_semantics A A m m a).
    Case (MapGet A m a); Trivial.
  Qed.

  Lemma MapDomRestrTo_Dom : (m:(Map A)) (m':(Map B))
      (eqmap (MapDomRestrTo A B m m') (MapDomRestrTo A unit m (MapDom B m'))).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDomRestrTo_semantics A B m m' a).
    Rewrite (MapDomRestrTo_semantics A unit m (MapDom B m') a).
    Elim (sumbool_of_bool (in_FSet a (MapDom B m'))). Intro H.
    Elim (MapDom_semantics_2 B m' a H). Intros y H0. Rewrite H0. Unfold in_FSet in_dom in H.
    Generalize H. Case (MapGet unit (MapDom B m') a); Trivial. Intro H1. Discriminate H1.
    Intro H. Rewrite (MapDom_semantics_4 B m' a H). Unfold in_FSet in_dom in H.
    Generalize H. Case (MapGet unit (MapDom B m') a). Trivial.
    Intros H0 H1. Discriminate H1.
  Qed.

  Lemma MapDomRestrBy_empty_m_1 : 
      (m:(Map B)) (MapDomRestrBy A B (M0 A) m)=(M0 A).
  Proof.
    Trivial.
  Qed.

  Lemma MapDomRestrBy_empty_m : 
      (m:(Map B)) (eqmap (MapDomRestrBy A B (M0 A) m) (M0 A)).
  Proof.
    Unfold eqmap eqm. Trivial.
  Qed.

  Lemma MapDomRestrBy_m_empty_1 : (m:(Map A)) (MapDomRestrBy A B m (M0 B))=m.
  Proof.
    Induction m;Trivial.
  Qed.

  Lemma MapDomRestrBy_m_empty : (m:(Map A)) (eqmap (MapDomRestrBy A B m (M0 B)) m).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDomRestrBy_m_empty_1 m). Reflexivity.
  Qed.

  Lemma MapDomRestrBy_Dom : (m:(Map A)) (m':(Map B))
      (eqmap (MapDomRestrBy A B m m') (MapDomRestrBy A unit m (MapDom B m'))).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDomRestrBy_semantics A B m m' a).
    Rewrite (MapDomRestrBy_semantics A unit m (MapDom B m') a).
    Elim (sumbool_of_bool (in_FSet a (MapDom B m'))). Intro H.
    Elim (MapDom_semantics_2 B m' a H). Intros y H0. Rewrite H0.
    Unfold in_FSet in_dom in H. Generalize H. Case (MapGet unit (MapDom B m') a); Trivial.
    Intro H1. Discriminate H1.
    Intro H. Rewrite (MapDom_semantics_4 B m' a H). Unfold in_FSet in_dom in H.
    Generalize H. Case (MapGet unit (MapDom B m') a). Trivial.
    Intros H0 H1. Discriminate H1.
  Qed.

  Lemma MapDomRestrBy_m_m_1 : (m:(Map A)) (eqmap (MapDomRestrBy A A m m) (M0 A)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDomRestrBy_semantics A A m m a).
    Case (MapGet A m a); Trivial.
  Qed.

  Lemma MapDomRestrBy_By : (m:(Map A)) (m':(Map B)) (m'':(Map B))
      (eqmap (MapDomRestrBy A B (MapDomRestrBy A B m m') m'')
             (MapDomRestrBy A B m (MapMerge B m' m''))).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrBy_semantics A B (MapDomRestrBy A B m m') m'' a).
    Rewrite (MapDomRestrBy_semantics A B m m' a).
    Rewrite (MapDomRestrBy_semantics A B m (MapMerge B m' m'') a).
    Rewrite (MapMerge_semantics B m' m'' a).
    Case (MapGet B m'' a); Case (MapGet B m' a); Trivial.
  Qed.

  Lemma MapDomRestrBy_By_comm : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (eqmap (MapDomRestrBy A C (MapDomRestrBy A B m m') m'')
             (MapDomRestrBy A B (MapDomRestrBy A C m m'') m')).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrBy_semantics A C (MapDomRestrBy A B m m') m'' a).
    Rewrite (MapDomRestrBy_semantics A B m m' a).
    Rewrite (MapDomRestrBy_semantics A B (MapDomRestrBy A C m m'') m' a).
    Rewrite (MapDomRestrBy_semantics A C m m'' a).
    Case (MapGet C m'' a); Case (MapGet B m' a); Trivial.
  Qed.

  Lemma MapDomRestrBy_To : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (eqmap (MapDomRestrBy A C (MapDomRestrTo A B m m') m'')
             (MapDomRestrTo A B m (MapDomRestrBy B C m' m''))).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrBy_semantics A C (MapDomRestrTo A B m m') m'' a).
    Rewrite (MapDomRestrTo_semantics A B m m' a).
    Rewrite (MapDomRestrTo_semantics A B m (MapDomRestrBy B C m' m'') a).
    Rewrite (MapDomRestrBy_semantics B C m' m'' a).
    Case (MapGet C m'' a); Case (MapGet B m' a); Trivial.
  Qed.

  Lemma MapDomRestrBy_To_comm : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (eqmap (MapDomRestrBy A C (MapDomRestrTo A B m m') m'')
             (MapDomRestrTo A B (MapDomRestrBy A C m m'') m')).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrBy_semantics A C (MapDomRestrTo A B m m') m'' a).
    Rewrite (MapDomRestrTo_semantics A B m m' a).
    Rewrite (MapDomRestrTo_semantics A B (MapDomRestrBy A C m m'') m' a).
    Rewrite (MapDomRestrBy_semantics A C m m'' a).
    Case (MapGet C m'' a); Case (MapGet B m' a); Trivial.
  Qed.

  Lemma MapDomRestrTo_By : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (eqmap (MapDomRestrTo A C (MapDomRestrBy A B m m') m'')
             (MapDomRestrTo A C m (MapDomRestrBy C B m'' m'))).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrTo_semantics A C (MapDomRestrBy A B m m') m'' a).
    Rewrite (MapDomRestrBy_semantics A B m m' a).
    Rewrite (MapDomRestrTo_semantics A C m (MapDomRestrBy C B m'' m') a).
    Rewrite (MapDomRestrBy_semantics C B m'' m' a).
    Case (MapGet C m'' a); Case (MapGet B m' a); Trivial.
  Qed.

  Lemma MapDomRestrTo_By_comm : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (eqmap (MapDomRestrTo A C (MapDomRestrBy A B m m') m'')
             (MapDomRestrBy A B (MapDomRestrTo A C m m'') m')).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrTo_semantics A C (MapDomRestrBy A B m m') m'' a).
    Rewrite (MapDomRestrBy_semantics A B m m' a).
    Rewrite (MapDomRestrBy_semantics A B (MapDomRestrTo A C m m'') m' a).
    Rewrite (MapDomRestrTo_semantics A C m m'' a).
    Case (MapGet C m'' a); Case (MapGet B m' a); Trivial.
  Qed.

  Lemma MapDomRestrTo_To_comm : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (eqmap (MapDomRestrTo A C (MapDomRestrTo A B m m') m'')
             (MapDomRestrTo A B (MapDomRestrTo A C m m'') m')).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrTo_semantics A C (MapDomRestrTo A B m m') m'' a).
    Rewrite (MapDomRestrTo_semantics A B m m' a).
    Rewrite (MapDomRestrTo_semantics A B (MapDomRestrTo A C m m'') m' a).
    Rewrite (MapDomRestrTo_semantics A C m m'' a).
    Case (MapGet C m'' a); Case (MapGet B m' a); Trivial.
  Qed.

  Lemma MapMerge_DomRestrTo : (m,m':(Map A)) (m'':(Map B))
      (eqmap (MapDomRestrTo A B (MapMerge A m m') m'')
             (MapMerge A (MapDomRestrTo A B m m'') (MapDomRestrTo A B m' m''))).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrTo_semantics A B (MapMerge A m m') m'' a).
    Rewrite (MapMerge_semantics A m m' a).
    Rewrite (MapMerge_semantics A (MapDomRestrTo A B m m'') (MapDomRestrTo A B m' m'') a).
    Rewrite (MapDomRestrTo_semantics A B m' m'' a).
    Rewrite (MapDomRestrTo_semantics A B m m'' a).
    Case (MapGet B m'' a); Case (MapGet A m' a); Trivial.
  Qed.

  Lemma MapMerge_DomRestrBy : (m,m':(Map A)) (m'':(Map B))
      (eqmap (MapDomRestrBy A B (MapMerge A m m') m'')
             (MapMerge A (MapDomRestrBy A B m m'') (MapDomRestrBy A B m' m''))).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrBy_semantics A B (MapMerge A m m') m'' a).
    Rewrite (MapMerge_semantics A m m' a).
    Rewrite (MapMerge_semantics A (MapDomRestrBy A B m m'') (MapDomRestrBy A B m' m'') a).
    Rewrite (MapDomRestrBy_semantics A B m' m'' a).
    Rewrite (MapDomRestrBy_semantics A B m m'' a).
    Case (MapGet B m'' a); Case (MapGet A m' a); Trivial.
  Qed.

  Lemma MapDelta_empty_m_1 : (m:(Map A)) (MapDelta A (M0 A) m)=m.
  Proof.
    Trivial.
  Qed.

  Lemma MapDelta_empty_m : (m:(Map A)) (eqmap (MapDelta A (M0 A) m) m).
  Proof.
    Unfold eqmap eqm. Trivial.
  Qed.

  Lemma MapDelta_m_empty_1 : (m:(Map A)) (MapDelta A m (M0 A))=m.
  Proof.
    Induction m;Trivial.
  Qed.

  Lemma MapDelta_m_empty : (m:(Map A)) (eqmap (MapDelta A m (M0 A)) m).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite MapDelta_m_empty_1. Reflexivity.
  Qed.

  Lemma MapDelta_nilpotent : (m:(Map A)) (eqmap (MapDelta A m m) (M0 A)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDelta_semantics A m m a).
    Case (MapGet A m a); Trivial.
  Qed.

  Lemma MapDelta_as_Merge : (m,m':(Map A)) (eqmap (MapDelta A m m')
      	(MapMerge A (MapDomRestrBy A A m m') (MapDomRestrBy A A m' m))).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDelta_semantics A m m' a).
    Rewrite (MapMerge_semantics A (MapDomRestrBy A A m m') (MapDomRestrBy A A m' m) a).
    Rewrite (MapDomRestrBy_semantics A A m' m a).
    Rewrite (MapDomRestrBy_semantics A A m m' a).
    Case (MapGet A m a); Case (MapGet A m' a); Trivial.
  Qed.

  Lemma MapDelta_as_DomRestrBy : (m,m':(Map A)) (eqmap (MapDelta A m m')
      	(MapDomRestrBy A A (MapMerge A m m') (MapDomRestrTo A A m m'))).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDelta_semantics A m m' a).
    Rewrite (MapDomRestrBy_semantics A A (MapMerge A m m') (MapDomRestrTo A A m m') a).
    Rewrite (MapDomRestrTo_semantics A A m m' a). Rewrite (MapMerge_semantics A m m' a).
    Case (MapGet A m a); Case (MapGet A m' a); Trivial.
  Qed.

  Lemma MapDelta_as_DomRestrBy_2 : (m,m':(Map A)) (eqmap (MapDelta A m m')
      	(MapDomRestrBy A A (MapMerge A m m') (MapDomRestrTo A A m' m))).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDelta_semantics A m m' a).
    Rewrite (MapDomRestrBy_semantics A A (MapMerge A m m') (MapDomRestrTo A A m' m) a).
    Rewrite (MapDomRestrTo_semantics A A m' m a). Rewrite (MapMerge_semantics A m m' a).
    Case (MapGet A m a); Case (MapGet A m' a); Trivial.
  Qed.

  Lemma MapDelta_sym : (m,m':(Map A)) (eqmap (MapDelta A m m') (MapDelta A m' m)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDelta_semantics A m m' a).
    Rewrite (MapDelta_semantics A m' m a). 
    Case (MapGet A m a); Case (MapGet A m' a); Trivial.
  Qed.

  Lemma MapDelta_ext : (m1,m2,m'1,m'2:(Map A))
      (eqmap m1 m'1) -> (eqmap m2 m'2) -> 
        (eqmap (MapDelta A m1 m2) (MapDelta A m'1 m'2)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite (MapDelta_semantics A m1 m2 a).
    Rewrite (MapDelta_semantics A m'1 m'2 a). Rewrite (H a). Rewrite (H0 a). Reflexivity.
  Qed.

  Lemma MapDelta_ext_l : (m1,m'1,m2:(Map A))
      (eqmap m1 m'1) -> (eqmap (MapDelta A m1 m2) (MapDelta A m'1 m2)).
  Proof.
    Intros. Apply MapDelta_ext. Assumption.
    Apply eqmap_refl.
  Qed.

  Lemma MapDelta_ext_r : (m1,m2,m'2:(Map A))
      (eqmap m2 m'2) -> (eqmap (MapDelta A m1 m2) (MapDelta A m1 m'2)).
  Proof.
    Intros. Apply MapDelta_ext. Apply eqmap_refl.
    Assumption.
  Qed.

  Lemma MapDom_Split_1 : (m:(Map A)) (m':(Map B))
      (eqmap m (MapMerge A (MapDomRestrTo A B m m') (MapDomRestrBy A B m m'))).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapMerge_semantics A (MapDomRestrTo A B m m') (MapDomRestrBy A B m m') a).
    Rewrite (MapDomRestrBy_semantics A B m m' a).
    Rewrite (MapDomRestrTo_semantics A B m m' a).
    Case (MapGet B m' a); Case (MapGet A m a); Trivial.
  Qed.
 
  Lemma MapDom_Split_2 : (m:(Map A)) (m':(Map B))
      (eqmap m (MapMerge A (MapDomRestrBy A B m m') (MapDomRestrTo A B m m'))).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapMerge_semantics A (MapDomRestrBy A B m m') (MapDomRestrTo A B m m') a).
    Rewrite (MapDomRestrBy_semantics A B m m' a).
    Rewrite (MapDomRestrTo_semantics A B m m' a).
    Case (MapGet B m' a); Case (MapGet A m a); Trivial.
  Qed.

  Lemma MapDom_Split_3 : (m:(Map A)) (m':(Map B))
      (eqmap (MapDomRestrTo A A (MapDomRestrTo A B m m') (MapDomRestrBy A B m m')) 
	(M0 A)).
  Proof.
    Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrTo_semantics A A (MapDomRestrTo A B m m') (MapDomRestrBy A B m m') a).
    Rewrite (MapDomRestrBy_semantics A B m m' a).
    Rewrite (MapDomRestrTo_semantics A B m m' a).
    Case (MapGet B m' a); Case (MapGet A m a); Trivial.
  Qed.

End MapAxioms.

Lemma MapDomRestrTo_ext : (A,B:Set) 
    (m1:(Map A)) (m2:(Map B)) (m'1:(Map A)) (m'2:(Map B))
      (eqmap A m1 m'1) -> (eqmap B m2 m'2) ->
        (eqmap A (MapDomRestrTo A B m1 m2) (MapDomRestrTo A B m'1 m'2)).
Proof.
  Unfold eqmap eqm. Intros. Rewrite (MapDomRestrTo_semantics A B m1 m2 a).
  Rewrite (MapDomRestrTo_semantics A B m'1 m'2 a). Rewrite (H a). Rewrite (H0 a). Reflexivity.
Qed.

Lemma MapDomRestrTo_ext_l : (A,B:Set) (m1:(Map A)) (m2:(Map B)) (m'1:(Map A))
    (eqmap A m1 m'1) ->
      (eqmap A (MapDomRestrTo A B m1 m2) (MapDomRestrTo A B m'1 m2)).
Proof.
  Intros. Apply MapDomRestrTo_ext; [ Assumption | Apply eqmap_refl ].
Qed.

Lemma MapDomRestrTo_ext_r : (A,B:Set) (m1:(Map A)) (m2:(Map B)) (m'2:(Map B))
    (eqmap B m2 m'2) ->
      (eqmap A (MapDomRestrTo A B m1 m2) (MapDomRestrTo A B m1 m'2)).
Proof.
  Intros. Apply MapDomRestrTo_ext; [ Apply eqmap_refl | Assumption ].
Qed.

Lemma MapDomRestrBy_ext : (A,B:Set) 
    (m1:(Map A)) (m2:(Map B)) (m'1:(Map A)) (m'2:(Map B))
      (eqmap A m1 m'1) -> (eqmap B m2 m'2) ->
        (eqmap A (MapDomRestrBy A B m1 m2) (MapDomRestrBy A B m'1 m'2)).
Proof.
  Unfold eqmap eqm. Intros. Rewrite (MapDomRestrBy_semantics A B m1 m2 a).
  Rewrite (MapDomRestrBy_semantics A B m'1 m'2 a). Rewrite (H a). Rewrite (H0 a). Reflexivity.
Qed.

Lemma MapDomRestrBy_ext_l : (A,B:Set) (m1:(Map A)) (m2:(Map B)) (m'1:(Map A))
    (eqmap A m1 m'1) ->
      (eqmap A (MapDomRestrBy A B m1 m2) (MapDomRestrBy A B m'1 m2)).
Proof.
  Intros. Apply MapDomRestrBy_ext; [ Assumption | Apply eqmap_refl ].
Qed.

Lemma MapDomRestrBy_ext_r : (A,B:Set) (m1:(Map A)) (m2:(Map B)) (m'2:(Map B))
    (eqmap B m2 m'2) ->
      (eqmap A (MapDomRestrBy A B m1 m2) (MapDomRestrBy A B m1 m'2)).
Proof.
  Intros. Apply MapDomRestrBy_ext; [ Apply eqmap_refl | Assumption ].
Qed.

Lemma MapDomRestrBy_m_m : (A:Set) (m:(Map A))
    (eqmap A (MapDomRestrBy A unit m (MapDom A m)) (M0 A)).
Proof.
  Intros. Apply eqmap_trans with m':=(MapDomRestrBy A A m m). Apply eqmap_sym.
  Apply MapDomRestrBy_Dom.
  Apply MapDomRestrBy_m_m_1.
Qed.

Lemma FSetDelta_assoc : (s,s',s'':FSet)
    (eqmap unit (MapDelta ? (MapDelta ? s s') s'') (MapDelta ? s (MapDelta ? s' s''))).
Proof.
  Unfold eqmap eqm. Intros. Rewrite (MapDelta_semantics unit (MapDelta unit s s') s'' a).
  Rewrite (MapDelta_semantics unit s s' a).
  Rewrite (MapDelta_semantics unit s (MapDelta unit s' s'') a).
  Rewrite (MapDelta_semantics unit s' s'' a).
  Case (MapGet ? s a); Case (MapGet ? s' a); Case (MapGet ? s'' a); Trivial.
  Intros. Elim u. Elim u1. Reflexivity.
Qed.

Lemma FSet_ext : (s,s':FSet) ((a:ad) (in_FSet a s)=(in_FSet a s')) -> (eqmap unit s s').
Proof.
  Unfold in_FSet eqmap eqm. Intros. Elim (sumbool_of_bool (in_dom ? a s)). Intro H0.
  Elim (in_dom_some ? s a H0). Intros y H1. Rewrite (H a) in H0. Elim (in_dom_some ? s' a H0).
  Intros y' H2. Rewrite H1. Rewrite H2. Elim y. Elim y'. Reflexivity.
  Intro H0. Rewrite (in_dom_none ? s a H0). Rewrite (H a) in H0. Rewrite (in_dom_none ? s' a H0).
  Reflexivity.
Qed.

Lemma FSetUnion_comm : (s,s':FSet) (eqmap unit (FSetUnion s s') (FSetUnion s' s)).
Proof.
  Intros. Apply FSet_ext. Intro. Rewrite in_FSet_union. Rewrite in_FSet_union. Apply orb_sym.
Qed.

Lemma FSetUnion_assoc : (s,s',s'':FSet) (eqmap unit
      (FSetUnion (FSetUnion s s') s'') (FSetUnion s (FSetUnion s' s''))).
Proof.
  Exact (MapMerge_assoc unit).
Qed.

Lemma FSetUnion_M0_s : (s:FSet) (eqmap unit (FSetUnion (M0 unit) s) s).
Proof.
  Exact (MapMerge_empty_m unit).
Qed.

Lemma FSetUnion_s_M0 : (s:FSet) (eqmap unit (FSetUnion s (M0 unit)) s).
Proof.
  Exact (MapMerge_m_empty unit).
Qed.

Lemma FSetUnion_idempotent : (s:FSet) (eqmap unit (FSetUnion s s) s).
Proof.
  Exact (MapMerge_idempotent unit).
Qed.

Lemma FSetInter_comm : (s,s':FSet) (eqmap unit (FSetInter s s') (FSetInter s' s)).
Proof.
  Intros. Apply FSet_ext. Intro. Rewrite in_FSet_inter. Rewrite in_FSet_inter. Apply andb_sym.
Qed.

Lemma FSetInter_assoc : (s,s',s'':FSet) (eqmap unit
      (FSetInter (FSetInter s s') s'') (FSetInter s (FSetInter s' s''))).
Proof.
  Exact (MapDomRestrTo_assoc unit unit unit).
Qed.

Lemma FSetInter_M0_s : (s:FSet) (eqmap unit (FSetInter (M0 unit) s) (M0 unit)).
Proof.
  Exact (MapDomRestrTo_empty_m unit unit).
Qed.

Lemma FSetInter_s_M0 : (s:FSet) (eqmap unit (FSetInter s (M0 unit)) (M0 unit)).
Proof.
  Exact (MapDomRestrTo_m_empty unit unit).
Qed.

Lemma FSetInter_idempotent : (s:FSet) (eqmap unit (FSetInter s s) s).
Proof.
  Exact (MapDomRestrTo_idempotent unit).
Qed.

Lemma FSetUnion_Inter_l : (s,s',s'':FSet) (eqmap unit
      (FSetUnion (FSetInter s s') s'') (FSetInter (FSetUnion s s'') (FSetUnion s' s''))).
Proof.
  Intros. Apply FSet_ext. Intro. Rewrite in_FSet_union. Rewrite in_FSet_inter.
  Rewrite in_FSet_inter. Rewrite in_FSet_union. Rewrite in_FSet_union.
  Case (in_FSet a s); Case (in_FSet a s'); Case (in_FSet a s''); Reflexivity.
Qed.

Lemma FSetUnion_Inter_r : (s,s',s'':FSet) (eqmap unit
      (FSetUnion s (FSetInter s' s'')) (FSetInter (FSetUnion s s') (FSetUnion s s''))).
Proof.
  Intros. Apply FSet_ext. Intro. Rewrite in_FSet_union. Rewrite in_FSet_inter.
  Rewrite in_FSet_inter. Rewrite in_FSet_union. Rewrite in_FSet_union.
  Case (in_FSet a s); Case (in_FSet a s'); Case (in_FSet a s''); Reflexivity.
Qed.

Lemma FSetInter_Union_l : (s,s',s'':FSet) (eqmap unit
      (FSetInter (FSetUnion s s') s'') (FSetUnion (FSetInter s s'') (FSetInter s' s''))).
Proof.
  Intros. Apply FSet_ext. Intro. Rewrite in_FSet_inter. Rewrite in_FSet_union.
  Rewrite in_FSet_union. Rewrite in_FSet_inter. Rewrite in_FSet_inter.
  Case (in_FSet a s); Case (in_FSet a s'); Case (in_FSet a s''); Reflexivity.
Qed.

Lemma FSetInter_Union_r : (s,s',s'':FSet) (eqmap unit
      (FSetInter s (FSetUnion s' s'')) (FSetUnion (FSetInter s s') (FSetInter s s''))).
Proof.
  Intros. Apply FSet_ext. Intro. Rewrite in_FSet_inter. Rewrite in_FSet_union.
  Rewrite in_FSet_union. Rewrite in_FSet_inter. Rewrite in_FSet_inter.
  Case (in_FSet a s); Case (in_FSet a s'); Case (in_FSet a s''); Reflexivity.
Qed.

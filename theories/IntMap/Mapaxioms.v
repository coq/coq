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
Require Import NArith.
Require Import Ndigits.
Require Import Ndec.
Require Import Map.
Require Import Fset.

Section MapAxioms.

  Variables A B C : Type.

  Lemma eqm_sym : forall f f':ad -> option A, eqm A f f' -> eqm A f' f.
  Proof.
    unfold eqm in |- *. intros. rewrite H. reflexivity.
  Qed.

  Lemma eqm_refl : forall f:ad -> option A, eqm A f f.
  Proof.
    unfold eqm in |- *. trivial.
  Qed.

  Lemma eqm_trans :
   forall f f' f'':ad -> option A, eqm A f f' -> eqm A f' f'' -> eqm A f f''.
  Proof.
    unfold eqm in |- *. intros. rewrite H. exact (H0 a).
  Qed.

  Definition eqmap (m m':Map A) := eqm A (MapGet A m) (MapGet A m').

  Lemma eqmap_sym : forall m m':Map A, eqmap m m' -> eqmap m' m.
  Proof.
    intros. unfold eqmap in |- *. apply eqm_sym. assumption.
  Qed.

  Lemma eqmap_refl : forall m:Map A, eqmap m m.
  Proof.
    intros. unfold eqmap in |- *. apply eqm_refl.
  Qed.

  Lemma eqmap_trans :
   forall m m' m'':Map A, eqmap m m' -> eqmap m' m'' -> eqmap m m''.
  Proof.
    intros. exact (eqm_trans (MapGet A m) (MapGet A m') (MapGet A m'') H H0).
  Qed.

  Lemma MapPut_as_Merge :
   forall (m:Map A) (a:ad) (y:A),
     eqmap (MapPut A m a y) (MapMerge A m (M1 A a y)).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapPut_semantics A m a y a0).
    rewrite (MapMerge_semantics A m (M1 A a y) a0). unfold MapGet at 2.
    elim (sumbool_of_bool (Neqb a a0)); intro H; rewrite H; reflexivity.
  Qed.

  Lemma MapPut_ext :
   forall m m':Map A,
     eqmap m m' ->
     forall (a:ad) (y:A), eqmap (MapPut A m a y) (MapPut A m' a y).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapPut_semantics A m' a y a0).
    rewrite (MapPut_semantics A m a y a0). 
    case (Neqb a a0); [ reflexivity | apply H ].
  Qed.

  Lemma MapPut_behind_as_Merge :
   forall (m:Map A) (a:ad) (y:A),
     eqmap (MapPut_behind A m a y) (MapMerge A (M1 A a y) m).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapPut_behind_semantics A m a y a0).
    rewrite (MapMerge_semantics A (M1 A a y) m a0). reflexivity.
  Qed.

  Lemma MapPut_behind_ext :
   forall m m':Map A,
     eqmap m m' ->
     forall (a:ad) (y:A),
       eqmap (MapPut_behind A m a y) (MapPut_behind A m' a y).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapPut_behind_semantics A m' a y a0).
    rewrite (MapPut_behind_semantics A m a y a0). rewrite (H a0). reflexivity.
  Qed.

  Lemma MapMerge_empty_m_1 : forall m:Map A, MapMerge A (M0 A) m = m.
  Proof.
    trivial.
  Qed.

  Lemma MapMerge_empty_m : forall m:Map A, eqmap (MapMerge A (M0 A) m) m.
  Proof.
    unfold eqmap, eqm in |- *. trivial.
  Qed.

  Lemma MapMerge_m_empty_1 : forall m:Map A, MapMerge A m (M0 A) = m.
  Proof.
    simple induction m; trivial.
  Qed.

  Lemma MapMerge_m_empty : forall m:Map A, eqmap (MapMerge A m (M0 A)) m.
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite MapMerge_m_empty_1. reflexivity.
  Qed.

  Lemma MapMerge_empty_l :
   forall m m':Map A, eqmap (MapMerge A m m') (M0 A) -> eqmap m (M0 A).
  Proof.
    unfold eqmap, eqm in |- *. intros. cut (MapGet A (MapMerge A m m') a = MapGet A (M0 A) a).
    rewrite (MapMerge_semantics A m m' a). case (MapGet A m' a); trivial.
    intros. discriminate H0.
    exact (H a).
  Qed.

  Lemma MapMerge_empty_r :
   forall m m':Map A, eqmap (MapMerge A m m') (M0 A) -> eqmap m' (M0 A).
  Proof.
    unfold eqmap, eqm in |- *. intros. cut (MapGet A (MapMerge A m m') a = MapGet A (M0 A) a).
    rewrite (MapMerge_semantics A m m' a). case (MapGet A m' a); trivial.
    exact (H a).
  Qed.

  Lemma MapMerge_assoc :
   forall m m' m'':Map A,
     eqmap (MapMerge A (MapMerge A m m') m'')
       (MapMerge A m (MapMerge A m' m'')).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapMerge_semantics A (MapMerge A m m') m'' a).
    rewrite (MapMerge_semantics A m (MapMerge A m' m'') a). rewrite (MapMerge_semantics A m m' a).
    rewrite (MapMerge_semantics A m' m'' a).
    case (MapGet A m'' a); case (MapGet A m' a); trivial.
  Qed.

  Lemma MapMerge_idempotent : forall m:Map A, eqmap (MapMerge A m m) m.
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapMerge_semantics A m m a).
    case (MapGet A m a); trivial.
  Qed.

  Lemma MapMerge_ext :
   forall m1 m2 m'1 m'2:Map A,
     eqmap m1 m'1 ->
     eqmap m2 m'2 -> eqmap (MapMerge A m1 m2) (MapMerge A m'1 m'2).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapMerge_semantics A m1 m2 a).
    rewrite (MapMerge_semantics A m'1 m'2 a). rewrite (H a). rewrite (H0 a). reflexivity.
  Qed.

  Lemma MapMerge_ext_l :
   forall m1 m'1 m2:Map A,
     eqmap m1 m'1 -> eqmap (MapMerge A m1 m2) (MapMerge A m'1 m2).
  Proof.
    intros. apply MapMerge_ext. assumption.
    apply eqmap_refl.
  Qed.

  Lemma MapMerge_ext_r :
   forall m1 m2 m'2:Map A,
     eqmap m2 m'2 -> eqmap (MapMerge A m1 m2) (MapMerge A m1 m'2).
  Proof.
    intros. apply MapMerge_ext. apply eqmap_refl.
    assumption.
  Qed.

  Lemma MapMerge_RestrTo_l :
   forall m m' m'':Map A,
     eqmap (MapMerge A (MapDomRestrTo A A m m') m'')
       (MapDomRestrTo A A (MapMerge A m m'') (MapMerge A m' m'')).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapMerge_semantics A (MapDomRestrTo A A m m') m'' a).
    rewrite (MapDomRestrTo_semantics A A m m' a).
    rewrite
     (MapDomRestrTo_semantics A A (MapMerge A m m'') (MapMerge A m' m'') a)
     .
    rewrite (MapMerge_semantics A m' m'' a). rewrite (MapMerge_semantics A m m'' a).
    case (MapGet A m'' a); case (MapGet A m' a); reflexivity.
  Qed.

  Lemma MapRemove_as_RestrBy :
   forall (m:Map A) (a:ad) (y:B),
     eqmap (MapRemove A m a) (MapDomRestrBy A B m (M1 B a y)).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapRemove_semantics A m a a0).
    rewrite (MapDomRestrBy_semantics A B m (M1 B a y) a0). elim (sumbool_of_bool (Neqb a a0)).
    intro H. rewrite H. rewrite (Neqb_complete a a0 H). rewrite (M1_semantics_1 B a0 y).
    reflexivity.
    intro H. rewrite H. rewrite (M1_semantics_2 B a a0 y H). reflexivity.
  Qed.

  Lemma MapRemove_ext :
   forall m m':Map A,
     eqmap m m' -> forall a:ad, eqmap (MapRemove A m a) (MapRemove A m' a).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapRemove_semantics A m' a a0).
    rewrite (MapRemove_semantics A m a a0). 
    case (Neqb a a0); [ reflexivity | apply H ].
  Qed.

  Lemma MapDomRestrTo_empty_m_1 :
   forall m:Map B, MapDomRestrTo A B (M0 A) m = M0 A.
  Proof.
    trivial.
  Qed.

  Lemma MapDomRestrTo_empty_m :
   forall m:Map B, eqmap (MapDomRestrTo A B (M0 A) m) (M0 A).
  Proof.
    unfold eqmap, eqm in |- *. trivial.
  Qed.

  Lemma MapDomRestrTo_m_empty_1 :
   forall m:Map A, MapDomRestrTo A B m (M0 B) = M0 A.
  Proof.
    simple induction m; trivial.
  Qed.

  Lemma MapDomRestrTo_m_empty :
   forall m:Map A, eqmap (MapDomRestrTo A B m (M0 B)) (M0 A).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDomRestrTo_m_empty_1 m). reflexivity.
  Qed.

  Lemma MapDomRestrTo_assoc :
   forall (m:Map A) (m':Map B) (m'':Map C),
     eqmap (MapDomRestrTo A C (MapDomRestrTo A B m m') m'')
       (MapDomRestrTo A B m (MapDomRestrTo B C m' m'')).
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrTo_semantics A C (MapDomRestrTo A B m m') m'' a).
    rewrite (MapDomRestrTo_semantics A B m m' a).
    rewrite (MapDomRestrTo_semantics A B m (MapDomRestrTo B C m' m'') a).
    rewrite (MapDomRestrTo_semantics B C m' m'' a).
    case (MapGet C m'' a); case (MapGet B m' a); trivial.
  Qed.

  Lemma MapDomRestrTo_idempotent :
   forall m:Map A, eqmap (MapDomRestrTo A A m m) m.
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDomRestrTo_semantics A A m m a).
    case (MapGet A m a); trivial.
  Qed.

  Lemma MapDomRestrTo_Dom :
   forall (m:Map A) (m':Map B),
     eqmap (MapDomRestrTo A B m m') (MapDomRestrTo A unit m (MapDom B m')).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDomRestrTo_semantics A B m m' a).
    rewrite (MapDomRestrTo_semantics A unit m (MapDom B m') a).
    elim (sumbool_of_bool (in_FSet a (MapDom B m'))). intro H.
    elim (MapDom_semantics_2 B m' a H). intros y H0. rewrite H0. unfold in_FSet, in_dom in H.
    generalize H. case (MapGet unit (MapDom B m') a); trivial. intro H1. discriminate H1.
    intro H. rewrite (MapDom_semantics_4 B m' a H). unfold in_FSet, in_dom in H.
    generalize H. case (MapGet unit (MapDom B m') a); trivial.
    intros H0 H1. discriminate H1.
  Qed.

  Lemma MapDomRestrBy_empty_m_1 :
   forall m:Map B, MapDomRestrBy A B (M0 A) m = M0 A.
  Proof.
    trivial.
  Qed.

  Lemma MapDomRestrBy_empty_m :
   forall m:Map B, eqmap (MapDomRestrBy A B (M0 A) m) (M0 A).
  Proof.
    unfold eqmap, eqm in |- *. trivial.
  Qed.

  Lemma MapDomRestrBy_m_empty_1 :
   forall m:Map A, MapDomRestrBy A B m (M0 B) = m.
  Proof.
    simple induction m; trivial.
  Qed.

  Lemma MapDomRestrBy_m_empty :
   forall m:Map A, eqmap (MapDomRestrBy A B m (M0 B)) m.
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDomRestrBy_m_empty_1 m). reflexivity.
  Qed.

  Lemma MapDomRestrBy_Dom :
   forall (m:Map A) (m':Map B),
     eqmap (MapDomRestrBy A B m m') (MapDomRestrBy A unit m (MapDom B m')).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDomRestrBy_semantics A B m m' a).
    rewrite (MapDomRestrBy_semantics A unit m (MapDom B m') a).
    elim (sumbool_of_bool (in_FSet a (MapDom B m'))). intro H.
    elim (MapDom_semantics_2 B m' a H). intros y H0. rewrite H0.
    unfold in_FSet, in_dom in H. generalize H. case (MapGet unit (MapDom B m') a); trivial.
    intro H1. discriminate H1.
    intro H. rewrite (MapDom_semantics_4 B m' a H). unfold in_FSet, in_dom in H.
    generalize H. case (MapGet unit (MapDom B m') a); trivial.
    intros H0 H1. discriminate H1.
  Qed.

  Lemma MapDomRestrBy_m_m_1 :
   forall m:Map A, eqmap (MapDomRestrBy A A m m) (M0 A).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDomRestrBy_semantics A A m m a).
    case (MapGet A m a); trivial.
  Qed.

  Lemma MapDomRestrBy_By :
   forall (m:Map A) (m' m'':Map B),
     eqmap (MapDomRestrBy A B (MapDomRestrBy A B m m') m'')
       (MapDomRestrBy A B m (MapMerge B m' m'')).
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrBy_semantics A B (MapDomRestrBy A B m m') m'' a).
    rewrite (MapDomRestrBy_semantics A B m m' a).
    rewrite (MapDomRestrBy_semantics A B m (MapMerge B m' m'') a).
    rewrite (MapMerge_semantics B m' m'' a).
    case (MapGet B m'' a); case (MapGet B m' a); trivial.
  Qed.

  Lemma MapDomRestrBy_By_comm :
   forall (m:Map A) (m':Map B) (m'':Map C),
     eqmap (MapDomRestrBy A C (MapDomRestrBy A B m m') m'')
       (MapDomRestrBy A B (MapDomRestrBy A C m m'') m').
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrBy_semantics A C (MapDomRestrBy A B m m') m'' a).
    rewrite (MapDomRestrBy_semantics A B m m' a).
    rewrite (MapDomRestrBy_semantics A B (MapDomRestrBy A C m m'') m' a).
    rewrite (MapDomRestrBy_semantics A C m m'' a).
    case (MapGet C m'' a); case (MapGet B m' a); trivial.
  Qed.

  Lemma MapDomRestrBy_To :
   forall (m:Map A) (m':Map B) (m'':Map C),
     eqmap (MapDomRestrBy A C (MapDomRestrTo A B m m') m'')
       (MapDomRestrTo A B m (MapDomRestrBy B C m' m'')).
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrBy_semantics A C (MapDomRestrTo A B m m') m'' a).
    rewrite (MapDomRestrTo_semantics A B m m' a).
    rewrite (MapDomRestrTo_semantics A B m (MapDomRestrBy B C m' m'') a).
    rewrite (MapDomRestrBy_semantics B C m' m'' a).
    case (MapGet C m'' a); case (MapGet B m' a); trivial.
  Qed.

  Lemma MapDomRestrBy_To_comm :
   forall (m:Map A) (m':Map B) (m'':Map C),
     eqmap (MapDomRestrBy A C (MapDomRestrTo A B m m') m'')
       (MapDomRestrTo A B (MapDomRestrBy A C m m'') m').
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrBy_semantics A C (MapDomRestrTo A B m m') m'' a).
    rewrite (MapDomRestrTo_semantics A B m m' a).
    rewrite (MapDomRestrTo_semantics A B (MapDomRestrBy A C m m'') m' a).
    rewrite (MapDomRestrBy_semantics A C m m'' a).
    case (MapGet C m'' a); case (MapGet B m' a); trivial.
  Qed.

  Lemma MapDomRestrTo_By :
   forall (m:Map A) (m':Map B) (m'':Map C),
     eqmap (MapDomRestrTo A C (MapDomRestrBy A B m m') m'')
       (MapDomRestrTo A C m (MapDomRestrBy C B m'' m')).
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrTo_semantics A C (MapDomRestrBy A B m m') m'' a).
    rewrite (MapDomRestrBy_semantics A B m m' a).
    rewrite (MapDomRestrTo_semantics A C m (MapDomRestrBy C B m'' m') a).
    rewrite (MapDomRestrBy_semantics C B m'' m' a).
    case (MapGet C m'' a); case (MapGet B m' a); trivial.
  Qed.

  Lemma MapDomRestrTo_By_comm :
   forall (m:Map A) (m':Map B) (m'':Map C),
     eqmap (MapDomRestrTo A C (MapDomRestrBy A B m m') m'')
       (MapDomRestrBy A B (MapDomRestrTo A C m m'') m').
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrTo_semantics A C (MapDomRestrBy A B m m') m'' a).
    rewrite (MapDomRestrBy_semantics A B m m' a).
    rewrite (MapDomRestrBy_semantics A B (MapDomRestrTo A C m m'') m' a).
    rewrite (MapDomRestrTo_semantics A C m m'' a).
    case (MapGet C m'' a); case (MapGet B m' a); trivial.
  Qed.

  Lemma MapDomRestrTo_To_comm :
   forall (m:Map A) (m':Map B) (m'':Map C),
     eqmap (MapDomRestrTo A C (MapDomRestrTo A B m m') m'')
       (MapDomRestrTo A B (MapDomRestrTo A C m m'') m').
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrTo_semantics A C (MapDomRestrTo A B m m') m'' a).
    rewrite (MapDomRestrTo_semantics A B m m' a).
    rewrite (MapDomRestrTo_semantics A B (MapDomRestrTo A C m m'') m' a).
    rewrite (MapDomRestrTo_semantics A C m m'' a).
    case (MapGet C m'' a); case (MapGet B m' a); trivial.
  Qed.

  Lemma MapMerge_DomRestrTo :
   forall (m m':Map A) (m'':Map B),
     eqmap (MapDomRestrTo A B (MapMerge A m m') m'')
       (MapMerge A (MapDomRestrTo A B m m'') (MapDomRestrTo A B m' m'')).
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrTo_semantics A B (MapMerge A m m') m'' a).
    rewrite (MapMerge_semantics A m m' a).
    rewrite
     (MapMerge_semantics A (MapDomRestrTo A B m m'')
        (MapDomRestrTo A B m' m'') a).
    rewrite (MapDomRestrTo_semantics A B m' m'' a).
    rewrite (MapDomRestrTo_semantics A B m m'' a).
    case (MapGet B m'' a); case (MapGet A m' a); trivial.
  Qed.

  Lemma MapMerge_DomRestrBy :
   forall (m m':Map A) (m'':Map B),
     eqmap (MapDomRestrBy A B (MapMerge A m m') m'')
       (MapMerge A (MapDomRestrBy A B m m'') (MapDomRestrBy A B m' m'')).
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDomRestrBy_semantics A B (MapMerge A m m') m'' a).
    rewrite (MapMerge_semantics A m m' a).
    rewrite
     (MapMerge_semantics A (MapDomRestrBy A B m m'')
        (MapDomRestrBy A B m' m'') a).
    rewrite (MapDomRestrBy_semantics A B m' m'' a).
    rewrite (MapDomRestrBy_semantics A B m m'' a).
    case (MapGet B m'' a); case (MapGet A m' a); trivial.
  Qed.

  Lemma MapDelta_empty_m_1 : forall m:Map A, MapDelta A (M0 A) m = m.
  Proof.
    trivial.
  Qed.

  Lemma MapDelta_empty_m : forall m:Map A, eqmap (MapDelta A (M0 A) m) m.
  Proof.
    unfold eqmap, eqm in |- *. trivial.
  Qed.

  Lemma MapDelta_m_empty_1 : forall m:Map A, MapDelta A m (M0 A) = m.
  Proof.
    simple induction m; trivial.
  Qed.

  Lemma MapDelta_m_empty : forall m:Map A, eqmap (MapDelta A m (M0 A)) m.
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite MapDelta_m_empty_1. reflexivity.
  Qed.

  Lemma MapDelta_nilpotent : forall m:Map A, eqmap (MapDelta A m m) (M0 A).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDelta_semantics A m m a).
    case (MapGet A m a); trivial.
  Qed.

  Lemma MapDelta_as_Merge :
   forall m m':Map A,
     eqmap (MapDelta A m m')
       (MapMerge A (MapDomRestrBy A A m m') (MapDomRestrBy A A m' m)).
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite (MapDelta_semantics A m m' a).
    rewrite
     (MapMerge_semantics A (MapDomRestrBy A A m m') (
        MapDomRestrBy A A m' m) a).
    rewrite (MapDomRestrBy_semantics A A m' m a).
    rewrite (MapDomRestrBy_semantics A A m m' a).
    case (MapGet A m a); case (MapGet A m' a); trivial.
  Qed.

  Lemma MapDelta_as_DomRestrBy :
   forall m m':Map A,
     eqmap (MapDelta A m m')
       (MapDomRestrBy A A (MapMerge A m m') (MapDomRestrTo A A m m')).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDelta_semantics A m m' a).
    rewrite
     (MapDomRestrBy_semantics A A (MapMerge A m m') (
        MapDomRestrTo A A m m') a).
    rewrite (MapDomRestrTo_semantics A A m m' a). rewrite (MapMerge_semantics A m m' a).
    case (MapGet A m a); case (MapGet A m' a); trivial.
  Qed.

  Lemma MapDelta_as_DomRestrBy_2 :
   forall m m':Map A,
     eqmap (MapDelta A m m')
       (MapDomRestrBy A A (MapMerge A m m') (MapDomRestrTo A A m' m)).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDelta_semantics A m m' a).
    rewrite
     (MapDomRestrBy_semantics A A (MapMerge A m m') (
        MapDomRestrTo A A m' m) a).
    rewrite (MapDomRestrTo_semantics A A m' m a). rewrite (MapMerge_semantics A m m' a).
    case (MapGet A m a); case (MapGet A m' a); trivial.
  Qed.

  Lemma MapDelta_sym :
   forall m m':Map A, eqmap (MapDelta A m m') (MapDelta A m' m).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDelta_semantics A m m' a).
    rewrite (MapDelta_semantics A m' m a). 
    case (MapGet A m a); case (MapGet A m' a); trivial.
  Qed.

  Lemma MapDelta_ext :
   forall m1 m2 m'1 m'2:Map A,
     eqmap m1 m'1 ->
     eqmap m2 m'2 -> eqmap (MapDelta A m1 m2) (MapDelta A m'1 m'2).
  Proof.
    unfold eqmap, eqm in |- *. intros. rewrite (MapDelta_semantics A m1 m2 a).
    rewrite (MapDelta_semantics A m'1 m'2 a). rewrite (H a). rewrite (H0 a). reflexivity.
  Qed.

  Lemma MapDelta_ext_l :
   forall m1 m'1 m2:Map A,
     eqmap m1 m'1 -> eqmap (MapDelta A m1 m2) (MapDelta A m'1 m2).
  Proof.
    intros. apply MapDelta_ext. assumption.
    apply eqmap_refl.
  Qed.

  Lemma MapDelta_ext_r :
   forall m1 m2 m'2:Map A,
     eqmap m2 m'2 -> eqmap (MapDelta A m1 m2) (MapDelta A m1 m'2).
  Proof.
    intros. apply MapDelta_ext. apply eqmap_refl.
    assumption.
  Qed.

  Lemma MapDom_Split_1 :
   forall (m:Map A) (m':Map B),
     eqmap m (MapMerge A (MapDomRestrTo A B m m') (MapDomRestrBy A B m m')).
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite
     (MapMerge_semantics A (MapDomRestrTo A B m m') (
        MapDomRestrBy A B m m') a).
    rewrite (MapDomRestrBy_semantics A B m m' a).
    rewrite (MapDomRestrTo_semantics A B m m' a).
    case (MapGet B m' a); case (MapGet A m a); trivial.
  Qed.
 
  Lemma MapDom_Split_2 :
   forall (m:Map A) (m':Map B),
     eqmap m (MapMerge A (MapDomRestrBy A B m m') (MapDomRestrTo A B m m')).
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite
     (MapMerge_semantics A (MapDomRestrBy A B m m') (
        MapDomRestrTo A B m m') a).
    rewrite (MapDomRestrBy_semantics A B m m' a).
    rewrite (MapDomRestrTo_semantics A B m m' a).
    case (MapGet B m' a); case (MapGet A m a); trivial.
  Qed.

  Lemma MapDom_Split_3 :
   forall (m:Map A) (m':Map B),
     eqmap
       (MapDomRestrTo A A (MapDomRestrTo A B m m') (MapDomRestrBy A B m m'))
       (M0 A).
  Proof.
    unfold eqmap, eqm in |- *. intros.
    rewrite
     (MapDomRestrTo_semantics A A (MapDomRestrTo A B m m')
        (MapDomRestrBy A B m m') a).
    rewrite (MapDomRestrBy_semantics A B m m' a).
    rewrite (MapDomRestrTo_semantics A B m m' a).
    case (MapGet B m' a); case (MapGet A m a); trivial.
  Qed.

End MapAxioms.

Lemma MapDomRestrTo_ext :
 forall (A B:Type) (m1:Map A) (m2:Map B) (m'1:Map A) 
   (m'2:Map B),
   eqmap A m1 m'1 ->
   eqmap B m2 m'2 ->
   eqmap A (MapDomRestrTo A B m1 m2) (MapDomRestrTo A B m'1 m'2).
Proof.
  unfold eqmap, eqm in |- *. intros. rewrite (MapDomRestrTo_semantics A B m1 m2 a).
  rewrite (MapDomRestrTo_semantics A B m'1 m'2 a). rewrite (H a). rewrite (H0 a). reflexivity.
Qed.

Lemma MapDomRestrTo_ext_l :
 forall (A B:Type) (m1:Map A) (m2:Map B) (m'1:Map A),
   eqmap A m1 m'1 ->
   eqmap A (MapDomRestrTo A B m1 m2) (MapDomRestrTo A B m'1 m2).
Proof.
  intros. apply MapDomRestrTo_ext; [ assumption | apply eqmap_refl ].
Qed.

Lemma MapDomRestrTo_ext_r :
 forall (A B:Type) (m1:Map A) (m2 m'2:Map B),
   eqmap B m2 m'2 ->
   eqmap A (MapDomRestrTo A B m1 m2) (MapDomRestrTo A B m1 m'2).
Proof.
  intros. apply MapDomRestrTo_ext; [ apply eqmap_refl | assumption ].
Qed.

Lemma MapDomRestrBy_ext :
 forall (A B:Type) (m1:Map A) (m2:Map B) (m'1:Map A) 
   (m'2:Map B),
   eqmap A m1 m'1 ->
   eqmap B m2 m'2 ->
   eqmap A (MapDomRestrBy A B m1 m2) (MapDomRestrBy A B m'1 m'2).
Proof.
  unfold eqmap, eqm in |- *. intros. rewrite (MapDomRestrBy_semantics A B m1 m2 a).
  rewrite (MapDomRestrBy_semantics A B m'1 m'2 a). rewrite (H a). rewrite (H0 a). reflexivity.
Qed.

Lemma MapDomRestrBy_ext_l :
 forall (A B:Type) (m1:Map A) (m2:Map B) (m'1:Map A),
   eqmap A m1 m'1 ->
   eqmap A (MapDomRestrBy A B m1 m2) (MapDomRestrBy A B m'1 m2).
Proof.
  intros. apply MapDomRestrBy_ext; [ assumption | apply eqmap_refl ].
Qed.

Lemma MapDomRestrBy_ext_r :
 forall (A B:Type) (m1:Map A) (m2 m'2:Map B),
   eqmap B m2 m'2 ->
   eqmap A (MapDomRestrBy A B m1 m2) (MapDomRestrBy A B m1 m'2).
Proof.
  intros. apply MapDomRestrBy_ext; [ apply eqmap_refl | assumption ].
Qed.

Lemma MapDomRestrBy_m_m :
 forall (A:Type) (m:Map A),
   eqmap A (MapDomRestrBy A unit m (MapDom A m)) (M0 A).
Proof.
  intros. apply eqmap_trans with (m' := MapDomRestrBy A A m m). apply eqmap_sym.
  apply MapDomRestrBy_Dom.
  apply MapDomRestrBy_m_m_1.
Qed.

Lemma FSetDelta_assoc :
 forall s s' s'':FSet,
   eqmap unit (MapDelta _ (MapDelta _ s s') s'')
     (MapDelta _ s (MapDelta _ s' s'')).
Proof.
  unfold eqmap, eqm in |- *. intros. rewrite (MapDelta_semantics unit (MapDelta unit s s') s'' a).
  rewrite (MapDelta_semantics unit s s' a).
  rewrite (MapDelta_semantics unit s (MapDelta unit s' s'') a).
  rewrite (MapDelta_semantics unit s' s'' a).
  case (MapGet _ s a); case (MapGet _ s' a); case (MapGet _ s'' a); trivial.
  intros. elim u. elim u1. reflexivity.
Qed.

Lemma FSet_ext :
 forall s s':FSet,
   (forall a:ad, in_FSet a s = in_FSet a s') -> eqmap unit s s'.
Proof.
  unfold in_FSet, eqmap, eqm in |- *. intros. elim (sumbool_of_bool (in_dom _ a s)). intro H0.
  elim (in_dom_some _ s a H0). intros y H1. rewrite (H a) in H0. elim (in_dom_some _ s' a H0).
  intros y' H2. rewrite H1. rewrite H2. elim y. elim y'. reflexivity.
  intro H0. rewrite (in_dom_none _ s a H0). rewrite (H a) in H0. rewrite (in_dom_none _ s' a H0).
  reflexivity.
Qed.

Lemma FSetUnion_comm :
 forall s s':FSet, eqmap unit (FSetUnion s s') (FSetUnion s' s).
Proof.
  intros. apply FSet_ext. intro. rewrite in_FSet_union. rewrite in_FSet_union. apply orb_comm.
Qed.

Lemma FSetUnion_assoc :
 forall s s' s'':FSet,
   eqmap unit (FSetUnion (FSetUnion s s') s'')
     (FSetUnion s (FSetUnion s' s'')).
Proof.
  exact (MapMerge_assoc unit).
Qed.

Lemma FSetUnion_M0_s : forall s:FSet, eqmap unit (FSetUnion (M0 unit) s) s.
Proof.
  exact (MapMerge_empty_m unit).
Qed.

Lemma FSetUnion_s_M0 : forall s:FSet, eqmap unit (FSetUnion s (M0 unit)) s.
Proof.
  exact (MapMerge_m_empty unit).
Qed.

Lemma FSetUnion_idempotent : forall s:FSet, eqmap unit (FSetUnion s s) s.
Proof.
  exact (MapMerge_idempotent unit).
Qed.

Lemma FSetInter_comm :
 forall s s':FSet, eqmap unit (FSetInter s s') (FSetInter s' s).
Proof.
  intros. apply FSet_ext. intro. rewrite in_FSet_inter. rewrite in_FSet_inter. apply andb_comm.
Qed.

Lemma FSetInter_assoc :
 forall s s' s'':FSet,
   eqmap unit (FSetInter (FSetInter s s') s'')
     (FSetInter s (FSetInter s' s'')).
Proof.
  exact (MapDomRestrTo_assoc unit unit unit).
Qed.

Lemma FSetInter_M0_s :
 forall s:FSet, eqmap unit (FSetInter (M0 unit) s) (M0 unit).
Proof.
  exact (MapDomRestrTo_empty_m unit unit).
Qed.

Lemma FSetInter_s_M0 :
 forall s:FSet, eqmap unit (FSetInter s (M0 unit)) (M0 unit).
Proof.
  exact (MapDomRestrTo_m_empty unit unit).
Qed.

Lemma FSetInter_idempotent : forall s:FSet, eqmap unit (FSetInter s s) s.
Proof.
  exact (MapDomRestrTo_idempotent unit).
Qed.

Lemma FSetUnion_Inter_l :
 forall s s' s'':FSet,
   eqmap unit (FSetUnion (FSetInter s s') s'')
     (FSetInter (FSetUnion s s'') (FSetUnion s' s'')).
Proof.
  intros. apply FSet_ext. intro. rewrite in_FSet_union. rewrite in_FSet_inter.
  rewrite in_FSet_inter. rewrite in_FSet_union. rewrite in_FSet_union.
  case (in_FSet a s); case (in_FSet a s'); case (in_FSet a s''); reflexivity.
Qed.

Lemma FSetUnion_Inter_r :
 forall s s' s'':FSet,
   eqmap unit (FSetUnion s (FSetInter s' s''))
     (FSetInter (FSetUnion s s') (FSetUnion s s'')).
Proof.
  intros. apply FSet_ext. intro. rewrite in_FSet_union. rewrite in_FSet_inter.
  rewrite in_FSet_inter. rewrite in_FSet_union. rewrite in_FSet_union.
  case (in_FSet a s); case (in_FSet a s'); case (in_FSet a s''); reflexivity.
Qed.

Lemma FSetInter_Union_l :
 forall s s' s'':FSet,
   eqmap unit (FSetInter (FSetUnion s s') s'')
     (FSetUnion (FSetInter s s'') (FSetInter s' s'')).
Proof.
  intros. apply FSet_ext. intro. rewrite in_FSet_inter. rewrite in_FSet_union.
  rewrite in_FSet_union. rewrite in_FSet_inter. rewrite in_FSet_inter.
  case (in_FSet a s); case (in_FSet a s'); case (in_FSet a s''); reflexivity.
Qed.

Lemma FSetInter_Union_r :
 forall s s' s'':FSet,
   eqmap unit (FSetInter s (FSetUnion s' s''))
     (FSetUnion (FSetInter s s') (FSetInter s s'')).
Proof.
  intros. apply FSet_ext. intro. rewrite in_FSet_inter. rewrite in_FSet_union.
  rewrite in_FSet_union. rewrite in_FSet_inter. rewrite in_FSet_inter.
  case (in_FSet a s); case (in_FSet a s'); case (in_FSet a s''); reflexivity.
Qed.
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

(*s Sets operations on maps *)

Require Import Bool.
Require Import Sumbool.
Require Import ZArith.
Require Import Addr.
Require Import Adist.
Require Import Addec.
Require Import Map.

Section Dom.

  Variables A B : Set.

  Fixpoint MapDomRestrTo (m:Map A) : Map B -> Map A :=
    match m with
    | M0 => fun _:Map B => M0 A
    | M1 a y =>
        fun m':Map B => match MapGet B m' a with
                        | NONE => M0 A
                        | _ => m
                        end
    | M2 m1 m2 =>
        fun m':Map B =>
          match m' with
          | M0 => M0 A
          | M1 a' y' =>
              match MapGet A m a' with
              | NONE => M0 A
              | SOME y => M1 A a' y
              end
          | M2 m'1 m'2 =>
              makeM2 A (MapDomRestrTo m1 m'1) (MapDomRestrTo m2 m'2)
          end
    end.

  Lemma MapDomRestrTo_semantics :
   forall (m:Map A) (m':Map B),
     eqm A (MapGet A (MapDomRestrTo m m'))
       (fun a0:ad =>
          match MapGet B m' a0 with
          | NONE => NONE A
          | _ => MapGet A m a0
          end).
  Proof.
    unfold eqm in |- *. simple induction m. simpl in |- *. intros. case (MapGet B m' a); trivial.
    intros. simpl in |- *. elim (sumbool_of_bool (ad_eq a a1)). intro H. rewrite H.
    rewrite <- (ad_eq_complete _ _ H). case (MapGet B m' a). reflexivity.
    intro. apply M1_semantics_1.
    intro H. rewrite H. case (MapGet B m' a). 
    case (MapGet B m' a1); reflexivity.
    case (MapGet B m' a1); intros; exact (M1_semantics_2 A a a1 a0 H).
    simple induction m'. trivial.
    unfold MapDomRestrTo in |- *. intros. elim (sumbool_of_bool (ad_eq a a1)).
    intro H1.
    rewrite (ad_eq_complete _ _ H1). rewrite (M1_semantics_1 B a1 a0).
    case (MapGet A (M2 A m0 m1) a1). reflexivity.
    intro. apply M1_semantics_1.
    intro H1. rewrite (M1_semantics_2 B a a1 a0 H1). case (MapGet A (M2 A m0 m1) a). reflexivity.
    intro. exact (M1_semantics_2 A a a1 a2 H1).
    intros. change
   (MapGet A (makeM2 A (MapDomRestrTo m0 m2) (MapDomRestrTo m1 m3)) a =
    match MapGet B (M2 B m2 m3) a with
    | NONE => NONE A
    | SOME _ => MapGet A (M2 A m0 m1) a
    end) in |- *.
    rewrite (makeM2_M2 A (MapDomRestrTo m0 m2) (MapDomRestrTo m1 m3) a).
    rewrite MapGet_M2_bit_0_if. rewrite (H0 m3 (ad_div_2 a)). rewrite (H m2 (ad_div_2 a)).
    rewrite (MapGet_M2_bit_0_if B m2 m3 a). rewrite (MapGet_M2_bit_0_if A m0 m1 a).
    case (ad_bit_0 a); reflexivity.
  Qed.

  Fixpoint MapDomRestrBy (m:Map A) : Map B -> Map A :=
    match m with
    | M0 => fun _:Map B => M0 A
    | M1 a y =>
        fun m':Map B => match MapGet B m' a with
                        | NONE => m
                        | _ => M0 A
                        end
    | M2 m1 m2 =>
        fun m':Map B =>
          match m' with
          | M0 => m
          | M1 a' y' => MapRemove A m a'
          | M2 m'1 m'2 =>
              makeM2 A (MapDomRestrBy m1 m'1) (MapDomRestrBy m2 m'2)
          end
    end.

  Lemma MapDomRestrBy_semantics :
   forall (m:Map A) (m':Map B),
     eqm A (MapGet A (MapDomRestrBy m m'))
       (fun a0:ad =>
          match MapGet B m' a0 with
          | NONE => MapGet A m a0
          | _ => NONE A
          end).
  Proof.
    unfold eqm in |- *. simple induction m. simpl in |- *. intros. case (MapGet B m' a); trivial.
    intros. simpl in |- *. elim (sumbool_of_bool (ad_eq a a1)). intro H. rewrite H.
    rewrite (ad_eq_complete _ _ H). case (MapGet B m' a1). apply M1_semantics_1.
    trivial.
    intro H. rewrite H. case (MapGet B m' a). rewrite (M1_semantics_2 A a a1 a0 H).
    case (MapGet B m' a1); trivial.
    case (MapGet B m' a1); trivial.
    simple induction m'. trivial.
    unfold MapDomRestrBy in |- *. intros. rewrite (MapRemove_semantics A (M2 A m0 m1) a a1).
    elim (sumbool_of_bool (ad_eq a a1)). intro H1. rewrite H1. rewrite (ad_eq_complete _ _ H1).
    rewrite (M1_semantics_1 B a1 a0). reflexivity.
    intro H1. rewrite H1. rewrite (M1_semantics_2 B a a1 a0 H1). reflexivity.
    intros. change
   (MapGet A (makeM2 A (MapDomRestrBy m0 m2) (MapDomRestrBy m1 m3)) a =
    match MapGet B (M2 B m2 m3) a with
    | NONE => MapGet A (M2 A m0 m1) a
    | SOME _ => NONE A
    end) in |- *.
    rewrite (makeM2_M2 A (MapDomRestrBy m0 m2) (MapDomRestrBy m1 m3) a).
    rewrite MapGet_M2_bit_0_if. rewrite (H0 m3 (ad_div_2 a)). rewrite (H m2 (ad_div_2 a)).
    rewrite (MapGet_M2_bit_0_if B m2 m3 a). rewrite (MapGet_M2_bit_0_if A m0 m1 a).
    case (ad_bit_0 a); reflexivity.
  Qed.

  Definition in_dom (a:ad) (m:Map A) :=
    match MapGet A m a with
    | NONE => false
    | _ => true
    end.

  Lemma in_dom_M0 : forall a:ad, in_dom a (M0 A) = false.
  Proof.
    trivial.
  Qed.

  Lemma in_dom_M1 : forall (a a0:ad) (y:A), in_dom a0 (M1 A a y) = ad_eq a a0.
  Proof.
    unfold in_dom in |- *. intros. simpl in |- *. case (ad_eq a a0); reflexivity.
  Qed.

  Lemma in_dom_M1_1 : forall (a:ad) (y:A), in_dom a (M1 A a y) = true.
  Proof.
    intros. rewrite in_dom_M1. apply ad_eq_correct.
  Qed.

  Lemma in_dom_M1_2 :
   forall (a a0:ad) (y:A), in_dom a0 (M1 A a y) = true -> a = a0.
  Proof.
    intros. apply (ad_eq_complete a a0). rewrite (in_dom_M1 a a0 y) in H. assumption.
  Qed.

  Lemma in_dom_some :
   forall (m:Map A) (a:ad),
     in_dom a m = true -> {y : A | MapGet A m a = SOME A y}.
  Proof.
    unfold in_dom in |- *. intros. elim (option_sum _ (MapGet A m a)). trivial.
    intro H0. rewrite H0 in H. discriminate H.
  Qed.

  Lemma in_dom_none :
   forall (m:Map A) (a:ad), in_dom a m = false -> MapGet A m a = NONE A.
  Proof.
    unfold in_dom in |- *. intros. elim (option_sum _ (MapGet A m a)). intro H0. elim H0.
    intros y H1. rewrite H1 in H. discriminate H.
    trivial.
  Qed.

  Lemma in_dom_put :
   forall (m:Map A) (a0:ad) (y0:A) (a:ad),
     in_dom a (MapPut A m a0 y0) = orb (ad_eq a a0) (in_dom a m).
  Proof.
    unfold in_dom in |- *. intros. rewrite (MapPut_semantics A m a0 y0 a).
    elim (sumbool_of_bool (ad_eq a a0)). intro H. rewrite H. rewrite (ad_eq_comm a a0) in H.
    rewrite H. rewrite orb_true_b. reflexivity.
    intro H. rewrite H. rewrite (ad_eq_comm a a0) in H. rewrite H. rewrite orb_false_b.
    reflexivity.
  Qed.

  Lemma in_dom_put_behind :
   forall (m:Map A) (a0:ad) (y0:A) (a:ad),
     in_dom a (MapPut_behind A m a0 y0) = orb (ad_eq a a0) (in_dom a m).
  Proof.
    unfold in_dom in |- *. intros. rewrite (MapPut_behind_semantics A m a0 y0 a).
    elim (sumbool_of_bool (ad_eq a a0)). intro H. rewrite H. rewrite (ad_eq_comm a a0) in H.
    rewrite H. case (MapGet A m a); reflexivity.
    intro H. rewrite H. rewrite (ad_eq_comm a a0) in H. rewrite H. case (MapGet A m a); trivial.
  Qed.

  Lemma in_dom_remove :
   forall (m:Map A) (a0 a:ad),
     in_dom a (MapRemove A m a0) = andb (negb (ad_eq a a0)) (in_dom a m).
  Proof.
    unfold in_dom in |- *. intros. rewrite (MapRemove_semantics A m a0 a).
    elim (sumbool_of_bool (ad_eq a a0)). intro H. rewrite H. rewrite (ad_eq_comm a a0) in H.
    rewrite H. reflexivity.
    intro H. rewrite H. rewrite (ad_eq_comm a a0) in H. rewrite H.
    case (MapGet A m a); reflexivity.
  Qed.

  Lemma in_dom_merge :
   forall (m m':Map A) (a:ad),
     in_dom a (MapMerge A m m') = orb (in_dom a m) (in_dom a m').
  Proof.
    unfold in_dom in |- *. intros. rewrite (MapMerge_semantics A m m' a).
    elim (option_sum A (MapGet A m' a)). intro H. elim H. intros y H0. rewrite H0.
    case (MapGet A m a); reflexivity.
    intro H. rewrite H. rewrite orb_b_false. reflexivity.
  Qed.

  Lemma in_dom_delta :
   forall (m m':Map A) (a:ad),
     in_dom a (MapDelta A m m') = xorb (in_dom a m) (in_dom a m').
  Proof.
    unfold in_dom in |- *. intros. rewrite (MapDelta_semantics A m m' a).
    elim (option_sum A (MapGet A m' a)). intro H. elim H. intros y H0. rewrite H0.
    case (MapGet A m a); reflexivity.
    intro H. rewrite H. case (MapGet A m a); reflexivity.
  Qed.

End Dom.

Section InDom.

  Variables A B : Set.

  Lemma in_dom_restrto :
   forall (m:Map A) (m':Map B) (a:ad),
     in_dom A a (MapDomRestrTo A B m m') =
     andb (in_dom A a m) (in_dom B a m').
  Proof.
    unfold in_dom in |- *. intros. rewrite (MapDomRestrTo_semantics A B m m' a).
    elim (option_sum B (MapGet B m' a)). intro H. elim H. intros y H0. rewrite H0.
    rewrite andb_b_true. reflexivity.
    intro H. rewrite H. rewrite andb_b_false. reflexivity.
  Qed.

  Lemma in_dom_restrby :
   forall (m:Map A) (m':Map B) (a:ad),
     in_dom A a (MapDomRestrBy A B m m') =
     andb (in_dom A a m) (negb (in_dom B a m')).
  Proof.
    unfold in_dom in |- *. intros. rewrite (MapDomRestrBy_semantics A B m m' a).
    elim (option_sum B (MapGet B m' a)). intro H. elim H. intros y H0. rewrite H0.
    unfold negb in |- *. rewrite andb_b_false. reflexivity.
    intro H. rewrite H. unfold negb in |- *. rewrite andb_b_true. reflexivity.
  Qed.

End InDom.

Definition FSet := Map unit.

Section FSetDefs.

  Variable A : Set.

  Definition in_FSet : ad -> FSet -> bool := in_dom unit.

  Fixpoint MapDom (m:Map A) : FSet :=
    match m with
    | M0 => M0 unit
    | M1 a _ => M1 unit a tt
    | M2 m m' => M2 unit (MapDom m) (MapDom m')
    end.

  Lemma MapDom_semantics_1 :
   forall (m:Map A) (a:ad) (y:A),
     MapGet A m a = SOME A y -> in_FSet a (MapDom m) = true.
  Proof.
    simple induction m. intros. discriminate H.
    unfold MapDom in |- *. unfold in_FSet in |- *. unfold in_dom in |- *. unfold MapGet in |- *. intros a y a0 y0.
    case (ad_eq a a0). trivial.
    intro. discriminate H.
    intros m0 H m1 H0 a y. rewrite (MapGet_M2_bit_0_if A m0 m1 a). simpl in |- *. unfold in_FSet in |- *.
    unfold in_dom in |- *. rewrite (MapGet_M2_bit_0_if unit (MapDom m0) (MapDom m1) a).
    case (ad_bit_0 a). unfold in_FSet, in_dom in H0. intro. apply H0 with (y := y). assumption.
    unfold in_FSet, in_dom in H. intro. apply H with (y := y). assumption.
  Qed.

  Lemma MapDom_semantics_2 :
   forall (m:Map A) (a:ad),
     in_FSet a (MapDom m) = true -> {y : A | MapGet A m a = SOME A y}.
  Proof.
    simple induction m. intros. discriminate H.
    unfold MapDom in |- *. unfold in_FSet in |- *. unfold in_dom in |- *. unfold MapGet in |- *. intros a y a0. case (ad_eq a a0).
    intro. split with y. reflexivity.
    intro. discriminate H.
    intros m0 H m1 H0 a. rewrite (MapGet_M2_bit_0_if A m0 m1 a). simpl in |- *. unfold in_FSet in |- *.
    unfold in_dom in |- *. rewrite (MapGet_M2_bit_0_if unit (MapDom m0) (MapDom m1) a).
    case (ad_bit_0 a). unfold in_FSet, in_dom in H0. intro. apply H0. assumption.
    unfold in_FSet, in_dom in H. intro. apply H. assumption.
  Qed.

  Lemma MapDom_semantics_3 :
   forall (m:Map A) (a:ad),
     MapGet A m a = NONE A -> in_FSet a (MapDom m) = false.
  Proof.
    intros. elim (sumbool_of_bool (in_FSet a (MapDom m))). intro H0.
    elim (MapDom_semantics_2 m a H0). intros y H1. rewrite H in H1. discriminate H1.
    trivial.
  Qed.

  Lemma MapDom_semantics_4 :
   forall (m:Map A) (a:ad),
     in_FSet a (MapDom m) = false -> MapGet A m a = NONE A.
  Proof.
    intros. elim (option_sum A (MapGet A m a)). intro H0. elim H0. intros y H1.
    rewrite (MapDom_semantics_1 m a y H1) in H. discriminate H.
    trivial.
  Qed.

  Lemma MapDom_Dom :
   forall (m:Map A) (a:ad), in_dom A a m = in_FSet a (MapDom m).
  Proof.
    intros. elim (sumbool_of_bool (in_FSet a (MapDom m))). intro H.
    elim (MapDom_semantics_2 m a H). intros y H0. rewrite H. unfold in_dom in |- *. rewrite H0.
    reflexivity.
    intro H. rewrite H. unfold in_dom in |- *. rewrite (MapDom_semantics_4 m a H). reflexivity.
  Qed.

  Definition FSetUnion (s s':FSet) : FSet := MapMerge unit s s'.

  Lemma in_FSet_union :
   forall (s s':FSet) (a:ad),
     in_FSet a (FSetUnion s s') = orb (in_FSet a s) (in_FSet a s').
  Proof.
    exact (in_dom_merge unit).
  Qed.

  Definition FSetInter (s s':FSet) : FSet := MapDomRestrTo unit unit s s'.

  Lemma in_FSet_inter :
   forall (s s':FSet) (a:ad),
     in_FSet a (FSetInter s s') = andb (in_FSet a s) (in_FSet a s').
  Proof.
    exact (in_dom_restrto unit unit).
  Qed.

  Definition FSetDiff (s s':FSet) : FSet := MapDomRestrBy unit unit s s'.

  Lemma in_FSet_diff :
   forall (s s':FSet) (a:ad),
     in_FSet a (FSetDiff s s') = andb (in_FSet a s) (negb (in_FSet a s')).
  Proof.
    exact (in_dom_restrby unit unit).
  Qed.

  Definition FSetDelta (s s':FSet) : FSet := MapDelta unit s s'.

  Lemma in_FSet_delta :
   forall (s s':FSet) (a:ad),
     in_FSet a (FSetDelta s s') = xorb (in_FSet a s) (in_FSet a s').
  Proof.
    exact (in_dom_delta unit).
  Qed.

End FSetDefs.

Lemma FSet_Dom : forall s:FSet, MapDom unit s = s.
Proof.
  simple induction s. trivial.
  simpl in |- *. intros a t. elim t. reflexivity.
  intros. simpl in |- *. rewrite H. rewrite H0. reflexivity.
Qed.
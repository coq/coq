(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

Require Import BinNat.
Require Import Ndigits.
Require Import Ndec.
Require Import Map.
Require Import Fset.
Require Import Mapaxioms.
Require Import Mapsubset.
Require Import Mapcard.
Require Import Mapcanon.
Require Import Mapc.
Require Import Bool.
Require Import Sumbool.
Require Import List.
Require Import Arith.
Require Import Mapiter.
Require Import Mapfold.

Section MapLists.

  Fixpoint ad_in_list (a:ad) (l:list ad) {struct l} : bool :=
    match l with
    | nil => false
    | a' :: l' => orb (Neqb a a') (ad_in_list a l')
    end.

  Fixpoint ad_list_stutters (l:list ad) : bool :=
    match l with
    | nil => false
    | a :: l' => orb (ad_in_list a l') (ad_list_stutters l')
    end.

  Lemma ad_in_list_forms_circuit :
   forall (x:ad) (l:list ad),
     ad_in_list x l = true ->
     {l1 : list ad &  {l2 : list ad | l = l1 ++ x :: l2}}.
  Proof.
    simple induction l. intro. discriminate H.
    intros. elim (sumbool_of_bool (Neqb x a)). intro H1. simpl in H0. split with (nil (A:=ad)).
    split with l0. rewrite (Neqb_complete _ _ H1). reflexivity.
    intro H2. simpl in H0. rewrite H2 in H0. simpl in H0. elim (H H0). intros l'1 H3.
    split with (a :: l'1). elim H3. intros l2 H4. split with l2. rewrite H4. reflexivity.
  Qed.

  Lemma ad_list_stutters_has_circuit :
   forall l:list ad,
     ad_list_stutters l = true ->
     {x : ad & 
     {l0 : list ad & 
     {l1 : list ad &  {l2 : list ad | l = l0 ++ x :: l1 ++ x :: l2}}}}.
  Proof.
    simple induction l. intro. discriminate H.
    intros. simpl in H0. elim (orb_true_elim _ _ H0). intro H1. split with a.
    split with (nil (A:=ad)). simpl in |- *. elim (ad_in_list_forms_circuit a l0 H1). intros l1 H2.
    split with l1. elim H2. intros l2 H3. split with l2. rewrite H3. reflexivity.
    intro H1. elim (H H1). intros x H2. split with x. elim H2. intros l1 H3.
    split with (a :: l1). elim H3. intros l2 H4. split with l2. elim H4. intros l3 H5.
    split with l3. rewrite H5. reflexivity.
  Qed.

  Fixpoint Elems (l:list ad) : FSet :=
    match l with
    | nil => M0 unit
    | a :: l' => MapPut _ (Elems l') a tt
    end.

  Lemma Elems_canon : forall l:list ad, mapcanon _ (Elems l).
  Proof.
    simple induction l. exact (M0_canon unit).
    intros. simpl in |- *. apply MapPut_canon. assumption.
  Qed.

  Lemma Elems_app :
   forall l l':list ad, Elems (l ++ l') = FSetUnion (Elems l) (Elems l').
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. rewrite (MapPut_as_Merge_c unit (Elems l0)).
    rewrite (MapPut_as_Merge_c unit (Elems (l0 ++ l'))).
    change
      (FSetUnion (Elems (l0 ++ l')) (M1 unit a tt) =
       FSetUnion (FSetUnion (Elems l0) (M1 unit a tt)) (Elems l')) 
     in |- *.
    rewrite FSetUnion_comm_c. rewrite (FSetUnion_comm_c (Elems l0) (M1 unit a tt)).
    rewrite FSetUnion_assoc_c. rewrite (H l'). reflexivity.
    apply M1_canon.
    apply Elems_canon.
    apply Elems_canon.
    apply Elems_canon.
    apply M1_canon.
    apply Elems_canon.
    apply M1_canon.
    apply Elems_canon.
    apply Elems_canon.
  Qed.

  Lemma Elems_rev : forall l:list ad, Elems (rev l) = Elems l.
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. rewrite Elems_app. simpl in |- *. rewrite (MapPut_as_Merge_c unit (Elems l0)).
    rewrite H. reflexivity.
    apply Elems_canon.
  Qed.

  Lemma ad_in_elems_in_list :
   forall (l:list ad) (a:ad), in_FSet a (Elems l) = ad_in_list a l.
  Proof.
    simple induction l. trivial.
    simpl in |- *. unfold in_FSet in |- *. intros. rewrite (in_dom_put _ (Elems l0) a tt a0).
    rewrite (H a0). reflexivity.
  Qed.

  Lemma ad_list_not_stutters_card :
   forall l:list ad,
     ad_list_stutters l = false -> length l = MapCard _ (Elems l).
  Proof.
    simple induction l. trivial.
    simpl in |- *. intros. rewrite MapCard_Put_2_conv. rewrite H. reflexivity.
    elim (orb_false_elim _ _ H0). trivial.
    elim (sumbool_of_bool (in_FSet a (Elems l0))). rewrite ad_in_elems_in_list.
    intro H1. rewrite H1 in H0. discriminate H0.
    exact (in_dom_none unit (Elems l0) a).
  Qed.

  Lemma ad_list_card : forall l:list ad, MapCard _ (Elems l) <= length l.
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. apply le_trans with (m := S (MapCard _ (Elems l0))). apply MapCard_Put_ub.
    apply le_n_S. assumption.
  Qed.

  Lemma ad_list_stutters_card :
   forall l:list ad,
     ad_list_stutters l = true -> MapCard _ (Elems l) < length l.
  Proof.
    simple induction l. intro. discriminate H.
    intros. simpl in |- *. simpl in H0. elim (orb_true_elim _ _ H0). intro H1.
    rewrite <- (ad_in_elems_in_list l0 a) in H1. elim (in_dom_some _ _ _ H1). intros y H2.
    rewrite (MapCard_Put_1_conv _ _ _ _ tt H2). apply le_lt_trans with (m := length l0).
    apply ad_list_card.
    apply lt_n_Sn.
    intro H1. apply le_lt_trans with (m := S (MapCard _ (Elems l0))). apply MapCard_Put_ub.
    apply lt_n_S. apply H. assumption.
  Qed.

  Lemma ad_list_not_stutters_card_conv :
   forall l:list ad,
     length l = MapCard _ (Elems l) -> ad_list_stutters l = false.
  Proof.
    intros. elim (sumbool_of_bool (ad_list_stutters l)). intro H0.
    cut (MapCard _ (Elems l) < length l). intro. rewrite H in H1. elim (lt_irrefl _ H1).
    exact (ad_list_stutters_card _ H0).
    trivial.
  Qed.

  Lemma ad_list_stutters_card_conv :
   forall l:list ad,
     MapCard _ (Elems l) < length l -> ad_list_stutters l = true.
  Proof.
    intros. elim (sumbool_of_bool (ad_list_stutters l)). trivial.
    intro H0. rewrite (ad_list_not_stutters_card _ H0) in H. elim (lt_irrefl _ H).
  Qed.

  Lemma ad_in_list_l :
   forall (l l':list ad) (a:ad),
     ad_in_list a l = true -> ad_in_list a (l ++ l') = true.
  Proof.
    simple induction l. intros. discriminate H.
    intros. simpl in |- *. simpl in H0. elim (orb_true_elim _ _ H0). intro H1. rewrite H1. reflexivity.
    intro H1. rewrite (H l' a0 H1). apply orb_b_true.
  Qed.

  Lemma ad_list_stutters_app_l :
   forall l l':list ad,
     ad_list_stutters l = true -> ad_list_stutters (l ++ l') = true.
  Proof.
    simple induction l. intros. discriminate H.
    intros. simpl in |- *. simpl in H0. elim (orb_true_elim _ _ H0). intro H1.
    rewrite (ad_in_list_l l0 l' a H1). reflexivity.
    intro H1. rewrite (H l' H1). apply orb_b_true.
  Qed.

  Lemma ad_in_list_r :
   forall (l l':list ad) (a:ad),
     ad_in_list a l' = true -> ad_in_list a (l ++ l') = true.
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. rewrite (H l' a0 H0). apply orb_b_true. 
  Qed.

  Lemma ad_list_stutters_app_r :
   forall l l':list ad,
     ad_list_stutters l' = true -> ad_list_stutters (l ++ l') = true.
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. rewrite (H l' H0). apply orb_b_true.
  Qed.

  Lemma ad_list_stutters_app_conv_l :
   forall l l':list ad,
     ad_list_stutters (l ++ l') = false -> ad_list_stutters l = false.
  Proof.
    intros. elim (sumbool_of_bool (ad_list_stutters l)). intro H0.
    rewrite (ad_list_stutters_app_l l l' H0) in H. discriminate H.
    trivial.
  Qed.

  Lemma ad_list_stutters_app_conv_r :
   forall l l':list ad,
     ad_list_stutters (l ++ l') = false -> ad_list_stutters l' = false.
  Proof.
    intros. elim (sumbool_of_bool (ad_list_stutters l')). intro H0.
    rewrite (ad_list_stutters_app_r l l' H0) in H. discriminate H.
    trivial.
  Qed.

  Lemma ad_in_list_app_1 :
   forall (l l':list ad) (x:ad), ad_in_list x (l ++ x :: l') = true.
  Proof.
    simple induction l. simpl in |- *. intros. rewrite (Neqb_correct x). reflexivity.
    intros. simpl in |- *. rewrite (H l' x). apply orb_b_true.
  Qed.

  Lemma ad_in_list_app :
   forall (l l':list ad) (x:ad),
     ad_in_list x (l ++ l') = orb (ad_in_list x l) (ad_in_list x l').
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. rewrite <- orb_assoc. rewrite (H l' x). reflexivity.
  Qed.

  Lemma ad_in_list_rev :
   forall (l:list ad) (x:ad), ad_in_list x (rev l) = ad_in_list x l.
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. rewrite ad_in_list_app. rewrite (H x). simpl in |- *. rewrite orb_b_false.
    apply orb_comm.
  Qed.

  Lemma ad_list_has_circuit_stutters :
   forall (l0 l1 l2:list ad) (x:ad),
     ad_list_stutters (l0 ++ x :: l1 ++ x :: l2) = true.
  Proof.
    simple induction l0. simpl in |- *. intros. rewrite (ad_in_list_app_1 l1 l2 x). reflexivity.
    intros. simpl in |- *. rewrite (H l1 l2 x). apply orb_b_true.
  Qed.

  Lemma ad_list_stutters_prev_l :
   forall (l l':list ad) (x:ad),
     ad_in_list x l = true -> ad_list_stutters (l ++ x :: l') = true.
  Proof.
    intros. elim (ad_in_list_forms_circuit _ _ H). intros l0 H0. elim H0. intros l1 H1.
    rewrite H1. rewrite app_ass. simpl in |- *. apply ad_list_has_circuit_stutters.
  Qed.

  Lemma ad_list_stutters_prev_conv_l :
   forall (l l':list ad) (x:ad),
     ad_list_stutters (l ++ x :: l') = false -> ad_in_list x l = false.
  Proof.
    intros. elim (sumbool_of_bool (ad_in_list x l)). intro H0.
    rewrite (ad_list_stutters_prev_l l l' x H0) in H. discriminate H.
    trivial.
  Qed.

  Lemma ad_list_stutters_prev_r :
   forall (l l':list ad) (x:ad),
     ad_in_list x l' = true -> ad_list_stutters (l ++ x :: l') = true.
  Proof.
    intros. elim (ad_in_list_forms_circuit _ _ H). intros l0 H0. elim H0. intros l1 H1.
    rewrite H1. apply ad_list_has_circuit_stutters.
  Qed.

  Lemma ad_list_stutters_prev_conv_r :
   forall (l l':list ad) (x:ad),
     ad_list_stutters (l ++ x :: l') = false -> ad_in_list x l' = false.
  Proof.
    intros. elim (sumbool_of_bool (ad_in_list x l')). intro H0.
    rewrite (ad_list_stutters_prev_r l l' x H0) in H. discriminate H.
    trivial.
  Qed.

  Lemma ad_list_Elems :
   forall l l':list ad,
     MapCard _ (Elems l) = MapCard _ (Elems l') ->
     length l = length l' -> ad_list_stutters l = ad_list_stutters l'.
  Proof.
    intros. elim (sumbool_of_bool (ad_list_stutters l)). intro H1. rewrite H1. apply sym_eq.
    apply ad_list_stutters_card_conv. rewrite <- H. rewrite <- H0. apply ad_list_stutters_card.
    assumption.
    intro H1. rewrite H1. apply sym_eq. apply ad_list_not_stutters_card_conv. rewrite <- H.
    rewrite <- H0. apply ad_list_not_stutters_card. assumption.
  Qed.

  Lemma ad_list_app_length :
   forall l l':list ad, length (l ++ l') = length l + length l'.
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. rewrite (H l'). reflexivity.
  Qed.

  Lemma ad_list_stutters_permute :
   forall l l':list ad,
     ad_list_stutters (l ++ l') = ad_list_stutters (l' ++ l).
  Proof.
    intros. apply ad_list_Elems. rewrite Elems_app. rewrite Elems_app.
    rewrite (FSetUnion_comm_c _ _ (Elems_canon l) (Elems_canon l')). reflexivity.
    rewrite ad_list_app_length. rewrite ad_list_app_length. apply plus_comm.
  Qed.

  Lemma ad_list_rev_length : forall l:list ad, length (rev l) = length l.
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. rewrite ad_list_app_length. simpl in |- *. rewrite H. rewrite <- plus_Snm_nSm.
    rewrite <- plus_n_O. reflexivity.
  Qed.

  Lemma ad_list_stutters_rev :
   forall l:list ad, ad_list_stutters (rev l) = ad_list_stutters l.
  Proof.
    intros. apply ad_list_Elems. rewrite Elems_rev. reflexivity.
    apply ad_list_rev_length.
  Qed.

  Lemma ad_list_app_rev :
   forall (l l':list ad) (x:ad), rev l ++ x :: l' = rev (x :: l) ++ l'.
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. rewrite (app_ass (rev l0) (a :: nil) (x :: l')). simpl in |- *.
    rewrite (H (x :: l') a). simpl in |- *.
    rewrite (app_ass (rev l0) (a :: nil) (x :: nil)). simpl in |- *.
    rewrite app_ass. simpl in |- *. rewrite app_ass. reflexivity.
  Qed.

  Section ListOfDomDef.

  Variable A : Type.

  Definition ad_list_of_dom :=
    MapFold A (list ad) nil (app (A:=ad)) (fun (a:ad) (_:A) => a :: nil).

  Lemma ad_in_list_of_dom_in_dom :
   forall (m:Map A) (a:ad), ad_in_list a (ad_list_of_dom m) = in_dom A a m.
  Proof.
    unfold ad_list_of_dom in |- *. intros.
    rewrite
     (MapFold_distr_l A (list ad) nil (app (A:=ad)) bool false orb ad
        (fun (a:ad) (l:list ad) => ad_in_list a l) (
        fun c:ad => refl_equal _) ad_in_list_app
        (fun (a0:ad) (_:A) => a0 :: nil) m a).
    simpl in |- *. rewrite (MapFold_orb A (fun (a0:ad) (_:A) => orb (Neqb a a0) false) m).
    elim
     (option_sum _
        (MapSweep A (fun (a0:ad) (_:A) => orb (Neqb a a0) false) m)). intro H. elim H.
    intro r. elim r. intros a0 y H0. rewrite H0. unfold in_dom in |- *.
    elim (orb_prop _ _ (MapSweep_semantics_1 _ _ _ _ _ H0)). intro H1.
    rewrite (Neqb_complete _ _ H1). rewrite (MapSweep_semantics_2 A _ _ _ _ H0). reflexivity.
    intro H1. discriminate H1.
    intro H. rewrite H. elim (sumbool_of_bool (in_dom A a m)). intro H0.
    elim (in_dom_some A m a H0). intros y H1.
    elim (orb_false_elim _ _ (MapSweep_semantics_3 _ _ _ H _ _ H1)). intro H2.
    rewrite (Neqb_correct a) in H2. discriminate H2.
    exact (sym_eq (y:=_)).
  Qed.

  Lemma Elems_of_list_of_dom :
   forall m:Map A, eqmap unit (Elems (ad_list_of_dom m)) (MapDom A m).
  Proof.
    unfold eqmap, eqm in |- *. intros. elim (sumbool_of_bool (in_FSet a (Elems (ad_list_of_dom m)))).
    intro H. elim (in_dom_some _ _ _ H). intro t. elim t. intro H0.
    rewrite (ad_in_elems_in_list (ad_list_of_dom m) a) in H.
    rewrite (ad_in_list_of_dom_in_dom m a) in H. rewrite (MapDom_Dom A m a) in H.
    elim (in_dom_some _ _ _ H). intro t'. elim t'. intro H1. rewrite H1. assumption.
    intro H. rewrite (in_dom_none _ _ _ H).
    rewrite (ad_in_elems_in_list (ad_list_of_dom m) a) in H.
    rewrite (ad_in_list_of_dom_in_dom m a) in H. rewrite (MapDom_Dom A m a) in H.
    rewrite (in_dom_none _ _ _ H). reflexivity.
  Qed.

  Lemma Elems_of_list_of_dom_c :
   forall m:Map A, mapcanon A m -> Elems (ad_list_of_dom m) = MapDom A m.
  Proof.
    intros. apply (mapcanon_unique unit). apply Elems_canon.
    apply MapDom_canon. assumption.
    apply Elems_of_list_of_dom.
  Qed.

  Lemma ad_list_of_dom_card_1 :
   forall (m:Map A) (pf:ad -> ad),
     length
       (MapFold1 A (list ad) nil (app (A:=ad)) (fun (a:ad) (_:A) => a :: nil)
          pf m) = MapCard A m.
  Proof.
    simple induction m; try trivial. simpl in |- *. intros. rewrite ad_list_app_length.
    rewrite (H (fun a0:ad => pf (Ndouble a0))). rewrite (H0 (fun a0:ad => pf (Ndouble_plus_one a0))).
    reflexivity.
  Qed.

  Lemma ad_list_of_dom_card :
   forall m:Map A, length (ad_list_of_dom m) = MapCard A m.
  Proof.
    exact (fun m:Map A => ad_list_of_dom_card_1 m (fun a:ad => a)).
  Qed.

  Lemma ad_list_of_dom_not_stutters :
   forall m:Map A, ad_list_stutters (ad_list_of_dom m) = false.
  Proof.
    intro. apply ad_list_not_stutters_card_conv. rewrite ad_list_of_dom_card. apply sym_eq.
    rewrite (MapCard_Dom A m). apply MapCard_ext. exact (Elems_of_list_of_dom m).
  Qed.

  End ListOfDomDef.

  Lemma ad_list_of_dom_Dom_1 :
   forall (A:Type) (m:Map A) (pf:ad -> ad),
     MapFold1 A (list ad) nil (app (A:=ad)) (fun (a:ad) (_:A) => a :: nil) pf
       m =
     MapFold1 unit (list ad) nil (app (A:=ad))
       (fun (a:ad) (_:unit) => a :: nil) pf (MapDom A m).
  Proof.
    simple induction m; try trivial. simpl in |- *. intros. rewrite (H (fun a0:ad => pf (Ndouble a0))).
    rewrite (H0 (fun a0:ad => pf (Ndouble_plus_one a0))). reflexivity.
  Qed.

  Lemma ad_list_of_dom_Dom :
   forall (A:Type) (m:Map A),
     ad_list_of_dom A m = ad_list_of_dom unit (MapDom A m).
  Proof.
    intros. exact (ad_list_of_dom_Dom_1 A m (fun a0:ad => a0)).
  Qed.

End MapLists.
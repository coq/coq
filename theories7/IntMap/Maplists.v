(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

Require Addr.
Require Addec.
Require Map.
Require Fset.
Require Mapaxioms.
Require Mapsubset.
Require Mapcard.
Require Mapcanon.
Require Mapc.
Require Bool.
Require Sumbool.
Require PolyList.
Require Arith.
Require Mapiter.
Require Mapfold.

Section MapLists.

  Fixpoint ad_in_list [a:ad;l:(list ad)] : bool :=
    Cases l of
	nil => false
      | (cons a' l') => (orb (ad_eq a a') (ad_in_list a l'))
    end.

  Fixpoint ad_list_stutters [l:(list ad)] : bool :=
    Cases l of
	nil => false
      | (cons a l') => (orb (ad_in_list a l') (ad_list_stutters l'))
    end.

  Lemma ad_in_list_forms_circuit : (x:ad) (l:(list ad)) (ad_in_list x l)=true ->
      {l1 : (list ad) & {l2 : (list ad) | l=(app l1 (cons x l2))}}.
  Proof.
    Induction l. Intro. Discriminate H.
    Intros. Elim (sumbool_of_bool (ad_eq x a)). Intro H1. Simpl in H0. Split with (nil ad).
    Split with l0. Rewrite (ad_eq_complete ? ? H1). Reflexivity.
    Intro H2. Simpl in H0. Rewrite H2 in H0. Simpl in H0. Elim (H H0). Intros l'1 H3.
    Split with (cons a l'1). Elim H3. Intros l2 H4. Split with l2. Rewrite H4. Reflexivity.
  Qed.

  Lemma ad_list_stutters_has_circuit : (l:(list ad)) (ad_list_stutters l)=true ->
      {x:ad & {l0 : (list ad) & {l1 : (list ad) & {l2 : (list ad) |
        l=(app l0 (cons x (app l1 (cons x l2))))}}}}.
  Proof.
    Induction l. Intro. Discriminate H.
    Intros. Simpl in H0. Elim (orb_true_elim ? ? H0). Intro H1. Split with a.
    Split with (nil ad). Simpl. Elim (ad_in_list_forms_circuit a l0 H1). Intros l1 H2.
    Split with l1. Elim H2. Intros l2 H3. Split with l2. Rewrite H3. Reflexivity.
    Intro H1. Elim (H H1). Intros x H2. Split with x. Elim H2. Intros l1 H3.
    Split with (cons a l1). Elim H3. Intros l2 H4. Split with l2. Elim H4. Intros l3 H5.
    Split with l3. Rewrite H5. Reflexivity.
  Qed.

  Fixpoint Elems [l:(list ad)] : FSet :=
    Cases l of
	nil => (M0 unit)
      | (cons a l') => (MapPut ? (Elems l') a tt)
    end.

  Lemma Elems_canon : (l:(list ad)) (mapcanon ? (Elems l)).
  Proof.
    Induction l. Exact (M0_canon unit).
    Intros. Simpl. Apply MapPut_canon. Assumption.
  Qed.

  Lemma Elems_app : (l,l':(list ad)) (Elems (app l l'))=(FSetUnion (Elems l) (Elems l')).
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Rewrite (MapPut_as_Merge_c unit (Elems l0)).
    Rewrite (MapPut_as_Merge_c unit (Elems (app l0 l'))).
    Change (FSetUnion (Elems (app l0 l')) (M1 unit a tt))
           =(FSetUnion (FSetUnion (Elems l0) (M1 unit a tt)) (Elems l')).
    Rewrite FSetUnion_comm_c. Rewrite (FSetUnion_comm_c (Elems l0) (M1 unit a tt)).
    Rewrite FSetUnion_assoc_c. Rewrite (H l'). Reflexivity.
    Apply M1_canon.
    Apply Elems_canon.
    Apply Elems_canon.
    Apply Elems_canon.
    Apply M1_canon.
    Apply Elems_canon.
    Apply M1_canon.
    Apply Elems_canon.
    Apply Elems_canon.
  Qed.

  Lemma Elems_rev : (l:(list ad)) (Elems (rev l))=(Elems l).
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Rewrite Elems_app. Simpl. Rewrite (MapPut_as_Merge_c unit (Elems l0)).
    Rewrite H. Reflexivity.
    Apply Elems_canon.
  Qed.

  Lemma ad_in_elems_in_list : (l:(list ad)) (a:ad) (in_FSet a (Elems l))=(ad_in_list a l).
  Proof.
    Induction l. Trivial.
    Simpl. Unfold in_FSet. Intros. Rewrite (in_dom_put ? (Elems l0) a tt a0).
    Rewrite (H a0). Reflexivity.
  Qed.

  Lemma ad_list_not_stutters_card : (l:(list ad)) (ad_list_stutters l)=false ->
      	  (length l)=(MapCard ? (Elems l)).
  Proof.
    Induction l. Trivial.
    Simpl. Intros. Rewrite MapCard_Put_2_conv. Rewrite H. Reflexivity.
    Elim (orb_false_elim ? ? H0). Trivial.
    Elim (sumbool_of_bool (in_FSet a (Elems l0))). Rewrite ad_in_elems_in_list.
    Intro H1. Rewrite H1 in H0. Discriminate H0.
    Exact (in_dom_none unit (Elems l0) a).
  Qed.

  Lemma ad_list_card : (l:(list ad)) (le (MapCard ? (Elems l)) (length l)).
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Apply le_trans with m:=(S (MapCard ? (Elems l0))). Apply MapCard_Put_ub.
    Apply le_n_S. Assumption.
  Qed.

  Lemma ad_list_stutters_card : (l:(list ad)) (ad_list_stutters l)=true ->
      	 (lt (MapCard ? (Elems l)) (length l)).
  Proof.
    Induction l. Intro. Discriminate H.
    Intros. Simpl. Simpl in H0. Elim (orb_true_elim ? ? H0). Intro H1.
    Rewrite <- (ad_in_elems_in_list l0 a) in H1. Elim (in_dom_some ? ? ? H1). Intros y H2.
    Rewrite (MapCard_Put_1_conv ? ? ? ? tt H2). Apply le_lt_trans with m:=(length l0).
    Apply ad_list_card.
    Apply lt_n_Sn.
    Intro H1. Apply le_lt_trans with m:=(S (MapCard ? (Elems l0))). Apply MapCard_Put_ub.
    Apply lt_n_S. Apply H. Assumption.
  Qed.

  Lemma ad_list_not_stutters_card_conv : (l:(list ad)) (length l)=(MapCard ? (Elems l)) ->
      (ad_list_stutters l)=false.
  Proof.
    Intros. Elim (sumbool_of_bool (ad_list_stutters l)). Intro H0.
    Cut (lt (MapCard ? (Elems l)) (length l)). Intro. Rewrite H in H1. Elim (lt_n_n ? H1).
    Exact (ad_list_stutters_card ? H0).
    Trivial.
  Qed.

  Lemma ad_list_stutters_card_conv : (l:(list ad)) (lt (MapCard ? (Elems l)) (length l)) ->
      (ad_list_stutters l)=true.
  Proof.
    Intros. Elim (sumbool_of_bool (ad_list_stutters l)). Trivial.
    Intro H0. Rewrite (ad_list_not_stutters_card ? H0) in H. Elim (lt_n_n ? H).
  Qed.

  Lemma ad_in_list_l : (l,l':(list ad)) (a:ad) (ad_in_list a l)=true ->
      (ad_in_list a (app l l'))=true.
  Proof.
    Induction l. Intros. Discriminate H.
    Intros. Simpl. Simpl in H0. Elim (orb_true_elim ? ? H0). Intro H1. Rewrite H1. Reflexivity.
    Intro H1. Rewrite (H l' a0 H1). Apply orb_b_true.
  Qed.

  Lemma ad_list_stutters_app_l : (l,l':(list ad)) (ad_list_stutters l)=true ->
      (ad_list_stutters (app l l'))=true.
  Proof.
    Induction l. Intros. Discriminate H.
    Intros. Simpl. Simpl in H0. Elim (orb_true_elim ? ? H0). Intro H1.
    Rewrite (ad_in_list_l l0 l' a H1). Reflexivity.
    Intro H1. Rewrite (H l' H1). Apply orb_b_true.
  Qed.

  Lemma ad_in_list_r : (l,l':(list ad)) (a:ad) (ad_in_list a l')=true ->
      (ad_in_list a (app l l'))=true.
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Rewrite (H l' a0 H0). Apply orb_b_true. 
  Qed.

  Lemma ad_list_stutters_app_r : (l,l':(list ad)) (ad_list_stutters l')=true ->
      (ad_list_stutters (app l l'))=true.
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Rewrite (H l' H0). Apply orb_b_true.
  Qed.

  Lemma ad_list_stutters_app_conv_l : (l,l':(list ad)) (ad_list_stutters (app l l'))=false ->
      (ad_list_stutters l)=false.
  Proof.
    Intros. Elim (sumbool_of_bool (ad_list_stutters l)). Intro H0.
    Rewrite (ad_list_stutters_app_l l l' H0) in H. Discriminate H.
    Trivial.
  Qed.

  Lemma ad_list_stutters_app_conv_r : (l,l':(list ad)) (ad_list_stutters (app l l'))=false ->
      (ad_list_stutters l')=false.
  Proof.
    Intros. Elim (sumbool_of_bool (ad_list_stutters l')). Intro H0.
    Rewrite (ad_list_stutters_app_r l l' H0) in H. Discriminate H.
    Trivial.
  Qed.

  Lemma ad_in_list_app_1 : (l,l':(list ad)) (x:ad) (ad_in_list x (app l (cons x l')))=true.
  Proof.
    Induction l. Simpl. Intros. Rewrite (ad_eq_correct x). Reflexivity.
    Intros. Simpl. Rewrite (H l' x). Apply orb_b_true.
  Qed.

  Lemma ad_in_list_app : (l,l':(list ad)) (x:ad)
      (ad_in_list x (app l l'))=(orb (ad_in_list x l) (ad_in_list x l')).
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Rewrite <- orb_assoc. Rewrite (H l' x). Reflexivity.
  Qed.

  Lemma ad_in_list_rev : (l:(list ad)) (x:ad)
      (ad_in_list x (rev l))=(ad_in_list x l).
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Rewrite ad_in_list_app. Rewrite (H x). Simpl. Rewrite orb_b_false.
    Apply orb_sym.
  Qed.

  Lemma ad_list_has_circuit_stutters : (l0,l1,l2:(list ad)) (x:ad)
      (ad_list_stutters (app l0 (cons x (app l1 (cons x l2)))))=true.
  Proof.
    Induction l0. Simpl. Intros. Rewrite (ad_in_list_app_1 l1 l2 x). Reflexivity.
    Intros. Simpl. Rewrite (H l1 l2 x). Apply orb_b_true.
  Qed.

  Lemma ad_list_stutters_prev_l : (l,l':(list ad)) (x:ad) (ad_in_list x l)=true ->
      (ad_list_stutters (app l (cons x l')))=true.
  Proof.
    Intros. Elim (ad_in_list_forms_circuit ? ? H). Intros l0 H0. Elim H0. Intros l1 H1.
    Rewrite H1. Rewrite app_ass. Simpl. Apply ad_list_has_circuit_stutters.
  Qed.

  Lemma ad_list_stutters_prev_conv_l : (l,l':(list ad)) (x:ad)
      (ad_list_stutters (app l (cons x l')))=false -> (ad_in_list x l)=false.
  Proof.
    Intros. Elim (sumbool_of_bool (ad_in_list x l)). Intro H0.
    Rewrite (ad_list_stutters_prev_l l l' x H0) in H. Discriminate H.
    Trivial.
  Qed.

  Lemma ad_list_stutters_prev_r : (l,l':(list ad)) (x:ad) (ad_in_list x l')=true ->
      (ad_list_stutters (app l (cons x l')))=true.
  Proof.
    Intros. Elim (ad_in_list_forms_circuit ? ? H). Intros l0 H0. Elim H0. Intros l1 H1.
    Rewrite H1. Apply ad_list_has_circuit_stutters.
  Qed.

  Lemma ad_list_stutters_prev_conv_r : (l,l':(list ad)) (x:ad)
      (ad_list_stutters (app l (cons x l')))=false -> (ad_in_list x l')=false.
  Proof.
    Intros. Elim (sumbool_of_bool (ad_in_list x l')). Intro H0.
    Rewrite (ad_list_stutters_prev_r l l' x H0) in H. Discriminate H.
    Trivial.
  Qed.

  Lemma ad_list_Elems : (l,l':(list ad)) (MapCard ? (Elems l))=(MapCard ? (Elems l')) ->
      (length l)=(length l') ->
        (ad_list_stutters l)=(ad_list_stutters l').
  Proof.
    Intros. Elim (sumbool_of_bool (ad_list_stutters l)). Intro H1. Rewrite H1. Apply sym_eq.
    Apply ad_list_stutters_card_conv. Rewrite <- H. Rewrite <- H0. Apply ad_list_stutters_card.
    Assumption.
    Intro H1. Rewrite H1. Apply sym_eq. Apply ad_list_not_stutters_card_conv. Rewrite <- H.
    Rewrite <- H0. Apply ad_list_not_stutters_card. Assumption.
  Qed.

  Lemma ad_list_app_length : (l,l':(list ad)) (length (app l l'))=(plus (length l) (length l')).
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Rewrite (H l'). Reflexivity.
  Qed.

  Lemma ad_list_stutters_permute : (l,l':(list ad))
      (ad_list_stutters (app l l'))=(ad_list_stutters (app l' l)).
  Proof.
    Intros. Apply ad_list_Elems. Rewrite Elems_app. Rewrite Elems_app.
    Rewrite (FSetUnion_comm_c ? ? (Elems_canon l) (Elems_canon l')). Reflexivity.
    Rewrite ad_list_app_length. Rewrite ad_list_app_length. Apply plus_sym.
  Qed.

  Lemma ad_list_rev_length : (l:(list ad)) (length (rev l))=(length l).
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Rewrite ad_list_app_length. Simpl. Rewrite H. Rewrite <- plus_Snm_nSm.
    Rewrite <- plus_n_O. Reflexivity.
  Qed.

  Lemma ad_list_stutters_rev : (l:(list ad)) (ad_list_stutters (rev l))=(ad_list_stutters l).
  Proof.
    Intros. Apply ad_list_Elems. Rewrite Elems_rev. Reflexivity.
    Apply ad_list_rev_length.
  Qed.

  Lemma ad_list_app_rev : (l,l':(list ad)) (x:ad)
      (app (rev l) (cons x l'))=(app (rev (cons x l)) l').
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Rewrite (app_ass (rev l0) (cons a (nil ad)) (cons x l')). Simpl.
    Rewrite (H (cons x l') a). Simpl.
    Rewrite (app_ass (rev l0) (cons a (nil ad)) (cons x (nil ad))). Simpl.
    Rewrite app_ass. Simpl. Rewrite app_ass. Reflexivity.
  Qed.

  Section ListOfDomDef.

  Variable A : Set.

  Definition ad_list_of_dom :=
      (MapFold A (list ad) (nil ad) (!app ad) [a:ad][_:A] (cons a (nil ad))).

  Lemma ad_in_list_of_dom_in_dom : (m:(Map A)) (a:ad)
      (ad_in_list a (ad_list_of_dom m))=(in_dom A a m).
  Proof.
    Unfold ad_list_of_dom. Intros.
    Rewrite (MapFold_distr_l A (list ad) (nil ad) (!app ad) bool false orb
              ad [a:ad][l:(list ad)](ad_in_list a l) [c:ad](refl_equal ? ?)
              ad_in_list_app [a0:ad][_:A](cons a0 (nil ad)) m a).
    Simpl. Rewrite (MapFold_orb A [a0:ad][_:A](orb (ad_eq a a0) false) m).
    Elim (option_sum ? (MapSweep A [a0:ad][_:A](orb (ad_eq a a0) false) m)). Intro H. Elim H.
    Intro r. Elim r. Intros a0 y H0. Rewrite H0. Unfold in_dom.
    Elim (orb_prop ? ? (MapSweep_semantics_1 ? ? ? ? ? H0)). Intro H1.
    Rewrite (ad_eq_complete ? ? H1). Rewrite (MapSweep_semantics_2 A ? ? ? ? H0). Reflexivity.
    Intro H1. Discriminate H1.
    Intro H. Rewrite H. Elim (sumbool_of_bool (in_dom A a m)). Intro H0.
    Elim (in_dom_some A m a H0). Intros y H1.
    Elim (orb_false_elim ? ? (MapSweep_semantics_3 ? ? ? H ? ? H1)). Intro H2.
    Rewrite (ad_eq_correct a) in H2. Discriminate H2.
    Exact (sym_eq ? ? ?).
  Qed.

  Lemma Elems_of_list_of_dom : 
      (m:(Map A)) (eqmap unit (Elems (ad_list_of_dom m)) (MapDom A m)).
  Proof.
    Unfold eqmap eqm. Intros. Elim (sumbool_of_bool (in_FSet a (Elems (ad_list_of_dom m)))).
    Intro H. Elim (in_dom_some ? ? ? H). Intro t. Elim t. Intro H0.
    Rewrite (ad_in_elems_in_list (ad_list_of_dom m) a) in H.
    Rewrite (ad_in_list_of_dom_in_dom m a) in H. Rewrite (MapDom_Dom A m a) in H.
    Elim (in_dom_some ? ? ? H). Intro t'. Elim t'. Intro H1. Rewrite H1. Assumption.
    Intro H. Rewrite (in_dom_none ? ? ? H).
    Rewrite (ad_in_elems_in_list (ad_list_of_dom m) a) in H.
    Rewrite (ad_in_list_of_dom_in_dom m a) in H. Rewrite (MapDom_Dom A m a) in H.
    Rewrite (in_dom_none ? ? ? H). Reflexivity.
  Qed.

  Lemma Elems_of_list_of_dom_c : (m:(Map A)) (mapcanon A m) ->
      (Elems (ad_list_of_dom m))=(MapDom A m).
  Proof.
    Intros. Apply (mapcanon_unique unit). Apply Elems_canon.
    Apply MapDom_canon. Assumption.
    Apply Elems_of_list_of_dom.
  Qed.

  Lemma ad_list_of_dom_card_1 : (m:(Map A)) (pf:ad->ad)
      (length (MapFold1 A (list ad) (nil ad) (app 1!ad) [a:ad][_:A](cons a (nil ad)) pf m))=
      (MapCard A m).
  Proof.
    Induction m; Try Trivial. Simpl. Intros. Rewrite ad_list_app_length.
    Rewrite (H [a0:ad](pf (ad_double a0))). Rewrite (H0 [a0:ad](pf (ad_double_plus_un a0))).
    Reflexivity.
  Qed.

  Lemma ad_list_of_dom_card : (m:(Map A)) (length (ad_list_of_dom m))=(MapCard A m).
  Proof.
    Exact [m:(Map A)](ad_list_of_dom_card_1 m [a:ad]a).
  Qed.

  Lemma ad_list_of_dom_not_stutters : 
      (m:(Map A)) (ad_list_stutters (ad_list_of_dom m))=false.
  Proof.
    Intro. Apply ad_list_not_stutters_card_conv. Rewrite ad_list_of_dom_card. Apply sym_eq.
    Rewrite (MapCard_Dom A m). Apply MapCard_ext. Exact (Elems_of_list_of_dom m).
  Qed.

  End ListOfDomDef.

  Lemma ad_list_of_dom_Dom_1 : (A:Set)
    (m:(Map A)) (pf:ad->ad)
      (MapFold1 A (list ad) (nil ad) (app 1!ad) 
        [a:ad][_:A](cons a (nil ad)) pf m)=
      (MapFold1 unit (list ad) (nil ad) (app 1!ad)
        [a:ad][_:unit](cons a (nil ad)) pf (MapDom A m)).
  Proof.
    Induction m; Try Trivial. Simpl. Intros. Rewrite (H [a0:ad](pf (ad_double a0))).
    Rewrite (H0 [a0:ad](pf (ad_double_plus_un a0))). Reflexivity.
  Qed.

  Lemma ad_list_of_dom_Dom : (A:Set) (m:(Map A))
      (ad_list_of_dom A m)=(ad_list_of_dom unit (MapDom A m)).
  Proof.
    Intros. Exact (ad_list_of_dom_Dom_1 A m [a0:ad]a0).
  Qed.

End MapLists.

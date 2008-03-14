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
Require Import Mapsubset.
Require Import List.
Require Import Lsort.
Require Import Peano_dec.

Section MapCard.

  Variables A B : Set.

  Lemma MapCard_M0 : MapCard A (M0 A) = 0.
  Proof.
    trivial.
  Qed.

  Lemma MapCard_M1 : forall (a:ad) (y:A), MapCard A (M1 A a y) = 1.
  Proof.
    trivial.
  Qed.

  Lemma MapCard_is_O :
   forall m:Map A, MapCard A m = 0 -> forall a:ad, MapGet A m a = None.
  Proof.
    simple induction m. trivial.
    intros a y H. discriminate H.
    intros. simpl in H1. elim (plus_is_O _ _ H1). intros. rewrite (MapGet_M2_bit_0_if A m0 m1 a).
    case (Nbit0 a). apply H0. assumption.
    apply H. assumption.
  Qed.

  Lemma MapCard_is_not_O :
   forall (m:Map A) (a:ad) (y:A),
     MapGet A m a = Some y -> {n : nat | MapCard A m = S n}.
  Proof.
    simple induction m. intros. discriminate H.
    intros a y a0 y0 H. simpl in H. elim (sumbool_of_bool (Neqb a a0)). intro H0. split with 0.
    reflexivity.
    intro H0. rewrite H0 in H. discriminate H.
    intros. elim (sumbool_of_bool (Nbit0 a)). intro H2.
    rewrite (MapGet_M2_bit_0_1 A a H2 m0 m1) in H1. elim (H0 (Ndiv2 a) y H1). intros n H3.
    simpl in |- *. rewrite H3. split with (MapCard A m0 + n).
    rewrite <- (plus_Snm_nSm (MapCard A m0) n). reflexivity.
    intro H2. rewrite (MapGet_M2_bit_0_0 A a H2 m0 m1) in H1. elim (H (Ndiv2 a) y H1).
    intros n H3. simpl in |- *. rewrite H3. split with (n + MapCard A m1). reflexivity.
  Qed.

  Lemma MapCard_is_one :
   forall m:Map A,
     MapCard A m = 1 -> {a : ad &  {y : A | MapGet A m a = Some y}}.
  Proof.
    simple induction m. intro. discriminate H.
    intros a y H. split with a. split with y. apply M1_semantics_1.
    intros. simpl in H1. elim (plus_is_one (MapCard A m0) (MapCard A m1) H1).
    intro H2. elim H2. intros. elim (H0 H4). intros a H5. split with (Ndouble_plus_one a).
    rewrite (MapGet_M2_bit_0_1 A _ (Ndouble_plus_one_bit0 a) m0 m1).
    rewrite Ndouble_plus_one_div2. exact H5.
    intro H2. elim H2. intros. elim (H H3). intros a H5. split with (Ndouble a).
    rewrite (MapGet_M2_bit_0_0 A _ (Ndouble_bit0 a) m0 m1).
    rewrite Ndouble_div2. exact H5.
  Qed.

  Lemma MapCard_is_one_unique :
   forall m:Map A,
     MapCard A m = 1 ->
     forall (a a':ad) (y y':A),
       MapGet A m a = Some y ->
       MapGet A m a' = Some y' -> a = a' /\ y = y'.
  Proof.
    simple induction m. intro. discriminate H.
    intros. elim (sumbool_of_bool (Neqb a a1)). intro H2. rewrite (Neqb_complete _ _ H2) in H0.
    rewrite (M1_semantics_1 A a1 a0) in H0. inversion H0. elim (sumbool_of_bool (Neqb a a')).
    intro H5. rewrite (Neqb_complete _ _ H5) in H1. rewrite (M1_semantics_1 A a' a0) in H1.
    inversion H1. rewrite <- (Neqb_complete _ _ H2). rewrite <- (Neqb_complete _ _ H5).
    rewrite <- H4. rewrite <- H6. split; reflexivity.
    intro H5. rewrite (M1_semantics_2 A a a' a0 H5) in H1. discriminate H1.
    intro H2. rewrite (M1_semantics_2 A a a1 a0 H2) in H0. discriminate H0.
    intros. simpl in H1. elim (plus_is_one _ _ H1). intro H4. elim H4. intros.
    rewrite (MapGet_M2_bit_0_if A m0 m1 a) in H2. elim (sumbool_of_bool (Nbit0 a)).
    intro H7. rewrite H7 in H2. rewrite (MapGet_M2_bit_0_if A m0 m1 a') in H3.
    elim (sumbool_of_bool (Nbit0 a')). intro H8. rewrite H8 in H3. elim (H0 H6 _ _ _ _ H2 H3).
    intros. split. rewrite <- (Ndiv2_double_plus_one a H7).
    rewrite <- (Ndiv2_double_plus_one a' H8). rewrite H9. reflexivity.
    assumption.
    intro H8. rewrite H8 in H3. rewrite (MapCard_is_O m0 H5 (Ndiv2 a')) in H3.
    discriminate H3.
    intro H7. rewrite H7 in H2. rewrite (MapCard_is_O m0 H5 (Ndiv2 a)) in H2.
    discriminate H2.
    intro H4. elim H4. intros. rewrite (MapGet_M2_bit_0_if A m0 m1 a) in H2.
    elim (sumbool_of_bool (Nbit0 a)). intro H7. rewrite H7 in H2.
    rewrite (MapCard_is_O m1 H6 (Ndiv2 a)) in H2. discriminate H2.
    intro H7. rewrite H7 in H2. rewrite (MapGet_M2_bit_0_if A m0 m1 a') in H3.
    elim (sumbool_of_bool (Nbit0 a')). intro H8. rewrite H8 in H3.
    rewrite (MapCard_is_O m1 H6 (Ndiv2 a')) in H3. discriminate H3.
    intro H8. rewrite H8 in H3. elim (H H5 _ _ _ _ H2 H3). intros. split.
    rewrite <- (Ndiv2_double a H7). rewrite <- (Ndiv2_double a' H8).
    rewrite H9. reflexivity.
    assumption.
  Qed.

  Lemma length_as_fold :
   forall (C:Set) (l:list C),
     length l = fold_right (fun (_:C) (n:nat) => S n) 0 l.
  Proof.
    simple induction l. reflexivity.
    intros. simpl in |- *. rewrite H. reflexivity.
  Qed.

  Lemma length_as_fold_2 :
   forall l:alist A,
     length l =
     fold_right (fun (r:ad * A) (n:nat) => let (a, y) := r in 1 + n) 0 l.
  Proof.
    simple induction l. reflexivity.
    intros. simpl in |- *. rewrite H. elim a; reflexivity.
  Qed.

  Lemma MapCard_as_Fold_1 :
   forall (m:Map A) (pf:ad -> ad),
     MapCard A m = MapFold1 A nat 0 plus (fun (_:ad) (_:A) => 1) pf m.
  Proof.
    simple induction m. trivial.
    trivial.
    intros. simpl in |- *. rewrite <- (H (fun a0:ad => pf (Ndouble a0))).
    rewrite <- (H0 (fun a0:ad => pf (Ndouble_plus_one a0))). reflexivity.
  Qed.

  Lemma MapCard_as_Fold :
   forall m:Map A,
     MapCard A m = MapFold A nat 0 plus (fun (_:ad) (_:A) => 1) m.
  Proof.
    intro. exact (MapCard_as_Fold_1 m (fun a0:ad => a0)).
  Qed.
 
  Lemma MapCard_as_length :
   forall m:Map A, MapCard A m = length (alist_of_Map A m).
  Proof.
    intro. rewrite MapCard_as_Fold. rewrite length_as_fold_2.
    apply MapFold_as_fold with
     (op := plus) (neutral := 0) (f := fun (_:ad) (_:A) => 1). exact plus_assoc_reverse.
    trivial.
    intro. rewrite <- plus_n_O. reflexivity.
  Qed.

  Lemma MapCard_Put1_equals_2 :
   forall (p:positive) (a a':ad) (y y':A),
     MapCard A (MapPut1 A a y a' y' p) = 2.
  Proof.
    simple induction p. intros. simpl in |- *. case (Nbit0 a); reflexivity.
    intros. simpl in |- *. case (Nbit0 a). exact (H (Ndiv2 a) (Ndiv2 a') y y').
    simpl in |- *. rewrite <- plus_n_O. exact (H (Ndiv2 a) (Ndiv2 a') y y').
    intros. simpl in |- *. case (Nbit0 a); reflexivity.
  Qed.

  Lemma MapCard_Put_sum :
   forall (m m':Map A) (a:ad) (y:A) (n n':nat),
     m' = MapPut A m a y ->
     n = MapCard A m -> n' = MapCard A m' -> {n' = n} + {n' = S n}.
  Proof.
    simple induction m. simpl in |- *. intros. rewrite H in H1. simpl in H1. right.
    rewrite H0. rewrite H1. reflexivity.
    intros a y m' a0 y0 n n' H H0 H1. simpl in H. elim (Ndiscr (Nxor a a0)). intro H2.
    elim H2. intros p H3. rewrite H3 in H. rewrite H in H1.
    rewrite (MapCard_Put1_equals_2 p a a0 y y0) in H1. simpl in H0. right.
    rewrite H0. rewrite H1. reflexivity.
    intro H2. rewrite H2 in H. rewrite H in H1. simpl in H1. simpl in H0. left.
    rewrite H0. rewrite H1. reflexivity.
    intros. simpl in H2. rewrite (MapPut_semantics_3_1 A m0 m1 a y) in H1.
    elim (sumbool_of_bool (Nbit0 a)). intro H4. rewrite H4 in H1.
    elim
     (H0 (MapPut A m1 (Ndiv2 a) y) (Ndiv2 a) y (
        MapCard A m1) (MapCard A (MapPut A m1 (Ndiv2 a) y)) (
        refl_equal _) (refl_equal _) (refl_equal _)).
    intro H5. rewrite H1 in H3. simpl in H3. rewrite H5 in H3. rewrite <- H2 in H3. left.
    assumption.
    intro H5. rewrite H1 in H3. simpl in H3. rewrite H5 in H3.
    rewrite <- (plus_Snm_nSm (MapCard A m0) (MapCard A m1)) in H3.
    simpl in H3. rewrite <- H2 in H3. right. assumption.
    intro H4. rewrite H4 in H1.
    elim
     (H (MapPut A m0 (Ndiv2 a) y) (Ndiv2 a) y (
        MapCard A m0) (MapCard A (MapPut A m0 (Ndiv2 a) y)) (
        refl_equal _) (refl_equal _) (refl_equal _)).
    intro H5. rewrite H1 in H3. simpl in H3. rewrite H5 in H3. rewrite <- H2 in H3.
    left. assumption.
    intro H5. rewrite H1 in H3. simpl in H3. rewrite H5 in H3. simpl in H3. rewrite <- H2 in H3.
    right. assumption.
  Qed.

  Lemma MapCard_Put_lb :
   forall (m:Map A) (a:ad) (y:A), MapCard A (MapPut A m a y) >= MapCard A m.
  Proof.
    unfold ge in |- *. intros.
    elim
     (MapCard_Put_sum m (MapPut A m a y) a y (MapCard A m)
        (MapCard A (MapPut A m a y)) (refl_equal _) (
        refl_equal _) (refl_equal _)).
    intro H. rewrite H. apply le_n.
    intro H. rewrite H. apply le_n_Sn.
  Qed.

  Lemma MapCard_Put_ub :
   forall (m:Map A) (a:ad) (y:A),
     MapCard A (MapPut A m a y) <= S (MapCard A m).
  Proof.
    intros.
    elim
     (MapCard_Put_sum m (MapPut A m a y) a y (MapCard A m)
        (MapCard A (MapPut A m a y)) (refl_equal _) (
        refl_equal _) (refl_equal _)).
    intro H. rewrite H. apply le_n_Sn.
    intro H. rewrite H. apply le_n.
  Qed.

  Lemma MapCard_Put_1 :
   forall (m:Map A) (a:ad) (y:A),
     MapCard A (MapPut A m a y) = MapCard A m ->
     {y : A | MapGet A m a = Some y}.
  Proof.
    simple induction m. intros. discriminate H.
    intros a y a0 y0 H. simpl in H. elim (Ndiscr (Nxor a a0)). intro H0. elim H0.
    intros p H1. rewrite H1 in H. rewrite (MapCard_Put1_equals_2 p a a0 y y0) in H.
    discriminate H.
    intro H0. rewrite H0 in H. rewrite (Nxor_eq _ _ H0). split with y. apply M1_semantics_1.
    intros. rewrite (MapPut_semantics_3_1 A m0 m1 a y) in H1. elim (sumbool_of_bool (Nbit0 a)).
    intro H2. rewrite H2 in H1. simpl in H1. elim (H0 (Ndiv2 a) y ((fun n m p:nat => plus_reg_l m p n) _ _ _ H1)).
    intros y0 H3. split with y0. rewrite <- H3. exact (MapGet_M2_bit_0_1 A a H2 m0 m1).
    intro H2. rewrite H2 in H1. simpl in H1.
    rewrite
     (plus_comm (MapCard A (MapPut A m0 (Ndiv2 a) y)) (MapCard A m1))
      in H1.
    rewrite (plus_comm (MapCard A m0) (MapCard A m1)) in H1.
    elim (H (Ndiv2 a) y ((fun n m p:nat => plus_reg_l m p n) _ _ _ H1)). intros y0 H3. split with y0.
    rewrite <- H3. exact (MapGet_M2_bit_0_0 A a H2 m0 m1).
  Qed.

  Lemma MapCard_Put_2 :
   forall (m:Map A) (a:ad) (y:A),
     MapCard A (MapPut A m a y) = S (MapCard A m) -> MapGet A m a = None.
  Proof.
    simple induction m. trivial.
    intros. simpl in H. elim (sumbool_of_bool (Neqb a a1)). intro H0.
    rewrite (Neqb_complete _ _ H0) in H. rewrite (Nxor_nilpotent a1) in H. discriminate H.
    intro H0. exact (M1_semantics_2 A a a1 a0 H0).
    intros. elim (sumbool_of_bool (Nbit0 a)). intro H2.
    rewrite (MapGet_M2_bit_0_1 A a H2 m0 m1). apply (H0 (Ndiv2 a) y).
    apply (fun n m p:nat => plus_reg_l m p n) with (n := MapCard A m0).
    rewrite <- (plus_Snm_nSm (MapCard A m0) (MapCard A m1)). simpl in H1. simpl in |- *. rewrite <- H1.
    clear H1.
    induction a. discriminate H2.
    induction p. reflexivity.
    discriminate H2.
    reflexivity.
    intro H2. rewrite (MapGet_M2_bit_0_0 A a H2 m0 m1). apply (H (Ndiv2 a) y).
    cut
     (MapCard A (MapPut A m0 (Ndiv2 a) y) + MapCard A m1 =
      S (MapCard A m0) + MapCard A m1).
    intro. rewrite (plus_comm (MapCard A (MapPut A m0 (Ndiv2 a) y)) (MapCard A m1))
   in H3.
    rewrite (plus_comm (S (MapCard A m0)) (MapCard A m1)) in H3. exact ((fun n m p:nat => plus_reg_l m p n) _ _ _ H3).
    simpl in |- *. simpl in H1. rewrite <- H1. induction a. trivial.
    induction p. discriminate H2.
    reflexivity.
    discriminate H2.
  Qed.

  Lemma MapCard_Put_1_conv :
   forall (m:Map A) (a:ad) (y y':A),
     MapGet A m a = Some y -> MapCard A (MapPut A m a y') = MapCard A m.
  Proof.
    intros.
    elim
     (MapCard_Put_sum m (MapPut A m a y') a y' (MapCard A m)
        (MapCard A (MapPut A m a y')) (refl_equal _) (
        refl_equal _) (refl_equal _)).
    trivial.
    intro H0. rewrite (MapCard_Put_2 m a y' H0) in H. discriminate H.
  Qed.

  Lemma MapCard_Put_2_conv :
   forall (m:Map A) (a:ad) (y:A),
     MapGet A m a = None -> MapCard A (MapPut A m a y) = S (MapCard A m).
  Proof.
    intros.
    elim
     (MapCard_Put_sum m (MapPut A m a y) a y (MapCard A m)
        (MapCard A (MapPut A m a y)) (refl_equal _) (
        refl_equal _) (refl_equal _)).
    intro H0. elim (MapCard_Put_1 m a y H0). intros y' H1. rewrite H1 in H. discriminate H.
    trivial.
  Qed.

  Lemma MapCard_ext :
   forall m m':Map A,
     eqm A (MapGet A m) (MapGet A m') -> MapCard A m = MapCard A m'.
  Proof.
    unfold eqm in |- *. intros. rewrite (MapCard_as_length m). rewrite (MapCard_as_length m').
    rewrite (alist_canonical A (alist_of_Map A m) (alist_of_Map A m')). reflexivity.
    unfold eqm in |- *. intro. rewrite (Map_of_alist_semantics A (alist_of_Map A m) a).
    rewrite (Map_of_alist_semantics A (alist_of_Map A m') a). rewrite (Map_of_alist_of_Map A m' a).
    rewrite (Map_of_alist_of_Map A m a). exact (H a).
    apply alist_of_Map_sorts2.
    apply alist_of_Map_sorts2.
  Qed.

  Lemma MapCard_Dom : forall m:Map A, MapCard A m = MapCard unit (MapDom A m).
  Proof.
    simple induction m; trivial. intros. simpl in |- *. rewrite H. rewrite H0. reflexivity.
  Qed.

  Lemma MapCard_Dom_Put_behind :
   forall (m:Map A) (a:ad) (y:A),
     MapDom A (MapPut_behind A m a y) = MapDom A (MapPut A m a y).
  Proof.
    simple induction m. trivial.
    intros a y a0 y0. simpl in |- *. elim (Ndiscr (Nxor a a0)). intro H. elim H.
    intros p H0. rewrite H0. reflexivity.
    intro H. rewrite H. rewrite (Nxor_eq _ _ H). reflexivity.
    intros. simpl in |- *. elim (Ndiscr a). intro H1. elim H1. intros p H2. rewrite H2. case p.
    intro p0. simpl in |- *. rewrite H0. reflexivity.
    intro p0. simpl in |- *. rewrite H. reflexivity.
    simpl in |- *. rewrite H0. reflexivity.
    intro H1. rewrite H1. simpl in |- *. rewrite H. reflexivity.
  Qed.

  Lemma MapCard_Put_behind_Put :
   forall (m:Map A) (a:ad) (y:A),
     MapCard A (MapPut_behind A m a y) = MapCard A (MapPut A m a y).
  Proof.
    intros. rewrite MapCard_Dom. rewrite MapCard_Dom. rewrite MapCard_Dom_Put_behind.
    reflexivity.
  Qed.

  Lemma MapCard_Put_behind_sum :
   forall (m m':Map A) (a:ad) (y:A) (n n':nat),
     m' = MapPut_behind A m a y ->
     n = MapCard A m -> n' = MapCard A m' -> {n' = n} + {n' = S n}.
  Proof.
    intros. apply (MapCard_Put_sum m (MapPut A m a y) a y n n'); trivial.
    rewrite <- MapCard_Put_behind_Put. rewrite <- H. assumption.
  Qed.

  Lemma MapCard_makeM2 :
   forall m m':Map A, MapCard A (makeM2 A m m') = MapCard A m + MapCard A m'.
  Proof.
    intros. rewrite (MapCard_ext _ _ (makeM2_M2 A m m')). reflexivity.
  Qed.
 
  Lemma MapCard_Remove_sum :
   forall (m m':Map A) (a:ad) (n n':nat),
     m' = MapRemove A m a ->
     n = MapCard A m -> n' = MapCard A m' -> {n = n'} + {n = S n'}.
  Proof.
    simple induction m. simpl in |- *. intros. rewrite H in H1. simpl in H1. left. rewrite H1. assumption.
    simpl in |- *. intros. elim (sumbool_of_bool (Neqb a a1)). intro H2. rewrite H2 in H.
    rewrite H in H1. simpl in H1. right. rewrite H1. assumption.
    intro H2. rewrite H2 in H. rewrite H in H1. simpl in H1. left. rewrite H1. assumption.
    intros. simpl in H1. simpl in H2. elim (sumbool_of_bool (Nbit0 a)). intro H4.
    rewrite H4 in H1. rewrite H1 in H3.
    rewrite (MapCard_makeM2 m0 (MapRemove A m1 (Ndiv2 a))) in H3.
    elim
     (H0 (MapRemove A m1 (Ndiv2 a)) (Ndiv2 a) (
        MapCard A m1) (MapCard A (MapRemove A m1 (Ndiv2 a)))
        (refl_equal _) (refl_equal _) (refl_equal _)).
    intro H5. rewrite H5 in H2. left. rewrite H3. exact H2.
    intro H5. rewrite H5 in H2.
    rewrite <-
     (plus_Snm_nSm (MapCard A m0) (MapCard A (MapRemove A m1 (Ndiv2 a))))
      in H2.
    right. rewrite H3. exact H2.
    intro H4. rewrite H4 in H1. rewrite H1 in H3.
    rewrite (MapCard_makeM2 (MapRemove A m0 (Ndiv2 a)) m1) in H3.
    elim
     (H (MapRemove A m0 (Ndiv2 a)) (Ndiv2 a) (
        MapCard A m0) (MapCard A (MapRemove A m0 (Ndiv2 a)))
        (refl_equal _) (refl_equal _) (refl_equal _)).
    intro H5. rewrite H5 in H2. left. rewrite H3. exact H2.
    intro H5. rewrite H5 in H2. right. rewrite H3. exact H2.
  Qed.

  Lemma MapCard_Remove_ub :
   forall (m:Map A) (a:ad), MapCard A (MapRemove A m a) <= MapCard A m.
  Proof.
    intros.
    elim
     (MapCard_Remove_sum m (MapRemove A m a) a (MapCard A m)
        (MapCard A (MapRemove A m a)) (refl_equal _) (
        refl_equal _) (refl_equal _)).
    intro H. rewrite H. apply le_n.
    intro H. rewrite H. apply le_n_Sn.
  Qed.

  Lemma MapCard_Remove_lb :
   forall (m:Map A) (a:ad), S (MapCard A (MapRemove A m a)) >= MapCard A m.
  Proof.
    unfold ge in |- *. intros.
    elim
     (MapCard_Remove_sum m (MapRemove A m a) a (MapCard A m)
        (MapCard A (MapRemove A m a)) (refl_equal _) (
        refl_equal _) (refl_equal _)).
    intro H. rewrite H. apply le_n_Sn.
    intro H. rewrite H. apply le_n.
  Qed.

  Lemma MapCard_Remove_1 :
   forall (m:Map A) (a:ad),
     MapCard A (MapRemove A m a) = MapCard A m -> MapGet A m a = None.
  Proof.
    simple induction m. trivial.
    simpl in |- *. intros a y a0 H. elim (sumbool_of_bool (Neqb a a0)). intro H0.
    rewrite H0 in H. discriminate H.
    intro H0. rewrite H0. reflexivity.
    intros. simpl in H1. elim (sumbool_of_bool (Nbit0 a)). intro H2. rewrite H2 in H1.
    rewrite (MapCard_makeM2 m0 (MapRemove A m1 (Ndiv2 a))) in H1.
    rewrite (MapGet_M2_bit_0_1 A a H2 m0 m1). apply H0. exact ((fun n m p:nat => plus_reg_l m p n) _ _ _ H1).
    intro H2. rewrite H2 in H1.
    rewrite (MapCard_makeM2 (MapRemove A m0 (Ndiv2 a)) m1) in H1.
    rewrite (MapGet_M2_bit_0_0 A a H2 m0 m1). apply H.
    rewrite
     (plus_comm (MapCard A (MapRemove A m0 (Ndiv2 a))) (MapCard A m1))
      in H1.
    rewrite (plus_comm (MapCard A m0) (MapCard A m1)) in H1. exact ((fun n m p:nat => plus_reg_l m p n) _ _ _ H1).
  Qed.

  Lemma MapCard_Remove_2 :
   forall (m:Map A) (a:ad),
     S (MapCard A (MapRemove A m a)) = MapCard A m ->
     {y : A | MapGet A m a = Some y}.
  Proof.
    simple induction m. intros. discriminate H.
    intros a y a0 H. simpl in H. elim (sumbool_of_bool (Neqb a a0)). intro H0.
    rewrite (Neqb_complete _ _ H0). split with y. exact (M1_semantics_1 A a0 y).
    intro H0. rewrite H0 in H. discriminate H.
    intros. simpl in H1. elim (sumbool_of_bool (Nbit0 a)). intro H2. rewrite H2 in H1.
    rewrite (MapCard_makeM2 m0 (MapRemove A m1 (Ndiv2 a))) in H1.
    rewrite (MapGet_M2_bit_0_1 A a H2 m0 m1). apply H0.
    change
      (S (MapCard A m0) + MapCard A (MapRemove A m1 (Ndiv2 a)) =
       MapCard A m0 + MapCard A m1) in H1.
    rewrite
     (plus_Snm_nSm (MapCard A m0) (MapCard A (MapRemove A m1 (Ndiv2 a))))
      in H1.
    exact ((fun n m p:nat => plus_reg_l m p n) _ _ _ H1).
    intro H2. rewrite H2 in H1. rewrite (MapGet_M2_bit_0_0 A a H2 m0 m1). apply H.
    rewrite (MapCard_makeM2 (MapRemove A m0 (Ndiv2 a)) m1) in H1.
    change
      (S (MapCard A (MapRemove A m0 (Ndiv2 a))) + MapCard A m1 =
       MapCard A m0 + MapCard A m1) in H1.
    rewrite
     (plus_comm (S (MapCard A (MapRemove A m0 (Ndiv2 a)))) (MapCard A m1))
      in H1.
    rewrite (plus_comm (MapCard A m0) (MapCard A m1)) in H1. exact ((fun n m p:nat => plus_reg_l m p n) _ _ _ H1).
  Qed.

  Lemma MapCard_Remove_1_conv :
   forall (m:Map A) (a:ad),
     MapGet A m a = None -> MapCard A (MapRemove A m a) = MapCard A m.
  Proof.
    intros.
    elim
     (MapCard_Remove_sum m (MapRemove A m a) a (MapCard A m)
        (MapCard A (MapRemove A m a)) (refl_equal _) (
        refl_equal _) (refl_equal _)).
    intro H0. rewrite H0. reflexivity.
    intro H0. elim (MapCard_Remove_2 m a (sym_eq H0)). intros y H1. rewrite H1 in H.
    discriminate H.
  Qed.

  Lemma MapCard_Remove_2_conv :
   forall (m:Map A) (a:ad) (y:A),
     MapGet A m a = Some y -> S (MapCard A (MapRemove A m a)) = MapCard A m.
  Proof.
    intros.
    elim
     (MapCard_Remove_sum m (MapRemove A m a) a (MapCard A m)
        (MapCard A (MapRemove A m a)) (refl_equal _) (
        refl_equal _) (refl_equal _)).
    intro H0. rewrite (MapCard_Remove_1 m a (sym_eq H0)) in H. discriminate H.
    intro H0. rewrite H0. reflexivity.
  Qed.

  Lemma MapMerge_Restr_Card :
   forall m m':Map A,
     MapCard A m + MapCard A m' =
     MapCard A (MapMerge A m m') + MapCard A (MapDomRestrTo A A m m').
  Proof.
    simple induction m. simpl in |- *. intro. apply plus_n_O.
    simpl in |- *. intros a y m'. elim (option_sum A (MapGet A m' a)). intro H. elim H. intros y0 H0.
    rewrite H0. rewrite MapCard_Put_behind_Put. rewrite (MapCard_Put_1_conv m' a y0 y H0).
    simpl in |- *. rewrite <- plus_Snm_nSm. apply plus_n_O.
    intro H. rewrite H. rewrite MapCard_Put_behind_Put. rewrite (MapCard_Put_2_conv m' a y H).
    apply plus_n_O.
    intros.
    change
      (MapCard A m0 + MapCard A m1 + MapCard A m' =
       MapCard A (MapMerge A (M2 A m0 m1) m') +
       MapCard A (MapDomRestrTo A A (M2 A m0 m1) m')) 
     in |- *.
    elim m'. reflexivity.
    intros a y. unfold MapMerge in |- *. unfold MapDomRestrTo in |- *.
    elim (option_sum A (MapGet A (M2 A m0 m1) a)). intro H1. elim H1. intros y0 H2. rewrite H2.
    rewrite (MapCard_Put_1_conv (M2 A m0 m1) a y0 y H2). reflexivity.
    intro H1. rewrite H1. rewrite (MapCard_Put_2_conv (M2 A m0 m1) a y H1). simpl in |- *.
    rewrite <- (plus_Snm_nSm (MapCard A m0 + MapCard A m1) 0). reflexivity.
    intros. simpl in |- *.
    rewrite
     (plus_permute_2_in_4 (MapCard A m0) (MapCard A m1) (
        MapCard A m2) (MapCard A m3)).
    rewrite (H m2). rewrite (H0 m3).
    rewrite
     (MapCard_makeM2 (MapDomRestrTo A A m0 m2) (MapDomRestrTo A A m1 m3))
     .
    apply plus_permute_2_in_4.
  Qed.

  Lemma MapMerge_disjoint_Card :
   forall m m':Map A,
     MapDisjoint A A m m' ->
     MapCard A (MapMerge A m m') = MapCard A m + MapCard A m'.
  Proof.
    intros. rewrite (MapMerge_Restr_Card m m').
    rewrite (MapCard_ext _ _ (MapDisjoint_imp_2 _ _ _ _ H)). apply plus_n_O.
  Qed.

  Lemma MapSplit_Card :
   forall (m:Map A) (m':Map B),
     MapCard A m =
     MapCard A (MapDomRestrTo A B m m') + MapCard A (MapDomRestrBy A B m m').
  Proof.
    intros. rewrite (MapCard_ext _ _ (MapDom_Split_1 A B m m')). apply MapMerge_disjoint_Card.
    apply MapDisjoint_2_imp. unfold MapDisjoint_2 in |- *. apply MapDom_Split_3.
  Qed.

  Lemma MapMerge_Card_ub :
   forall m m':Map A,
     MapCard A (MapMerge A m m') <= MapCard A m + MapCard A m'.
  Proof.
    intros. rewrite MapMerge_Restr_Card. apply le_plus_l.
  Qed.

  Lemma MapDomRestrTo_Card_ub_l :
   forall (m:Map A) (m':Map B),
     MapCard A (MapDomRestrTo A B m m') <= MapCard A m.
  Proof.
    intros. rewrite (MapSplit_Card m m'). apply le_plus_l.
  Qed.

  Lemma MapDomRestrBy_Card_ub_l :
   forall (m:Map A) (m':Map B),
     MapCard A (MapDomRestrBy A B m m') <= MapCard A m.
  Proof.
    intros. rewrite (MapSplit_Card m m'). apply le_plus_r.
  Qed.

  Lemma MapMerge_Card_disjoint :
   forall m m':Map A,
     MapCard A (MapMerge A m m') = MapCard A m + MapCard A m' ->
     MapDisjoint A A m m'.
  Proof.
    simple induction m. intros. apply Map_M0_disjoint.
    simpl in |- *. intros. rewrite (MapCard_Put_behind_Put m' a a0) in H. unfold MapDisjoint, in_dom in |- *.
    simpl in |- *. intros. elim (sumbool_of_bool (Neqb a a1)). intro H2.
    rewrite (Neqb_complete _ _ H2) in H. rewrite (MapCard_Put_2 m' a1 a0 H) in H1.
    discriminate H1.
    intro H2. rewrite H2 in H0. discriminate H0.
    simple induction m'. intros. apply Map_disjoint_M0.
    intros a y H1. rewrite <- (MapCard_ext _ _ (MapPut_as_Merge A (M2 A m0 m1) a y)) in H1.
    unfold MapCard at 3 in H1. rewrite <- (plus_Snm_nSm (MapCard A (M2 A m0 m1)) 0) in H1.
    rewrite <- (plus_n_O (S (MapCard A (M2 A m0 m1)))) in H1. unfold MapDisjoint, in_dom in |- *.
    unfold MapGet at 2 in |- *. intros. elim (sumbool_of_bool (Neqb a a0)). intro H4.
    rewrite <- (Neqb_complete _ _ H4) in H2. rewrite (MapCard_Put_2 _ _ _ H1) in H2.
    discriminate H2.
    intro H4. rewrite H4 in H3. discriminate H3.
    intros. unfold MapDisjoint in |- *. intros. elim (sumbool_of_bool (Nbit0 a)). intro H6.
    unfold MapDisjoint in H0. apply H0 with (m' := m3) (a := Ndiv2 a). apply le_antisym.
    apply MapMerge_Card_ub.
    apply (fun p n m:nat => plus_le_reg_l n m p) with
     (p := MapCard A m0 + MapCard A m2).
    rewrite
     (plus_permute_2_in_4 (MapCard A m0) (MapCard A m2) (
        MapCard A m1) (MapCard A m3)).
    change
      (MapCard A (M2 A (MapMerge A m0 m2) (MapMerge A m1 m3)) =
       MapCard A m0 + MapCard A m1 + (MapCard A m2 + MapCard A m3)) 
     in H3.
    rewrite <- H3. simpl in |- *. apply plus_le_compat_r. apply MapMerge_Card_ub.
    elim (in_dom_some _ _ _ H4). intros y H7. rewrite (MapGet_M2_bit_0_1 _ a H6 m0 m1) in H7.
    unfold in_dom in |- *. rewrite H7. reflexivity.
    elim (in_dom_some _ _ _ H5). intros y H7. rewrite (MapGet_M2_bit_0_1 _ a H6 m2 m3) in H7.
    unfold in_dom in |- *. rewrite H7. reflexivity.
    intro H6. unfold MapDisjoint in H. apply H with (m' := m2) (a := Ndiv2 a). apply le_antisym.
    apply MapMerge_Card_ub.
    apply (fun p n m:nat => plus_le_reg_l n m p) with
     (p := MapCard A m1 + MapCard A m3).
    rewrite
     (plus_comm (MapCard A m1 + MapCard A m3) (MapCard A m0 + MapCard A m2))
     .
    rewrite
     (plus_permute_2_in_4 (MapCard A m0) (MapCard A m2) (
        MapCard A m1) (MapCard A m3)).
    rewrite
     (plus_comm (MapCard A m1 + MapCard A m3) (MapCard A (MapMerge A m0 m2)))
     .
    change
      (MapCard A (MapMerge A m0 m2) + MapCard A (MapMerge A m1 m3) =
       MapCard A m0 + MapCard A m1 + (MapCard A m2 + MapCard A m3)) 
     in H3.
    rewrite <- H3. apply plus_le_compat_l. apply MapMerge_Card_ub.
    elim (in_dom_some _ _ _ H4). intros y H7. rewrite (MapGet_M2_bit_0_0 _ a H6 m0 m1) in H7.
    unfold in_dom in |- *. rewrite H7. reflexivity.
    elim (in_dom_some _ _ _ H5). intros y H7. rewrite (MapGet_M2_bit_0_0 _ a H6 m2 m3) in H7.
    unfold in_dom in |- *. rewrite H7. reflexivity.
  Qed.

  Lemma MapCard_is_Sn :
   forall (m:Map A) (n:nat),
     MapCard _ m = S n -> {a : ad | in_dom _ a m = true}.
  Proof.
    simple induction m. intros. discriminate H.
    intros a y n H. split with a. unfold in_dom in |- *. rewrite (M1_semantics_1 _ a y). reflexivity.
    intros. simpl in H1. elim (O_or_S (MapCard _ m0)). intro H2. elim H2. intros m2 H3.
    elim (H _ (sym_eq H3)). intros a H4. split with (Ndouble a). unfold in_dom in |- *.
    rewrite (MapGet_M2_bit_0_0 A (Ndouble a) (Ndouble_bit0 a) m0 m1).
    rewrite (Ndouble_div2 a). elim (in_dom_some _ _ _ H4). intros y H5. rewrite H5. reflexivity.
    intro H2. rewrite <- H2 in H1. simpl in H1. elim (H0 _ H1). intros a H3.
    split with (Ndouble_plus_one a). unfold in_dom in |- *.
    rewrite
     (MapGet_M2_bit_0_1 A (Ndouble_plus_one a) (Ndouble_plus_one_bit0 a)
        m0 m1).
    rewrite (Ndouble_plus_one_div2 a). elim (in_dom_some _ _ _ H3). intros y H4. rewrite H4.
    reflexivity.
  Qed.

End MapCard.

Section MapCard2.

  Variables A B : Set.

  Lemma MapSubset_card_eq_1 :
   forall (n:nat) (m:Map A) (m':Map B),
     MapSubset _ _ m m' ->
     MapCard _ m = n -> MapCard _ m' = n -> MapSubset _ _ m' m.
  Proof.
    simple induction n. intros. unfold MapSubset, in_dom in |- *. intro. rewrite (MapCard_is_O _ m H0 a).
    rewrite (MapCard_is_O _ m' H1 a). intro H2. discriminate H2.
    intros. elim (MapCard_is_Sn A m n0 H1). intros a H3. elim (in_dom_some _ _ _ H3).
    intros y H4. elim (in_dom_some _ _ _ (H0 _ H3)). intros y' H6.
    cut (eqmap _ (MapPut _ (MapRemove _ m a) a y) m). intro.
    cut (eqmap _ (MapPut _ (MapRemove _ m' a) a y') m'). intro.
    apply MapSubset_ext with
     (m0 := MapPut _ (MapRemove _ m' a) a y')
     (m2 := MapPut _ (MapRemove _ m a) a y).
    assumption.
    assumption.
    apply MapSubset_Put_mono. apply H. apply MapSubset_Remove_mono. assumption.
    rewrite <- (MapCard_Remove_2_conv _ m a y H4) in H1. inversion_clear H1. reflexivity.
    rewrite <- (MapCard_Remove_2_conv _ m' a y' H6) in H2. inversion_clear H2. reflexivity.
    unfold eqmap, eqm in |- *. intro. rewrite (MapPut_semantics _ (MapRemove B m' a) a y' a0).
    elim (sumbool_of_bool (Neqb a a0)). intro H7. rewrite H7. rewrite <- (Neqb_complete _ _ H7).
    apply sym_eq. assumption.
    intro H7. rewrite H7. rewrite (MapRemove_semantics _ m' a a0). rewrite H7. reflexivity.
    unfold eqmap, eqm in |- *. intro. rewrite (MapPut_semantics _ (MapRemove A m a) a y a0).
    elim (sumbool_of_bool (Neqb a a0)). intro H7. rewrite H7. rewrite <- (Neqb_complete _ _ H7).
    apply sym_eq. assumption.
    intro H7. rewrite H7. rewrite (MapRemove_semantics A m a a0). rewrite H7. reflexivity.
  Qed.

  Lemma MapDomRestrTo_Card_ub_r :
   forall (m:Map A) (m':Map B),
     MapCard A (MapDomRestrTo A B m m') <= MapCard B m'.
  Proof.
    simple induction m. intro. simpl in |- *. apply le_O_n.
    intros a y m'. simpl in |- *. elim (option_sum B (MapGet B m' a)). intro H. elim H. intros y0 H0.
    rewrite H0. elim (MapCard_is_not_O B m' a y0 H0). intros n H1. rewrite H1. simpl in |- *.
    apply le_n_S. apply le_O_n.
    intro H. rewrite H. simpl in |- *. apply le_O_n.
    simple induction m'. simpl in |- *. apply le_O_n.

    intros a y. unfold MapDomRestrTo in |- *. case (MapGet A (M2 A m0 m1) a). simpl in |- *. 
    intro. simpl in |- *. apply le_n.
    apply le_O_n.
    intros. simpl in |- *. rewrite
  (MapCard_makeM2 A (MapDomRestrTo A B m0 m2) (MapDomRestrTo A B m1 m3))
  .
    apply plus_le_compat. apply H.
    apply H0.
  Qed.

End MapCard2.

Section MapCard3.

  Variables A B : Set.

  Lemma MapMerge_Card_lb_l :
   forall m m':Map A, MapCard A (MapMerge A m m') >= MapCard A m.
  Proof.
    unfold ge in |- *. intros. apply ((fun p n m:nat => plus_le_reg_l n m p) (MapCard A m')).
    rewrite (plus_comm (MapCard A m') (MapCard A m)).
    rewrite (plus_comm (MapCard A m') (MapCard A (MapMerge A m m'))).
    rewrite (MapMerge_Restr_Card A m m'). apply plus_le_compat_l. apply MapDomRestrTo_Card_ub_r.
  Qed.

  Lemma MapMerge_Card_lb_r :
   forall m m':Map A, MapCard A (MapMerge A m m') >= MapCard A m'.
  Proof.
    unfold ge in |- *. intros. apply ((fun p n m:nat => plus_le_reg_l n m p) (MapCard A m)). rewrite (MapMerge_Restr_Card A m m').
    rewrite
     (plus_comm (MapCard A (MapMerge A m m'))
        (MapCard A (MapDomRestrTo A A m m'))).
    apply plus_le_compat_r. apply MapDomRestrTo_Card_ub_l.
  Qed.

  Lemma MapDomRestrBy_Card_lb :
   forall (m:Map A) (m':Map B),
     MapCard B m' + MapCard A (MapDomRestrBy A B m m') >= MapCard A m.
  Proof.
    unfold ge in |- *. intros. rewrite (MapSplit_Card A B m m'). apply plus_le_compat_r.
    apply MapDomRestrTo_Card_ub_r.
  Qed.

  Lemma MapSubset_Card_le :
   forall (m:Map A) (m':Map B),
     MapSubset A B m m' -> MapCard A m <= MapCard B m'.
  Proof.
    intros. apply le_trans with (m := MapCard B m' + MapCard A (MapDomRestrBy A B m m')).
    exact (MapDomRestrBy_Card_lb m m').
    rewrite (MapCard_ext _ _ _ (MapSubset_imp_2 _ _ _ _ H)). simpl in |- *. rewrite <- plus_n_O.
    apply le_n.
  Qed.

  Lemma MapSubset_card_eq :
   forall (m:Map A) (m':Map B),
     MapSubset _ _ m m' ->
     MapCard _ m' <= MapCard _ m -> eqmap _ (MapDom _ m) (MapDom _ m').
  Proof.
    intros. apply MapSubset_antisym. assumption.
    cut (MapCard B m' = MapCard A m). intro. apply (MapSubset_card_eq_1 A B (MapCard A m)).
    assumption.
    reflexivity.
    assumption.
    apply le_antisym. assumption.
    apply MapSubset_Card_le. assumption.
  Qed.

End MapCard3.
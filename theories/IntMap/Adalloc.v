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
Require Import ZArith.
Require Import Arith.
Require Import Addr.
Require Import Adist.
Require Import Addec.
Require Import Map.
Require Import Fset.

Section AdAlloc.

  Variable A : Set.

  Definition nat_of_ad (a:ad) :=
    match a with
    | ad_z => 0
    | ad_x p => nat_of_P p
    end.

  Fixpoint nat_le (m:nat) : nat -> bool :=
    match m with
    | O => fun _:nat => true
    | S m' =>
        fun n:nat => match n with
                     | O => false
                     | S n' => nat_le m' n'
                     end
    end.

  Lemma nat_le_correct : forall m n:nat, m <= n -> nat_le m n = true.
  Proof.
    induction m as [| m IHm]. trivial.
    destruct n. intro H. elim (le_Sn_O _ H).
    intros. simpl in |- *. apply IHm. apply le_S_n. assumption.
  Qed.

  Lemma nat_le_complete : forall m n:nat, nat_le m n = true -> m <= n.
  Proof.
    induction m. trivial with arith.
    destruct n. intro H. discriminate H.
    auto with arith.
  Qed.

  Lemma nat_le_correct_conv : forall m n:nat, m < n -> nat_le n m = false.
  Proof.
    intros. elim (sumbool_of_bool (nat_le n m)). intro H0.
    elim (lt_irrefl _ (lt_le_trans _ _ _ H (nat_le_complete _ _ H0))).
    trivial.
  Qed.

  Lemma nat_le_complete_conv : forall m n:nat, nat_le n m = false -> m < n.
  Proof.
    intros. elim (le_or_lt n m). intro. conditional trivial rewrite nat_le_correct in H. discriminate H.
    trivial.
  Qed.

  Definition ad_of_nat (n:nat) :=
    match n with
    | O => ad_z
    | S n' => ad_x (P_of_succ_nat n')
    end.

  Lemma ad_of_nat_of_ad : forall a:ad, ad_of_nat (nat_of_ad a) = a.
  Proof.
    destruct a as [| p]. reflexivity.
    simpl in |- *. elim (ZL4 p). intros n H. rewrite H. simpl in |- *. rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ in H.
    rewrite nat_of_P_inj with (1 := H). reflexivity.
  Qed.

  Lemma nat_of_ad_of_nat : forall n:nat, nat_of_ad (ad_of_nat n) = n.
  Proof.
    induction n. trivial.
    intros. simpl in |- *. apply nat_of_P_o_P_of_succ_nat_eq_succ.
  Qed.

  Definition ad_le (a b:ad) := nat_le (nat_of_ad a) (nat_of_ad b).

  Lemma ad_le_refl : forall a:ad, ad_le a a = true.
  Proof.
    intro. unfold ad_le in |- *. apply nat_le_correct. apply le_n.
  Qed.

  Lemma ad_le_antisym :
   forall a b:ad, ad_le a b = true -> ad_le b a = true -> a = b.
  Proof.
    unfold ad_le in |- *. intros. rewrite <- (ad_of_nat_of_ad a). rewrite <- (ad_of_nat_of_ad b).
    rewrite (le_antisym _ _ (nat_le_complete _ _ H) (nat_le_complete _ _ H0)). reflexivity.
  Qed.

  Lemma ad_le_trans :
   forall a b c:ad, ad_le a b = true -> ad_le b c = true -> ad_le a c = true.
  Proof.
    unfold ad_le in |- *. intros. apply nat_le_correct. apply le_trans with (m := nat_of_ad b).
    apply nat_le_complete. assumption.
    apply nat_le_complete. assumption.
  Qed.

  Lemma ad_le_lt_trans :
   forall a b c:ad,
     ad_le a b = true -> ad_le c b = false -> ad_le c a = false.
  Proof.
    unfold ad_le in |- *. intros. apply nat_le_correct_conv. apply le_lt_trans with (m := nat_of_ad b).
    apply nat_le_complete. assumption.
    apply nat_le_complete_conv. assumption.
  Qed.

  Lemma ad_lt_le_trans :
   forall a b c:ad,
     ad_le b a = false -> ad_le b c = true -> ad_le c a = false.
  Proof.
    unfold ad_le in |- *. intros. apply nat_le_correct_conv. apply lt_le_trans with (m := nat_of_ad b).
    apply nat_le_complete_conv. assumption.
    apply nat_le_complete. assumption.
  Qed.

  Lemma ad_lt_trans :
   forall a b c:ad,
     ad_le b a = false -> ad_le c b = false -> ad_le c a = false.
  Proof.
    unfold ad_le in |- *. intros. apply nat_le_correct_conv. apply lt_trans with (m := nat_of_ad b).
    apply nat_le_complete_conv. assumption.
    apply nat_le_complete_conv. assumption.
  Qed.

  Lemma ad_lt_le_weak : forall a b:ad, ad_le b a = false -> ad_le a b = true.
  Proof.
    unfold ad_le in |- *. intros. apply nat_le_correct. apply lt_le_weak.
    apply nat_le_complete_conv. assumption.
  Qed.

  Definition ad_min (a b:ad) := if ad_le a b then a else b.

  Lemma ad_min_choice : forall a b:ad, {ad_min a b = a} + {ad_min a b = b}.
  Proof.
    unfold ad_min in |- *. intros. elim (sumbool_of_bool (ad_le a b)). intro H. left. rewrite H.
    reflexivity.
    intro H. right. rewrite H. reflexivity.
  Qed.

  Lemma ad_min_le_1 : forall a b:ad, ad_le (ad_min a b) a = true.
  Proof.
    unfold ad_min in |- *. intros. elim (sumbool_of_bool (ad_le a b)). intro H. rewrite H.
    apply ad_le_refl.
    intro H. rewrite H. apply ad_lt_le_weak. assumption.
  Qed.

  Lemma ad_min_le_2 : forall a b:ad, ad_le (ad_min a b) b = true.
  Proof.
    unfold ad_min in |- *. intros. elim (sumbool_of_bool (ad_le a b)). intro H. rewrite H. assumption.
    intro H. rewrite H. apply ad_le_refl.
  Qed.

  Lemma ad_min_le_3 :
   forall a b c:ad, ad_le a (ad_min b c) = true -> ad_le a b = true.
  Proof.
    unfold ad_min in |- *. intros. elim (sumbool_of_bool (ad_le b c)). intro H0. rewrite H0 in H.
    assumption.
    intro H0. rewrite H0 in H. apply ad_lt_le_weak. apply ad_le_lt_trans with (b := c); assumption.
  Qed.

  Lemma ad_min_le_4 :
   forall a b c:ad, ad_le a (ad_min b c) = true -> ad_le a c = true.
  Proof.
    unfold ad_min in |- *. intros. elim (sumbool_of_bool (ad_le b c)). intro H0. rewrite H0 in H.
    apply ad_le_trans with (b := b); assumption.
    intro H0. rewrite H0 in H. assumption.
  Qed.

  Lemma ad_min_le_5 :
   forall a b c:ad,
     ad_le a b = true -> ad_le a c = true -> ad_le a (ad_min b c) = true.
  Proof.
    intros. elim (ad_min_choice b c). intro H1. rewrite H1. assumption.
    intro H1. rewrite H1. assumption.
  Qed.

  Lemma ad_min_lt_3 :
   forall a b c:ad, ad_le (ad_min b c) a = false -> ad_le b a = false.
  Proof.
    unfold ad_min in |- *. intros. elim (sumbool_of_bool (ad_le b c)). intro H0. rewrite H0 in H.
    assumption.
    intro H0. rewrite H0 in H. apply ad_lt_trans with (b := c); assumption.
  Qed.

  Lemma ad_min_lt_4 :
   forall a b c:ad, ad_le (ad_min b c) a = false -> ad_le c a = false.
  Proof.
    unfold ad_min in |- *. intros. elim (sumbool_of_bool (ad_le b c)). intro H0. rewrite H0 in H.
    apply ad_lt_le_trans with (b := b); assumption.
    intro H0. rewrite H0 in H. assumption.
  Qed.

  (** Allocator: returns an address not in the domain of [m].
  This allocator is optimal in that it returns the lowest possible address,
  in the usual ordering on integers. It is not the most efficient, however. *)
  Fixpoint ad_alloc_opt (m:Map A) : ad :=
    match m with
    | M0 => ad_z
    | M1 a _ => if ad_eq a ad_z then ad_x 1 else ad_z
    | M2 m1 m2 =>
        ad_min (ad_double (ad_alloc_opt m1))
          (ad_double_plus_un (ad_alloc_opt m2))
    end.

  Lemma ad_alloc_opt_allocates_1 :
   forall m:Map A, MapGet A m (ad_alloc_opt m) = NONE A.
  Proof.
    induction m as [| a| m0 H m1 H0]. reflexivity.
    simpl in |- *. elim (sumbool_of_bool (ad_eq a ad_z)). intro H. rewrite H.
    rewrite (ad_eq_complete _ _ H). reflexivity.
    intro H. rewrite H. rewrite H. reflexivity.
    intros. change
   (ad_alloc_opt (M2 A m0 m1)) with (ad_min (ad_double (ad_alloc_opt m0))
                                       (ad_double_plus_un (ad_alloc_opt m1)))
  in |- *.
    elim
     (ad_min_choice (ad_double (ad_alloc_opt m0))
        (ad_double_plus_un (ad_alloc_opt m1))).
    intro H1. rewrite H1. rewrite MapGet_M2_bit_0_0. rewrite ad_double_div_2. assumption.
    apply ad_double_bit_0.
    intro H1. rewrite H1. rewrite MapGet_M2_bit_0_1. rewrite ad_double_plus_un_div_2. assumption.
    apply ad_double_plus_un_bit_0.
  Qed.

  Lemma ad_alloc_opt_allocates :
   forall m:Map A, in_dom A (ad_alloc_opt m) m = false.
  Proof.
    unfold in_dom in |- *. intro. rewrite (ad_alloc_opt_allocates_1 m). reflexivity.
  Qed.

  (** Moreover, this is optimal: all addresses below [(ad_alloc_opt m)]
      are in [dom m]: *)

  Lemma nat_of_ad_double :
   forall a:ad, nat_of_ad (ad_double a) = 2 * nat_of_ad a.
  Proof.
    destruct a as [| p]. trivial.
    exact (nat_of_P_xO p).
  Qed.

  Lemma nat_of_ad_double_plus_un :
   forall a:ad, nat_of_ad (ad_double_plus_un a) = S (2 * nat_of_ad a).
  Proof.
    destruct a as [| p]. trivial.
    exact (nat_of_P_xI p).
  Qed.

  Lemma ad_le_double_mono :
   forall a b:ad,
     ad_le a b = true -> ad_le (ad_double a) (ad_double b) = true.
  Proof.
    unfold ad_le in |- *. intros. rewrite nat_of_ad_double. rewrite nat_of_ad_double. apply nat_le_correct.
    simpl in |- *. apply plus_le_compat. apply nat_le_complete. assumption.
    apply plus_le_compat. apply nat_le_complete. assumption.
    apply le_n.
  Qed.

  Lemma ad_le_double_plus_un_mono :
   forall a b:ad,
     ad_le a b = true ->
     ad_le (ad_double_plus_un a) (ad_double_plus_un b) = true.
  Proof.
    unfold ad_le in |- *. intros. rewrite nat_of_ad_double_plus_un. rewrite nat_of_ad_double_plus_un.
    apply nat_le_correct. apply le_n_S. simpl in |- *. apply plus_le_compat. apply nat_le_complete.
    assumption.
    apply plus_le_compat. apply nat_le_complete. assumption.
    apply le_n.
  Qed.

  Lemma ad_le_double_mono_conv :
   forall a b:ad,
     ad_le (ad_double a) (ad_double b) = true -> ad_le a b = true.
  Proof.
    unfold ad_le in |- *. intros a b. rewrite nat_of_ad_double. rewrite nat_of_ad_double. intro.
    apply nat_le_correct. apply (mult_S_le_reg_l 1). apply nat_le_complete. assumption.
  Qed.

  Lemma ad_le_double_plus_un_mono_conv :
   forall a b:ad,
     ad_le (ad_double_plus_un a) (ad_double_plus_un b) = true ->
     ad_le a b = true.
  Proof.
    unfold ad_le in |- *. intros a b. rewrite nat_of_ad_double_plus_un. rewrite nat_of_ad_double_plus_un.
    intro. apply nat_le_correct. apply (mult_S_le_reg_l 1). apply le_S_n. apply nat_le_complete.
    assumption.
  Qed.

  Lemma ad_lt_double_mono :
   forall a b:ad,
     ad_le a b = false -> ad_le (ad_double a) (ad_double b) = false.
  Proof.
    intros. elim (sumbool_of_bool (ad_le (ad_double a) (ad_double b))). intro H0.
    rewrite (ad_le_double_mono_conv _ _ H0) in H. discriminate H.
    trivial.
  Qed.

  Lemma ad_lt_double_plus_un_mono :
   forall a b:ad,
     ad_le a b = false ->
     ad_le (ad_double_plus_un a) (ad_double_plus_un b) = false.
  Proof.
    intros. elim (sumbool_of_bool (ad_le (ad_double_plus_un a) (ad_double_plus_un b))). intro H0.
    rewrite (ad_le_double_plus_un_mono_conv _ _ H0) in H. discriminate H.
    trivial.
  Qed.

  Lemma ad_lt_double_mono_conv :
   forall a b:ad,
     ad_le (ad_double a) (ad_double b) = false -> ad_le a b = false.
  Proof.
    intros. elim (sumbool_of_bool (ad_le a b)). intro H0. rewrite (ad_le_double_mono _ _ H0) in H.
    discriminate H.
    trivial.
  Qed.

  Lemma ad_lt_double_plus_un_mono_conv :
   forall a b:ad,
     ad_le (ad_double_plus_un a) (ad_double_plus_un b) = false ->
     ad_le a b = false.
  Proof.
    intros. elim (sumbool_of_bool (ad_le a b)). intro H0.
    rewrite (ad_le_double_plus_un_mono _ _ H0) in H. discriminate H.
    trivial.
  Qed.

  Lemma ad_alloc_opt_optimal_1 :
   forall (m:Map A) (a:ad),
     ad_le (ad_alloc_opt m) a = false -> {y : A | MapGet A m a = SOME A y}.
  Proof.
    induction m as [| a y| m0 H m1 H0]. simpl in |- *. unfold ad_le in |- *. simpl in |- *. intros. discriminate H.
    simpl in |- *. intros b H. elim (sumbool_of_bool (ad_eq a ad_z)). intro H0. rewrite H0 in H.
    unfold ad_le in H. cut (ad_z = b). intro. split with y. rewrite <- H1. rewrite H0. reflexivity.
    rewrite <- (ad_of_nat_of_ad b).
    rewrite <- (le_n_O_eq _ (le_S_n _ _ (nat_le_complete_conv _ _ H))). reflexivity.
    intro H0. rewrite H0 in H. discriminate H.
    intros. simpl in H1. elim (ad_double_or_double_plus_un a). intro H2. elim H2. intros a0 H3.
    rewrite H3 in H1. elim (H _ (ad_lt_double_mono_conv _ _ (ad_min_lt_3 _ _ _ H1))). intros y H4.
    split with y. rewrite H3. rewrite MapGet_M2_bit_0_0. rewrite ad_double_div_2. assumption.
    apply ad_double_bit_0.
    intro H2. elim H2. intros a0 H3. rewrite H3 in H1.
    elim (H0 _ (ad_lt_double_plus_un_mono_conv _ _ (ad_min_lt_4 _ _ _ H1))). intros y H4.
    split with y. rewrite H3. rewrite MapGet_M2_bit_0_1. rewrite ad_double_plus_un_div_2.
    assumption.
    apply ad_double_plus_un_bit_0.
  Qed.

  Lemma ad_alloc_opt_optimal :
   forall (m:Map A) (a:ad),
     ad_le (ad_alloc_opt m) a = false -> in_dom A a m = true.
  Proof.
    intros. unfold in_dom in |- *. elim (ad_alloc_opt_optimal_1 m a H). intros y H0. rewrite H0.
    reflexivity.
  Qed.

End AdAlloc.

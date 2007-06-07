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
Require Import Nnat.
Require Import Map.
Require Import Fset.

Section AdAlloc.

  Variable A : Set.

  (** Allocator: returns an address not in the domain of [m].
  This allocator is optimal in that it returns the lowest possible address,
  in the usual ordering on integers. It is not the most efficient, however. *)
  Fixpoint ad_alloc_opt (m:Map A) : ad :=
    match m with
    | M0 => N0
    | M1 a _ => if Neqb a N0 then Npos 1 else N0
    | M2 m1 m2 =>
        Nmin (Ndouble (ad_alloc_opt m1))
          (Ndouble_plus_one (ad_alloc_opt m2))
    end.

  Lemma ad_alloc_opt_allocates_1 :
   forall m:Map A, MapGet A m (ad_alloc_opt m) = None.
  Proof.
    induction m as [| a| m0 H m1 H0]. reflexivity.
    simpl in |- *. elim (sumbool_of_bool (Neqb a N0)). intro H. rewrite H.
    rewrite (Neqb_complete _ _ H). reflexivity.
    intro H. rewrite H. rewrite H. reflexivity.
    intros. change
   (ad_alloc_opt (M2 A m0 m1)) with (Nmin (Ndouble (ad_alloc_opt m0))
                                       (Ndouble_plus_one (ad_alloc_opt m1)))
  in |- *.
    elim
     (Nmin_choice (Ndouble (ad_alloc_opt m0))
        (Ndouble_plus_one (ad_alloc_opt m1))).
    intro H1. rewrite H1. rewrite MapGet_M2_bit_0_0. rewrite Ndouble_div2. assumption.
    apply Ndouble_bit0.
    intro H1. rewrite H1. rewrite MapGet_M2_bit_0_1. rewrite Ndouble_plus_one_div2. assumption.
    apply Ndouble_plus_one_bit0.
  Qed.

  Lemma ad_alloc_opt_allocates :
   forall m:Map A, in_dom A (ad_alloc_opt m) m = false.
  Proof.
    unfold in_dom in |- *. intro. rewrite (ad_alloc_opt_allocates_1 m). reflexivity.
  Qed.

  (** Moreover, this is optimal: all addresses below [(ad_alloc_opt m)]
      are in [dom m]: *)

  Lemma ad_alloc_opt_optimal_1 :
   forall (m:Map A) (a:ad),
     Nleb (ad_alloc_opt m) a = false -> {y : A | MapGet A m a = Some y}.
  Proof.
    induction m as [| a y| m0 H m1 H0]. simpl in |- *. unfold Nle in |- *. simpl in |- *. intros. discriminate H.
    simpl in |- *. intros b H. elim (sumbool_of_bool (Neqb a N0)). intro H0. rewrite H0 in H.
    unfold Nleb in H. cut (N0 = b). intro. split with y. rewrite <- H1. rewrite H0. reflexivity.
    rewrite <- (N_of_nat_of_N b).
    rewrite <- (le_n_O_eq _ (le_S_n _ _ (leb_complete_conv _ _ H))). reflexivity.
    intro H0. rewrite H0 in H. discriminate H.
    intros. simpl in H1. elim (Ndouble_or_double_plus_un a). intro H2. elim H2. intros a0 H3.
    rewrite H3 in H1. elim (H _ (Nltb_double_mono_conv _ _ (Nmin_lt_3 _ _ _ H1))). intros y H4.
    split with y. rewrite H3. rewrite MapGet_M2_bit_0_0. rewrite Ndouble_div2. assumption.
    apply Ndouble_bit0.
    intro H2. elim H2. intros a0 H3. rewrite H3 in H1.
    elim (H0 _ (Nltb_double_plus_one_mono_conv _ _ (Nmin_lt_4 _ _ _ H1))). intros y H4.
    split with y. rewrite H3. rewrite MapGet_M2_bit_0_1. rewrite Ndouble_plus_one_div2.
    assumption.
    apply Ndouble_plus_one_bit0.
  Qed.

  Lemma ad_alloc_opt_optimal :
   forall (m:Map A) (a:ad),
     Nleb (ad_alloc_opt m) a = false -> in_dom A a m = true.
  Proof.
    intros. unfold in_dom in |- *. elim (ad_alloc_opt_optimal_1 m a H). intros y H0. rewrite H0.
    reflexivity.
  Qed.

End AdAlloc.

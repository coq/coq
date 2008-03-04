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
Require Import List.
Require Import Mapiter.

Section LSort.

  Variable A : Type.

  Fixpoint alist_sorted (l:alist A) : bool :=
    match l with
    | nil => true
    | (a, _) :: l' =>
        match l' with
        | nil => true
        | (a', y') :: l'' => andb (Nless a a') (alist_sorted l')
        end
    end.

  Fixpoint alist_nth_ad (n:nat) (l:alist A) {struct l} : ad :=
    match l with
    | nil => N0 (* dummy *)
    | (a, y) :: l' => match n with
                      | O => a
                      | S n' => alist_nth_ad n' l'
                      end
    end.

  Definition alist_sorted_1 (l:alist A) :=
    forall n:nat,
      S (S n) <= length l ->
      Nless (alist_nth_ad n l) (alist_nth_ad (S n) l) = true.

  Lemma alist_sorted_imp_1 :
   forall l:alist A, alist_sorted l = true -> alist_sorted_1 l.
  Proof.
    unfold alist_sorted_1 in |- *. simple induction l. intros. elim (le_Sn_O (S n) H0).
    intro r. elim r. intros a y. simple induction l0. intros. simpl in H1.
    elim (le_Sn_O n (le_S_n (S n) 0 H1)).
    intro r0. elim r0. intros a0 y0. simple induction n. intros. simpl in |- *. simpl in H1.
    exact (proj1 (andb_prop _ _ H1)).
    intros. change
   (Nless (alist_nth_ad n0 ((a0, y0) :: l1))
      (alist_nth_ad (S n0) ((a0, y0) :: l1)) = true) 
  in |- *.
    apply H0. exact (proj2 (andb_prop _ _ H1)).
    apply le_S_n. exact H3.
  Qed.

  Definition alist_sorted_2 (l:alist A) :=
    forall m n:nat,
      m < n ->
      S n <= length l -> Nless (alist_nth_ad m l) (alist_nth_ad n l) = true.

  Lemma alist_sorted_1_imp_2 :
   forall l:alist A, alist_sorted_1 l -> alist_sorted_2 l.
  Proof.
    unfold alist_sorted_1, alist_sorted_2, lt in |- *. intros l H m n H0. elim H0. exact (H m).
    intros. apply Nless_trans with (a' := alist_nth_ad m0 l). apply H2. apply le_Sn_le.
    assumption.
    apply H. assumption.
  Qed.

  Lemma alist_sorted_2_imp :
   forall l:alist A, alist_sorted_2 l -> alist_sorted l = true.
  Proof.
    unfold alist_sorted_2, lt in |- *. simple induction l. trivial.
    intro r. elim r. intros a y. simple induction l0. trivial.
    intro r0. elim r0. intros a0 y0. intros.
    change (andb (Nless a a0) (alist_sorted ((a0, y0) :: l1)) = true)
     in |- *.
    apply andb_true_intro. split. apply (H1 0 1). apply le_n.
    simpl in |- *. apply le_n_S. apply le_n_S. apply le_O_n.
    apply H0. intros. apply (H1 (S m) (S n)). apply le_n_S. assumption.
    exact (le_n_S _ _ H3).
  Qed.

  Lemma app_length :
   forall (C:Type) (l l':list C), length (l ++ l') = length l + length l'.
  Proof.
    simple induction l. trivial.
    intros. simpl in |- *. rewrite (H l'). reflexivity.
  Qed.

  Lemma aapp_length :
   forall l l':alist A, length (aapp A l l') = length l + length l'.
  Proof.
    exact (app_length (ad * A)).
  Qed.

  Lemma alist_nth_ad_aapp_1 :
   forall (l l':alist A) (n:nat),
     S n <= length l -> alist_nth_ad n (aapp A l l') = alist_nth_ad n l.
  Proof.
    simple induction l. intros. elim (le_Sn_O n H).
    intro r. elim r. intros a y l' H l''. simple induction n. trivial.
    intros. simpl in |- *. apply H. apply le_S_n. exact H1.
  Qed.

  Lemma alist_nth_ad_aapp_2 :
   forall (l l':alist A) (n:nat),
     S n <= length l' ->
     alist_nth_ad (length l + n) (aapp A l l') = alist_nth_ad n l'.
  Proof.
    simple induction l. trivial.
    intro r. elim r. intros a y l' H l'' n H0. simpl in |- *. apply H. exact H0.
  Qed.

  Lemma interval_split :
   forall p q n:nat,
     S n <= p + q -> {n' : nat | S n' <= q /\ n = p + n'} + {S n <= p}.
  Proof.
    simple induction p. simpl in |- *. intros. left. split with n. split; [ assumption | reflexivity ].
    intros p' H q. simple induction n. intros. right. apply le_n_S. apply le_O_n.
    intros. elim (H _ _ (le_S_n _ _ H1)). intro H2. left. elim H2. intros n' H3.
    elim H3. intros H4 H5. split with n'. split; [ assumption | rewrite H5; reflexivity ].
    intro H2. right. apply le_n_S. assumption.
  Qed.

  Lemma alist_conc_sorted :
   forall l l':alist A,
     alist_sorted_2 l ->
     alist_sorted_2 l' ->
     (forall n n':nat,
        S n <= length l ->
        S n' <= length l' ->
        Nless (alist_nth_ad n l) (alist_nth_ad n' l') = true) ->
     alist_sorted_2 (aapp A l l').
  Proof.
    unfold alist_sorted_2, lt in |- *. intros. rewrite (aapp_length l l') in H3.
    elim
     (interval_split (length l) (length l') m
        (le_trans _ _ _ (le_n_S _ _ (lt_le_weak m n H2)) H3)).
    intro H4. elim H4. intros m' H5. elim H5. intros. rewrite H7.
    rewrite (alist_nth_ad_aapp_2 l l' m' H6). elim (interval_split (length l) (length l') n H3).
    intro H8. elim H8. intros n' H9. elim H9. intros. rewrite H11.
    rewrite (alist_nth_ad_aapp_2 l l' n' H10). apply H0. rewrite H7 in H2. rewrite H11 in H2.
    change (S (length l) + m' <= length l + n') in H2.
    rewrite (plus_Snm_nSm (length l) m') in H2. exact ((fun p n m:nat => plus_le_reg_l n m p) (length l) (S m') n' H2).
    exact H10.
    intro H8. rewrite H7 in H2. cut (S (length l) <= length l). intros. elim (le_Sn_n _ H9).
    apply le_trans with (m := S n). apply le_n_S. apply le_trans with (m := S (length l + m')).
    apply le_trans with (m := length l + m'). apply le_plus_l.
    apply le_n_Sn.
    exact H2.
    exact H8.
    intro H4. rewrite (alist_nth_ad_aapp_1 l l' m H4).
    elim (interval_split (length l) (length l') n H3). intro H5. elim H5. intros n' H6. elim H6.
    intros. rewrite H8. rewrite (alist_nth_ad_aapp_2 l l' n' H7). exact (H1 m n' H4 H7).
    intro H5. rewrite (alist_nth_ad_aapp_1 l l' n H5). exact (H m n H2 H5).
  Qed.

  Lemma alist_nth_ad_semantics :
   forall (l:alist A) (n:nat),
     S n <= length l ->
     {y : A | alist_semantics A l (alist_nth_ad n l) = Some y}.
  Proof.
    simple induction l. intros. elim (le_Sn_O _ H).
    intro r. elim r. intros a y l0 H. simple induction n. simpl in |- *. intro. split with y.
    rewrite (Neqb_correct a). reflexivity.
    intros. elim (H _ (le_S_n _ _ H0)). intros y0 H2.
    elim (sumbool_of_bool (Neqb a (alist_nth_ad n0 l0))). intro H3. split with y.
    rewrite (Neqb_complete _ _ H3). simpl in |- *. rewrite (Neqb_correct (alist_nth_ad n0 l0)).
    reflexivity.
    intro H3. split with y0. simpl in |- *. rewrite H3. assumption.
  Qed.

  Lemma alist_of_Map_nth_ad :
   forall (m:Map A) (pf:ad -> ad) (l:alist A),
     l =
     MapFold1 A (alist A) (anil A) (aapp A)
       (fun (a0:ad) (y:A) => acons A (a0, y) (anil A)) pf m ->
     forall n:nat, S n <= length l -> {a' : ad | alist_nth_ad n l = pf a'}.
  Proof.
    intros. elim (alist_nth_ad_semantics l n H0). intros y H1.
    apply (alist_of_Map_semantics_1_1 A m pf (alist_nth_ad n l) y).
    rewrite <- H. assumption.
  Qed.

  Definition ad_monotonic (pf:ad -> ad) :=
    forall a a':ad, Nless a a' = true -> Nless (pf a) (pf a') = true.

  Lemma Ndouble_monotonic : ad_monotonic Ndouble.
  Proof.
    unfold ad_monotonic in |- *. intros. rewrite Nless_def_1. assumption.
  Qed.

  Lemma Ndouble_plus_one_monotonic : ad_monotonic Ndouble_plus_one.
  Proof.
    unfold ad_monotonic in |- *. intros. rewrite Nless_def_2. assumption.
  Qed.

  Lemma ad_comp_monotonic :
   forall pf pf':ad -> ad,
     ad_monotonic pf ->
     ad_monotonic pf' -> ad_monotonic (fun a0:ad => pf (pf' a0)).
  Proof.
    unfold ad_monotonic in |- *. intros. apply H. apply H0. exact H1.
  Qed.

  Lemma ad_comp_double_monotonic :
   forall pf:ad -> ad,
     ad_monotonic pf -> ad_monotonic (fun a0:ad => pf (Ndouble a0)).
  Proof.
    intros. apply ad_comp_monotonic. assumption.
    exact Ndouble_monotonic.
  Qed.

  Lemma ad_comp_double_plus_un_monotonic :
   forall pf:ad -> ad,
     ad_monotonic pf -> ad_monotonic (fun a0:ad => pf (Ndouble_plus_one a0)).
  Proof.
    intros. apply ad_comp_monotonic. assumption.
    exact Ndouble_plus_one_monotonic.
  Qed.

  Lemma alist_of_Map_sorts_1 :
   forall (m:Map A) (pf:ad -> ad),
     ad_monotonic pf ->
     alist_sorted_2
       (MapFold1 A (alist A) (anil A) (aapp A)
          (fun (a:ad) (y:A) => acons A (a, y) (anil A)) pf m).
  Proof.
    simple induction m. simpl in |- *. intros. apply alist_sorted_1_imp_2. apply alist_sorted_imp_1. reflexivity.
    intros. simpl in |- *. apply alist_sorted_1_imp_2. apply alist_sorted_imp_1. reflexivity.
    intros. simpl in |- *. apply alist_conc_sorted.
    exact
     (H (fun a0:ad => pf (Ndouble a0)) (ad_comp_double_monotonic pf H1)).
    exact
     (H0 (fun a0:ad => pf (Ndouble_plus_one a0))
        (ad_comp_double_plus_un_monotonic pf H1)).
    intros. elim
  (alist_of_Map_nth_ad m0 (fun a0:ad => pf (Ndouble a0))
     (MapFold1 A (alist A) (anil A) (aapp A)
        (fun (a0:ad) (y:A) => acons A (a0, y) (anil A))
        (fun a0:ad => pf (Ndouble a0)) m0) (refl_equal _) n H2).
    intros a H4. rewrite H4. elim
  (alist_of_Map_nth_ad m1 (fun a0:ad => pf (Ndouble_plus_one a0))
     (MapFold1 A (alist A) (anil A) (aapp A)
        (fun (a0:ad) (y:A) => acons A (a0, y) (anil A))
        (fun a0:ad => pf (Ndouble_plus_one a0)) m1) (
     refl_equal _) n' H3).
    intros a' H5. rewrite H5. unfold ad_monotonic in H1. apply H1. apply Nless_def_3.
  Qed.

  Lemma alist_of_Map_sorts :
   forall m:Map A, alist_sorted (alist_of_Map A m) = true.
  Proof.
    intro. apply alist_sorted_2_imp.
    exact
     (alist_of_Map_sorts_1 m (fun a0:ad => a0)
        (fun (a a':ad) (p:Nless a a' = true) => p)).
  Qed.

  Lemma alist_of_Map_sorts1 :
   forall m:Map A, alist_sorted_1 (alist_of_Map A m).
  Proof.
    intro. apply alist_sorted_imp_1. apply alist_of_Map_sorts.
  Qed.
 
  Lemma alist_of_Map_sorts2 :
   forall m:Map A, alist_sorted_2 (alist_of_Map A m).
  Proof.
    intro. apply alist_sorted_1_imp_2. apply alist_of_Map_sorts1.
  Qed.

  Lemma alist_too_low :
   forall (l:alist A) (a a':ad) (y:A),
     Nless a a' = true ->
     alist_sorted_2 ((a', y) :: l) ->
     alist_semantics A ((a', y) :: l) a = None.
  Proof.
    simple induction l. intros. simpl in |- *. elim (sumbool_of_bool (Neqb a' a)). intro H1.
    rewrite (Neqb_complete _ _ H1) in H. rewrite (Nless_not_refl a) in H. discriminate H.
    intro H1. rewrite H1. reflexivity.
    intro r. elim r. intros a y l0 H a0 a1 y0 H0 H1.
    change
      (match Neqb a1 a0 with
       | true => Some y0
       | false => alist_semantics A ((a, y) :: l0) a0
       end = None) in |- *.
    elim (sumbool_of_bool (Neqb a1 a0)). intro H2. rewrite (Neqb_complete _ _ H2) in H0.
    rewrite (Nless_not_refl a0) in H0. discriminate H0.
    intro H2. rewrite H2. apply H. apply Nless_trans with (a' := a1). assumption.
    unfold alist_sorted_2 in H1. apply (H1 0 1). apply lt_n_Sn.
    simpl in |- *. apply le_n_S. apply le_n_S. apply le_O_n.
    apply alist_sorted_1_imp_2. apply alist_sorted_imp_1.
    cut (alist_sorted ((a1, y0) :: (a, y) :: l0) = true). intro H3.
    exact (proj2 (andb_prop _ _ H3)).
    apply alist_sorted_2_imp. assumption.
  Qed.

  Lemma alist_semantics_nth_ad :
   forall (l:alist A) (a:ad) (y:A),
     alist_semantics A l a = Some y ->
     {n : nat | S n <= length l /\ alist_nth_ad n l = a}.
  Proof.
    simple induction l. intros. discriminate H.
    intro r. elim r. intros a y l0 H a0 y0 H0. simpl in H0. elim (sumbool_of_bool (Neqb a a0)).
    intro H1. rewrite H1 in H0. split with 0. split. simpl in |- *. apply le_n_S. apply le_O_n.
    simpl in |- *. exact (Neqb_complete _ _ H1).
    intro H1. rewrite H1 in H0. elim (H a0 y0 H0). intros n' H2. split with (S n'). split.
    simpl in |- *. apply le_n_S. exact (proj1 H2).
    exact (proj2 H2).
  Qed.

  Lemma alist_semantics_tail :
   forall (l:alist A) (a:ad) (y:A),
     alist_sorted_2 ((a, y) :: l) ->
     eqm A (alist_semantics A l)
       (fun a0:ad =>
          if Neqb a a0 then None else alist_semantics A ((a, y) :: l) a0).
  Proof.
    unfold eqm in |- *. intros. elim (sumbool_of_bool (Neqb a a0)). intro H0. rewrite H0.
    rewrite <- (Neqb_complete _ _ H0). unfold alist_sorted_2 in H.
    elim (option_sum A (alist_semantics A l a)). intro H1. elim H1. intros y0 H2.
    elim (alist_semantics_nth_ad l a y0 H2). intros n H3. elim H3. intros.
    cut
     (Nless (alist_nth_ad 0 ((a, y) :: l))
        (alist_nth_ad (S n) ((a, y) :: l)) = true).
    intro. simpl in H6. rewrite H5 in H6. rewrite (Nless_not_refl a) in H6. discriminate H6.
    apply H. apply lt_O_Sn.
    simpl in |- *. apply le_n_S. assumption.
    trivial.
    intro H0. simpl in |- *. rewrite H0. reflexivity.
  Qed.

  Lemma alist_semantics_same_tail :
   forall (l l':alist A) (a:ad) (y:A),
     alist_sorted_2 ((a, y) :: l) ->
     alist_sorted_2 ((a, y) :: l') ->
     eqm A (alist_semantics A ((a, y) :: l))
       (alist_semantics A ((a, y) :: l')) ->
     eqm A (alist_semantics A l) (alist_semantics A l').
  Proof.
    unfold eqm in |- *. intros. rewrite (alist_semantics_tail _ _ _ H a0).
    rewrite (alist_semantics_tail _ _ _ H0 a0). case (Neqb a a0). reflexivity.
    exact (H1 a0).
  Qed.

  Lemma alist_sorted_tail :
   forall (l:alist A) (a:ad) (y:A),
     alist_sorted_2 ((a, y) :: l) -> alist_sorted_2 l.
  Proof.
    unfold alist_sorted_2 in |- *. intros. apply (H (S m) (S n)). apply lt_n_S. assumption.
    simpl in |- *. apply le_n_S. assumption.
  Qed.

  Lemma alist_canonical :
   forall l l':alist A,
     eqm A (alist_semantics A l) (alist_semantics A l') ->
     alist_sorted_2 l -> alist_sorted_2 l' -> l = l'.
  Proof.
    unfold eqm in |- *. simple induction l. simple induction l'. trivial.
    intro r. elim r. intros a y l0 H H0 H1 H2. simpl in H0.
    cut
     (None =
      match Neqb a a with
      | true => Some y
      | false => alist_semantics A l0 a
      end).
    rewrite (Neqb_correct a). intro. discriminate H3.
    exact (H0 a).
    intro r. elim r. intros a y l0 H. simple induction l'. intros. simpl in H0.
    cut
     (match Neqb a a with
      | true => Some y
      | false => alist_semantics A l0 a
      end = None).
    rewrite (Neqb_correct a). intro. discriminate H3.
    exact (H0 a).
    intro r'. elim r'. intros a' y' l'0 H0 H1 H2 H3. elim (Nless_total a a'). intro H4.
    elim H4. intro H5.
    cut
     (alist_semantics A ((a, y) :: l0) a =
      alist_semantics A ((a', y') :: l'0) a).
    intro. rewrite (alist_too_low l'0 a a' y' H5 H3) in H6. simpl in H6.
    rewrite (Neqb_correct a) in H6. discriminate H6.
    exact (H1 a).
    intro H5. cut
  (alist_semantics A ((a, y) :: l0) a' =
   alist_semantics A ((a', y') :: l'0) a').
    intro. rewrite (alist_too_low l0 a' a y H5 H2) in H6. simpl in H6.
    rewrite (Neqb_correct a') in H6. discriminate H6.
    exact (H1 a').
    intro H4. rewrite H4.
    cut
     (alist_semantics A ((a, y) :: l0) a =
      alist_semantics A ((a', y') :: l'0) a).
    intro. simpl in H5. rewrite H4 in H5. rewrite (Neqb_correct a') in H5. inversion H5.
    rewrite H4 in H1. rewrite H7 in H1. cut (l0 = l'0). intro. rewrite H6. reflexivity.
    apply H. rewrite H4 in H2. rewrite H7 in H2.
    exact (alist_semantics_same_tail l0 l'0 a' y' H2 H3 H1).
    exact (alist_sorted_tail _ _ _ H2).
    exact (alist_sorted_tail _ _ _ H3).
    exact (H1 a).
  Qed.

End LSort.
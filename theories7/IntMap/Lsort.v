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
Require PolyList.
Require Mapiter.

Section LSort.

  Variable A : Set.

  Fixpoint ad_less_1 [a,a':ad; p:positive] : bool :=
    Cases p of
        (xO p') => (ad_less_1 (ad_div_2 a) (ad_div_2 a') p')
      | _ => (andb (negb (ad_bit_0 a)) (ad_bit_0 a'))
    end.

  Definition ad_less := [a,a':ad] Cases (ad_xor a a') of
      	                              ad_z => false
				    | (ad_x p) => (ad_less_1 a a' p)
				  end.

  Lemma ad_bit_0_less : (a,a':ad) (ad_bit_0 a)=false -> (ad_bit_0 a')=true -> 
      (ad_less a a')=true.
  Proof.
    Intros. Elim (ad_sum (ad_xor a a')). Intro H1. Elim H1. Intros p H2. Unfold ad_less.
    Rewrite H2. Generalize H2. Elim p. Intros. Simpl. Rewrite H. Rewrite H0. Reflexivity.
    Intros. Cut (ad_bit_0 (ad_xor a a'))=false. Intro. Rewrite (ad_xor_bit_0 a a') in H5.
    Rewrite H in H5. Rewrite H0 in H5. Discriminate H5.
    Rewrite H4. Reflexivity.
    Intro. Simpl. Rewrite H. Rewrite H0. Reflexivity.
    Intro H1. Cut (ad_bit_0 (ad_xor a a'))=false. Intro. Rewrite (ad_xor_bit_0 a a') in H2.
    Rewrite H in H2. Rewrite H0 in H2. Discriminate H2.
    Rewrite H1. Reflexivity.
  Qed.

  Lemma ad_bit_0_gt : (a,a':ad) (ad_bit_0 a)=true -> (ad_bit_0 a')=false -> 
      (ad_less a a')=false.
  Proof.
    Intros. Elim (ad_sum (ad_xor a a')). Intro H1. Elim H1. Intros p H2. Unfold ad_less.
    Rewrite H2. Generalize H2. Elim p. Intros. Simpl. Rewrite H. Rewrite H0. Reflexivity.
    Intros. Cut (ad_bit_0 (ad_xor a a'))=false. Intro. Rewrite (ad_xor_bit_0 a a') in H5.
    Rewrite H in H5. Rewrite H0 in H5. Discriminate H5.
    Rewrite H4. Reflexivity.
    Intro. Simpl. Rewrite H. Rewrite H0. Reflexivity.
    Intro H1. Unfold ad_less. Rewrite H1. Reflexivity.
  Qed.

  Lemma ad_less_not_refl : (a:ad) (ad_less a a)=false.
  Proof.
    Intro. Unfold ad_less. Rewrite (ad_xor_nilpotent a). Reflexivity.
  Qed.

  Lemma ad_ind_double : 
      (a:ad)(P:ad->Prop) (P ad_z) ->
      	((a:ad) (P a) -> (P (ad_double a))) ->
      	((a:ad) (P a) -> (P (ad_double_plus_un a))) -> (P a).
  Proof.
    Intros; Elim a. Trivial.
    Induction p. Intros. 
    Apply (H1 (ad_x p0)); Trivial.
    Intros; Apply (H0 (ad_x p0)); Trivial.
    Intros; Apply (H1 ad_z); Assumption.
  Qed.

  Lemma ad_rec_double : 
      (a:ad)(P:ad->Set) (P ad_z) ->
      	((a:ad) (P a) -> (P (ad_double a))) ->
      	((a:ad) (P a) -> (P (ad_double_plus_un a))) -> (P a).
  Proof.
    Intros; Elim a. Trivial.
    Induction p. Intros. 
    Apply (H1 (ad_x p0)); Trivial.
    Intros; Apply (H0 (ad_x p0)); Trivial.
    Intros; Apply (H1 ad_z); Assumption.
  Qed.

  Lemma ad_less_def_1 : (a,a':ad) (ad_less (ad_double a) (ad_double a'))=(ad_less a a').
  Proof.
    Induction a. Induction a'. Reflexivity.
    Trivial.
    Induction a'. Unfold ad_less. Simpl. (Elim p; Trivial).
    Unfold ad_less. Simpl. Intro. Case (p_xor p p0). Reflexivity.
    Trivial.
  Qed.

  Lemma ad_less_def_2 : (a,a':ad)
      (ad_less (ad_double_plus_un a) (ad_double_plus_un a'))=(ad_less a a').
  Proof.
    Induction a. Induction a'. Reflexivity.
    Trivial.
    Induction a'. Unfold ad_less. Simpl. (Elim p; Trivial).
    Unfold ad_less. Simpl. Intro. Case (p_xor p p0). Reflexivity.
    Trivial.
  Qed.

  Lemma ad_less_def_3 : (a,a':ad) (ad_less (ad_double a) (ad_double_plus_un a'))=true.
  Proof.
    Intros. Apply ad_bit_0_less. Apply ad_double_bit_0.
    Apply ad_double_plus_un_bit_0.
  Qed.

  Lemma ad_less_def_4 : (a,a':ad) (ad_less (ad_double_plus_un a) (ad_double a'))=false.
  Proof.
    Intros. Apply ad_bit_0_gt. Apply ad_double_plus_un_bit_0.
    Apply ad_double_bit_0.
  Qed.

  Lemma ad_less_z : (a:ad) (ad_less a ad_z)=false.
  Proof.
    Induction a. Reflexivity.
    Unfold ad_less. Intro. Rewrite (ad_xor_neutral_right (ad_x p)). (Elim p; Trivial).
  Qed.

  Lemma ad_z_less_1 : (a:ad) (ad_less ad_z a)=true -> {p:positive | a=(ad_x p)}.
  Proof.
    Induction a. Intro. Discriminate H.
    Intros. Split with p. Reflexivity.
  Qed.

  Lemma ad_z_less_2 : (a:ad) (ad_less ad_z a)=false -> a=ad_z.
  Proof.
    Induction a. Trivial.
    Unfold ad_less. Simpl. Cut (p:positive)(ad_less_1 ad_z (ad_x p) p)=false->False.
    Intros. Elim (H p H0).
    Induction p. Intros. Discriminate H0.
    Intros. Exact (H H0).
    Intro. Discriminate H.
  Qed.

  Lemma ad_less_trans : (a,a',a'':ad)
      (ad_less a a')=true -> (ad_less a' a'')=true -> (ad_less a a'')=true.
  Proof.
    Intro a. Apply ad_ind_double with P:=[a:ad]
          (a',a'':ad)
           (ad_less a a')=true
            ->(ad_less a' a'')=true->(ad_less a a'')=true.
    Intros. Elim (sumbool_of_bool (ad_less ad_z a'')). Trivial.
    Intro H1. Rewrite (ad_z_less_2 a'' H1) in H0. Rewrite (ad_less_z a') in H0. Discriminate H0.
    Intros a0 H a'. Apply ad_ind_double with P:=[a':ad]
          (a'':ad)
           (ad_less (ad_double a0) a')=true
            ->(ad_less a' a'')=true->(ad_less (ad_double a0) a'')=true.
    Intros. Rewrite (ad_less_z (ad_double a0)) in H0. Discriminate H0.
    Intros a1 H0 a'' H1. Rewrite (ad_less_def_1 a0 a1) in H1.
    Apply ad_ind_double with P:=[a'':ad]
          (ad_less (ad_double a1) a'')=true
           ->(ad_less (ad_double a0) a'')=true.
    Intro. Rewrite (ad_less_z (ad_double a1)) in H2. Discriminate H2.
    Intros. Rewrite (ad_less_def_1 a1 a2) in H3. Rewrite (ad_less_def_1 a0 a2).
    Exact (H a1 a2 H1 H3).
    Intros. Apply ad_less_def_3.
    Intros a1 H0 a'' H1. Apply ad_ind_double with P:=[a'':ad]
          (ad_less (ad_double_plus_un a1) a'')=true
           ->(ad_less (ad_double a0) a'')=true.
    Intro. Rewrite (ad_less_z (ad_double_plus_un a1)) in H2. Discriminate H2.
    Intros. Rewrite (ad_less_def_4 a1 a2) in H3. Discriminate H3.
    Intros. Apply ad_less_def_3.
    Intros a0 H a'. Apply ad_ind_double with P:=[a':ad]
          (a'':ad)
           (ad_less (ad_double_plus_un a0) a')=true
            ->(ad_less a' a'')=true
               ->(ad_less (ad_double_plus_un a0) a'')=true.
    Intros. Rewrite (ad_less_z (ad_double_plus_un a0)) in H0. Discriminate H0.
    Intros. Rewrite (ad_less_def_4 a0 a1) in H1. Discriminate H1.
    Intros a1 H0 a'' H1. Apply ad_ind_double with P:=[a'':ad]
          (ad_less (ad_double_plus_un a1) a'')=true
           ->(ad_less (ad_double_plus_un a0) a'')=true.
    Intro. Rewrite (ad_less_z (ad_double_plus_un a1)) in H2. Discriminate H2.
    Intros. Rewrite (ad_less_def_4 a1 a2) in H3. Discriminate H3.
    Rewrite (ad_less_def_2 a0 a1) in H1. Intros. Rewrite (ad_less_def_2 a1 a2) in H3.
    Rewrite (ad_less_def_2 a0 a2). Exact (H a1 a2 H1 H3).
  Qed.

  Fixpoint alist_sorted [l:(alist A)] : bool :=
    Cases l of
      	nil => true
      | (cons (a, _) l') => Cases l' of
                                nil => true
			      | (cons (a', y') l'') => (andb (ad_less a a')
			                                     (alist_sorted l'))
			    end
    end.

  Fixpoint alist_nth_ad [n:nat; l:(alist A)] : ad :=
    Cases l of
      	nil => ad_z (* dummy *)
      | (cons (a, y) l') => Cases n of
                                O => a
			      | (S n') => (alist_nth_ad n' l')
			    end
    end.

  Definition alist_sorted_1 := [l:(alist A)]
      (n:nat) (le (S (S n)) (length l)) ->
      	(ad_less (alist_nth_ad n l) (alist_nth_ad (S n) l))=true.

  Lemma alist_sorted_imp_1 : (l:(alist A)) (alist_sorted l)=true -> (alist_sorted_1 l).
  Proof.
    Unfold alist_sorted_1. Induction l. Intros. Elim (le_Sn_O (S n) H0).
    Intro r. Elim r. Intros a y. Induction l0. Intros. Simpl in H1.
    Elim (le_Sn_O n (le_S_n (S n) O H1)).
    Intro r0. Elim r0. Intros a0 y0. Induction n. Intros. Simpl. Simpl in H1.
    Exact (proj1 ? ? (andb_prop ? ? H1)).
    Intros. Change (ad_less (alist_nth_ad n0 (cons (a0,y0) l1))
      	                    (alist_nth_ad (S n0) (cons (a0,y0) l1)))=true.
    Apply H0. Exact (proj2 ? ? (andb_prop ? ? H1)).
    Apply le_S_n. Exact H3.
  Qed.

  Definition alist_sorted_2 := [l:(alist A)]
    (m,n:nat) (lt m n) -> (le (S n) (length l)) ->
      	(ad_less (alist_nth_ad m l) (alist_nth_ad n l))=true.

  Lemma alist_sorted_1_imp_2 : (l:(alist A)) (alist_sorted_1 l) -> (alist_sorted_2 l).
  Proof.
    Unfold alist_sorted_1 alist_sorted_2 lt. Intros l H m n H0. Elim H0. Exact (H m).
    Intros. Apply ad_less_trans with a':=(alist_nth_ad m0 l). Apply H2. Apply le_trans_S.
    Assumption.
    Apply H. Assumption.
  Qed.

  Lemma alist_sorted_2_imp : (l:(alist A)) (alist_sorted_2 l) -> (alist_sorted l)=true.
  Proof.
    Unfold alist_sorted_2 lt. Induction l. Trivial.
    Intro r. Elim r. Intros a y. Induction l0. Trivial.
    Intro r0. Elim r0. Intros a0 y0. Intros.
    Change (andb (ad_less a a0) (alist_sorted (cons (a0,y0) l1)))=true.
    Apply andb_true_intro. Split. Apply (H1 (0) (1)). Apply le_n.
    Simpl. Apply le_n_S. Apply le_n_S. Apply le_O_n.
    Apply H0. Intros. Apply (H1 (S m) (S n)). Apply le_n_S. Assumption.
    Exact (le_n_S ? ? H3).
  Qed.

  Lemma app_length : (C:Set) (l,l':(list C)) (length (app l l'))=(plus (length l) (length l')).
  Proof.
    Induction l. Trivial.
    Intros. Simpl. Rewrite (H l'). Reflexivity.
  Qed.

  Lemma aapp_length : (l,l':(alist A)) (length (aapp A l l'))=(plus (length l) (length l')).
  Proof.
    Exact (app_length ad*A).
  Qed.

  Lemma alist_nth_ad_aapp_1 : (l,l':(alist A)) (n:nat)
      (le (S n) (length l)) -> (alist_nth_ad n (aapp A l l'))=(alist_nth_ad n l).
  Proof.
    Induction l. Intros. Elim (le_Sn_O n H).
    Intro r. Elim r. Intros a y l' H l''. Induction n. Trivial.
    Intros. Simpl. Apply H. Apply le_S_n. Exact H1.
  Qed.

  Lemma alist_nth_ad_aapp_2 : (l,l':(alist A)) (n:nat)
      (le (S n) (length l')) ->
      	(alist_nth_ad (plus (length l) n) (aapp A l l'))=(alist_nth_ad n l').
  Proof.
    Induction l. Trivial.
    Intro r. Elim r. Intros a y l' H l'' n H0. Simpl. Apply H. Exact H0.
  Qed.

  Lemma interval_split : (p,q,n:nat) (le (S n) (plus p q)) ->
      {n' : nat | (le (S n') q) /\ n=(plus p n')}+{(le (S n) p)}.
  Proof.
    Induction p. Simpl. Intros. Left . Split with n. (Split; [ Assumption | Reflexivity ]).
    Intros p' H q. Induction n. Intros. Right . Apply le_n_S. Apply le_O_n.
    Intros. Elim (H ? ? (le_S_n ? ? H1)). Intro H2. Left . Elim H2. Intros n' H3.
    Elim H3. Intros H4 H5. Split with n'. (Split; [ Assumption | Rewrite H5; Reflexivity ]).
    Intro H2. Right . Apply le_n_S. Assumption.
  Qed.

  Lemma alist_conc_sorted : (l,l':(alist A)) (alist_sorted_2 l) -> (alist_sorted_2 l') ->
      ((n,n':nat) (le (S n) (length l)) -> (le (S n') (length l')) ->
      	  (ad_less (alist_nth_ad n l) (alist_nth_ad n' l'))=true) ->
      	(alist_sorted_2 (aapp A l l')).
  Proof.
    Unfold alist_sorted_2 lt. Intros. Rewrite (aapp_length l l') in H3.
    Elim (interval_split (length l) (length l') m
            (le_trans ? ? ? (le_n_S ? ? (lt_le_weak m n H2)) H3)).
    Intro H4. Elim H4. Intros m' H5. Elim H5. Intros. Rewrite H7.
    Rewrite (alist_nth_ad_aapp_2 l l' m' H6). Elim (interval_split (length l) (length l') n H3).
    Intro H8. Elim H8. Intros n' H9. Elim H9. Intros. Rewrite H11.
    Rewrite (alist_nth_ad_aapp_2 l l' n' H10). Apply H0. Rewrite H7 in H2. Rewrite H11 in H2.
    Change (le (plus (S (length l)) m') (plus (length l) n')) in H2.
    Rewrite (plus_Snm_nSm (length l) m') in H2. Exact (simpl_le_plus_l (length l) (S m') n' H2).
    Exact H10.
    Intro H8. Rewrite H7 in H2. Cut (le (S (length l)) (length l)). Intros. Elim (le_Sn_n ? H9).
    Apply le_trans with m:=(S n). Apply le_n_S. Apply le_trans with m:=(S (plus (length l) m')).
    Apply le_trans with m:=(plus (length l) m'). Apply le_plus_l.
    Apply le_n_Sn.
    Exact H2.
    Exact H8.
    Intro H4. Rewrite (alist_nth_ad_aapp_1 l l' m H4).
    Elim (interval_split (length l) (length l') n H3). Intro H5. Elim H5. Intros n' H6. Elim H6.
    Intros. Rewrite H8. Rewrite (alist_nth_ad_aapp_2 l l' n' H7). Exact (H1 m n' H4 H7).
    Intro H5. Rewrite (alist_nth_ad_aapp_1 l l' n H5). Exact (H m n H2 H5).
  Qed.

  Lemma alist_nth_ad_semantics : (l:(alist A)) (n:nat) (le (S n) (length l)) ->
      {y:A | (alist_semantics A l (alist_nth_ad n l))=(SOME A y)}.
  Proof.
    Induction l. Intros. Elim (le_Sn_O ? H).
    Intro r. Elim r. Intros a y l0 H. Induction n. Simpl. Intro. Split with y.
    Rewrite (ad_eq_correct a). Reflexivity.
    Intros. Elim (H ? (le_S_n ? ? H1)). Intros y0 H2.
    Elim (sumbool_of_bool (ad_eq a (alist_nth_ad n0 l0))). Intro H3. Split with y.
    Rewrite (ad_eq_complete ? ? H3). Simpl. Rewrite (ad_eq_correct (alist_nth_ad n0 l0)).
    Reflexivity.
    Intro H3. Split with y0. Simpl. Rewrite H3. Assumption.
  Qed.

  Lemma alist_of_Map_nth_ad : (m:(Map A)) (pf:ad->ad)
      (l:(alist A)) l=(MapFold1 A (alist A) (anil A) (aapp A)
                                [a0:ad][y:A](acons A (a0,y) (anil A)) pf m) ->
      	(n:nat) (le (S n) (length l)) -> {a':ad | (alist_nth_ad n l)=(pf a')}.
  Proof.
    Intros. Elim (alist_nth_ad_semantics l n H0). Intros y H1.
    Apply (alist_of_Map_semantics_1_1 A m pf (alist_nth_ad n l) y).
    Rewrite <- H. Assumption.
  Qed.

  Definition ad_monotonic := [pf:ad->ad] (a,a':ad)
      (ad_less a a')=true -> (ad_less (pf a) (pf a'))=true.

  Lemma ad_double_monotonic : (ad_monotonic ad_double).
  Proof.
    Unfold ad_monotonic. Intros. Rewrite ad_less_def_1. Assumption.
  Qed.

  Lemma ad_double_plus_un_monotonic : (ad_monotonic ad_double_plus_un).
  Proof.
    Unfold ad_monotonic. Intros. Rewrite ad_less_def_2. Assumption.
  Qed.

  Lemma ad_comp_monotonic : (pf,pf':ad->ad) (ad_monotonic pf) -> (ad_monotonic pf') ->
      (ad_monotonic [a0:ad] (pf (pf' a0))).
  Proof.
    Unfold ad_monotonic. Intros. Apply H. Apply H0. Exact H1.
  Qed.

  Lemma ad_comp_double_monotonic : (pf:ad->ad) (ad_monotonic pf) ->
      (ad_monotonic [a0:ad] (pf (ad_double a0))).
  Proof.
    Intros. Apply ad_comp_monotonic. Assumption.
    Exact ad_double_monotonic.
  Qed.

  Lemma ad_comp_double_plus_un_monotonic : (pf:ad->ad) (ad_monotonic pf) ->
      (ad_monotonic [a0:ad] (pf (ad_double_plus_un a0))).
  Proof.
    Intros. Apply ad_comp_monotonic. Assumption.
    Exact ad_double_plus_un_monotonic.
  Qed.

  Lemma alist_of_Map_sorts_1 : (m:(Map A)) (pf:ad->ad) (ad_monotonic pf) ->
      (alist_sorted_2 (MapFold1 A (alist A) (anil A) (aapp A)
                                [a:ad][y:A](acons A (a,y) (anil A)) pf m)).
  Proof.
    Induction m. Simpl. Intros. Apply alist_sorted_1_imp_2. Apply alist_sorted_imp_1. Reflexivity.
    Intros. Simpl. Apply alist_sorted_1_imp_2. Apply alist_sorted_imp_1. Reflexivity.
    Intros. Simpl. Apply alist_conc_sorted.
    Exact (H [a0:ad](pf (ad_double a0)) (ad_comp_double_monotonic pf H1)).
    Exact (H0 [a0:ad](pf (ad_double_plus_un a0)) (ad_comp_double_plus_un_monotonic pf H1)).
    Intros. Elim (alist_of_Map_nth_ad m0 [a0:ad](pf (ad_double a0))
       (MapFold1 A (alist A) (anil A) (aapp A)
         [a0:ad][y:A](acons A (a0,y) (anil A))
         [a0:ad](pf (ad_double a0)) m0) (refl_equal ? ?) n H2).
    Intros a H4. Rewrite H4. Elim (alist_of_Map_nth_ad m1 [a0:ad](pf (ad_double_plus_un a0))
       (MapFold1 A (alist A) (anil A) (aapp A)
         [a0:ad][y:A](acons A (a0,y) (anil A))
         [a0:ad](pf (ad_double_plus_un a0)) m1) (refl_equal ? ?) n' H3).
    Intros a' H5. Rewrite H5. Unfold ad_monotonic in H1. Apply H1. Apply ad_less_def_3.
  Qed.

  Lemma alist_of_Map_sorts : (m:(Map A)) (alist_sorted (alist_of_Map A m))=true.
  Proof.
    Intro. Apply alist_sorted_2_imp.
    Exact (alist_of_Map_sorts_1 m [a0:ad]a0 [a,a':ad][p:(ad_less a a')=true]p).
  Qed.

  Lemma alist_of_Map_sorts1 : (m:(Map A)) (alist_sorted_1 (alist_of_Map A m)).
  Proof.
    Intro. Apply alist_sorted_imp_1. Apply alist_of_Map_sorts.
  Qed.
 
  Lemma alist_of_Map_sorts2 : (m:(Map A)) (alist_sorted_2 (alist_of_Map A m)).
  Proof.
    Intro. Apply alist_sorted_1_imp_2. Apply alist_of_Map_sorts1.
  Qed.
 
  Lemma ad_less_total : (a,a':ad) {(ad_less a a')=true}+{(ad_less a' a)=true}+{a=a'}.
  Proof.
    Intro a. Refine (ad_rec_double a [a:ad] (a':ad){(ad_less a a')=true}+{(ad_less a' a)=true}+{a=a'}
                            ? ? ?).
    Intro. Elim (sumbool_of_bool (ad_less ad_z a')). Intro H. Left . Left . Assumption.
    Intro H. Right . Rewrite (ad_z_less_2 a' H). Reflexivity.
    Intros a0 H a'. Refine (ad_rec_double a' [a':ad] {(ad_less (ad_double a0) a')=true}
                                 +{(ad_less a' (ad_double a0))=true}+{(ad_double a0)=a'} ? ? ?).
    Elim (sumbool_of_bool (ad_less ad_z (ad_double a0))). Intro H0. Left . Right . Assumption.
    Intro H0. Right . Exact (ad_z_less_2 ? H0).
    Intros a1 H0. Rewrite ad_less_def_1. Rewrite ad_less_def_1. Elim (H a1). Intro H1.
    Left . Assumption.
    Intro H1. Right . Rewrite H1. Reflexivity.
    Intros a1 H0. Left . Left . Apply ad_less_def_3.
    Intros a0 H a'. Refine (ad_rec_double a' [a':ad] {(ad_less (ad_double_plus_un a0) a')=true}
                                 +{(ad_less a' (ad_double_plus_un a0))=true}
                                 +{(ad_double_plus_un a0)=a'} ? ? ?).
    Left . Right . (Case a0; Reflexivity).
    Intros a1 H0. Left . Right . Apply ad_less_def_3.
    Intros a1 H0. Rewrite ad_less_def_2. Rewrite ad_less_def_2. Elim (H a1). Intro H1.
    Left . Assumption.
    Intro H1. Right . Rewrite H1. Reflexivity.
  Qed.

  Lemma alist_too_low : (l:(alist A)) (a,a':ad) (y:A)
      (ad_less a a')=true -> (alist_sorted_2 (cons (a',y) l)) ->
      	(alist_semantics A (cons (a',y) l) a)=(NONE A).
  Proof.
    Induction l. Intros. Simpl. Elim (sumbool_of_bool (ad_eq a' a)). Intro H1.
    Rewrite (ad_eq_complete ? ? H1) in H. Rewrite (ad_less_not_refl a) in H. Discriminate H.
    Intro H1. Rewrite H1. Reflexivity.
    Intro r. Elim r. Intros a y l0 H a0 a1 y0 H0 H1.
    Change (Case (ad_eq a1 a0) of
               (SOME A y0)
               (alist_semantics A (cons (a,y) l0) a0)
               end)=(NONE A).
    Elim (sumbool_of_bool (ad_eq a1 a0)). Intro H2. Rewrite (ad_eq_complete ? ? H2) in H0.
    Rewrite (ad_less_not_refl a0) in H0. Discriminate H0.
    Intro H2. Rewrite H2. Apply H. Apply ad_less_trans with a':=a1. Assumption.
    Unfold alist_sorted_2 in H1. Apply (H1 (0) (1)). Apply lt_n_Sn.
    Simpl. Apply le_n_S. Apply le_n_S. Apply le_O_n.
    Apply alist_sorted_1_imp_2. Apply alist_sorted_imp_1.
    Cut (alist_sorted (cons (a1,y0) (cons (a,y) l0)))=true. Intro H3.
    Exact (proj2 ? ? (andb_prop ? ? H3)).
    Apply alist_sorted_2_imp. Assumption.
  Qed.

  Lemma alist_semantics_nth_ad : (l:(alist A)) (a:ad) (y:A)
      (alist_semantics A l a)=(SOME A y) ->
      	{n:nat | (le (S n) (length l)) /\ (alist_nth_ad n l)=a}.
  Proof.
    Induction l. Intros. Discriminate H.
    Intro r. Elim r. Intros a y l0 H a0 y0 H0. Simpl in H0. Elim (sumbool_of_bool (ad_eq a a0)).
    Intro H1. Rewrite H1 in H0. Split with O. Split. Simpl. Apply le_n_S. Apply le_O_n.
    Simpl. Exact (ad_eq_complete ? ? H1).
    Intro H1. Rewrite H1 in H0. Elim (H a0 y0 H0). Intros n' H2. Split with (S n'). Split.
    Simpl. Apply le_n_S. Exact (proj1 ? ? H2).
    Exact (proj2 ? ? H2).
  Qed.

  Lemma alist_semantics_tail : (l:(alist A)) (a:ad) (y:A)
      (alist_sorted_2 (cons (a,y) l)) ->
      	(eqm A (alist_semantics A l) [a0:ad] if (ad_eq a a0)
                                             then (NONE A)
					     else (alist_semantics A (cons (a,y) l) a0)).
  Proof.
    Unfold eqm. Intros. Elim (sumbool_of_bool (ad_eq a a0)). Intro H0. Rewrite H0.
    Rewrite <- (ad_eq_complete ? ? H0). Unfold alist_sorted_2 in H.
    Elim (option_sum A (alist_semantics A l a)). Intro H1. Elim H1. Intros y0 H2.
    Elim (alist_semantics_nth_ad l a y0 H2). Intros n H3. Elim H3. Intros.
    Cut (ad_less (alist_nth_ad (0) (cons (a,y) l)) (alist_nth_ad (S n) (cons (a,y) l)))=true.
    Intro. Simpl in H6. Rewrite H5 in H6. Rewrite (ad_less_not_refl a) in H6. Discriminate H6.
    Apply H. Apply lt_O_Sn.
    Simpl. Apply le_n_S. Assumption.
    Trivial.
    Intro H0. Simpl. Rewrite H0. Reflexivity.
  Qed.

  Lemma alist_semantics_same_tail : (l,l':(alist A)) (a:ad) (y:A)
      (alist_sorted_2 (cons (a,y) l)) -> (alist_sorted_2 (cons (a,y) l')) ->
      	(eqm A (alist_semantics A (cons (a,y) l)) (alist_semantics A (cons (a,y) l'))) ->
	  (eqm A (alist_semantics A l) (alist_semantics A l')).
  Proof.
    Unfold eqm. Intros. Rewrite (alist_semantics_tail ? ? ? H a0).
    Rewrite (alist_semantics_tail ? ? ? H0 a0). Case (ad_eq a a0). Reflexivity.
    Exact (H1 a0).
  Qed.

  Lemma alist_sorted_tail : (l:(alist A)) (a:ad) (y:A)
      (alist_sorted_2 (cons (a,y) l)) -> (alist_sorted_2 l).
  Proof.
    Unfold alist_sorted_2. Intros. Apply (H (S m) (S n)). Apply lt_n_S. Assumption.
    Simpl. Apply le_n_S. Assumption.
  Qed.

  Lemma alist_canonical : (l,l':(alist A))
      (eqm A (alist_semantics A l) (alist_semantics A l')) ->
      	(alist_sorted_2 l) -> (alist_sorted_2 l') -> l=l'.
  Proof.
    Unfold eqm. Induction l. Induction l'. Trivial.
    Intro r. Elim r. Intros a y l0 H H0 H1 H2. Simpl in H0.
    Cut (NONE A)=(Case (ad_eq a a) of (SOME A y)
                           (alist_semantics A l0 a)
                           end).
    Rewrite (ad_eq_correct a). Intro. Discriminate H3.
    Exact (H0 a).
    Intro r. Elim r. Intros a y l0 H. Induction l'. Intros. Simpl in H0.
    Cut (Case (ad_eq a a) of (SOME A y)
                         (alist_semantics A l0 a)
                         end)=(NONE A).
    Rewrite (ad_eq_correct a). Intro. Discriminate H3.
    Exact (H0 a).
    Intro r'. Elim r'. Intros a' y' l'0 H0 H1 H2 H3. Elim (ad_less_total a a'). Intro H4.
    Elim H4. Intro H5.
    Cut (alist_semantics A (cons (a,y) l0) a)=(alist_semantics A (cons (a',y') l'0) a).
    Intro. Rewrite (alist_too_low l'0 a a' y' H5 H3) in H6. Simpl in H6.
    Rewrite (ad_eq_correct a) in H6. Discriminate H6.
    Exact (H1 a).
    Intro H5. Cut (alist_semantics A (cons (a,y) l0) a')=(alist_semantics A (cons (a',y') l'0) a').
    Intro. Rewrite (alist_too_low l0 a' a y H5 H2) in H6. Simpl in H6.
    Rewrite (ad_eq_correct a') in H6. Discriminate H6.
    Exact (H1 a').
    Intro H4. Rewrite H4.
    Cut (alist_semantics A (cons (a,y) l0) a)=(alist_semantics A (cons (a',y') l'0) a).
    Intro. Simpl in H5. Rewrite H4 in H5. Rewrite (ad_eq_correct a') in H5. Inversion H5.
    Rewrite H4 in H1. Rewrite H7 in H1. Cut l0=l'0. Intro. Rewrite H6. Reflexivity.
    Apply H. Rewrite H4 in H2. Rewrite H7 in H2.
    Exact (alist_semantics_same_tail l0 l'0 a' y' H2 H3 H1).
    Exact (alist_sorted_tail ? ? ? H2).
    Exact (alist_sorted_tail ? ? ? H3).
    Exact (H1 a).
  Qed.

End LSort.

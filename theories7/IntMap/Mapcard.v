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
Require Mapaxioms.
Require Mapiter.
Require Fset.
Require Mapsubset.
Require PolyList.
Require Lsort.
Require Peano_dec.

Section MapCard.

  Variable A, B : Set.

  Lemma MapCard_M0 : (MapCard A (M0 A))=O.
  Proof.
    Trivial.
  Qed.

  Lemma MapCard_M1 : (a:ad) (y:A) (MapCard A (M1 A a y))=(1).
  Proof.
    Trivial.
  Qed.

  Lemma MapCard_is_O : (m:(Map A)) (MapCard A m)=O -> 
      (a:ad) (MapGet A m a)=(NONE A).
  Proof.
    Induction m. Trivial.
    Intros a y H. Discriminate H.
    Intros. Simpl in H1. Elim (plus_is_O ? ? H1). Intros. Rewrite (MapGet_M2_bit_0_if A m0 m1 a).
    Case (ad_bit_0 a). Apply H0. Assumption.
    Apply H. Assumption.
  Qed.

  Lemma MapCard_is_not_O : (m:(Map A)) (a:ad) (y:A) (MapGet A m a)=(SOME A y) ->
      {n:nat | (MapCard A m)=(S n)}.
  Proof.
    Induction m. Intros. Discriminate H.
    Intros a y a0 y0 H. Simpl in H. Elim (sumbool_of_bool (ad_eq a a0)). Intro H0. Split with O.
    Reflexivity.
    Intro H0. Rewrite H0 in H. Discriminate H.
    Intros. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H2.
    Rewrite (MapGet_M2_bit_0_1 A a H2 m0 m1) in H1. Elim (H0 (ad_div_2 a) y H1). Intros n H3.
    Simpl. Rewrite H3. Split with (plus (MapCard A m0) n).
    Rewrite <- (plus_Snm_nSm (MapCard A m0) n). Reflexivity.
    Intro H2. Rewrite (MapGet_M2_bit_0_0 A a H2 m0 m1) in H1. Elim (H (ad_div_2 a) y H1).
    Intros n H3. Simpl. Rewrite H3. Split with (plus n (MapCard A m1)). Reflexivity.
  Qed.

  Lemma MapCard_is_one : (m:(Map A)) (MapCard A m)=(1) ->
      {a:ad & {y:A | (MapGet A m a)=(SOME A y)}}.
  Proof.
    Induction m. Intro. Discriminate H.
    Intros a y H. Split with a. Split with y. Apply M1_semantics_1.
    Intros. Simpl in H1. Elim (plus_is_one (MapCard A m0) (MapCard A m1) H1).
    Intro H2. Elim H2. Intros. Elim (H0 H4). Intros a H5. Split with (ad_double_plus_un a).
    Rewrite (MapGet_M2_bit_0_1 A ? (ad_double_plus_un_bit_0 a) m0 m1).
    Rewrite ad_double_plus_un_div_2. Exact H5.
    Intro H2. Elim H2. Intros. Elim (H H3). Intros a H5. Split with (ad_double a).
    Rewrite (MapGet_M2_bit_0_0 A ? (ad_double_bit_0 a) m0 m1).
    Rewrite ad_double_div_2. Exact H5.
  Qed.

  Lemma MapCard_is_one_unique : (m:(Map A)) (MapCard A m)=(1) -> (a,a':ad) (y,y':A) 
      (MapGet A m a)=(SOME A y) -> (MapGet A m a')=(SOME A y') ->
        a=a' /\ y=y'.
  Proof.
    Induction m. Intro. Discriminate H.
    Intros. Elim (sumbool_of_bool (ad_eq a a1)). Intro H2. Rewrite (ad_eq_complete ? ? H2) in H0.
    Rewrite (M1_semantics_1 A a1 a0) in H0. Inversion H0. Elim (sumbool_of_bool (ad_eq a a')).
    Intro H5. Rewrite (ad_eq_complete ? ? H5) in H1. Rewrite (M1_semantics_1 A a' a0) in H1.
    Inversion H1. Rewrite <- (ad_eq_complete ? ? H2). Rewrite <- (ad_eq_complete ? ? H5).
    Rewrite <- H4. Rewrite <- H6. (Split; Reflexivity).
    Intro H5. Rewrite (M1_semantics_2 A a a' a0 H5) in H1. Discriminate H1.
    Intro H2. Rewrite (M1_semantics_2 A a a1 a0 H2) in H0. Discriminate H0.
    Intros. Simpl in H1. Elim (plus_is_one ? ? H1). Intro H4. Elim H4. Intros.
    Rewrite (MapGet_M2_bit_0_if A m0 m1 a) in H2. Elim (sumbool_of_bool (ad_bit_0 a)).
    Intro H7. Rewrite H7 in H2. Rewrite (MapGet_M2_bit_0_if A m0 m1 a') in H3.
    Elim (sumbool_of_bool (ad_bit_0 a')). Intro H8. Rewrite H8 in H3. Elim (H0 H6 ? ? ? ? H2 H3).
    Intros. Split. Rewrite <- (ad_div_2_double_plus_un a H7).
    Rewrite <- (ad_div_2_double_plus_un a' H8). Rewrite H9. Reflexivity.
    Assumption.
    Intro H8. Rewrite H8 in H3. Rewrite (MapCard_is_O m0 H5 (ad_div_2 a')) in H3.
    Discriminate H3.
    Intro H7. Rewrite H7 in H2. Rewrite (MapCard_is_O m0 H5 (ad_div_2 a)) in H2.
    Discriminate H2.
    Intro H4. Elim H4. Intros. Rewrite (MapGet_M2_bit_0_if A m0 m1 a) in H2.
    Elim (sumbool_of_bool (ad_bit_0 a)). Intro H7. Rewrite H7 in H2.
    Rewrite (MapCard_is_O m1 H6 (ad_div_2 a)) in H2. Discriminate H2.
    Intro H7. Rewrite H7 in H2. Rewrite (MapGet_M2_bit_0_if A m0 m1 a') in H3.
    Elim (sumbool_of_bool (ad_bit_0 a')). Intro H8. Rewrite H8 in H3.
    Rewrite (MapCard_is_O m1 H6 (ad_div_2 a')) in H3. Discriminate H3.
    Intro H8. Rewrite H8 in H3. Elim (H H5 ? ? ? ? H2 H3). Intros. Split.
    Rewrite <- (ad_div_2_double a H7). Rewrite <- (ad_div_2_double a' H8).
    Rewrite H9. Reflexivity.
    Assumption.
  Qed.

  Lemma length_as_fold : (C:Set) (l:(list C)) 
      (length l)=(fold_right [_:C][n:nat](S n) O l).
  Proof.
    Induction l. Reflexivity.
    Intros. Simpl. Rewrite H. Reflexivity.
  Qed.

  Lemma length_as_fold_2 : (l:(alist A)) 
      (length l)=(fold_right [r:ad*A][n:nat]let (a,y)=r in (plus (1) n) O l).
  Proof.
    Induction l. Reflexivity.
    Intros. Simpl. Rewrite H. (Elim a; Reflexivity).
  Qed.

  Lemma MapCard_as_Fold_1 : (m:(Map A)) (pf:ad->ad)
      (MapCard A m)=(MapFold1 A nat O plus [_:ad][_:A](1) pf m).
  Proof.
    Induction m. Trivial.
    Trivial.
    Intros. Simpl. Rewrite <- (H [a0:ad](pf (ad_double a0))).
    Rewrite <- (H0 [a0:ad](pf (ad_double_plus_un a0))). Reflexivity.
  Qed.

  Lemma MapCard_as_Fold : 
      (m:(Map A)) (MapCard A m)=(MapFold A nat O plus [_:ad][_:A](1) m).
  Proof.
    Intro. Exact (MapCard_as_Fold_1 m [a0:ad]a0).
  Qed.
 
  Lemma MapCard_as_length : (m:(Map A)) (MapCard A m)=(length (alist_of_Map A m)).
  Proof.
    Intro. Rewrite MapCard_as_Fold. Rewrite length_as_fold_2.
    Apply MapFold_as_fold with op:=plus neutral:=O f:=[_:ad][_:A](1). Exact plus_assoc_r.
    Trivial.
    Intro. Rewrite <- plus_n_O. Reflexivity.
  Qed.

  Lemma MapCard_Put1_equals_2 : (p:positive) (a,a':ad) (y,y':A)
      (MapCard A (MapPut1 A a y a' y' p))=(2).
  Proof.
    Induction p. Intros. Simpl. (Case (ad_bit_0 a); Reflexivity).
    Intros. Simpl. Case (ad_bit_0 a). Exact (H (ad_div_2 a) (ad_div_2 a') y y').
    Simpl. Rewrite <- plus_n_O. Exact (H (ad_div_2 a) (ad_div_2 a') y y').
    Intros. Simpl. (Case (ad_bit_0 a); Reflexivity).
  Qed.

  Lemma MapCard_Put_sum : (m,m':(Map A)) (a:ad) (y:A) (n,n':nat)
      m'=(MapPut A m a y) -> n=(MapCard A m) -> n'=(MapCard A m') ->
        {n'=n}+{n'=(S n)}.
  Proof.
    Induction m. Simpl. Intros. Rewrite H in H1. Simpl in H1. Right .
    Rewrite H0. Rewrite H1. Reflexivity.
    Intros a y m' a0 y0 n n' H H0 H1. Simpl in H. Elim (ad_sum (ad_xor a a0)). Intro H2.
    Elim H2. Intros p H3. Rewrite H3 in H. Rewrite H in H1.
    Rewrite (MapCard_Put1_equals_2 p a a0 y y0) in H1. Simpl in H0. Right .
    Rewrite H0. Rewrite H1. Reflexivity.
    Intro H2. Rewrite H2 in H. Rewrite H in H1. Simpl in H1. Simpl in H0. Left .
    Rewrite H0. Rewrite H1. Reflexivity.
    Intros. Simpl in H2. Rewrite (MapPut_semantics_3_1 A m0 m1 a y) in H1.
    Elim (sumbool_of_bool (ad_bit_0 a)). Intro H4. Rewrite H4 in H1.
    Elim (H0 (MapPut A m1 (ad_div_2 a) y) (ad_div_2 a) y (MapCard A m1)
       (MapCard A (MapPut A m1 (ad_div_2 a) y)) (refl_equal ? ?)
       (refl_equal ? ?) (refl_equal ? ?)).
    Intro H5. Rewrite H1 in H3. Simpl in H3. Rewrite H5 in H3. Rewrite <- H2 in H3. Left .
    Assumption.
    Intro H5. Rewrite H1 in H3. Simpl in H3. Rewrite H5 in H3.
    Rewrite <- (plus_Snm_nSm (MapCard A m0) (MapCard A m1)) in H3.
    Simpl in H3. Rewrite <- H2 in H3. Right . Assumption.
    Intro H4. Rewrite H4 in H1.
    Elim (H (MapPut A m0 (ad_div_2 a) y) (ad_div_2 a) y (MapCard A m0)
       (MapCard A (MapPut A m0 (ad_div_2 a) y)) (refl_equal ? ?)
       (refl_equal ? ?) (refl_equal ? ?)).
    Intro H5. Rewrite H1 in H3. Simpl in H3. Rewrite H5 in H3. Rewrite <- H2 in H3.
    Left . Assumption.
    Intro H5. Rewrite H1 in H3. Simpl in H3. Rewrite H5 in H3. Simpl in H3. Rewrite <- H2 in H3.
    Right . Assumption.
  Qed.

  Lemma MapCard_Put_lb : (m:(Map A)) (a:ad) (y:A)
      (ge (MapCard A (MapPut A m a y)) (MapCard A m)).
  Proof.
    Unfold ge. Intros.
    Elim (MapCard_Put_sum m (MapPut A m a y) a y (MapCard A m)
       (MapCard A (MapPut A m a y)) (refl_equal ? ?) (refl_equal ? ?)
       (refl_equal ? ?)).
    Intro H. Rewrite H. Apply le_n.
    Intro H. Rewrite H. Apply le_n_Sn.
  Qed.

  Lemma MapCard_Put_ub : (m:(Map A)) (a:ad) (y:A)
      (le (MapCard A (MapPut A m a y)) (S (MapCard A m))).
  Proof.
    Intros.
    Elim (MapCard_Put_sum m (MapPut A m a y) a y (MapCard A m)
       (MapCard A (MapPut A m a y)) (refl_equal ? ?) (refl_equal ? ?)
       (refl_equal ? ?)).
    Intro H. Rewrite H. Apply le_n_Sn.
    Intro H. Rewrite H. Apply le_n.
  Qed.

  Lemma MapCard_Put_1 : (m:(Map A)) (a:ad) (y:A)
      (MapCard A (MapPut A m a y))=(MapCard A m) -> 
        {y:A | (MapGet A m a)=(SOME A y)}.
  Proof.
    Induction m. Intros. Discriminate H.
    Intros a y a0 y0 H. Simpl in H. Elim (ad_sum (ad_xor a a0)). Intro H0. Elim H0.
    Intros p H1. Rewrite H1 in H. Rewrite (MapCard_Put1_equals_2 p a a0 y y0) in H.
    Discriminate H.
    Intro H0. Rewrite H0 in H. Rewrite (ad_xor_eq ? ? H0). Split with y. Apply M1_semantics_1.
    Intros. Rewrite (MapPut_semantics_3_1 A m0 m1 a y) in H1. Elim (sumbool_of_bool (ad_bit_0 a)).
    Intro H2. Rewrite H2 in H1. Simpl in H1. Elim (H0 (ad_div_2 a) y (simpl_plus_l ? ? ? H1)).
    Intros y0 H3. Split with y0. Rewrite <- H3. Exact (MapGet_M2_bit_0_1 A a H2 m0 m1).
    Intro H2. Rewrite H2 in H1. Simpl in H1.
    Rewrite (plus_sym (MapCard A (MapPut A m0 (ad_div_2 a) y)) (MapCard A m1)) in H1.
    Rewrite (plus_sym (MapCard A m0) (MapCard A m1)) in H1.
    Elim (H (ad_div_2 a) y (simpl_plus_l ? ? ? H1)). Intros y0 H3. Split with y0.
    Rewrite <- H3. Exact (MapGet_M2_bit_0_0 A a H2 m0 m1).
  Qed.

  Lemma MapCard_Put_2 : (m:(Map A)) (a:ad) (y:A)
      (MapCard A (MapPut A m a y))=(S (MapCard A m)) -> (MapGet A m a)=(NONE A).
  Proof.
    Induction m. Trivial.
    Intros. Simpl in H. Elim (sumbool_of_bool (ad_eq a a1)). Intro H0.
    Rewrite (ad_eq_complete ? ? H0) in H. Rewrite (ad_xor_nilpotent a1) in H. Discriminate H.
    Intro H0. Exact (M1_semantics_2 A a a1 a0 H0).
    Intros. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H2.
    Rewrite (MapGet_M2_bit_0_1 A a H2 m0 m1). Apply (H0 (ad_div_2 a) y).
    Apply simpl_plus_l with n:=(MapCard A m0).
    Rewrite <- (plus_Snm_nSm (MapCard A m0) (MapCard A m1)). Simpl in H1. Simpl. Rewrite <- H1.
    Clear H1.
    NewInduction a. Discriminate H2.
    NewInduction p. Reflexivity.
    Discriminate H2.
    Reflexivity.
    Intro H2. Rewrite (MapGet_M2_bit_0_0 A a H2 m0 m1). Apply (H (ad_div_2 a) y).
    Cut (plus (MapCard A (MapPut A m0 (ad_div_2 a) y)) (MapCard A m1))
         =(plus (S (MapCard A m0)) (MapCard A m1)).
    Intro. Rewrite (plus_sym (MapCard A (MapPut A m0 (ad_div_2 a) y)) (MapCard A m1)) in H3.
    Rewrite (plus_sym (S (MapCard A m0)) (MapCard A m1)) in H3. Exact (simpl_plus_l ? ? ? H3).
    Simpl. Simpl in H1. Rewrite <- H1. NewInduction a. Trivial.
    NewInduction p. Discriminate H2.
    Reflexivity.
    Discriminate H2.
  Qed.

  Lemma MapCard_Put_1_conv : (m:(Map A)) (a:ad) (y,y':A)
      (MapGet A m a)=(SOME A y) -> (MapCard A (MapPut A m a y'))=(MapCard A m).
  Proof.
    Intros.
    Elim (MapCard_Put_sum m (MapPut A m a y') a y' (MapCard A m)
           (MapCard A (MapPut A m a y')) (refl_equal ? ?) (refl_equal ? ?)
           (refl_equal ? ?)).
    Trivial.
    Intro H0. Rewrite (MapCard_Put_2 m a y' H0) in H. Discriminate H.
  Qed.

  Lemma MapCard_Put_2_conv : (m:(Map A)) (a:ad) (y:A)
      (MapGet A m a)=(NONE A) -> (MapCard A (MapPut A m a y))=(S (MapCard A m)).
  Proof.
    Intros.
    Elim (MapCard_Put_sum m (MapPut A m a y) a y (MapCard A m)
           (MapCard A (MapPut A m a y)) (refl_equal ? ?) (refl_equal ? ?)
           (refl_equal ? ?)).
    Intro H0. Elim (MapCard_Put_1 m a y H0). Intros y' H1. Rewrite H1 in H. Discriminate H.
    Trivial.
  Qed.

  Lemma MapCard_ext : (m,m':(Map A))
      (eqm A (MapGet A m) (MapGet A m')) -> (MapCard A m)=(MapCard A m').
  Proof.
    Unfold eqm. Intros. Rewrite (MapCard_as_length m). Rewrite (MapCard_as_length m').
    Rewrite (alist_canonical A (alist_of_Map A m) (alist_of_Map A m')). Reflexivity.
    Unfold eqm. Intro. Rewrite (Map_of_alist_semantics A (alist_of_Map A m) a).
    Rewrite (Map_of_alist_semantics A (alist_of_Map A m') a). Rewrite (Map_of_alist_of_Map A m' a).
    Rewrite (Map_of_alist_of_Map A m a). Exact (H a).
    Apply alist_of_Map_sorts2.
    Apply alist_of_Map_sorts2.
  Qed.

  Lemma MapCard_Dom : (m:(Map A)) (MapCard A m)=(MapCard unit (MapDom A m)).
  Proof.
    (Induction m; Trivial). Intros. Simpl. Rewrite H. Rewrite H0. Reflexivity.
  Qed.

  Lemma MapCard_Dom_Put_behind : (m:(Map A)) (a:ad) (y:A)
      (MapDom A (MapPut_behind A m a y))=(MapDom A (MapPut A m a y)).
  Proof.
    Induction m. Trivial.
    Intros a y a0 y0. Simpl. Elim (ad_sum (ad_xor a a0)). Intro H. Elim H.
    Intros p H0. Rewrite H0. Reflexivity.
    Intro H. Rewrite H. Rewrite (ad_xor_eq ? ? H). Reflexivity.
    Intros. Simpl. Elim (ad_sum a). Intro H1. Elim H1. Intros p H2. Rewrite H2. Case p.
    Intro p0. Simpl. Rewrite H0. Reflexivity.
    Intro p0. Simpl. Rewrite H. Reflexivity.
    Simpl. Rewrite H0. Reflexivity.
    Intro H1. Rewrite H1. Simpl. Rewrite H. Reflexivity.
  Qed.

  Lemma MapCard_Put_behind_Put : (m:(Map A)) (a:ad) (y:A)
      (MapCard A (MapPut_behind A m a y))=(MapCard A (MapPut A m a y)).
  Proof.
    Intros. Rewrite MapCard_Dom. Rewrite MapCard_Dom. Rewrite MapCard_Dom_Put_behind.
    Reflexivity.
  Qed.

  Lemma MapCard_Put_behind_sum : (m,m':(Map A)) (a:ad) (y:A) (n,n':nat)
      m'=(MapPut_behind A m a y) -> n=(MapCard A m) -> n'=(MapCard A m') ->
        {n'=n}+{n'=(S n)}.
  Proof.
    Intros. (Apply (MapCard_Put_sum m (MapPut A m a y) a y n n'); Trivial).
    Rewrite <- MapCard_Put_behind_Put. Rewrite <- H. Assumption.
  Qed.

  Lemma MapCard_makeM2 : (m,m':(Map A))
      (MapCard A (makeM2 A m m'))=(plus (MapCard A m) (MapCard A m')).
  Proof.
    Intros. Rewrite (MapCard_ext ? ? (makeM2_M2 A m m')). Reflexivity.
  Qed.
 
  Lemma MapCard_Remove_sum : (m,m':(Map A)) (a:ad) (n,n':nat)
      m'=(MapRemove A m a) -> n=(MapCard A m) -> n'=(MapCard A m') ->
        {n=n'}+{n=(S n')}.
  Proof.
    Induction m. Simpl. Intros. Rewrite H in H1. Simpl in H1. Left . Rewrite H1. Assumption.
    Simpl. Intros. Elim (sumbool_of_bool (ad_eq a a1)). Intro H2. Rewrite H2 in H.
    Rewrite H in H1. Simpl in H1. Right . Rewrite H1. Assumption.
    Intro H2. Rewrite H2 in H. Rewrite H in H1. Simpl in H1. Left . Rewrite H1. Assumption.
    Intros. Simpl in H1. Simpl in H2. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H4.
    Rewrite H4 in H1. Rewrite H1 in H3.
    Rewrite (MapCard_makeM2 m0 (MapRemove A m1 (ad_div_2 a))) in H3.
    Elim (H0 (MapRemove A m1 (ad_div_2 a)) (ad_div_2 a) (MapCard A m1)
             (MapCard A (MapRemove A m1 (ad_div_2 a))) (refl_equal ? ?)
             (refl_equal ? ?) (refl_equal ? ?)).
    Intro H5. Rewrite H5 in H2. Left . Rewrite H3. Exact H2.
    Intro H5. Rewrite H5 in H2.
    Rewrite <- (plus_Snm_nSm (MapCard A m0) (MapCard A (MapRemove A m1 (ad_div_2 a)))) in H2.
    Right . Rewrite H3. Exact H2.
    Intro H4. Rewrite H4 in H1. Rewrite H1 in H3.
    Rewrite (MapCard_makeM2 (MapRemove A m0 (ad_div_2 a)) m1) in H3.
    Elim (H (MapRemove A m0 (ad_div_2 a)) (ad_div_2 a) (MapCard A m0)
            (MapCard A (MapRemove A m0 (ad_div_2 a))) (refl_equal ? ?)
            (refl_equal ? ?) (refl_equal ? ?)).
    Intro H5. Rewrite H5 in H2. Left . Rewrite H3. Exact H2.
    Intro H5. Rewrite H5 in H2. Right . Rewrite H3. Exact H2.
  Qed.

  Lemma MapCard_Remove_ub : (m:(Map A)) (a:ad)
      (le (MapCard A (MapRemove A m a)) (MapCard A m)).
  Proof.
    Intros.
    Elim (MapCard_Remove_sum m (MapRemove A m a) a (MapCard A m)
           (MapCard A (MapRemove A m a)) (refl_equal ? ?) (refl_equal ? ?)
           (refl_equal ? ?)).
    Intro H. Rewrite H. Apply le_n.
    Intro H. Rewrite H. Apply le_n_Sn.
  Qed.

  Lemma MapCard_Remove_lb : (m:(Map A)) (a:ad)
      (ge (S (MapCard A (MapRemove A m a))) (MapCard A m)).
  Proof.
    Unfold ge. Intros.
    Elim (MapCard_Remove_sum m (MapRemove A m a) a (MapCard A m)
           (MapCard A (MapRemove A m a)) (refl_equal ? ?) (refl_equal ? ?)
           (refl_equal ? ?)).
    Intro H. Rewrite H. Apply le_n_Sn.
    Intro H. Rewrite H. Apply le_n.
  Qed.

  Lemma MapCard_Remove_1 : (m:(Map A)) (a:ad)
      (MapCard A (MapRemove A m a))=(MapCard A m) -> (MapGet A m a)=(NONE A).
  Proof.
    Induction m. Trivial.
    Simpl. Intros a y a0 H. Elim (sumbool_of_bool (ad_eq a a0)). Intro H0.
    Rewrite H0 in H. Discriminate H.
    Intro H0. Rewrite H0. Reflexivity.
    Intros. Simpl in H1. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H2. Rewrite H2 in H1.
    Rewrite (MapCard_makeM2 m0 (MapRemove A m1 (ad_div_2 a))) in H1.
    Rewrite (MapGet_M2_bit_0_1 A a H2 m0 m1). Apply H0. Exact (simpl_plus_l ? ? ? H1).
    Intro H2. Rewrite H2 in H1.
    Rewrite (MapCard_makeM2 (MapRemove A m0 (ad_div_2 a)) m1) in H1.
    Rewrite (MapGet_M2_bit_0_0 A a H2 m0 m1). Apply H.
    Rewrite (plus_sym (MapCard A (MapRemove A m0 (ad_div_2 a))) (MapCard A m1)) in H1.
    Rewrite (plus_sym (MapCard A m0) (MapCard A m1)) in H1. Exact (simpl_plus_l ? ? ? H1).
  Qed.

  Lemma MapCard_Remove_2 : (m:(Map A)) (a:ad)
      (S (MapCard A (MapRemove A m a)))=(MapCard A m) -> 
        {y:A | (MapGet A m a)=(SOME A y)}.
  Proof.
    Induction m. Intros. Discriminate H.
    Intros a y a0 H. Simpl in H. Elim (sumbool_of_bool (ad_eq a a0)). Intro H0.
    Rewrite (ad_eq_complete ? ? H0). Split with y. Exact (M1_semantics_1 A a0 y).
    Intro H0. Rewrite H0 in H. Discriminate H.
    Intros. Simpl in H1. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H2. Rewrite H2 in H1.
    Rewrite (MapCard_makeM2 m0 (MapRemove A m1 (ad_div_2 a))) in H1.
    Rewrite (MapGet_M2_bit_0_1 A a H2 m0 m1). Apply H0.
    Change (plus (S (MapCard A m0)) (MapCard A (MapRemove A m1 (ad_div_2 a))))
            =(plus (MapCard A m0) (MapCard A m1)) in H1.
    Rewrite (plus_Snm_nSm (MapCard A m0) (MapCard A (MapRemove A m1 (ad_div_2 a)))) in H1.
    Exact (simpl_plus_l ? ? ? H1).
    Intro H2. Rewrite H2 in H1. Rewrite (MapGet_M2_bit_0_0 A a H2 m0 m1). Apply H.
    Rewrite (MapCard_makeM2 (MapRemove A m0 (ad_div_2 a)) m1) in H1.
    Change (plus (S (MapCard A (MapRemove A m0 (ad_div_2 a)))) (MapCard A m1))
      	   =(plus (MapCard A m0) (MapCard A m1)) in H1.
    Rewrite (plus_sym (S (MapCard A (MapRemove A m0 (ad_div_2 a)))) (MapCard A m1)) in H1.
    Rewrite (plus_sym (MapCard A m0) (MapCard A m1)) in H1. Exact (simpl_plus_l ? ? ? H1).
  Qed.

  Lemma MapCard_Remove_1_conv : (m:(Map A)) (a:ad)
      (MapGet A m a)=(NONE A) -> (MapCard A (MapRemove A m a))=(MapCard A m).
  Proof.
    Intros.
    Elim (MapCard_Remove_sum m (MapRemove A m a) a (MapCard A m)
           (MapCard A (MapRemove A m a)) (refl_equal ? ?) (refl_equal ? ?)
           (refl_equal ? ?)).
    Intro H0. Rewrite H0. Reflexivity.
    Intro H0. Elim (MapCard_Remove_2 m a (sym_eq ? ? ? H0)). Intros y H1. Rewrite H1 in H.
    Discriminate H.
  Qed.

  Lemma MapCard_Remove_2_conv : (m:(Map A)) (a:ad) (y:A)
      (MapGet A m a)=(SOME A y) -> 
        (S (MapCard A (MapRemove A m a)))=(MapCard A m).
  Proof.
    Intros.
    Elim (MapCard_Remove_sum m (MapRemove A m a) a (MapCard A m)
           (MapCard A (MapRemove A m a)) (refl_equal ? ?) (refl_equal ? ?)
           (refl_equal ? ?)).
    Intro H0. Rewrite (MapCard_Remove_1 m a (sym_eq ? ? ? H0)) in H. Discriminate H.
    Intro H0. Rewrite H0. Reflexivity.
  Qed.

  Lemma MapMerge_Restr_Card : (m,m':(Map A))
      (plus (MapCard A m) (MapCard A m'))=
      (plus (MapCard A (MapMerge A m m')) (MapCard A (MapDomRestrTo A A m m'))).
  Proof.
    Induction m. Simpl. Intro. Apply plus_n_O.
    Simpl. Intros a y m'. Elim (option_sum A (MapGet A m' a)). Intro H. Elim H. Intros y0 H0.
    Rewrite H0. Rewrite MapCard_Put_behind_Put. Rewrite (MapCard_Put_1_conv m' a y0 y H0).
    Simpl. Rewrite <- plus_Snm_nSm. Apply plus_n_O.
    Intro H. Rewrite H. Rewrite MapCard_Put_behind_Put. Rewrite (MapCard_Put_2_conv m' a y H).
    Apply plus_n_O.
    Intros.
    Change (plus (plus (MapCard A m0) (MapCard A m1)) (MapCard A m'))
            =(plus (MapCard A (MapMerge A (M2 A m0 m1) m'))
               (MapCard A (MapDomRestrTo A A (M2 A m0 m1) m'))).
    Elim m'. Reflexivity.
    Intros a y. Unfold MapMerge. Unfold MapDomRestrTo.
    Elim (option_sum A (MapGet A (M2 A m0 m1) a)). Intro H1. Elim H1. Intros y0 H2. Rewrite H2.
    Rewrite (MapCard_Put_1_conv (M2 A m0 m1) a y0 y H2). Reflexivity.
    Intro H1. Rewrite H1. Rewrite (MapCard_Put_2_conv (M2 A m0 m1) a y H1). Simpl.
    Rewrite <- (plus_Snm_nSm (plus (MapCard A m0) (MapCard A m1)) O). Reflexivity.
    Intros. Simpl.
    Rewrite (plus_permute_2_in_4 (MapCard A m0) (MapCard A m1) (MapCard A m2) (MapCard A m3)).
    Rewrite (H m2). Rewrite (H0 m3).
    Rewrite (MapCard_makeM2 (MapDomRestrTo A A m0 m2) (MapDomRestrTo A A m1 m3)).
    Apply plus_permute_2_in_4.
  Qed.

  Lemma MapMerge_disjoint_Card : (m,m':(Map A)) (MapDisjoint A A m m') ->
      	(MapCard A (MapMerge A m m'))=(plus (MapCard A m) (MapCard A m')).
  Proof.
    Intros. Rewrite (MapMerge_Restr_Card m m').
    Rewrite (MapCard_ext ? ? (MapDisjoint_imp_2 ? ? ? ? H)). Apply plus_n_O.
  Qed.

  Lemma MapSplit_Card : (m:(Map A)) (m':(Map B))
      (MapCard A m)=(plus (MapCard A (MapDomRestrTo A B m m'))
                          (MapCard A (MapDomRestrBy A B m m'))).
  Proof.
    Intros. Rewrite (MapCard_ext ? ? (MapDom_Split_1 A B m m')). Apply MapMerge_disjoint_Card.
    Apply MapDisjoint_2_imp. Unfold MapDisjoint_2. Apply MapDom_Split_3.
  Qed.

  Lemma MapMerge_Card_ub : (m,m':(Map A))
      (le (MapCard A (MapMerge A m m')) (plus (MapCard A m) (MapCard A m'))).
  Proof.
    Intros. Rewrite MapMerge_Restr_Card. Apply le_plus_l.
  Qed.

  Lemma MapDomRestrTo_Card_ub_l : (m:(Map A)) (m':(Map B))
      (le (MapCard A (MapDomRestrTo A B m m')) (MapCard A m)).
  Proof.
    Intros. Rewrite (MapSplit_Card m m'). Apply le_plus_l.
  Qed.

  Lemma MapDomRestrBy_Card_ub_l : (m:(Map A)) (m':(Map B))
      (le (MapCard A (MapDomRestrBy A B m m')) (MapCard A m)).
  Proof.
    Intros. Rewrite (MapSplit_Card m m'). Apply le_plus_r.
  Qed.

  Lemma MapMerge_Card_disjoint : (m,m':(Map A))
      (MapCard A (MapMerge A m m'))=(plus (MapCard A m) (MapCard A m')) ->
        (MapDisjoint A A m m').
  Proof.
    Induction m. Intros. Apply Map_M0_disjoint.
    Simpl. Intros. Rewrite (MapCard_Put_behind_Put m' a a0) in H. Unfold MapDisjoint in_dom.
    Simpl. Intros. Elim (sumbool_of_bool (ad_eq a a1)). Intro H2.
    Rewrite (ad_eq_complete ? ? H2) in H. Rewrite (MapCard_Put_2 m' a1 a0 H) in H1.
    Discriminate H1.
    Intro H2. Rewrite H2 in H0. Discriminate H0.
    Induction m'. Intros. Apply Map_disjoint_M0.
    Intros a y H1. Rewrite <- (MapCard_ext ? ? (MapPut_as_Merge A (M2 A m0 m1) a y)) in H1.
    Unfold 3 MapCard in H1. Rewrite <- (plus_Snm_nSm (MapCard A (M2 A m0 m1)) O) in H1.
    Rewrite <- (plus_n_O (S (MapCard A (M2 A m0 m1)))) in H1. Unfold MapDisjoint in_dom.
    Unfold 2 MapGet. Intros. Elim (sumbool_of_bool (ad_eq a a0)). Intro H4.
    Rewrite <- (ad_eq_complete ? ? H4) in H2. Rewrite (MapCard_Put_2 ? ? ? H1) in H2.
    Discriminate H2.
    Intro H4. Rewrite H4 in H3. Discriminate H3.
    Intros. Unfold MapDisjoint. Intros. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H6.
    Unfold MapDisjoint in H0. Apply H0 with m':=m3 a:=(ad_div_2 a). Apply le_antisym.
    Apply MapMerge_Card_ub.
    Apply simpl_le_plus_l with p:=(plus (MapCard A m0) (MapCard A m2)).
    Rewrite (plus_permute_2_in_4 (MapCard A m0) (MapCard A m2) (MapCard A m1) (MapCard A m3)).
    Change (MapCard A (M2 A (MapMerge A m0 m2) (MapMerge A m1 m3)))
           =(plus (plus (MapCard A m0) (MapCard A m1)) (plus (MapCard A m2) (MapCard A m3))) in H3.
    Rewrite <- H3. Simpl. Apply le_reg_r. Apply MapMerge_Card_ub.
    Elim (in_dom_some ? ? ? H4). Intros y H7. Rewrite (MapGet_M2_bit_0_1 ? a H6 m0 m1) in H7.
    Unfold in_dom. Rewrite H7. Reflexivity.
    Elim (in_dom_some ? ? ? H5). Intros y H7. Rewrite (MapGet_M2_bit_0_1 ? a H6 m2 m3) in H7.
    Unfold in_dom. Rewrite H7. Reflexivity.
    Intro H6. Unfold MapDisjoint in H. Apply H with m':=m2 a:=(ad_div_2 a). Apply le_antisym.
    Apply MapMerge_Card_ub.
    Apply simpl_le_plus_l with p:=(plus (MapCard A m1) (MapCard A m3)).
    Rewrite (plus_sym (plus (MapCard A m1) (MapCard A m3)) (plus (MapCard A m0) (MapCard A m2))).
    Rewrite (plus_permute_2_in_4 (MapCard A m0) (MapCard A m2) (MapCard A m1) (MapCard A m3)).
    Rewrite (plus_sym (plus (MapCard A m1) (MapCard A m3)) (MapCard A (MapMerge A m0 m2))).
    Change (plus (MapCard A (MapMerge A m0 m2)) (MapCard A (MapMerge A m1 m3)))
           =(plus (plus (MapCard A m0) (MapCard A m1)) (plus (MapCard A m2) (MapCard A m3))) in H3.
    Rewrite <- H3. Apply le_reg_l. Apply MapMerge_Card_ub.
    Elim (in_dom_some ? ? ? H4). Intros y H7. Rewrite (MapGet_M2_bit_0_0 ? a H6 m0 m1) in H7.
    Unfold in_dom. Rewrite H7. Reflexivity.
    Elim (in_dom_some ? ? ? H5). Intros y H7. Rewrite (MapGet_M2_bit_0_0 ? a H6 m2 m3) in H7.
    Unfold in_dom. Rewrite H7. Reflexivity.
  Qed.

  Lemma MapCard_is_Sn : (m:(Map A)) (n:nat) (MapCard ? m)=(S n) -> 
      {a:ad | (in_dom ? a m)=true}.
  Proof.
    Induction m. Intros. Discriminate H.
    Intros a y n H. Split with a. Unfold in_dom. Rewrite (M1_semantics_1 ? a y). Reflexivity.
    Intros. Simpl in H1. Elim (O_or_S (MapCard ? m0)). Intro H2. Elim H2. Intros m2 H3.
    Elim (H ? (sym_eq ? ? ? H3)). Intros a H4. Split with (ad_double a). Unfold in_dom.
    Rewrite (MapGet_M2_bit_0_0 A (ad_double a) (ad_double_bit_0 a) m0 m1).
    Rewrite (ad_double_div_2 a). Elim (in_dom_some ? ? ? H4). Intros y H5. Rewrite H5. Reflexivity.
    Intro H2. Rewrite <- H2 in H1. Simpl in H1. Elim (H0 ? H1). Intros a H3.
    Split with (ad_double_plus_un a). Unfold in_dom.
    Rewrite (MapGet_M2_bit_0_1 A (ad_double_plus_un a) (ad_double_plus_un_bit_0 a) m0 m1).
    Rewrite (ad_double_plus_un_div_2 a). Elim (in_dom_some ? ? ? H3). Intros y H4. Rewrite H4.
    Reflexivity.
  Qed.

End MapCard.

Section MapCard2.

  Variable A, B : Set.

  Lemma MapSubset_card_eq_1 : (n:nat) (m:(Map A)) (m':(Map B))
      (MapSubset ? ? m m') -> (MapCard ? m)=n -> (MapCard ? m')=n ->
        (MapSubset ? ? m' m).
  Proof.
    Induction n. Intros. Unfold MapSubset in_dom. Intro. Rewrite (MapCard_is_O ? m H0 a).
    Rewrite (MapCard_is_O ? m' H1 a). Intro H2. Discriminate H2.
    Intros. Elim (MapCard_is_Sn A m n0 H1). Intros a H3. Elim (in_dom_some ? ? ? H3).
    Intros y H4. Elim (in_dom_some ? ? ? (H0 ? H3)). Intros y' H6.
    Cut (eqmap ? (MapPut ? (MapRemove ? m a) a y) m). Intro.
    Cut (eqmap ? (MapPut ? (MapRemove ? m' a) a y') m'). Intro.
    Apply MapSubset_ext with m0:=(MapPut ? (MapRemove ? m' a) a y')
                             m2:=(MapPut ? (MapRemove ? m a) a y).
    Assumption.
    Assumption.
    Apply MapSubset_Put_mono. Apply H. Apply MapSubset_Remove_mono. Assumption.
    Rewrite <- (MapCard_Remove_2_conv ? m a y H4) in H1. Inversion_clear H1. Reflexivity.
    Rewrite <- (MapCard_Remove_2_conv ? m' a y' H6) in H2. Inversion_clear H2. Reflexivity.
    Unfold eqmap eqm. Intro. Rewrite (MapPut_semantics ? (MapRemove B m' a) a y' a0).
    Elim (sumbool_of_bool (ad_eq a a0)). Intro H7. Rewrite H7. Rewrite <- (ad_eq_complete ? ? H7).
    Apply sym_eq. Assumption.
    Intro H7. Rewrite H7. Rewrite (MapRemove_semantics ? m' a a0). Rewrite H7. Reflexivity.
    Unfold eqmap eqm. Intro. Rewrite (MapPut_semantics ? (MapRemove A m a) a y a0).
    Elim (sumbool_of_bool (ad_eq a a0)). Intro H7. Rewrite H7. Rewrite <- (ad_eq_complete ? ? H7).
    Apply sym_eq. Assumption.
    Intro H7. Rewrite H7. Rewrite (MapRemove_semantics A m a a0). Rewrite H7. Reflexivity.
  Qed.

  Lemma MapDomRestrTo_Card_ub_r : (m:(Map A)) (m':(Map B))
      (le (MapCard A (MapDomRestrTo A B m m')) (MapCard B m')).
  Proof.
    Induction m. Intro. Simpl. Apply le_O_n.
    Intros a y m'. Simpl. Elim (option_sum B (MapGet B m' a)). Intro H. Elim H. Intros y0 H0.
    Rewrite H0. Elim (MapCard_is_not_O B m' a y0 H0). Intros n H1. Rewrite H1. Simpl.
    Apply le_n_S. Apply le_O_n.
    Intro H. Rewrite H. Simpl. Apply le_O_n.
    Induction m'. Simpl. Apply le_O_n.

    Intros a y. Unfold MapDomRestrTo. Case (MapGet A (M2 A m0 m1) a). Simpl. Apply le_O_n.
    Intro. Simpl. Apply le_n.
    Intros. Simpl. Rewrite (MapCard_makeM2 A (MapDomRestrTo A B m0 m2) (MapDomRestrTo A B m1 m3)).
    Apply le_plus_plus. Apply H.
    Apply H0.
  Qed.

End MapCard2.

Section MapCard3.

  Variable A, B : Set.

  Lemma MapMerge_Card_lb_l : (m,m':(Map A))
      (ge (MapCard A (MapMerge A m m')) (MapCard A m)).
  Proof.
    Unfold ge. Intros. Apply (simpl_le_plus_l (MapCard A m')).
    Rewrite (plus_sym (MapCard A m') (MapCard A m)).
    Rewrite (plus_sym (MapCard A m') (MapCard A (MapMerge A m m'))).
    Rewrite (MapMerge_Restr_Card A m m'). Apply le_reg_l. Apply MapDomRestrTo_Card_ub_r.
  Qed.

  Lemma MapMerge_Card_lb_r : (m,m':(Map A))
      (ge (MapCard A (MapMerge A m m')) (MapCard A m')).
  Proof.
    Unfold ge. Intros. Apply (simpl_le_plus_l (MapCard A m)). Rewrite (MapMerge_Restr_Card A m m').
    Rewrite (plus_sym (MapCard A (MapMerge A m m')) (MapCard A (MapDomRestrTo A A m m'))).
    Apply le_reg_r. Apply MapDomRestrTo_Card_ub_l.
  Qed.

  Lemma MapDomRestrBy_Card_lb : (m:(Map A)) (m':(Map B))
      (ge (plus (MapCard B m') (MapCard A (MapDomRestrBy A B m m'))) (MapCard A m)).
  Proof.
    Unfold ge. Intros. Rewrite (MapSplit_Card A B m m'). Apply le_reg_r.
    Apply MapDomRestrTo_Card_ub_r.
  Qed.

  Lemma MapSubset_Card_le : (m:(Map A)) (m':(Map B))
      (MapSubset A B m m') -> (le (MapCard A m) (MapCard B m')).
  Proof.
    Intros. Apply le_trans with m:=(plus (MapCard B m') (MapCard A (MapDomRestrBy A B m m'))).
    Exact (MapDomRestrBy_Card_lb m m').
    Rewrite (MapCard_ext ? ? ? (MapSubset_imp_2 ? ? ? ? H)). Simpl. Rewrite <- plus_n_O.
    Apply le_n.
  Qed.

  Lemma MapSubset_card_eq : (m:(Map A)) (m':(Map B))
      (MapSubset ? ? m m') -> (le (MapCard ? m') (MapCard ? m)) ->
        (eqmap ? (MapDom ? m) (MapDom ? m')).
  Proof.
    Intros. Apply MapSubset_antisym. Assumption.
    Cut (MapCard B m')=(MapCard A m). Intro. Apply (MapSubset_card_eq_1 A B (MapCard A m)).
    Assumption.
    Reflexivity.
    Assumption.
    Apply le_antisym. Assumption.
    Apply MapSubset_Card_le. Assumption.
  Qed.

End MapCard3.

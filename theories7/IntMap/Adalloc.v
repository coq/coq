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
Require ZArith.
Require Arith.
Require Addr.
Require Adist.
Require Addec.
Require Map.
Require Fset.

Section AdAlloc.

  Variable A : Set.

  Definition nat_of_ad := [a:ad] Cases a of
                                     ad_z => O
				   | (ad_x p) => (convert p)
			         end.

  Fixpoint nat_le [m:nat] : nat -> bool :=
    Cases m of
        O => [_:nat] true
      | (S m') => [n:nat] Cases n of
                              O => false
			    | (S n') => (nat_le m' n')
			  end
    end.

  Lemma nat_le_correct : (m,n:nat) (le m n) -> (nat_le m n)=true.
  Proof.
    NewInduction m as [|m IHm]. Trivial.
    NewDestruct n. Intro H. Elim (le_Sn_O ? H).
    Intros. Simpl. Apply IHm. Apply le_S_n. Assumption.
  Qed.

  Lemma nat_le_complete : (m,n:nat) (nat_le m n)=true -> (le m n).
  Proof.
    NewInduction m. Trivial with arith.
    NewDestruct n. Intro H. Discriminate H.
    Auto with arith.
  Qed.

  Lemma nat_le_correct_conv : (m,n:nat) (lt m n) -> (nat_le n m)=false.
  Proof.
    Intros. Elim (sumbool_of_bool (nat_le n m)). Intro H0.
    Elim (lt_n_n ? (lt_le_trans ? ? ? H (nat_le_complete ? ? H0))).
    Trivial.
  Qed.

  Lemma nat_le_complete_conv : (m,n:nat) (nat_le n m)=false -> (lt m n).
  Proof.
    Intros. Elim (le_or_lt n m). Intro. Conditional Trivial Rewrite nat_le_correct in H. Discriminate H.
    Trivial.
  Qed.

  Definition ad_of_nat := [n:nat] Cases n of
                                      O => ad_z
				    | (S n') => (ad_x (anti_convert n'))
				  end.

  Lemma ad_of_nat_of_ad : (a:ad) (ad_of_nat (nat_of_ad a))=a.
  Proof.
    NewDestruct a as [|p]. Reflexivity.
    Simpl. Elim (ZL4 p). Intros n H. Rewrite H. Simpl. Rewrite <- bij1 in H.
    Rewrite convert_intro with 1:=H. Reflexivity.
  Qed.

  Lemma nat_of_ad_of_nat : (n:nat) (nat_of_ad (ad_of_nat n))=n.
  Proof.
    NewInduction n. Trivial.
    Intros. Simpl. Apply bij1.
  Qed.

  Definition ad_le := [a,b:ad] (nat_le (nat_of_ad a) (nat_of_ad b)).

  Lemma ad_le_refl : (a:ad) (ad_le a a)=true.
  Proof.
    Intro. Unfold ad_le. Apply nat_le_correct. Apply le_n.
  Qed.

  Lemma ad_le_antisym : (a,b:ad) (ad_le a b)=true -> (ad_le b a)=true -> a=b.
  Proof.
    Unfold ad_le. Intros. Rewrite <- (ad_of_nat_of_ad a). Rewrite <- (ad_of_nat_of_ad b).
    Rewrite (le_antisym ? ? (nat_le_complete ? ? H) (nat_le_complete ? ? H0)). Reflexivity.
  Qed.

  Lemma ad_le_trans : (a,b,c:ad) (ad_le a b)=true -> (ad_le b c)=true -> 
      (ad_le a c)=true.
  Proof.
    Unfold ad_le. Intros. Apply nat_le_correct. Apply le_trans with m:=(nat_of_ad b).
    Apply nat_le_complete. Assumption.
    Apply nat_le_complete. Assumption.
  Qed.

  Lemma ad_le_lt_trans : (a,b,c:ad) (ad_le a b)=true -> (ad_le c b)=false -> 
      (ad_le c a)=false.
  Proof.
    Unfold ad_le. Intros. Apply nat_le_correct_conv. Apply le_lt_trans with m:=(nat_of_ad b).
    Apply nat_le_complete. Assumption.
    Apply nat_le_complete_conv. Assumption.
  Qed.

  Lemma ad_lt_le_trans : (a,b,c:ad) (ad_le b a)=false -> (ad_le b c)=true -> 
      (ad_le c a)=false.
  Proof.
    Unfold ad_le. Intros. Apply nat_le_correct_conv. Apply lt_le_trans with m:=(nat_of_ad b).
    Apply nat_le_complete_conv. Assumption.
    Apply nat_le_complete. Assumption.
  Qed.

  Lemma ad_lt_trans : (a,b,c:ad) (ad_le b a)=false -> (ad_le c b)=false -> 
      (ad_le c a)=false.
  Proof.
    Unfold ad_le. Intros. Apply nat_le_correct_conv. Apply lt_trans with m:=(nat_of_ad b).
    Apply nat_le_complete_conv. Assumption.
    Apply nat_le_complete_conv. Assumption.
  Qed.

  Lemma ad_lt_le_weak : (a,b:ad) (ad_le b a)=false -> (ad_le a b)=true.
  Proof.
    Unfold ad_le. Intros. Apply nat_le_correct. Apply lt_le_weak.
    Apply nat_le_complete_conv. Assumption.
  Qed.

  Definition ad_min := [a,b:ad] if (ad_le a b) then a else b.

  Lemma ad_min_choice : (a,b:ad) {(ad_min a b)=a}+{(ad_min a b)=b}.
  Proof.
    Unfold ad_min. Intros. Elim (sumbool_of_bool (ad_le a b)). Intro H. Left . Rewrite H.
    Reflexivity.
    Intro H. Right . Rewrite H. Reflexivity.
  Qed.

  Lemma ad_min_le_1 : (a,b:ad) (ad_le (ad_min a b) a)=true.
  Proof.
    Unfold ad_min. Intros. Elim (sumbool_of_bool (ad_le a b)). Intro H. Rewrite H.
    Apply ad_le_refl.
    Intro H. Rewrite H. Apply ad_lt_le_weak. Assumption.
  Qed.

  Lemma ad_min_le_2 : (a,b:ad) (ad_le (ad_min a b) b)=true.
  Proof.
    Unfold ad_min. Intros. Elim (sumbool_of_bool (ad_le a b)). Intro H. Rewrite H. Assumption.
    Intro H. Rewrite H. Apply ad_le_refl.
  Qed.

  Lemma ad_min_le_3 : (a,b,c:ad) (ad_le a (ad_min b c))=true -> (ad_le a b)=true.
  Proof.
    Unfold ad_min. Intros. Elim (sumbool_of_bool (ad_le b c)). Intro H0. Rewrite H0 in H.
    Assumption.
    Intro H0. Rewrite H0 in H. Apply ad_lt_le_weak. Apply ad_le_lt_trans with b:=c; Assumption.
  Qed.

  Lemma ad_min_le_4 : (a,b,c:ad) (ad_le a (ad_min b c))=true -> (ad_le a c)=true.
  Proof.
    Unfold ad_min. Intros. Elim (sumbool_of_bool (ad_le b c)). Intro H0. Rewrite H0 in H.
    Apply ad_le_trans with b:=b; Assumption.
    Intro H0. Rewrite H0 in H. Assumption.
  Qed.

  Lemma ad_min_le_5 : (a,b,c:ad) (ad_le a b)=true -> (ad_le a c)=true ->
      (ad_le a (ad_min b c))=true.
  Proof.
    Intros. Elim (ad_min_choice b c). Intro H1. Rewrite H1. Assumption.
    Intro H1. Rewrite H1. Assumption.
  Qed.

  Lemma ad_min_lt_3 : (a,b,c:ad) (ad_le (ad_min b c) a)=false -> (ad_le b a)=false.
  Proof.
    Unfold ad_min. Intros. Elim (sumbool_of_bool (ad_le b c)). Intro H0. Rewrite H0 in H.
    Assumption.
    Intro H0. Rewrite H0 in H. Apply ad_lt_trans with b:=c; Assumption.
  Qed.

  Lemma ad_min_lt_4 : (a,b,c:ad) (ad_le (ad_min b c) a)=false -> (ad_le c a)=false.
  Proof.
    Unfold ad_min. Intros. Elim (sumbool_of_bool (ad_le b c)). Intro H0. Rewrite H0 in H.
    Apply ad_lt_le_trans with b:=b; Assumption.
    Intro H0. Rewrite H0 in H. Assumption.
  Qed.

  (** Allocator: returns an address not in the domain of [m].
  This allocator is optimal in that it returns the lowest possible address,
  in the usual ordering on integers. It is not the most efficient, however. *)
  Fixpoint ad_alloc_opt [m:(Map A)] : ad :=
    Cases m of
        M0 => ad_z
      | (M1 a _) => if (ad_eq a ad_z)
                    then (ad_x xH)
		    else ad_z
      | (M2 m1 m2) => (ad_min (ad_double (ad_alloc_opt m1))
                              (ad_double_plus_un (ad_alloc_opt m2)))
    end.

  Lemma ad_alloc_opt_allocates_1 : (m:(Map A)) (MapGet A m (ad_alloc_opt m))=(NONE A).
  Proof.
    NewInduction m as [|a|m0 H m1 H0]. Reflexivity.
    Simpl. Elim (sumbool_of_bool (ad_eq a ad_z)). Intro H. Rewrite H.
    Rewrite (ad_eq_complete ? ? H). Reflexivity.
    Intro H. Rewrite H. Rewrite H. Reflexivity.
    Intros. Change (ad_alloc_opt (M2 A m0 m1)) with
         (ad_min (ad_double (ad_alloc_opt m0)) (ad_double_plus_un (ad_alloc_opt m1))).
    Elim (ad_min_choice (ad_double (ad_alloc_opt m0)) (ad_double_plus_un (ad_alloc_opt m1))).
    Intro H1. Rewrite H1. Rewrite MapGet_M2_bit_0_0. Rewrite ad_double_div_2. Assumption.
    Apply ad_double_bit_0.
    Intro H1. Rewrite H1. Rewrite MapGet_M2_bit_0_1. Rewrite ad_double_plus_un_div_2. Assumption.
    Apply ad_double_plus_un_bit_0.
  Qed.

  Lemma ad_alloc_opt_allocates : (m:(Map A)) (in_dom A (ad_alloc_opt m) m)=false.
  Proof.
    Unfold in_dom. Intro. Rewrite (ad_alloc_opt_allocates_1 m). Reflexivity.
  Qed.

  (** Moreover, this is optimal: all addresses below [(ad_alloc_opt m)]
      are in [dom m]: *)

  Lemma nat_of_ad_double : (a:ad) (nat_of_ad (ad_double a))=(mult (2) (nat_of_ad a)).
  Proof.
    NewDestruct a as [|p]. Trivial.
    Exact (convert_xO p).
  Qed.

  Lemma nat_of_ad_double_plus_un : (a:ad)
      (nat_of_ad (ad_double_plus_un a))=(S (mult (2) (nat_of_ad a))).
  Proof.
    NewDestruct a as [|p]. Trivial.
    Exact (convert_xI p).
  Qed.

  Lemma ad_le_double_mono : (a,b:ad) (ad_le a b)=true -> 
      (ad_le (ad_double a) (ad_double b))=true.
  Proof.
    Unfold ad_le. Intros. Rewrite nat_of_ad_double. Rewrite nat_of_ad_double. Apply nat_le_correct.
    Simpl. Apply le_plus_plus. Apply nat_le_complete. Assumption.
    Apply le_plus_plus. Apply nat_le_complete. Assumption.
    Apply le_n.
  Qed.

  Lemma ad_le_double_plus_un_mono : (a,b:ad) (ad_le a b)=true ->
      (ad_le (ad_double_plus_un a) (ad_double_plus_un b))=true.
  Proof.
    Unfold ad_le. Intros. Rewrite nat_of_ad_double_plus_un. Rewrite nat_of_ad_double_plus_un.
    Apply nat_le_correct. Apply le_n_S. Simpl. Apply le_plus_plus. Apply nat_le_complete.
    Assumption.
    Apply le_plus_plus. Apply nat_le_complete. Assumption.
    Apply le_n.
  Qed.

  Lemma ad_le_double_mono_conv : (a,b:ad) (ad_le (ad_double a) (ad_double b))=true ->
      (ad_le a b)=true.
  Proof.
    Unfold ad_le. Intros a b. Rewrite nat_of_ad_double. Rewrite nat_of_ad_double. Intro.
    Apply nat_le_correct. Apply (mult_le_conv_1 (1)). Apply nat_le_complete. Assumption.
  Qed.

  Lemma ad_le_double_plus_un_mono_conv : (a,b:ad)
      (ad_le (ad_double_plus_un a) (ad_double_plus_un b))=true -> (ad_le a b)=true.
  Proof.
    Unfold ad_le. Intros a b. Rewrite nat_of_ad_double_plus_un. Rewrite nat_of_ad_double_plus_un.
    Intro. Apply nat_le_correct. Apply (mult_le_conv_1 (1)). Apply le_S_n. Apply nat_le_complete.
    Assumption.
  Qed.

  Lemma ad_lt_double_mono : (a,b:ad) (ad_le a b)=false ->
      (ad_le (ad_double a) (ad_double b))=false.
  Proof.
    Intros. Elim (sumbool_of_bool (ad_le (ad_double a) (ad_double b))). Intro H0.
    Rewrite (ad_le_double_mono_conv ? ? H0) in H. Discriminate H.
    Trivial.
  Qed.

  Lemma ad_lt_double_plus_un_mono : (a,b:ad) (ad_le a b)=false ->
      (ad_le (ad_double_plus_un a) (ad_double_plus_un b))=false.
  Proof.
    Intros. Elim (sumbool_of_bool (ad_le (ad_double_plus_un a) (ad_double_plus_un b))). Intro H0.
    Rewrite (ad_le_double_plus_un_mono_conv ? ? H0) in H. Discriminate H.
    Trivial.
  Qed.

  Lemma ad_lt_double_mono_conv : (a,b:ad) (ad_le (ad_double a) (ad_double b))=false ->
      (ad_le a b)=false.
  Proof.
    Intros. Elim (sumbool_of_bool (ad_le a b)). Intro H0. Rewrite (ad_le_double_mono ? ? H0) in H.
    Discriminate H.
    Trivial.
  Qed.

  Lemma ad_lt_double_plus_un_mono_conv : (a,b:ad)
      (ad_le (ad_double_plus_un a) (ad_double_plus_un b))=false -> (ad_le a b)=false.
  Proof.
    Intros. Elim (sumbool_of_bool (ad_le a b)). Intro H0.
    Rewrite (ad_le_double_plus_un_mono ? ? H0) in H. Discriminate H.
    Trivial.
  Qed.

  Lemma ad_alloc_opt_optimal_1 : (m:(Map A)) (a:ad) (ad_le (ad_alloc_opt m) a)=false ->
      {y:A | (MapGet A m a)=(SOME A y)}.
  Proof.
    NewInduction m as [|a y|m0 H m1 H0]. Simpl. Unfold ad_le. Simpl. Intros. Discriminate H.
    Simpl. Intros b H. Elim (sumbool_of_bool (ad_eq a ad_z)). Intro H0. Rewrite H0 in H.
    Unfold ad_le in H. Cut ad_z=b. Intro. Split with y. Rewrite <- H1. Rewrite H0. Reflexivity.
    Rewrite <- (ad_of_nat_of_ad b).
    Rewrite <- (le_n_O_eq ? (le_S_n ? ? (nat_le_complete_conv ? ? H))). Reflexivity.
    Intro H0. Rewrite H0 in H. Discriminate H.
    Intros. Simpl in H1. Elim (ad_double_or_double_plus_un a). Intro H2. Elim H2. Intros a0 H3.
    Rewrite H3 in H1. Elim (H ? (ad_lt_double_mono_conv ? ? (ad_min_lt_3 ? ? ? H1))). Intros y H4.
    Split with y. Rewrite H3. Rewrite MapGet_M2_bit_0_0. Rewrite ad_double_div_2. Assumption.
    Apply ad_double_bit_0.
    Intro H2. Elim H2. Intros a0 H3. Rewrite H3 in H1.
    Elim (H0 ? (ad_lt_double_plus_un_mono_conv ? ? (ad_min_lt_4 ? ? ? H1))). Intros y H4.
    Split with y. Rewrite H3. Rewrite MapGet_M2_bit_0_1. Rewrite ad_double_plus_un_div_2.
    Assumption.
    Apply ad_double_plus_un_bit_0.
  Qed.

  Lemma ad_alloc_opt_optimal : (m:(Map A)) (a:ad) (ad_le (ad_alloc_opt m) a)=false ->
      (in_dom A a m)=true.
  Proof.
    Intros. Unfold in_dom. Elim (ad_alloc_opt_optimal_1 m a H). Intros y H0. Rewrite H0.
    Reflexivity.
  Qed.

End AdAlloc.

V7only [
(* Moved to NArith *)
Notation positive_to_nat_2 := positive_to_nat_2.
Notation positive_to_nat_4 := positive_to_nat_4.
].

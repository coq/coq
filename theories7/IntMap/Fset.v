(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

(*s Sets operations on maps *)

Require Bool.
Require Sumbool.
Require ZArith.
Require Addr.
Require Adist.
Require Addec.
Require Map.

Section Dom.

  Variable A, B : Set.

  Fixpoint MapDomRestrTo [m:(Map A)] : (Map B) -> (Map A) :=
    Cases m of
        M0 => [_:(Map B)] (M0 A)
      | (M1 a y) => [m':(Map B)] Cases (MapGet B m' a) of
                                 NONE => (M0 A)
			       | _ => m
			     end
      | (M2 m1 m2) => [m':(Map B)] Cases m' of
                                   M0 => (M0 A)
				 | (M1 a' y') => Cases (MapGet A m a') of
				                     NONE => (M0 A)
						   | (SOME y) => (M1 A a' y)
						 end
				 | (M2 m'1 m'2) => (makeM2 A (MapDomRestrTo m1 m'1)
				                             (MapDomRestrTo m2 m'2))
			       end
    end.

  Lemma MapDomRestrTo_semantics : (m:(Map A)) (m':(Map B))
      (eqm A (MapGet A (MapDomRestrTo m m'))
             [a0:ad] Cases (MapGet B m' a0) of
	               NONE => (NONE A)
		     | _ => (MapGet A m a0)
		   end).
  Proof.
    Unfold eqm. Induction m. Simpl. Intros. Case (MapGet B m' a); Trivial.
    Intros. Simpl. Elim (sumbool_of_bool (ad_eq a a1)). Intro H. Rewrite H.
    Rewrite <- (ad_eq_complete ? ? H). Case (MapGet B m' a). Reflexivity.
    Intro. Apply M1_semantics_1.
    Intro H. Rewrite H. Case (MapGet B m' a). 
    Case (MapGet B m' a1); Reflexivity.
    Case (MapGet B m' a1); Intros; Exact (M1_semantics_2 A a a1 a0 H).
    Induction m'. Trivial.
    Unfold MapDomRestrTo. Intros. Elim (sumbool_of_bool (ad_eq a a1)).
    Intro H1.
    Rewrite (ad_eq_complete ? ? H1). Rewrite (M1_semantics_1 B a1 a0).
    Case (MapGet A (M2 A m0 m1) a1). Reflexivity.
    Intro. Apply M1_semantics_1.
    Intro H1. Rewrite (M1_semantics_2 B a a1 a0 H1). Case (MapGet A (M2 A m0 m1) a). Reflexivity.
    Intro. Exact (M1_semantics_2 A a a1 a2 H1).
    Intros. Change (MapGet A (makeM2 A (MapDomRestrTo m0 m2) (MapDomRestrTo m1 m3)) a)
        =(Cases (MapGet B (M2 B m2 m3) a) of
            NONE => (NONE A)
          | (SOME _) => (MapGet A (M2 A m0 m1) a)
          end).
    Rewrite (makeM2_M2 A (MapDomRestrTo m0 m2) (MapDomRestrTo m1 m3) a).
    Rewrite MapGet_M2_bit_0_if. Rewrite (H0 m3 (ad_div_2 a)). Rewrite (H m2 (ad_div_2 a)).
    Rewrite (MapGet_M2_bit_0_if B m2 m3 a). Rewrite (MapGet_M2_bit_0_if A m0 m1 a).
    Case (ad_bit_0 a); Reflexivity.
  Qed.

  Fixpoint MapDomRestrBy [m:(Map A)] : (Map B) -> (Map A) :=
    Cases m of
        M0 => [_:(Map B)] (M0 A)
      | (M1 a y) => [m':(Map B)] Cases (MapGet B m' a) of
                                 NONE => m
			       | _ => (M0 A)
			     end
      | (M2 m1 m2) => [m':(Map B)] Cases m' of
                                   M0 => m
				 | (M1 a' y') => (MapRemove A m a')
				 | (M2 m'1 m'2) => (makeM2 A (MapDomRestrBy m1 m'1)
				                             (MapDomRestrBy m2 m'2))
			       end
    end.

  Lemma MapDomRestrBy_semantics : (m:(Map A)) (m':(Map B))
      (eqm A (MapGet A (MapDomRestrBy m m'))
             [a0:ad] Cases (MapGet B m' a0) of
	               NONE => (MapGet A m a0)
		     | _ => (NONE A)
		   end).
  Proof.
    Unfold eqm. Induction m. Simpl. Intros. Case (MapGet B m' a); Trivial.
    Intros. Simpl. Elim (sumbool_of_bool (ad_eq a a1)). Intro H. Rewrite H.
    Rewrite (ad_eq_complete ? ? H). Case (MapGet B m' a1). Apply M1_semantics_1.
    Trivial.
    Intro H. Rewrite H. Case (MapGet B m' a). Rewrite (M1_semantics_2 A a a1 a0 H).
    Case (MapGet B m' a1); Trivial.
    Case (MapGet B m' a1); Trivial.
    Induction m'. Trivial.
    Unfold MapDomRestrBy. Intros. Rewrite (MapRemove_semantics A (M2 A m0 m1) a a1).
    Elim (sumbool_of_bool (ad_eq a a1)). Intro H1. Rewrite H1. Rewrite (ad_eq_complete ? ? H1).
    Rewrite (M1_semantics_1 B a1 a0). Reflexivity.
    Intro H1. Rewrite H1. Rewrite (M1_semantics_2 B a a1 a0 H1). Reflexivity.
    Intros. Change (MapGet A (makeM2 A (MapDomRestrBy m0 m2) (MapDomRestrBy m1 m3)) a)
        =(Cases (MapGet B (M2 B m2 m3) a) of
            NONE => (MapGet A (M2 A m0 m1) a)
          | (SOME _) => (NONE A)
          end).
    Rewrite (makeM2_M2 A (MapDomRestrBy m0 m2) (MapDomRestrBy m1 m3) a).
    Rewrite MapGet_M2_bit_0_if. Rewrite (H0 m3 (ad_div_2 a)). Rewrite (H m2 (ad_div_2 a)).
    Rewrite (MapGet_M2_bit_0_if B m2 m3 a). Rewrite (MapGet_M2_bit_0_if A m0 m1 a).
    Case (ad_bit_0 a); Reflexivity.
  Qed.

  Definition in_dom := [a:ad; m:(Map A)]
    Cases (MapGet A m a) of
        NONE => false
      | _ => true
    end.

  Lemma in_dom_M0 : (a:ad) (in_dom a (M0 A))=false.
  Proof.
    Trivial.
  Qed.

  Lemma in_dom_M1 : (a,a0:ad) (y:A) (in_dom a0 (M1 A a y))=(ad_eq a a0).
  Proof.
    Unfold in_dom. Intros. Simpl. Case (ad_eq a a0); Reflexivity.
  Qed.

  Lemma in_dom_M1_1 : (a:ad) (y:A) (in_dom a (M1 A a y))=true.
  Proof.
    Intros. Rewrite in_dom_M1. Apply ad_eq_correct.
  Qed.

  Lemma in_dom_M1_2 : (a,a0:ad) (y:A) (in_dom a0 (M1 A a y))=true -> a=a0.
  Proof.
    Intros. Apply (ad_eq_complete a a0). Rewrite (in_dom_M1 a a0 y) in H. Assumption.
  Qed.

  Lemma in_dom_some : (m:(Map A)) (a:ad) (in_dom a m)=true ->
      {y:A | (MapGet A m a)=(SOME A y)}.
  Proof.
    Unfold in_dom. Intros. Elim (option_sum ? (MapGet A m a)). Trivial.
    Intro H0. Rewrite H0 in H. Discriminate H.
  Qed.

  Lemma in_dom_none : (m:(Map A)) (a:ad) (in_dom a m)=false ->
      (MapGet A m a)=(NONE A).
  Proof.
    Unfold in_dom. Intros. Elim (option_sum ? (MapGet A m a)). Intro H0. Elim H0.
    Intros y H1. Rewrite H1 in H. Discriminate H.
    Trivial.
  Qed.

  Lemma in_dom_put : (m:(Map A)) (a0:ad) (y0:A) (a:ad)
      (in_dom a (MapPut A m a0 y0))=(orb (ad_eq a a0) (in_dom a m)).
  Proof.
    Unfold in_dom. Intros. Rewrite (MapPut_semantics A m a0 y0 a).
    Elim (sumbool_of_bool (ad_eq a a0)). Intro H. Rewrite H. Rewrite (ad_eq_comm a a0) in H.
    Rewrite H. Rewrite orb_true_b. Reflexivity.
    Intro H. Rewrite H. Rewrite (ad_eq_comm a a0) in H. Rewrite H. Rewrite orb_false_b.
    Reflexivity.
  Qed.

  Lemma in_dom_put_behind : (m:(Map A)) (a0:ad) (y0:A) (a:ad)
      (in_dom a (MapPut_behind A m a0 y0))=(orb (ad_eq a a0) (in_dom a m)).
  Proof.
    Unfold in_dom. Intros. Rewrite (MapPut_behind_semantics A m a0 y0 a).
    Elim (sumbool_of_bool (ad_eq a a0)). Intro H. Rewrite H. Rewrite (ad_eq_comm a a0) in H.
    Rewrite H. Case (MapGet A m a); Reflexivity.
    Intro H. Rewrite H. Rewrite (ad_eq_comm a a0) in H. Rewrite H. Case (MapGet A m a); Trivial.
  Qed.

  Lemma in_dom_remove : (m:(Map A)) (a0:ad) (a:ad)
      (in_dom a (MapRemove A m a0))=(andb (negb (ad_eq a a0)) (in_dom a m)).
  Proof.
    Unfold in_dom. Intros. Rewrite (MapRemove_semantics A m a0 a).
    Elim (sumbool_of_bool (ad_eq a a0)). Intro H. Rewrite H. Rewrite (ad_eq_comm a a0) in H.
    Rewrite H. Reflexivity.
    Intro H. Rewrite H. Rewrite (ad_eq_comm a a0) in H. Rewrite H.
    Case (MapGet A m a); Reflexivity.
  Qed.

  Lemma in_dom_merge : (m,m':(Map A)) (a:ad)
      (in_dom a (MapMerge A m m'))=(orb (in_dom a m) (in_dom a m')).
  Proof.
    Unfold in_dom. Intros. Rewrite (MapMerge_semantics A m m' a).
    Elim (option_sum A (MapGet A m' a)). Intro H. Elim H. Intros y H0. Rewrite H0.
    Case (MapGet A m a); Reflexivity.
    Intro H. Rewrite H. Rewrite orb_b_false. Reflexivity.
  Qed.

  Lemma in_dom_delta : (m,m':(Map A)) (a:ad)
      (in_dom a (MapDelta A m m'))=(xorb (in_dom a m) (in_dom a m')).
  Proof.
    Unfold in_dom. Intros. Rewrite (MapDelta_semantics A m m' a).
    Elim (option_sum A (MapGet A m' a)). Intro H. Elim H. Intros y H0. Rewrite H0.
    Case (MapGet A m a); Reflexivity.
    Intro H. Rewrite H. Case (MapGet A m a); Reflexivity.
  Qed.

End Dom.

Section InDom.

  Variable A, B : Set.

  Lemma in_dom_restrto : (m:(Map A)) (m':(Map B)) (a:ad)
    (in_dom A a (MapDomRestrTo A B m m'))=(andb (in_dom A a m) (in_dom B a m')).
  Proof.
    Unfold in_dom. Intros. Rewrite (MapDomRestrTo_semantics A B m m' a).
    Elim (option_sum B (MapGet B m' a)). Intro H. Elim H. Intros y H0. Rewrite H0.
    Rewrite andb_b_true. Reflexivity.
    Intro H. Rewrite H. Rewrite andb_b_false. Reflexivity.
  Qed.

  Lemma in_dom_restrby : (m:(Map A)) (m':(Map B)) (a:ad)
    (in_dom A a (MapDomRestrBy A B m m'))=(andb (in_dom A a m) (negb (in_dom B a m'))).
  Proof.
    Unfold in_dom. Intros. Rewrite (MapDomRestrBy_semantics A B m m' a).
    Elim (option_sum B (MapGet B m' a)). Intro H. Elim H. Intros y H0. Rewrite H0.
    Unfold negb. Rewrite andb_b_false. Reflexivity.
    Intro H. Rewrite H. Unfold negb. Rewrite andb_b_true. Reflexivity.
  Qed.

End InDom.

Definition FSet := (Map unit).

Section FSetDefs.

  Variable A : Set.

  Definition in_FSet : ad -> FSet -> bool := (in_dom unit).

  Fixpoint MapDom [m:(Map A)] : FSet :=
    Cases m of
      	M0 => (M0 unit)
      | (M1 a _) => (M1 unit a tt)
      | (M2 m m') => (M2 unit (MapDom m) (MapDom m'))
    end.

  Lemma MapDom_semantics_1 : (m:(Map A)) (a:ad) 
      (y:A) (MapGet A m a)=(SOME A y) -> (in_FSet a (MapDom m))=true.
  Proof.
    Induction m. Intros. Discriminate H.
    Unfold MapDom. Unfold in_FSet. Unfold in_dom. Unfold MapGet. Intros a y a0 y0.
    Case (ad_eq a a0). Trivial.
    Intro. Discriminate H.
    Intros m0 H m1 H0 a y. Rewrite (MapGet_M2_bit_0_if A m0 m1 a). Simpl. Unfold in_FSet.
    Unfold in_dom. Rewrite (MapGet_M2_bit_0_if unit (MapDom m0) (MapDom m1) a).
    Case (ad_bit_0 a). Unfold in_FSet in_dom in H0. Intro. Apply H0 with y:=y. Assumption.
    Unfold in_FSet in_dom in H. Intro. Apply H with y:=y. Assumption.
  Qed.

  Lemma MapDom_semantics_2 : (m:(Map A)) (a:ad) 
      (in_FSet a (MapDom m))=true -> {y:A | (MapGet A m a)=(SOME A y)}.
  Proof.
    Induction m. Intros. Discriminate H.
    Unfold MapDom. Unfold in_FSet. Unfold in_dom. Unfold MapGet. Intros a y a0. Case (ad_eq a a0).
    Intro. Split with y. Reflexivity.
    Intro. Discriminate H.
    Intros m0 H m1 H0 a. Rewrite (MapGet_M2_bit_0_if A m0 m1 a). Simpl. Unfold in_FSet.
    Unfold in_dom. Rewrite (MapGet_M2_bit_0_if unit (MapDom m0) (MapDom m1) a).
    Case (ad_bit_0 a). Unfold in_FSet in_dom in H0. Intro. Apply H0. Assumption.
    Unfold in_FSet in_dom in H. Intro. Apply H. Assumption.
  Qed.

  Lemma MapDom_semantics_3 : (m:(Map A)) (a:ad) 
      (MapGet A m a)=(NONE A) -> (in_FSet a (MapDom m))=false.
  Proof.
    Intros. Elim (sumbool_of_bool (in_FSet a (MapDom m))). Intro H0.
    Elim (MapDom_semantics_2 m a H0). Intros y H1. Rewrite H in H1. Discriminate H1.
    Trivial.
  Qed.

  Lemma MapDom_semantics_4 : (m:(Map A)) (a:ad) 
      (in_FSet a (MapDom m))=false -> (MapGet A m a)=(NONE A).
  Proof.
    Intros. Elim (option_sum A (MapGet A m a)). Intro H0. Elim H0. Intros y H1.
    Rewrite (MapDom_semantics_1 m a y H1) in H. Discriminate H.
    Trivial.
  Qed.

  Lemma MapDom_Dom : (m:(Map A)) (a:ad) (in_dom A a m)=(in_FSet a (MapDom m)).
  Proof.
    Intros. Elim (sumbool_of_bool (in_FSet a (MapDom m))). Intro H.
    Elim (MapDom_semantics_2 m a H). Intros y H0. Rewrite H. Unfold in_dom. Rewrite H0.
    Reflexivity.
    Intro H. Rewrite H. Unfold in_dom. Rewrite (MapDom_semantics_4 m a H). Reflexivity.
  Qed.

  Definition FSetUnion : FSet -> FSet -> FSet := [s,s':FSet] (MapMerge unit s s').

  Lemma in_FSet_union : (s,s':FSet) (a:ad)
      (in_FSet a (FSetUnion s s'))=(orb (in_FSet a s) (in_FSet a s')).
  Proof.
    Exact (in_dom_merge unit).
  Qed.

  Definition FSetInter : FSet -> FSet -> FSet := [s,s':FSet] (MapDomRestrTo unit unit s s').

  Lemma in_FSet_inter : (s,s':FSet) (a:ad)
      (in_FSet a (FSetInter s s'))=(andb (in_FSet a s) (in_FSet a s')).
  Proof.
    Exact (in_dom_restrto unit unit).
  Qed.

  Definition FSetDiff : FSet -> FSet -> FSet := [s,s':FSet] (MapDomRestrBy unit unit s s').

  Lemma in_FSet_diff : (s,s':FSet) (a:ad)
      (in_FSet a (FSetDiff s s'))=(andb (in_FSet a s) (negb (in_FSet a s'))).
  Proof.
    Exact (in_dom_restrby unit unit).
  Qed.

  Definition FSetDelta : FSet -> FSet -> FSet := [s,s':FSet] (MapDelta unit s s').

  Lemma in_FSet_delta : (s,s':FSet) (a:ad)
      (in_FSet a (FSetDelta s s'))=(xorb (in_FSet a s) (in_FSet a s')).
  Proof.
    Exact (in_dom_delta unit).
  Qed.

End FSetDefs.

Lemma FSet_Dom : (s:FSet) (MapDom unit s)=s.
Proof.
  Induction s. Trivial.
  Simpl. Intros a t. Elim t. Reflexivity.
  Intros. Simpl. Rewrite H. Rewrite H0. Reflexivity.
Qed.

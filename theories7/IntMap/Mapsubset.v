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
Require Fset.
Require Mapaxioms.
Require Mapiter.

Section MapSubsetDef.

  Variable A, B : Set.

  Definition MapSubset := [m:(Map A)] [m':(Map B)]
      (a:ad) (in_dom A a m)=true -> (in_dom B a m')=true.

  Definition MapSubset_1 := [m:(Map A)] [m':(Map B)]
      Cases (MapSweep A [a:ad][_:A] (negb (in_dom B a m')) m) of
          NONE => true
	| _ => false
      end.

  Definition MapSubset_2 := [m:(Map A)] [m':(Map B)] 
      (eqmap A (MapDomRestrBy A B m m') (M0 A)).

  Lemma MapSubset_imp_1 : (m:(Map A)) (m':(Map B))
      (MapSubset m m') -> (MapSubset_1 m m')=true.
  Proof.
    Unfold MapSubset MapSubset_1. Intros.
    Elim (option_sum ? (MapSweep A [a:ad][_:A](negb (in_dom B a m')) m)).
    Intro H0. Elim H0. Intro r. Elim r. Intros a y H1. Cut (negb (in_dom B a m'))=true.
    Intro. Cut (in_dom A a m)=false. Intro. Unfold in_dom in H3.
    Rewrite (MapSweep_semantics_2 ? ? m a y H1) in H3. Discriminate H3.
    Elim (sumbool_of_bool (in_dom A a m)). Intro H3. Rewrite (H a H3) in H2. Discriminate H2.
    Trivial.
    Exact (MapSweep_semantics_1 ? ? m a y H1).
    Intro H0. Rewrite H0. Reflexivity.
  Qed.

  Lemma MapSubset_1_imp : (m:(Map A)) (m':(Map B))
      (MapSubset_1 m m')=true -> (MapSubset m m').
  Proof.
    Unfold MapSubset MapSubset_1. Unfold 2 in_dom. Intros. Elim (option_sum ? (MapGet A m a)).
    Intro H1. Elim H1. Intros y H2.
    Elim (option_sum ? (MapSweep A [a:ad][_:A](negb (in_dom B a m')) m)). Intro H3.
    Elim H3. Intro r. Elim r. Intros a' y' H4. Rewrite H4 in H. Discriminate H.
    Intro H3. Cut (negb (in_dom B a m'))=false. Intro. Rewrite (negb_intro (in_dom B a m')).
    Rewrite H4. Reflexivity.
    Exact (MapSweep_semantics_3 ? ? m H3 a y H2).
    Intro H1. Rewrite H1 in H0. Discriminate H0.
  Qed.

  Lemma map_dom_empty_1 : 
      (m:(Map A)) (eqmap A m (M0 A)) -> (a:ad) (in_dom ? a m)=false.
  Proof.
    Unfold eqmap eqm in_dom. Intros. Rewrite (H a). Reflexivity.
  Qed.

  Lemma map_dom_empty_2 : 
      (m:(Map A)) ((a:ad) (in_dom ? a m)=false) -> (eqmap A m (M0 A)).
  Proof.
    Unfold eqmap eqm in_dom. Intros.
    Cut (Cases (MapGet A m a) of NONE => false | (SOME _) => true end)=false.
    Case (MapGet A m a). Trivial.
    Intros. Discriminate H0.
    Exact (H a).
  Qed.

  Lemma MapSubset_imp_2 : 
      (m:(Map A)) (m':(Map B)) (MapSubset m m') -> (MapSubset_2 m m').
  Proof.
    Unfold MapSubset MapSubset_2. Intros. Apply map_dom_empty_2. Intro. Rewrite in_dom_restrby.
    Elim (sumbool_of_bool (in_dom A a m)). Intro H0. Rewrite H0. Rewrite (H a H0). Reflexivity.
    Intro H0. Rewrite H0. Reflexivity.
  Qed.

  Lemma MapSubset_2_imp : 
      (m:(Map A)) (m':(Map B)) (MapSubset_2 m m') -> (MapSubset m m').
  Proof.
    Unfold MapSubset MapSubset_2. Intros. Cut (in_dom ? a (MapDomRestrBy A B m m'))=false.
    Rewrite in_dom_restrby. Intro. Elim (andb_false_elim ? ? H1). Rewrite H0.
    Intro H2. Discriminate H2.
    Intro H2. Rewrite (negb_intro (in_dom B a m')). Rewrite H2. Reflexivity.
    Exact (map_dom_empty_1 ? H a).
  Qed.

End MapSubsetDef.

Section MapSubsetOrder.

  Variable A, B, C : Set.

  Lemma MapSubset_refl : (m:(Map A)) (MapSubset A A m m).
  Proof.
      Unfold MapSubset. Trivial.
  Qed.

  Lemma MapSubset_antisym : (m:(Map A)) (m':(Map B))
      (MapSubset A B m m') -> (MapSubset B A m' m) -> 
        (eqmap unit (MapDom A m) (MapDom B m')).
  Proof.
    Unfold MapSubset eqmap eqm. Intros. Elim (option_sum ? (MapGet ? (MapDom A m) a)).
    Intro H1. Elim H1. Intro t. Elim t. Intro H2. Elim (option_sum ? (MapGet ? (MapDom B m') a)).
    Intro H3. Elim H3. Intro t'. Elim t'. Intro H4. Rewrite H4. Exact H2. 
    Intro H3. Cut (in_dom B a m')=true. Intro. Rewrite (MapDom_Dom B m' a) in H4.
    Unfold in_FSet in_dom in H4. Rewrite H3 in H4. Discriminate H4.
    Apply H. Rewrite (MapDom_Dom A m a). Unfold in_FSet in_dom. Rewrite H2. Reflexivity.
    Intro H1. Elim (option_sum ? (MapGet ? (MapDom B m') a)). Intro H2. Elim H2. Intros t H3.
    Cut (in_dom A a m)=true. Intro. Rewrite (MapDom_Dom A m a) in H4. Unfold in_FSet in_dom in H4.
    Rewrite H1 in H4. Discriminate H4.
    Apply H0. Rewrite (MapDom_Dom B m' a). Unfold in_FSet in_dom. Rewrite H3. Reflexivity.
    Intro H2. Rewrite H2. Exact H1.
  Qed.

  Lemma MapSubset_trans : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (MapSubset A B m m') -> (MapSubset B C m' m'') -> (MapSubset A C m m'').
  Proof.
    Unfold MapSubset. Intros. Apply H0. Apply H. Assumption.
  Qed.

End MapSubsetOrder.

Section FSubsetOrder.

  Lemma FSubset_refl : (s:FSet) (MapSubset ? ? s s).
  Proof.
    Exact (MapSubset_refl unit).
  Qed.

  Lemma FSubset_antisym : (s,s':FSet)
      (MapSubset ? ? s s') -> (MapSubset ? ? s' s) -> (eqmap unit s s').
  Proof.
    Intros. Rewrite <- (FSet_Dom s). Rewrite <- (FSet_Dom s').
    Exact (MapSubset_antisym ? ? s s' H H0).
  Qed.

  Lemma FSubset_trans : (s,s',s'':FSet)
      (MapSubset ? ? s s') -> (MapSubset ? ? s' s'') -> (MapSubset ? ? s s'').
  Proof.
    Exact (MapSubset_trans unit unit unit).
  Qed.

End FSubsetOrder.

Section MapSubsetExtra.

  Variable A, B : Set.

  Lemma MapSubset_Dom_1 : (m:(Map A)) (m':(Map B))
      (MapSubset A B m m') -> (MapSubset unit unit (MapDom A m) (MapDom B m')).
  Proof.
    Unfold MapSubset. Intros. Elim (MapDom_semantics_2 ? m a H0). Intros y H1.
    Cut (in_dom A a m)=true->(in_dom B a m')=true. Intro. Unfold in_dom in H2.
    Rewrite H1 in H2. Elim (option_sum ? (MapGet B m' a)). Intro H3. Elim H3.
    Intros y' H4. Exact (MapDom_semantics_1 ? m' a y' H4).
    Intro H3. Rewrite H3 in H2. Cut false=true. Intro. Discriminate H4.
    Apply H2. Reflexivity.
    Exact (H a).
  Qed.

  Lemma MapSubset_Dom_2 : (m:(Map A)) (m':(Map B))
      (MapSubset unit unit (MapDom A m) (MapDom B m')) -> (MapSubset A B m m').
  Proof.
    Unfold MapSubset. Intros. Unfold in_dom in H0. Elim (option_sum ? (MapGet A m a)).
    Intro H1. Elim H1. Intros y H2.
    Elim (MapDom_semantics_2 ? ? ? (H a (MapDom_semantics_1 ? ? ? ? H2))). Intros y' H3.
    Unfold in_dom. Rewrite H3. Reflexivity.
    Intro H1. Rewrite H1 in H0. Discriminate H0.
  Qed.

  Lemma MapSubset_1_Dom : (m:(Map A)) (m':(Map B))
      (MapSubset_1 A B m m')=(MapSubset_1 unit unit (MapDom A m) (MapDom B m')).
  Proof.
    Intros. Elim (sumbool_of_bool (MapSubset_1 A B m m')). Intro H. Rewrite H.
    Apply sym_eq. Apply MapSubset_imp_1. Apply MapSubset_Dom_1. Exact (MapSubset_1_imp ? ? ? ? H).
    Intro H. Rewrite H. Elim (sumbool_of_bool (MapSubset_1 unit unit (MapDom A m) (MapDom B m'))).
    Intro H0.
    Rewrite (MapSubset_imp_1 ? ? ? ? (MapSubset_Dom_2 ? ? (MapSubset_1_imp ? ? ? ? H0))) in H.
    Discriminate H.
    Intro. Apply sym_eq. Assumption.
  Qed.

  Lemma MapSubset_Put : (m:(Map A)) (a:ad) (y:A) (MapSubset A A m (MapPut A m a y)).
  Proof.
    Unfold MapSubset. Intros. Rewrite in_dom_put. Rewrite H. Apply orb_b_true.
  Qed.

  Lemma MapSubset_Put_mono : (m:(Map A)) (m':(Map B)) (a:ad) (y:A) (y':B)
      (MapSubset A B m m') -> (MapSubset A B (MapPut A m a y) (MapPut B m' a y')).
  Proof.
    Unfold MapSubset. Intros. Rewrite in_dom_put. Rewrite (in_dom_put A m a y a0) in H0.
    Elim (orb_true_elim ? ? H0). Intro H1. Rewrite H1. Reflexivity.
    Intro H1. Rewrite (H ? H1). Apply orb_b_true.
  Qed.

  Lemma MapSubset_Put_behind : 
      (m:(Map A)) (a:ad) (y:A) (MapSubset A A m (MapPut_behind A m a y)).
  Proof.
    Unfold MapSubset. Intros. Rewrite in_dom_put_behind. Rewrite H. Apply orb_b_true.
  Qed.

  Lemma MapSubset_Put_behind_mono : (m:(Map A)) (m':(Map B)) (a:ad) (y:A) (y':B)
      (MapSubset A B m m') -> 
        (MapSubset A B (MapPut_behind A m a y) (MapPut_behind B m' a y')).
  Proof.
    Unfold MapSubset. Intros. Rewrite in_dom_put_behind.
    Rewrite (in_dom_put_behind A m a y a0) in H0.
    Elim (orb_true_elim ? ? H0). Intro H1. Rewrite H1. Reflexivity.
    Intro H1. Rewrite (H ? H1). Apply orb_b_true.
  Qed.

  Lemma MapSubset_Remove : (m:(Map A)) (a:ad) (MapSubset A A (MapRemove A m a) m).
  Proof.
    Unfold MapSubset. Intros. Unfold MapSubset. Intros. Rewrite (in_dom_remove ? m a a0) in H.
    Elim (andb_prop ? ? H). Trivial.
  Qed.

  Lemma MapSubset_Remove_mono : (m:(Map A)) (m':(Map B)) (a:ad)
      (MapSubset A B m m') -> (MapSubset A B (MapRemove A m a) (MapRemove B m' a)).
  Proof.
    Unfold MapSubset. Intros. Rewrite in_dom_remove. Rewrite (in_dom_remove A m a a0) in H0.
    Elim (andb_prop ? ? H0). Intros. Rewrite H1. Rewrite (H ? H2). Reflexivity.
  Qed.

  Lemma MapSubset_Merge_l : (m,m':(Map A)) (MapSubset A A m (MapMerge A m m')).
  Proof.
    Unfold MapSubset. Intros. Rewrite in_dom_merge. Rewrite H. Reflexivity.
  Qed.

  Lemma MapSubset_Merge_r : (m,m':(Map A)) (MapSubset A A m' (MapMerge A m m')).
  Proof.
    Unfold MapSubset. Intros. Rewrite in_dom_merge. Rewrite H. Apply orb_b_true.
  Qed.

  Lemma MapSubset_Merge_mono : (m,m':(Map A)) (m'',m''':(Map B))
      (MapSubset A B m m'') -> (MapSubset A B m' m''') ->
      	(MapSubset A B (MapMerge A m m') (MapMerge B m'' m''')).
  Proof.
    Unfold MapSubset. Intros. Rewrite in_dom_merge. Rewrite (in_dom_merge A m m' a) in H1.
    Elim (orb_true_elim ? ? H1). Intro H2. Rewrite (H ? H2). Reflexivity.
    Intro H2. Rewrite (H0 ? H2). Apply orb_b_true.
  Qed.

  Lemma MapSubset_DomRestrTo_l : (m:(Map A)) (m':(Map B))
      (MapSubset A A (MapDomRestrTo A B m m') m).
  Proof.
    Unfold MapSubset. Intros. Rewrite (in_dom_restrto ? ? m m' a) in H. Elim (andb_prop ? ? H).
    Trivial.
  Qed.

  Lemma MapSubset_DomRestrTo_r: (m:(Map A)) (m':(Map B))
      (MapSubset A B (MapDomRestrTo A B m m') m').
  Proof.
    Unfold MapSubset. Intros. Rewrite (in_dom_restrto ? ? m m' a) in H. Elim (andb_prop ? ? H).
    Trivial.
  Qed.

  Lemma MapSubset_ext : (m0,m1:(Map A)) (m2,m3:(Map B))
      (eqmap A m0 m1) -> (eqmap B m2 m3) ->
        (MapSubset A B m0 m2) -> (MapSubset A B m1 m3).
  Proof.
    Intros. Apply MapSubset_2_imp. Unfold MapSubset_2.
    Apply eqmap_trans with m':=(MapDomRestrBy A B m0 m2). Apply MapDomRestrBy_ext. Apply eqmap_sym.
    Assumption.
    Apply eqmap_sym. Assumption.
    Exact (MapSubset_imp_2 ? ? ? ? H1).
  Qed.

  Variable C, D : Set.

  Lemma MapSubset_DomRestrTo_mono : 
      (m:(Map A)) (m':(Map B)) (m'':(Map C)) (m''':(Map D))
        (MapSubset ? ? m m'') -> (MapSubset ? ?  m' m''') ->
      	  (MapSubset ? ? (MapDomRestrTo ? ? m m') (MapDomRestrTo ? ? m'' m''')).
  Proof.
    Unfold MapSubset. Intros. Rewrite in_dom_restrto. Rewrite (in_dom_restrto A B m m' a) in H1.
    Elim (andb_prop ? ? H1). Intros. Rewrite (H ? H2). Rewrite (H0 ? H3). Reflexivity.
  Qed.

  Lemma MapSubset_DomRestrBy_l : (m:(Map A)) (m':(Map B))
      (MapSubset A A (MapDomRestrBy A B m m') m).
  Proof.
    Unfold MapSubset. Intros. Rewrite (in_dom_restrby ? ? m m' a) in H. Elim (andb_prop ? ? H).
    Trivial.
  Qed.

  Lemma MapSubset_DomRestrBy_mono : 
      (m:(Map A)) (m':(Map B)) (m'':(Map C)) (m''':(Map D))
        (MapSubset ? ? m m'') -> (MapSubset ? ?  m''' m') ->
      	  (MapSubset ? ? (MapDomRestrBy ? ? m m') (MapDomRestrBy ? ? m'' m''')).
  Proof.
    Unfold MapSubset. Intros. Rewrite in_dom_restrby. Rewrite (in_dom_restrby A B m m' a) in H1.
    Elim (andb_prop ? ? H1). Intros. Rewrite (H ? H2). Elim (sumbool_of_bool (in_dom D a m''')).
    Intro H4. Rewrite (H0 ? H4) in H3. Discriminate H3.
    Intro H4. Rewrite H4. Reflexivity.
  Qed.
  
End MapSubsetExtra.

Section MapDisjointDef.

  Variable A, B : Set.

  Definition MapDisjoint := [m:(Map A)] [m':(Map B)]
      (a:ad) (in_dom A a m)=true -> (in_dom B a m')=true -> False.

  Definition MapDisjoint_1 := [m:(Map A)] [m':(Map B)]
      Cases (MapSweep A [a:ad][_:A] (in_dom B a m') m) of
          NONE => true
	| _ => false
      end.

  Definition MapDisjoint_2 := [m:(Map A)] [m':(Map B)] 
      (eqmap A (MapDomRestrTo A B m m') (M0 A)).

  Lemma MapDisjoint_imp_1 : (m:(Map A)) (m':(Map B))
      (MapDisjoint m m') -> (MapDisjoint_1 m m')=true.
  Proof.
    Unfold MapDisjoint MapDisjoint_1. Intros.
    Elim (option_sum ? (MapSweep A [a:ad][_:A](in_dom B a m') m)). Intro H0. Elim H0.
    Intro r. Elim r. Intros a y H1. Cut (in_dom A a m)=true->(in_dom B a m')=true->False.
    Intro. Unfold 1 in_dom in H2. Rewrite (MapSweep_semantics_2 ? ? ? ? ? H1) in H2.
    Rewrite (MapSweep_semantics_1 ? ? ? ? ? H1) in H2. Elim (H2 (refl_equal ? ?) (refl_equal ? ?)).
    Exact (H a).
    Intro H0. Rewrite H0. Reflexivity.
  Qed.

  Lemma MapDisjoint_1_imp : (m:(Map A)) (m':(Map B))
      (MapDisjoint_1 m m')=true -> (MapDisjoint m m').
  Proof.
    Unfold MapDisjoint MapDisjoint_1. Intros.
    Elim (option_sum ? (MapSweep A [a:ad][_:A](in_dom B a m') m)). Intro H2. Elim H2.
    Intro r. Elim r. Intros a' y' H3. Rewrite H3 in H. Discriminate H.
    Intro H2. Unfold in_dom in H0. Elim (option_sum ? (MapGet A m a)). Intro H3. Elim H3.
    Intros y H4. Rewrite (MapSweep_semantics_3 ? ? ? H2 a y H4) in H1. Discriminate H1.
    Intro H3. Rewrite H3 in H0. Discriminate H0.
  Qed.

  Lemma MapDisjoint_imp_2 : (m:(Map A)) (m':(Map B)) (MapDisjoint m m') -> 
      (MapDisjoint_2 m m').
  Proof.
    Unfold MapDisjoint MapDisjoint_2. Unfold eqmap eqm. Intros.
    Rewrite (MapDomRestrTo_semantics A B m m' a).
    Cut (in_dom A a m)=true->(in_dom B a m')=true->False. Intro.
    Elim (option_sum ? (MapGet A m a)). Intro H1. Elim H1. Intros y H2. Unfold 1 in_dom in H0.
    Elim (option_sum ? (MapGet B m' a)). Intro H3. Elim H3. Intros y' H4. Unfold 1 in_dom in H0.
    Rewrite H4 in H0. Rewrite H2 in H0. Elim (H0 (refl_equal ? ?) (refl_equal ? ?)).
    Intro H3. Rewrite H3. Reflexivity.
    Intro H1. Rewrite H1. Case (MapGet B m' a); Reflexivity.
    Exact (H a).
  Qed.

  Lemma MapDisjoint_2_imp : (m:(Map A)) (m':(Map B)) (MapDisjoint_2 m m') -> 
      (MapDisjoint m m').
  Proof.
    Unfold MapDisjoint MapDisjoint_2. Unfold eqmap eqm. Intros. Elim (in_dom_some ? ? ? H0).
    Intros y H2. Elim (in_dom_some ? ? ? H1). Intros y' H3.
    Cut (MapGet A (MapDomRestrTo A B m m') a)=(NONE A). Intro.
    Rewrite (MapDomRestrTo_semantics ? ? m m' a) in H4. Rewrite H3 in H4. Rewrite H2 in H4.
    Discriminate H4.
    Exact (H a).
  Qed.

  Lemma Map_M0_disjoint : (m:(Map B)) (MapDisjoint (M0 A) m).
  Proof.
    Unfold MapDisjoint in_dom. Intros. Discriminate H.
  Qed.

  Lemma Map_disjoint_M0 : (m:(Map A)) (MapDisjoint m (M0 B)).
  Proof.
    Unfold MapDisjoint in_dom. Intros. Discriminate H0.
  Qed.

End MapDisjointDef.

Section MapDisjointExtra.

  Variable A, B : Set.

  Lemma MapDisjoint_ext : (m0,m1:(Map A)) (m2,m3:(Map B))
      (eqmap A m0 m1) -> (eqmap B m2 m3) -> 
        (MapDisjoint A B m0 m2) -> (MapDisjoint A B m1 m3).
  Proof.
    Intros. Apply MapDisjoint_2_imp. Unfold MapDisjoint_2.
    Apply eqmap_trans with m':=(MapDomRestrTo A B m0 m2). Apply eqmap_sym. Apply MapDomRestrTo_ext.
    Assumption.
    Assumption.
    Exact (MapDisjoint_imp_2 ? ? ? ? H1).
  Qed.

  Lemma MapMerge_disjoint : (m,m':(Map A)) (MapDisjoint A A m m') ->
      	(a:ad) (in_dom A a (MapMerge A m m'))=
	       (orb (andb (in_dom A a m) (negb (in_dom A a m')))
	            (andb (in_dom A a m') (negb (in_dom A a m)))).
  Proof.
    Unfold MapDisjoint. Intros. Rewrite in_dom_merge. Elim (sumbool_of_bool (in_dom A a m)).
    Intro H0. Rewrite H0. Elim (sumbool_of_bool (in_dom A a m')). Intro H1. Elim (H a H0 H1).
    Intro H1. Rewrite H1. Reflexivity.
    Intro H0. Rewrite H0. Simpl. Rewrite andb_b_true. Reflexivity.
  Qed.

  Lemma MapDisjoint_M2_l : (m0,m1:(Map A)) (m2,m3:(Map B))
      (MapDisjoint A B (M2 A m0 m1) (M2 B m2 m3)) -> (MapDisjoint A B m0 m2).
  Proof.
    Unfold MapDisjoint in_dom. Intros. Elim (option_sum ? (MapGet A m0 a)). Intro H2.
    Elim H2. Intros y H3. Elim (option_sum ? (MapGet B m2 a)). Intro H4. Elim H4.
    Intros y' H5. Apply (H (ad_double a)).
    Rewrite (MapGet_M2_bit_0_0 ? (ad_double a) (ad_double_bit_0 a) m0 m1).
    Rewrite (ad_double_div_2 a). Rewrite H3. Reflexivity.
    Rewrite (MapGet_M2_bit_0_0 ? (ad_double a) (ad_double_bit_0 a) m2 m3).
    Rewrite (ad_double_div_2 a). Rewrite H5. Reflexivity.
    Intro H4. Rewrite H4 in H1. Discriminate H1.
    Intro H2. Rewrite H2 in H0. Discriminate H0.
  Qed.

  Lemma MapDisjoint_M2_r : (m0,m1:(Map A)) (m2,m3:(Map B))
      (MapDisjoint A B (M2 A m0 m1) (M2 B m2 m3)) -> (MapDisjoint A B m1 m3).
  Proof.
    Unfold MapDisjoint in_dom. Intros. Elim (option_sum ? (MapGet A m1 a)). Intro H2.
    Elim H2. Intros y H3. Elim (option_sum ? (MapGet B m3 a)). Intro H4. Elim H4.
    Intros y' H5. Apply (H (ad_double_plus_un a)).
    Rewrite (MapGet_M2_bit_0_1 ? (ad_double_plus_un a) (ad_double_plus_un_bit_0 a) m0 m1).
    Rewrite (ad_double_plus_un_div_2 a). Rewrite H3. Reflexivity.
    Rewrite (MapGet_M2_bit_0_1 ? (ad_double_plus_un a) (ad_double_plus_un_bit_0 a) m2 m3).
    Rewrite (ad_double_plus_un_div_2 a). Rewrite H5. Reflexivity.
    Intro H4. Rewrite H4 in H1. Discriminate H1.
    Intro H2. Rewrite H2 in H0. Discriminate H0.
  Qed.

  Lemma MapDisjoint_M2 : (m0,m1:(Map A)) (m2,m3:(Map B))
      (MapDisjoint A B m0 m2) -> (MapDisjoint A B m1 m3) ->
      	(MapDisjoint A B (M2 A m0 m1) (M2 B m2 m3)).
  Proof.
    Unfold MapDisjoint in_dom. Intros. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H3.
    Rewrite (MapGet_M2_bit_0_1 A a H3 m0 m1) in H1.
    Rewrite (MapGet_M2_bit_0_1 B a H3 m2 m3) in H2. Exact (H0 (ad_div_2 a) H1 H2).
    Intro H3. Rewrite (MapGet_M2_bit_0_0 A a H3 m0 m1) in H1.
    Rewrite (MapGet_M2_bit_0_0 B a H3 m2 m3) in H2. Exact (H (ad_div_2 a) H1 H2).
  Qed.

  Lemma MapDisjoint_M1_l : (m:(Map A)) (a:ad) (y:B)
      (MapDisjoint B A (M1 B a y) m) -> (in_dom A a m)=false.
  Proof.
    Unfold MapDisjoint. Intros. Elim (sumbool_of_bool (in_dom A a m)). Intro H0.
    Elim (H a (in_dom_M1_1 B a y) H0).
    Trivial.
  Qed.

  Lemma MapDisjoint_M1_r : (m:(Map A)) (a:ad) (y:B)
      (MapDisjoint A B m (M1 B a y)) -> (in_dom A a m)=false.
  Proof.
    Unfold MapDisjoint. Intros. Elim (sumbool_of_bool (in_dom A a m)). Intro H0.
    Elim (H a H0 (in_dom_M1_1 B a y)).
    Trivial.
  Qed.

  Lemma MapDisjoint_M1_conv_l : (m:(Map A)) (a:ad) (y:B)
      (in_dom A a m)=false -> (MapDisjoint B A (M1 B a y) m).
  Proof.
    Unfold MapDisjoint. Intros. Rewrite (in_dom_M1_2 B a a0 y H0) in H. Rewrite H1 in H.
    Discriminate H.
  Qed.

  Lemma MapDisjoint_M1_conv_r : (m:(Map A)) (a:ad) (y:B)
      (in_dom A a m)=false -> (MapDisjoint A B m (M1 B a y)).
  Proof.
    Unfold MapDisjoint. Intros. Rewrite (in_dom_M1_2 B a a0 y H1) in H. Rewrite H0 in H.
    Discriminate H.
  Qed.
 
  Lemma MapDisjoint_sym : (m:(Map A)) (m':(Map B))
      (MapDisjoint A B m m') -> (MapDisjoint B A m' m).
  Proof.
    Unfold MapDisjoint. Intros. Exact (H ? H1 H0).
  Qed.

  Lemma MapDisjoint_empty : (m:(Map A)) (MapDisjoint A A m m) -> (eqmap A m (M0 A)).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite <- (MapDomRestrTo_idempotent A m a).
    Exact (MapDisjoint_imp_2 A A m m H a).
  Qed.

  Lemma MapDelta_disjoint : (m,m':(Map A)) (MapDisjoint A A m m') ->
      (eqmap A (MapDelta A m m') (MapMerge A m m')).
  Proof.
    Intros.
    Apply eqmap_trans with m':=(MapDomRestrBy A A (MapMerge A m m') (MapDomRestrTo A A m m')).
    Apply MapDelta_as_DomRestrBy.
    Apply eqmap_trans with m':=(MapDomRestrBy A A (MapMerge A m m') (M0 A)).
    Apply MapDomRestrBy_ext. Apply eqmap_refl.
    Exact (MapDisjoint_imp_2 A A m m' H).
    Apply MapDomRestrBy_m_empty.
  Qed.

  Variable C : Set.

  Lemma MapDomRestr_disjoint : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (MapDisjoint A B (MapDomRestrTo A C m m'') (MapDomRestrBy B C m' m'')).
  Proof.
    Unfold MapDisjoint. Intros m m' m'' a. Rewrite in_dom_restrto. Rewrite in_dom_restrby.
    Intros. Elim (andb_prop ? ? H). Elim (andb_prop ? ? H0). Intros. Rewrite H4 in H2.
    Discriminate H2.
  Qed.

  Lemma MapDelta_RestrTo_disjoint : (m,m':(Map A))
      (MapDisjoint A A (MapDelta A m m') (MapDomRestrTo A A m m')).
  Proof.
    Unfold MapDisjoint. Intros m m' a. Rewrite in_dom_delta. Rewrite in_dom_restrto.
    Intros. Elim (andb_prop ? ? H0). Intros. Rewrite H1 in H. Rewrite H2 in H. Discriminate H.
  Qed.

  Lemma MapDelta_RestrTo_disjoint_2 : (m,m':(Map A))
      (MapDisjoint A A (MapDelta A m m') (MapDomRestrTo A A m' m)).
  Proof.
    Unfold MapDisjoint. Intros m m' a. Rewrite in_dom_delta. Rewrite in_dom_restrto.
    Intros. Elim (andb_prop ? ? H0). Intros. Rewrite H1 in H. Rewrite H2 in H. Discriminate H.
  Qed.

  Variable D : Set.

  Lemma MapSubset_Disjoint : (m:(Map A)) (m':(Map B)) (m'':(Map C)) (m''':(Map D))
      (MapSubset ? ? m m') -> (MapSubset ? ? m'' m''') -> (MapDisjoint ? ? m' m''') ->
        (MapDisjoint ? ? m m'').
  Proof.
    Unfold MapSubset MapDisjoint. Intros. Exact (H1 ? (H ? H2) (H0 ? H3)).
  Qed.

  Lemma MapSubset_Disjoint_l : (m:(Map A)) (m':(Map B)) (m'':(Map C))
      (MapSubset ? ? m m') -> (MapDisjoint ? ? m' m'') ->
        (MapDisjoint ? ? m m'').
  Proof.
    Unfold MapSubset MapDisjoint. Intros. Exact (H0 ? (H ? H1) H2).
  Qed.

  Lemma MapSubset_Disjoint_r : (m:(Map A)) (m'':(Map C)) (m''':(Map D))
      (MapSubset ? ? m'' m''') -> (MapDisjoint ? ? m m''') ->
        (MapDisjoint ? ? m m'').
  Proof.
    Unfold MapSubset MapDisjoint. Intros. Exact (H0 ? H1 (H ? H2)).
  Qed.

End MapDisjointExtra.

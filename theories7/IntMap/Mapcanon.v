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
Require PolyList.
Require Lsort.
Require Mapsubset.
Require Mapcard.

Section MapCanon.

  Variable A : Set.

  Inductive mapcanon : (Map A) -> Prop :=
      M0_canon : (mapcanon (M0 A))
    | M1_canon : (a:ad) (y:A) (mapcanon (M1 A a y))
    | M2_canon : (m1,m2:(Map A)) (mapcanon m1) -> (mapcanon m2) ->
        (le (2) (MapCard A (M2 A m1 m2))) -> (mapcanon (M2 A m1 m2)).

  Lemma mapcanon_M2 : 
      (m1,m2:(Map A)) (mapcanon (M2 A m1 m2)) -> (le (2) (MapCard A (M2 A m1 m2))).
  Proof.
    Intros. Inversion H. Assumption.
  Qed.

  Lemma mapcanon_M2_1 : (m1,m2:(Map A)) (mapcanon (M2 A m1 m2)) -> (mapcanon m1).
  Proof.
    Intros. Inversion H. Assumption.
  Qed.

  Lemma mapcanon_M2_2 : (m1,m2:(Map A)) (mapcanon (M2 A m1 m2)) -> (mapcanon m2).
  Proof.
    Intros. Inversion H. Assumption.
  Qed.

  Lemma M2_eqmap_1 : (m0,m1,m2,m3:(Map A)) 
      (eqmap A (M2 A m0 m1) (M2 A m2 m3)) -> (eqmap A m0 m2).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite <- (ad_double_div_2 a).
    Rewrite <- (MapGet_M2_bit_0_0 A ? (ad_double_bit_0 a) m0 m1).
    Rewrite <- (MapGet_M2_bit_0_0 A ? (ad_double_bit_0 a) m2 m3).
    Exact (H (ad_double a)).
  Qed.

  Lemma M2_eqmap_2 : (m0,m1,m2,m3:(Map A)) 
      (eqmap A (M2 A m0 m1) (M2 A m2 m3)) -> (eqmap A m1 m3).
  Proof.
    Unfold eqmap eqm. Intros. Rewrite <- (ad_double_plus_un_div_2 a).
    Rewrite <- (MapGet_M2_bit_0_1 A ? (ad_double_plus_un_bit_0 a) m0 m1).
    Rewrite <- (MapGet_M2_bit_0_1 A ? (ad_double_plus_un_bit_0 a) m2 m3).
    Exact (H (ad_double_plus_un a)).
  Qed.

  Lemma mapcanon_unique : (m,m':(Map A)) (mapcanon m) -> (mapcanon m') ->
      (eqmap A m m') -> m=m'.
  Proof.
    Induction m. Induction m'. Trivial.
    Intros a y H H0 H1. Cut (NONE A)=(MapGet A (M1 A a y) a). Simpl. Rewrite (ad_eq_correct a).
    Intro. Discriminate H2.
    Exact (H1 a).
    Intros. Cut (le (2) (MapCard A (M0 A))). Intro. Elim (le_Sn_O ? H4).
    Rewrite (MapCard_ext A ? ? H3). Exact (mapcanon_M2 ? ? H2).
    Intros a y. Induction m'. Intros. Cut (MapGet A (M1 A a y) a)=(NONE A). Simpl.
    Rewrite (ad_eq_correct a). Intro. Discriminate H2.
    Exact (H1 a).
    Intros a0 y0 H H0 H1. Cut (MapGet A (M1 A a y) a)=(MapGet A (M1 A a0 y0) a). Simpl.
    Rewrite (ad_eq_correct a). Intro. Elim (sumbool_of_bool (ad_eq a0 a)). Intro H3.
    Rewrite H3 in H2. Inversion H2. Rewrite (ad_eq_complete ? ? H3). Reflexivity.
    Intro H3. Rewrite H3 in H2. Discriminate H2.
    Exact (H1 a).
    Intros. Cut (le (2) (MapCard A (M1 A a y))). Intro. Elim (le_Sn_O ? (le_S_n ? ? H4)).
    Rewrite (MapCard_ext A ? ? H3). Exact (mapcanon_M2 ? ? H2).
    Induction m'. Intros. Cut (le (2) (MapCard A (M0 A))). Intro. Elim (le_Sn_O ? H4).
    Rewrite <- (MapCard_ext A ? ? H3). Exact (mapcanon_M2 ? ? H1).
    Intros a y H1 H2 H3. Cut (le (2) (MapCard A (M1 A a y))). Intro.
    Elim (le_Sn_O ? (le_S_n ? ? H4)).
    Rewrite <- (MapCard_ext A ? ? H3). Exact (mapcanon_M2 ? ? H1).
    Intros. Rewrite (H m2). Rewrite (H0 m3). Reflexivity.
    Exact (mapcanon_M2_2 ? ? H3).
    Exact (mapcanon_M2_2 ? ? H4).
    Exact (M2_eqmap_2 ? ? ? ? H5).
    Exact (mapcanon_M2_1 ? ? H3).
    Exact (mapcanon_M2_1 ? ? H4).
    Exact (M2_eqmap_1 ? ? ? ? H5).
  Qed.

  Lemma MapPut1_canon : 
      (p:positive) (a,a':ad) (y,y':A) (mapcanon (MapPut1 A a y a' y' p)).
  Proof.
    Induction p. Simpl. Intros. Case (ad_bit_0 a). Apply M2_canon. Apply M1_canon.
    Apply M1_canon.
    Apply le_n.
    Apply M2_canon. Apply M1_canon.
    Apply M1_canon.
    Apply le_n.
    Simpl. Intros. Case (ad_bit_0 a). Apply M2_canon. Apply M0_canon.
    Apply H.
    Simpl. Rewrite MapCard_Put1_equals_2. Apply le_n.
    Apply M2_canon. Apply H.
    Apply M0_canon.
    Simpl. Rewrite MapCard_Put1_equals_2. Apply le_n.
    Simpl. Simpl. Intros. Case (ad_bit_0 a). Apply M2_canon. Apply M1_canon.
    Apply M1_canon.
    Simpl. Apply le_n.
    Apply M2_canon. Apply M1_canon.
    Apply M1_canon.
    Simpl. Apply le_n.
  Qed.

  Lemma MapPut_canon : 
      (m:(Map A)) (mapcanon m) -> (a:ad) (y:A) (mapcanon (MapPut A m a y)).
  Proof.
    Induction m. Intros. Simpl. Apply M1_canon.
    Intros a0 y0 H a y. Simpl. Case (ad_xor a0 a). Apply M1_canon.
    Intro. Apply MapPut1_canon.
    Intros. Simpl. Elim a. Apply M2_canon. Apply H. Exact (mapcanon_M2_1 m0 m1 H1).
    Exact (mapcanon_M2_2 m0 m1 H1).
    Simpl. Apply le_trans with m:=(plus (MapCard A m0) (MapCard A m1)). Exact (mapcanon_M2 ? ? H1).
    Apply le_plus_plus. Exact (MapCard_Put_lb A m0 ad_z y).
    Apply le_n.
    Intro. Case p. Intro. Apply M2_canon. Exact (mapcanon_M2_1 m0 m1 H1).
    Apply H0. Exact (mapcanon_M2_2 m0 m1 H1).
    Simpl. Apply le_trans with m:=(plus (MapCard A m0) (MapCard A m1)).
    Exact (mapcanon_M2 m0 m1 H1).
    Apply le_reg_l. Exact (MapCard_Put_lb A m1 (ad_x p0) y).
    Intro. Apply M2_canon. Apply H. Exact (mapcanon_M2_1 m0 m1 H1).
    Exact (mapcanon_M2_2 m0 m1 H1).
    Simpl. Apply le_trans with m:=(plus (MapCard A m0) (MapCard A m1)).
    Exact (mapcanon_M2 m0 m1 H1).
    Apply le_reg_r. Exact (MapCard_Put_lb A m0 (ad_x p0) y).
    Apply M2_canon. Apply (mapcanon_M2_1 m0 m1 H1).
    Apply H0. Apply (mapcanon_M2_2 m0 m1 H1).
    Simpl. Apply le_trans with m:=(plus (MapCard A m0) (MapCard A m1)).
    Exact (mapcanon_M2 m0 m1 H1).
    Apply le_reg_l. Exact (MapCard_Put_lb A m1 ad_z y).
  Qed.

  Lemma MapPut_behind_canon : (m:(Map A)) (mapcanon m) ->
      (a:ad) (y:A) (mapcanon (MapPut_behind A m a y)).
  Proof.
    Induction m. Intros. Simpl. Apply M1_canon.
    Intros a0 y0 H a y. Simpl. Case (ad_xor a0 a). Apply M1_canon.
    Intro. Apply MapPut1_canon.
    Intros. Simpl. Elim a. Apply M2_canon. Apply H. Exact (mapcanon_M2_1 m0 m1 H1).
    Exact (mapcanon_M2_2 m0 m1 H1).
    Simpl. Apply le_trans with m:=(plus (MapCard A m0) (MapCard A m1)). Exact (mapcanon_M2 ? ? H1).
    Apply le_plus_plus. Rewrite MapCard_Put_behind_Put. Exact (MapCard_Put_lb A m0 ad_z y).
    Apply le_n.
    Intro. Case p. Intro. Apply M2_canon. Exact (mapcanon_M2_1 m0 m1 H1).
    Apply H0. Exact (mapcanon_M2_2 m0 m1 H1).
    Simpl. Apply le_trans with m:=(plus (MapCard A m0) (MapCard A m1)).
    Exact (mapcanon_M2 m0 m1 H1).
    Apply le_reg_l. Rewrite MapCard_Put_behind_Put. Exact (MapCard_Put_lb A m1 (ad_x p0) y).
    Intro. Apply M2_canon. Apply H. Exact (mapcanon_M2_1 m0 m1 H1).
    Exact (mapcanon_M2_2 m0 m1 H1).
    Simpl. Apply le_trans with m:=(plus (MapCard A m0) (MapCard A m1)).
    Exact (mapcanon_M2 m0 m1 H1).
    Apply le_reg_r. Rewrite MapCard_Put_behind_Put. Exact (MapCard_Put_lb A m0 (ad_x p0) y).
    Apply M2_canon. Apply (mapcanon_M2_1 m0 m1 H1).
    Apply H0. Apply (mapcanon_M2_2 m0 m1 H1).
    Simpl. Apply le_trans with m:=(plus (MapCard A m0) (MapCard A m1)).
    Exact (mapcanon_M2 m0 m1 H1).
    Apply le_reg_l. Rewrite MapCard_Put_behind_Put. Exact (MapCard_Put_lb A m1 ad_z y).
  Qed.

  Lemma makeM2_canon : 
      (m,m':(Map A)) (mapcanon m) -> (mapcanon m') -> (mapcanon (makeM2 A m m')).
  Proof.
    Intro. Case m. Intro. Case m'. Intros. Exact M0_canon.
    Intros a y H H0. Exact (M1_canon (ad_double_plus_un a) y).
    Intros. Simpl. (Apply M2_canon; Try Assumption). Exact (mapcanon_M2 m0 m1 H0).
    Intros a y m'. Case m'. Intros. Exact (M1_canon (ad_double a) y).
    Intros a0 y0 H H0. Simpl. (Apply M2_canon; Try Assumption). Apply le_n.
    Intros. Simpl. (Apply M2_canon; Try Assumption).
    Apply le_trans with m:=(MapCard A (M2 A m0 m1)). Exact (mapcanon_M2 ? ? H0).
    Exact (le_plus_r (MapCard A (M1 A a y)) (MapCard A (M2 A m0 m1))).
    Simpl. Intros. (Apply M2_canon; Try Assumption).
    Apply le_trans with m:=(MapCard A (M2 A m0 m1)). Exact (mapcanon_M2 ? ? H).
    Exact (le_plus_l (MapCard A (M2 A m0 m1)) (MapCard A m')).
  Qed.

  Fixpoint MapCanonicalize [m:(Map A)] : (Map A) :=
      Cases m of
          (M2 m0 m1) => (makeM2 A (MapCanonicalize m0) (MapCanonicalize m1))
	| _ => m
      end.

  Lemma mapcanon_exists_1 : (m:(Map A)) (eqmap A m (MapCanonicalize m)).
  Proof.
    Induction m. Apply eqmap_refl.
    Intros. Apply eqmap_refl.
    Intros. Simpl. Unfold eqmap eqm. Intro.
    Rewrite (makeM2_M2 A (MapCanonicalize m0) (MapCanonicalize m1) a).
    Rewrite MapGet_M2_bit_0_if. Rewrite MapGet_M2_bit_0_if.
    Rewrite <- (H (ad_div_2 a)). Rewrite <- (H0 (ad_div_2 a)). Reflexivity.
  Qed.

  Lemma mapcanon_exists_2 : (m:(Map A)) (mapcanon (MapCanonicalize m)).
  Proof.
    Induction m. Apply M0_canon.
    Intros. Simpl. Apply M1_canon.
    Intros. Simpl. (Apply makeM2_canon; Assumption).
  Qed.

  Lemma mapcanon_exists : 
      (m:(Map A)) {m':(Map A) | (eqmap A m m') /\ (mapcanon m')}.
  Proof.
    Intro. Split with (MapCanonicalize m). Split. Apply mapcanon_exists_1.
    Apply mapcanon_exists_2.
  Qed.

  Lemma MapRemove_canon : 
      (m:(Map A)) (mapcanon m) -> (a:ad) (mapcanon (MapRemove A m a)).
  Proof.
    Induction m. Intros. Exact M0_canon.
    Intros a y H a0. Simpl. Case (ad_eq a a0). Exact M0_canon.
    Assumption.
    Intros. Simpl. Case (ad_bit_0 a). Apply makeM2_canon. Exact (mapcanon_M2_1 ? ? H1).
    Apply H0. Exact (mapcanon_M2_2 ? ? H1).
    Apply makeM2_canon. Apply H. Exact (mapcanon_M2_1 ? ? H1).
    Exact (mapcanon_M2_2 ? ? H1).
  Qed.

  Lemma MapMerge_canon : (m,m':(Map A)) (mapcanon m) -> (mapcanon m') ->
      (mapcanon (MapMerge A m m')).
  Proof.
    Induction m. Intros. Exact H0.
    Simpl. Intros a y m' H H0. Exact (MapPut_behind_canon m' H0 a y).
    Induction m'. Intros. Exact H1.
    Intros a y H1 H2. Unfold MapMerge. Exact (MapPut_canon ? H1 a y).
    Intros. Simpl. Apply M2_canon. Apply H. Exact (mapcanon_M2_1 ? ? H3).
    Exact (mapcanon_M2_1 ? ? H4).
    Apply H0. Exact (mapcanon_M2_2 ? ? H3).
    Exact (mapcanon_M2_2 ? ? H4).
    Change (le (2) (MapCard A (MapMerge A (M2 A m0 m1) (M2 A m2 m3)))).
    Apply le_trans with m:=(MapCard A (M2 A m0 m1)). Exact (mapcanon_M2 ? ? H3).
    Exact (MapMerge_Card_lb_l A (M2 A m0 m1) (M2 A m2 m3)).
  Qed.

  Lemma MapDelta_canon : (m,m':(Map A)) (mapcanon m) -> (mapcanon m') ->
      (mapcanon (MapDelta A m m')).
  Proof.
    Induction m. Intros. Exact H0.
    Simpl. Intros a y m' H H0. Case (MapGet A m' a). Exact (MapPut_canon m' H0 a y).
    Intro. Exact (MapRemove_canon m' H0 a).
    Induction m'. Intros. Exact H1.
    Unfold MapDelta. Intros a y H1 H2. Case (MapGet A (M2 A m0 m1) a).
    Exact (MapPut_canon ? H1 a y).
    Intro. Exact (MapRemove_canon ? H1 a).
    Intros. Simpl. Apply makeM2_canon. Apply H. Exact (mapcanon_M2_1 ? ? H3).
    Exact (mapcanon_M2_1 ? ? H4).
    Apply H0. Exact (mapcanon_M2_2 ? ? H3).
    Exact (mapcanon_M2_2 ? ? H4).
  Qed.

  Variable B : Set.

  Lemma MapDomRestrTo_canon : (m:(Map A)) (mapcanon m) ->
      (m':(Map B)) (mapcanon (MapDomRestrTo A B m m')).
  Proof.
    Induction m. Intros. Exact M0_canon.
    Simpl. Intros a y H m'. Case (MapGet B m' a). Exact M0_canon.
    Intro. Apply M1_canon.
    Induction m'. Exact M0_canon.
    Unfold MapDomRestrTo. Intros a y. Case (MapGet A (M2 A m0 m1) a). Exact M0_canon.
    Intro. Apply M1_canon.
    Intros. Simpl. Apply makeM2_canon. Apply H. Exact (mapcanon_M2_1 m0 m1 H1).
    Apply H0. Exact (mapcanon_M2_2 m0 m1 H1).
  Qed.

  Lemma MapDomRestrBy_canon : (m:(Map A)) (mapcanon m) ->
      (m':(Map B)) (mapcanon (MapDomRestrBy A B m m')).
  Proof.
    Induction m. Intros. Exact M0_canon.
    Simpl. Intros a y H m'. Case (MapGet B m' a). Assumption.
    Intro. Exact M0_canon.
    Induction m'. Exact H1.
    Intros a y. Simpl. Case (ad_bit_0 a). Apply makeM2_canon. Exact (mapcanon_M2_1 ? ? H1).
    Apply MapRemove_canon. Exact (mapcanon_M2_2 ? ? H1).
    Apply makeM2_canon. Apply MapRemove_canon. Exact (mapcanon_M2_1 ? ? H1).
    Exact (mapcanon_M2_2 ? ? H1).
    Intros. Simpl. Apply makeM2_canon. Apply H. Exact (mapcanon_M2_1 ? ? H1).
    Apply H0. Exact (mapcanon_M2_2 ? ? H1).
  Qed.

  Lemma Map_of_alist_canon : (l:(alist A)) (mapcanon (Map_of_alist A l)).
  Proof.
    Induction l. Exact M0_canon.
    Intro r. Elim r. Intros a y l0 H. Simpl. Apply MapPut_canon. Assumption.
  Qed.

  Lemma MapSubset_c_1 : (m:(Map A)) (m':(Map B)) (mapcanon m) ->
      (MapSubset A B m m') -> (MapDomRestrBy A B m m')=(M0 A).
  Proof.
    Intros. Apply mapcanon_unique. Apply MapDomRestrBy_canon. Assumption.
    Apply M0_canon.
    Exact (MapSubset_imp_2 ? ? m m' H0).
  Qed.

  Lemma MapSubset_c_2 : (m:(Map A)) (m':(Map B))
      (MapDomRestrBy A B m m')=(M0 A) -> (MapSubset A B m m').
  Proof.
    Intros. Apply MapSubset_2_imp. Unfold MapSubset_2. Rewrite H. Apply eqmap_refl.
  Qed.

End MapCanon.

Section FSetCanon.

  Variable A : Set.

  Lemma MapDom_canon : (m:(Map A)) (mapcanon A m) -> (mapcanon unit (MapDom A m)).
  Proof.
    Induction m. Intro. Exact (M0_canon unit).
    Intros a y H. Exact (M1_canon unit a ?).
    Intros. Simpl. Apply M2_canon. Apply H. Exact (mapcanon_M2_1 A ? ? H1).
    Apply H0. Exact (mapcanon_M2_2 A ? ? H1).
    Change (le (2) (MapCard unit (MapDom A (M2 A m0 m1)))). Rewrite <- MapCard_Dom.
    Exact (mapcanon_M2 A ? ? H1).
  Qed.

End FSetCanon.

Section MapFoldCanon.

  Variable A, B : Set.

  Lemma MapFold_canon_1 : (m0:(Map B)) (mapcanon B m0) ->
      (op : (Map B) -> (Map B) -> (Map B))
      	((m1:(Map B)) (mapcanon B m1) -> (m2:(Map B)) (mapcanon B m2) ->
	  (mapcanon B (op m1 m2))) ->
      (f : ad->A->(Map B)) ((a:ad) (y:A) (mapcanon B (f a y))) ->
	(m:(Map A)) (pf : ad->ad) (mapcanon B (MapFold1 A (Map B) m0 op f pf m)).
  Proof.
    Induction m. Intro. Exact H.
    Intros a y pf. Simpl. Apply H1.
    Intros. Simpl. Apply H0. Apply H2.
    Apply H3.
  Qed.

  Lemma MapFold_canon : (m0:(Map B)) (mapcanon B m0) ->
      (op : (Map B) -> (Map B) -> (Map B))
      	((m1:(Map B)) (mapcanon B m1) -> (m2:(Map B)) (mapcanon B m2) ->
	  (mapcanon B (op m1 m2))) ->
      (f : ad->A->(Map B)) ((a:ad) (y:A) (mapcanon B (f a y))) ->
	(m:(Map A)) (mapcanon B (MapFold A (Map B) m0 op f m)).
  Proof.
    Intros. Exact (MapFold_canon_1 m0 H op H0 f H1 m [a:ad]a).
  Qed.

  Lemma MapCollect_canon : 
      (f : ad->A->(Map B)) ((a:ad) (y:A) (mapcanon B (f a y))) ->
	(m:(Map A)) (mapcanon B (MapCollect A B f m)).
  Proof.
    Intros. Rewrite MapCollect_as_Fold. Apply MapFold_canon. Apply M0_canon.
    Intros. Exact (MapMerge_canon B m1 m2 H0 H1).
    Assumption.
  Qed.

End MapFoldCanon.

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i   	  $Id$      i*)

Require Bool.
Require Sumbool.
Require ZArith.
Require Addr.
Require Adist.
Require Addec.
Require Map.
Require Fset.
Require Mapaxioms.
Require Mapiter.
Require Lsort.
Require Mapsubset.
Require PolyList.

Section MapFoldResults.

  Variable A : Set.

  Variable M : Set.
  Variable neutral : M.
  Variable op : M -> M -> M.

  Variable nleft : (a:M) (op neutral a)=a.
  Variable nright : (a:M) (op a neutral)=a.
  Variable assoc : (a,b,c:M) (op (op a b) c)=(op a (op b c)).

  Lemma MapFold_ext : (f:ad->A->M) (m,m':(Map A)) (eqmap A m m') ->
      (MapFold ? ? neutral op f m)=(MapFold ? ? neutral op f m').
  Proof.
    Intros. Rewrite (MapFold_as_fold A M neutral op assoc nleft nright f m).
    Rewrite (MapFold_as_fold A M neutral op assoc nleft nright f m').
    Cut (alist_of_Map A m)=(alist_of_Map A m'). Intro. Rewrite H0. Reflexivity.
    Apply alist_canonical. Unfold eqmap in H. Apply eqm_trans with f':=(MapGet A m).
    Apply eqm_sym. Apply alist_of_Map_semantics.
    Apply eqm_trans with f':=(MapGet A m'). Assumption.
    Apply alist_of_Map_semantics.
    Apply alist_of_Map_sorts2.
    Apply alist_of_Map_sorts2.
  Qed.

  Lemma MapFold_ext_f_1 : (m:(Map A)) (f,g:ad->A->M) (pf:ad->ad)
      ((a:ad) (y:A) (MapGet ? m a)=(SOME ? y) -> (f (pf a) y)=(g (pf a) y)) ->
        (MapFold1 ? ? neutral op f pf m)=(MapFold1 ? ? neutral op g pf m).
  Proof.
    Induction m. Trivial.
    Simpl. Intros. Apply H. Rewrite (ad_eq_correct a). Reflexivity.
    Intros. Simpl. Rewrite (H f g [a0:ad](pf (ad_double a0))).
    Rewrite (H0 f g [a0:ad](pf (ad_double_plus_un a0))). Reflexivity.
    Intros. Apply H1. Rewrite MapGet_M2_bit_0_1. Rewrite ad_double_plus_un_div_2. Assumption.
    Apply ad_double_plus_un_bit_0.
    Intros. Apply H1. Rewrite MapGet_M2_bit_0_0. Rewrite ad_double_div_2. Assumption.
    Apply ad_double_bit_0.
  Qed.

  Lemma MapFold_ext_f : (f,g:ad->A->M) (m:(Map A))
      ((a:ad) (y:A) (MapGet ? m a)=(SOME ? y) -> (f a y)=(g a y)) ->
        (MapFold ? ? neutral op f m)=(MapFold ? ? neutral op g m).
  Proof.
    Intros. Exact (MapFold_ext_f_1 m f g [a0:ad]a0 H).
  Qed.

  Lemma MapFold1_as_Fold_1 : (m:(Map A)) (f,f':ad->A->M) (pf, pf':ad->ad)
      ((a:ad) (y:A) (f (pf a) y)=(f' (pf' a) y)) ->
        (MapFold1 ? ? neutral op f pf m)=(MapFold1 ? ? neutral op f' pf' m).
  Proof.
    Induction m. Trivial.
    Intros. Simpl. Apply H.
    Intros. Simpl.
    Rewrite (H f f' [a0:ad](pf (ad_double a0)) [a0:ad](pf' (ad_double a0))).
    Rewrite (H0 f f' [a0:ad](pf (ad_double_plus_un a0)) [a0:ad](pf' (ad_double_plus_un a0))).
    Reflexivity.
    Intros. Apply H1.
    Intros. Apply H1.
  Qed.

  Lemma MapFold1_as_Fold : (f:ad->A->M) (pf:ad->ad) (m:(Map A))
      (MapFold1 ? ? neutral op f pf m)=(MapFold ? ? neutral op [a:ad][y:A] (f (pf a) y) m).
  Proof.
    Intros. Unfold MapFold. Apply MapFold1_as_Fold_1. Trivial.
  Qed.

  Lemma MapFold1_ext : (f:ad->A->M) (m,m':(Map A)) (eqmap A m m') -> (pf:ad->ad)
      (MapFold1 ? ? neutral op f pf m)=(MapFold1 ? ? neutral op f pf m').
  Proof.
    Intros. Rewrite MapFold1_as_Fold. Rewrite MapFold1_as_Fold. Apply MapFold_ext. Assumption.
  Qed.

  Variable comm : (a,b:M) (op a b)=(op b a).

  Lemma MapFold_Put_disjoint_1 : (p:positive)
        (f:ad->A->M) (pf:ad->ad) (a1,a2:ad) (y1,y2:A) 
	  (ad_xor a1 a2)=(ad_x p) ->
      	    (MapFold1 A M neutral op f pf (MapPut1 A a1 y1 a2 y2 p))=
	    (op (f (pf a1) y1) (f (pf a2) y2)).
  Proof.
    Induction p. Intros. Simpl. Elim (sumbool_of_bool (ad_bit_0 a1)). Intro H1. Rewrite H1.
    Simpl. Rewrite ad_div_2_double_plus_un. Rewrite ad_div_2_double. Apply comm.
    Change (ad_bit_0 a2)=(negb true). Rewrite <- H1. Rewrite (ad_neg_bit_0_2 ? ? ? H0).
    Rewrite negb_elim. Reflexivity.
    Assumption.
    Intro H1. Rewrite H1. Simpl. Rewrite ad_div_2_double. Rewrite ad_div_2_double_plus_un.
    Reflexivity.
    Change (ad_bit_0 a2)=(negb false). Rewrite <- H1. Rewrite (ad_neg_bit_0_2 ? ? ? H0).
    Rewrite negb_elim. Reflexivity.
    Assumption.
    Simpl. Intros. Elim (sumbool_of_bool (ad_bit_0 a1)). Intro H1. Rewrite H1. Simpl.
    Rewrite nleft.
    Rewrite (H f [a0:ad](pf (ad_double_plus_un a0)) (ad_div_2 a1) (ad_div_2 a2) y1 y2).
    Rewrite ad_div_2_double_plus_un. Rewrite ad_div_2_double_plus_un. Reflexivity.
    Rewrite <- (ad_same_bit_0 ? ? ? H0). Assumption.
    Assumption.
    Rewrite <- ad_xor_div_2. Rewrite H0. Reflexivity.
    Intro H1. Rewrite H1. Simpl. Rewrite nright.
    Rewrite (H f [a0:ad](pf (ad_double a0)) (ad_div_2 a1) (ad_div_2 a2) y1 y2).
    Rewrite ad_div_2_double. Rewrite ad_div_2_double. Reflexivity.
    Rewrite <- (ad_same_bit_0 ? ? ? H0). Assumption.
    Assumption.
    Rewrite <- ad_xor_div_2. Rewrite H0. Reflexivity.
    Intros. Simpl. Elim (sumbool_of_bool (ad_bit_0 a1)). Intro H0. Rewrite H0. Simpl.
    Rewrite ad_div_2_double. Rewrite ad_div_2_double_plus_un. Apply comm.
    Assumption.
    Change (ad_bit_0 a2)=(negb true). Rewrite <- H0. Rewrite (ad_neg_bit_0_1 ? ? H).
    Rewrite negb_elim. Reflexivity.
    Intro H0. Rewrite H0. Simpl. Rewrite ad_div_2_double. Rewrite ad_div_2_double_plus_un.
    Reflexivity.
    Change (ad_bit_0 a2)=(negb false). Rewrite <- H0. Rewrite (ad_neg_bit_0_1 ? ? H).
    Rewrite negb_elim. Reflexivity.
    Assumption.
  Qed.

  Lemma MapFold_Put_disjoint_2 : 
        (f:ad->A->M) (m:(Map A)) (a:ad) (y:A) (pf:ad->ad)
	  (MapGet A m a)=(NONE A) ->
      	    (MapFold1 A M neutral op f pf (MapPut A m a y))=
	    (op (f (pf a) y) (MapFold1 A M neutral op f pf m)).
  Proof.
    Induction m. Intros. Simpl. Rewrite (nright (f (pf a) y)). Reflexivity.
    Intros a1 y1 a2 y2 pf H. Simpl. Elim (ad_sum (ad_xor a1 a2)). Intro H0. Elim H0.
    Intros p H1. Rewrite H1. Rewrite comm. Exact (MapFold_Put_disjoint_1 p f pf a1 a2 y1 y2 H1).
    Intro H0. Rewrite (ad_eq_complete ? ? (ad_xor_eq_true ? ? H0)) in H.
    Rewrite (M1_semantics_1 A a2 y1) in H. Discriminate H.
    Intros. Elim (sumbool_of_bool (ad_bit_0 a)). Intro H2.
    Cut (MapPut A (M2 A m0 m1) a y)=(M2 A m0 (MapPut A m1 (ad_div_2 a) y)). Intro.
    Rewrite H3. Simpl. Rewrite (H0 (ad_div_2 a) y [a0:ad](pf (ad_double_plus_un a0))).
    Rewrite ad_div_2_double_plus_un. Rewrite <- assoc.
    Rewrite (comm (MapFold1 A M neutral op f [a0:ad](pf (ad_double a0)) m0) (f (pf a) y)).
    Rewrite assoc. Reflexivity.
    Assumption.
    Rewrite (MapGet_M2_bit_0_1 A a H2 m0 m1) in H1. Assumption.
    Simpl. Elim (ad_sum a). Intro H3. Elim H3. Intro p. Elim p. Intros p0 H4 H5. Rewrite H5.
    Reflexivity.
    Intros p0 H4 H5. Rewrite H5 in H2. Discriminate H2.
    Intro H4. Rewrite H4. Reflexivity.
    Intro H3. Rewrite H3 in H2. Discriminate H2.
    Intro H2. Cut (MapPut A (M2 A m0 m1) a y)=(M2 A (MapPut A m0 (ad_div_2 a) y) m1).
    Intro. Rewrite H3. Simpl. Rewrite (H (ad_div_2 a) y [a0:ad](pf (ad_double a0))).
    Rewrite ad_div_2_double. Rewrite <- assoc. Reflexivity.
    Assumption.
    Rewrite (MapGet_M2_bit_0_0 A a H2 m0 m1) in H1. Assumption.
    Simpl. Elim (ad_sum a). Intro H3. Elim H3. Intro p. Elim p. Intros p0 H4 H5. Rewrite H5 in H2.
    Discriminate H2.
    Intros p0 H4 H5. Rewrite H5. Reflexivity.
    Intro H4. Rewrite H4 in H2. Discriminate H2.
    Intro H3. Rewrite H3. Reflexivity.
  Qed.

  Lemma MapFold_Put_disjoint : 
        (f:ad->A->M) (m:(Map A)) (a:ad) (y:A)
	  (MapGet A m a)=(NONE A) ->
      	    (MapFold A M neutral op f (MapPut A m a y))=
	    (op (f a y) (MapFold A M neutral op f m)).
  Proof.
    Intros. Exact (MapFold_Put_disjoint_2 f m a y [a0:ad]a0 H).
  Qed.

  Lemma MapFold_Put_behind_disjoint_2 : 
        (f:ad->A->M) (m:(Map A)) (a:ad) (y:A) (pf:ad->ad)
	  (MapGet A m a)=(NONE A) ->
      	    (MapFold1 A M neutral op f pf (MapPut_behind A m a y))=
	    (op (f (pf a) y) (MapFold1 A M neutral op f pf m)).
  Proof.
    Intros. Cut (eqmap A (MapPut_behind A m a y) (MapPut A m a y)). Intro.
    Rewrite (MapFold1_ext f ? ? H0 pf). Apply MapFold_Put_disjoint_2. Assumption.
    Apply eqmap_trans with m':=(MapMerge A (M1 A a y) m). Apply MapPut_behind_as_Merge.
    Apply eqmap_trans with m':=(MapMerge A m (M1 A a y)).
    Apply eqmap_trans with m':=(MapDelta A (M1 A a y) m). Apply eqmap_sym. Apply MapDelta_disjoint.
    Unfold MapDisjoint. Unfold in_dom. Simpl. Intros. Elim (sumbool_of_bool (ad_eq a a0)).
    Intro H2. Rewrite (ad_eq_complete ? ? H2) in H. Rewrite H in H1. Discriminate H1.
    Intro H2. Rewrite H2 in H0. Discriminate H0.
    Apply eqmap_trans with m':=(MapDelta A m (M1 A a y)). Apply MapDelta_sym.
    Apply MapDelta_disjoint. Unfold MapDisjoint. Unfold in_dom. Simpl. Intros.
    Elim (sumbool_of_bool (ad_eq a a0)). Intro H2. Rewrite (ad_eq_complete ? ? H2) in H.
    Rewrite H in H0. Discriminate H0.
    Intro H2. Rewrite H2 in H1. Discriminate H1.
    Apply eqmap_sym. Apply MapPut_as_Merge.
  Qed.

  Lemma MapFold_Put_behind_disjoint : 
        (f:ad->A->M) (m:(Map A)) (a:ad) (y:A)
	  (MapGet A m a)=(NONE A) ->
      	    (MapFold A M neutral op f (MapPut_behind A m a y))
            =(op (f a y) (MapFold A M neutral op f m)).
  Proof.
    Intros. Exact (MapFold_Put_behind_disjoint_2 f m a y [a0:ad]a0 H).
  Qed.

  Lemma MapFold_Merge_disjoint_1 :
        (f:ad->A->M) (m1,m2:(Map A)) (pf:ad->ad)
	  (MapDisjoint A A m1 m2) ->
      	    (MapFold1 A M neutral op f pf (MapMerge A m1 m2))=
	    (op (MapFold1 A M neutral op f pf m1) (MapFold1 A M neutral op f pf m2)).
  Proof.
    Induction m1. Simpl. Intros. Rewrite nleft. Reflexivity.
    Intros. Unfold MapMerge. Apply (MapFold_Put_behind_disjoint_2 f m2 a a0 pf).
    Apply in_dom_none. Exact (MapDisjoint_M1_l ? ? m2 a a0 H).
    Induction m2. Intros. Simpl. Rewrite nright. Reflexivity.
    Intros. Unfold MapMerge. Rewrite (MapFold_Put_disjoint_2 f (M2 A m m0) a a0 pf). Apply comm.
    Apply in_dom_none. Exact (MapDisjoint_M1_r ? ? (M2 A m m0) a a0 H1).
    Intros. Simpl. Rewrite (H m3 [a0:ad](pf (ad_double a0))).
    Rewrite (H0 m4 [a0:ad](pf (ad_double_plus_un a0))).
    Cut (a,b,c,d:M)(op (op a b) (op c d))=(op (op a c) (op b d)). Intro. Apply H4.
    Intros. Rewrite assoc. Rewrite <- (assoc b c d). Rewrite (comm b c). Rewrite (assoc c b d).
    Rewrite assoc. Reflexivity.
    Exact (MapDisjoint_M2_r ? ? ? ? ? ? H3).
    Exact (MapDisjoint_M2_l ? ? ? ? ? ? H3).
  Qed.

  Lemma MapFold_Merge_disjoint :
        (f:ad->A->M) (m1,m2:(Map A))
	  (MapDisjoint A A m1 m2) ->
      	    (MapFold A M neutral op f (MapMerge A m1 m2))=
	    (op (MapFold A M neutral op f m1) (MapFold A M neutral op f m2)).
  Proof.
    Intros. Exact (MapFold_Merge_disjoint_1 f m1 m2 [a0:ad]a0 H).
  Qed.
 
End MapFoldResults.

Section MapFoldDistr.

  Variable A : Set.

  Variable M : Set.
  Variable neutral : M.
  Variable op : M -> M -> M.

  Variable M' : Set.
  Variable neutral' : M'.
  Variable op' : M' -> M' -> M'.

  Variable N : Set.

  Variable times : M -> N -> M'.

  Variable absorb : (c:N)(times neutral c)=neutral'.
  Variable distr : (a,b:M) (c:N) (times (op a b) c) = (op' (times a c) (times b c)).

  Lemma MapFold_distr_r_1 : (f:ad->A->M) (m:(Map A)) (c:N) (pf:ad->ad)
      (times (MapFold1 A M neutral op f pf m) c)=
      (MapFold1 A M' neutral' op' [a:ad][y:A] (times (f a y) c) pf m).
  Proof.
    Induction m. Intros. Exact (absorb c).
    Trivial.
    Intros. Simpl. Rewrite distr. Rewrite H. Rewrite H0. Reflexivity.
  Qed.

  Lemma MapFold_distr_r : (f:ad->A->M) (m:(Map A)) (c:N)
      (times (MapFold A M neutral op f m) c)=
      (MapFold A M' neutral' op' [a:ad][y:A] (times (f a y) c) m).
  Proof.
    Intros. Exact (MapFold_distr_r_1 f m c [a:ad]a).
  Qed.

End MapFoldDistr.

Section MapFoldDistrL.

  Variable A : Set.

  Variable M : Set.
  Variable neutral : M.
  Variable op : M -> M -> M.

  Variable M' : Set.
  Variable neutral' : M'.
  Variable op' : M' -> M' -> M'.

  Variable N : Set.

  Variable times : N -> M -> M'.

  Variable absorb : (c:N)(times c neutral)=neutral'.
  Variable distr : (a,b:M) (c:N) (times c (op a b)) = (op' (times c a) (times c b)).

  Lemma MapFold_distr_l : (f:ad->A->M) (m:(Map A)) (c:N)
      (times c (MapFold A M neutral op f m))=
      (MapFold A M' neutral' op' [a:ad][y:A] (times c (f a y)) m).
  Proof.
    Intros. Apply MapFold_distr_r with times:=[a:M][b:N](times b a); Assumption.
  Qed.

End MapFoldDistrL.

Section MapFoldExists.

  Variable A : Set.

  Lemma MapFold_orb_1 : (f:ad->A->bool) (m:(Map A)) (pf:ad->ad)
      	       	      (MapFold1 A bool false orb f pf m)=
                      (Cases (MapSweep1 A f pf m) of
		           (SOME _) => true
			 | _ => false
	               end).
  Proof.
    Induction m. Trivial.
    Intros a y pf. Simpl. Unfold MapSweep2. (Case (f (pf a) y); Reflexivity).
    Intros. Simpl. Rewrite (H [a0:ad](pf (ad_double a0))).
    Rewrite (H0 [a0:ad](pf (ad_double_plus_un a0))).
    Case (MapSweep1 A f [a0:ad](pf (ad_double a0)) m0); Reflexivity.
  Qed.

  Lemma MapFold_orb : (f:ad->A->bool) (m:(Map A)) (MapFold A bool false orb f m)=
                      (Cases (MapSweep A f m) of
		           (SOME _) => true
			 | _ => false
	               end).
  Proof.
    Intros. Exact (MapFold_orb_1 f m [a:ad]a).
  Qed.

End MapFoldExists.

Section DMergeDef.

  Variable A : Set.

  Definition DMerge := (MapFold (Map A) (Map A) (M0 A) (MapMerge A) [_:ad][m:(Map A)] m).

  Lemma in_dom_DMerge_1 : (m:(Map (Map A))) (a:ad) (in_dom A a (DMerge m))=
                              (Cases (MapSweep ? [_:ad][m0:(Map A)] (in_dom A a m0) m) of
			           (SOME _) => true
				 | _ => false
		               end).
  Proof.
    Unfold DMerge. Intros.
    Rewrite (MapFold_distr_l (Map A) (Map A) (M0 A) (MapMerge A) bool false
               orb ad (in_dom A) [c:ad](refl_equal ? ?) (in_dom_merge A)).
    Apply MapFold_orb.
  Qed.

  Lemma in_dom_DMerge_2 : (m:(Map (Map A))) (a:ad) (in_dom A a (DMerge m))=true ->
                               {b:ad & {m0:(Map A) | (MapGet ? m b)=(SOME ? m0) /\
			                             (in_dom A a m0)=true}}.
  Proof.
    Intros m a. Rewrite in_dom_DMerge_1.
    Elim (option_sum ? (MapSweep (Map A) [_:ad][m0:(Map A)](in_dom A a m0) m)).
    Intro H. Elim H. Intro r. Elim r. Intros b m0 H0. Intro. Split with b. Split with m0.
    Split. Exact (MapSweep_semantics_2 ? ? ? ? ? H0).
    Exact (MapSweep_semantics_1 ? ? ? ? ? H0).
    Intro H. Rewrite H. Intro. Discriminate H0.
  Qed.

  Lemma in_dom_DMerge_3 : (m:(Map (Map A))) (a,b:ad) (m0:(Map A))
      (MapGet ? m a)=(SOME ? m0) -> (in_dom A b m0)=true -> 
        (in_dom A b (DMerge m))=true.
  Proof.
    Intros m a b m0 H H0. Rewrite in_dom_DMerge_1.
    Elim (MapSweep_semantics_4 ? [_:ad][m'0:(Map A)](in_dom A b m'0) ? ? ? H H0).
    Intros a' H1. Elim H1. Intros m'0 H2. Rewrite H2. Reflexivity.
  Qed.

End DMergeDef.

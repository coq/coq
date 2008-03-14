(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i   	  $Id$      i*)

Require Import Bool.
Require Import Sumbool.
Require Import NArith.
Require Import Ndigits.
Require Import Ndec.
Require Import Map.
Require Import Fset.
Require Import Mapaxioms.
Require Import Mapiter.
Require Import Lsort.
Require Import Mapsubset.
Require Import List.

Section MapFoldResults.

  Variable A : Set.

  Variable M : Set.
  Variable neutral : M.
  Variable op : M -> M -> M.

  Variable nleft : forall a:M, op neutral a = a.
  Variable nright : forall a:M, op a neutral = a.
  Variable assoc : forall a b c:M, op (op a b) c = op a (op b c).

  Lemma MapFold_ext :
   forall (f:ad -> A -> M) (m m':Map A),
     eqmap A m m' -> MapFold _ _ neutral op f m = MapFold _ _ neutral op f m'.
  Proof.
    intros. rewrite (MapFold_as_fold A M neutral op assoc nleft nright f m).
    rewrite (MapFold_as_fold A M neutral op assoc nleft nright f m').
    cut (alist_of_Map A m = alist_of_Map A m'). intro. rewrite H0. reflexivity.
    apply alist_canonical. unfold eqmap in H. apply eqm_trans with (f' := MapGet A m).
    apply eqm_sym. apply alist_of_Map_semantics.
    apply eqm_trans with (f' := MapGet A m'). assumption.
    apply alist_of_Map_semantics.
    apply alist_of_Map_sorts2.
    apply alist_of_Map_sorts2.
  Qed.

  Lemma MapFold_ext_f_1 :
   forall (m:Map A) (f g:ad -> A -> M) (pf:ad -> ad),
     (forall (a:ad) (y:A), MapGet _ m a = Some y -> f (pf a) y = g (pf a) y) ->
     MapFold1 _ _ neutral op f pf m = MapFold1 _ _ neutral op g pf m.
  Proof.
    simple induction m. trivial.
    simpl in |- *. intros. apply H. rewrite (Neqb_correct a). reflexivity.
    intros. simpl in |- *. rewrite (H f g (fun a0:ad => pf (Ndouble a0))).
    rewrite (H0 f g (fun a0:ad => pf (Ndouble_plus_one a0))). reflexivity.
    intros. apply H1. rewrite MapGet_M2_bit_0_1. rewrite Ndouble_plus_one_div2. assumption.
    apply Ndouble_plus_one_bit0.
    intros. apply H1. rewrite MapGet_M2_bit_0_0. rewrite Ndouble_div2. assumption.
    apply Ndouble_bit0.
  Qed.

  Lemma MapFold_ext_f :
   forall (f g:ad -> A -> M) (m:Map A),
     (forall (a:ad) (y:A), MapGet _ m a = Some y -> f a y = g a y) ->
     MapFold _ _ neutral op f m = MapFold _ _ neutral op g m.
  Proof.
    intros. exact (MapFold_ext_f_1 m f g (fun a0:ad => a0) H).
  Qed.

  Lemma MapFold1_as_Fold_1 :
   forall (m:Map A) (f f':ad -> A -> M) (pf pf':ad -> ad),
     (forall (a:ad) (y:A), f (pf a) y = f' (pf' a) y) ->
     MapFold1 _ _ neutral op f pf m = MapFold1 _ _ neutral op f' pf' m.
  Proof.
    simple induction m. trivial.
    intros. simpl in |- *. apply H.
    intros. simpl in |- *.
    rewrite
     (H f f' (fun a0:ad => pf (Ndouble a0))
        (fun a0:ad => pf' (Ndouble a0))).
    rewrite
     (H0 f f' (fun a0:ad => pf (Ndouble_plus_one a0))
        (fun a0:ad => pf' (Ndouble_plus_one a0))).
    reflexivity.
    intros. apply H1.
    intros. apply H1.
  Qed.

  Lemma MapFold1_as_Fold :
   forall (f:ad -> A -> M) (pf:ad -> ad) (m:Map A),
     MapFold1 _ _ neutral op f pf m =
     MapFold _ _ neutral op (fun (a:ad) (y:A) => f (pf a) y) m.
  Proof.
    intros. unfold MapFold in |- *. apply MapFold1_as_Fold_1. trivial.
  Qed.

  Lemma MapFold1_ext :
   forall (f:ad -> A -> M) (m m':Map A),
     eqmap A m m' ->
     forall pf:ad -> ad,
       MapFold1 _ _ neutral op f pf m = MapFold1 _ _ neutral op f pf m'.
  Proof.
    intros. rewrite MapFold1_as_Fold. rewrite MapFold1_as_Fold. apply MapFold_ext. assumption.
  Qed.

  Variable comm : forall a b:M, op a b = op b a.

  Lemma MapFold_Put_disjoint_1 :
   forall (p:positive) (f:ad -> A -> M) (pf:ad -> ad) 
     (a1 a2:ad) (y1 y2:A),
     Nxor a1 a2 = Npos p ->
     MapFold1 A M neutral op f pf (MapPut1 A a1 y1 a2 y2 p) =
     op (f (pf a1) y1) (f (pf a2) y2).
  Proof.
    simple induction p. intros. simpl in |- *. elim (sumbool_of_bool (Nbit0 a1)). intro H1. rewrite H1.
    simpl in |- *. rewrite Ndiv2_double_plus_one. rewrite Ndiv2_double. apply comm.
    change (Nbit0 a2 = negb true) in |- *. rewrite <- H1. rewrite (Nneg_bit0_2 _ _ _ H0).
    rewrite negb_elim. reflexivity.
    assumption.
    intro H1. rewrite H1. simpl in |- *. rewrite Ndiv2_double. rewrite Ndiv2_double_plus_one.
    reflexivity.
    change (Nbit0 a2 = negb false) in |- *. rewrite <- H1. rewrite (Nneg_bit0_2 _ _ _ H0).
    rewrite negb_elim. reflexivity.
    assumption.
    simpl in |- *. intros. elim (sumbool_of_bool (Nbit0 a1)). intro H1. rewrite H1. simpl in |- *.
    rewrite nleft.
    rewrite
     (H f (fun a0:ad => pf (Ndouble_plus_one a0)) (
        Ndiv2 a1) (Ndiv2 a2) y1 y2).
    rewrite Ndiv2_double_plus_one. rewrite Ndiv2_double_plus_one. reflexivity.
    unfold Nodd.
    rewrite <- (Nsame_bit0 _ _ _ H0). assumption.
    assumption.
    rewrite <- Nxor_div2. rewrite H0. reflexivity.
    intro H1. rewrite H1. simpl in |- *. rewrite nright.
    rewrite
     (H f (fun a0:ad => pf (Ndouble a0)) (Ndiv2 a1) (Ndiv2 a2) y1 y2)
     .
    rewrite Ndiv2_double. rewrite Ndiv2_double. reflexivity.
    unfold Neven.
    rewrite <- (Nsame_bit0 _ _ _ H0). assumption.
    assumption.
    rewrite <- Nxor_div2. rewrite H0. reflexivity.
    intros. simpl in |- *. elim (sumbool_of_bool (Nbit0 a1)). intro H0. rewrite H0. simpl in |- *.
    rewrite Ndiv2_double. rewrite Ndiv2_double_plus_one. apply comm.
    assumption.
    change (Nbit0 a2 = negb true) in |- *. rewrite <- H0. rewrite (Nneg_bit0_1 _ _ H).
    rewrite negb_elim. reflexivity.
    intro H0. rewrite H0. simpl in |- *. rewrite Ndiv2_double. rewrite Ndiv2_double_plus_one.
    reflexivity.
    change (Nbit0 a2 = negb false) in |- *. rewrite <- H0. rewrite (Nneg_bit0_1 _ _ H).
    rewrite negb_elim. reflexivity.
    assumption.
  Qed.

  Lemma MapFold_Put_disjoint_2 :
   forall (f:ad -> A -> M) (m:Map A) (a:ad) (y:A) (pf:ad -> ad),
     MapGet A m a = None ->
     MapFold1 A M neutral op f pf (MapPut A m a y) =
     op (f (pf a) y) (MapFold1 A M neutral op f pf m).
  Proof.
    simple induction m. intros. simpl in |- *. rewrite (nright (f (pf a) y)). reflexivity.
    intros a1 y1 a2 y2 pf H. simpl in |- *. elim (Ndiscr (Nxor a1 a2)). intro H0. elim H0.
    intros p H1. rewrite H1. rewrite comm. exact (MapFold_Put_disjoint_1 p f pf a1 a2 y1 y2 H1).
    intro H0. rewrite (Neqb_complete _ _ (Nxor_eq_true _ _ H0)) in H.
    rewrite (M1_semantics_1 A a2 y1) in H. discriminate H.
    intros. elim (sumbool_of_bool (Nbit0 a)). intro H2.
    cut (MapPut A (M2 A m0 m1) a y = M2 A m0 (MapPut A m1 (Ndiv2 a) y)). intro.
    rewrite H3. simpl in |- *. rewrite (H0 (Ndiv2 a) y (fun a0:ad => pf (Ndouble_plus_one a0))).
    rewrite Ndiv2_double_plus_one. rewrite <- assoc.
    rewrite
     (comm (MapFold1 A M neutral op f (fun a0:ad => pf (Ndouble a0)) m0)
        (f (pf a) y)).
    rewrite assoc. reflexivity.
    assumption.
    rewrite (MapGet_M2_bit_0_1 A a H2 m0 m1) in H1. assumption.
    simpl in |- *. elim (Ndiscr a). intro H3. elim H3. intro p. elim p. intros p0 H4 H5. rewrite H5.
    reflexivity.
    intros p0 H4 H5. rewrite H5 in H2. discriminate H2.
    intro H4. rewrite H4. reflexivity.
    intro H3. rewrite H3 in H2. discriminate H2.
    intro H2. cut (MapPut A (M2 A m0 m1) a y = M2 A (MapPut A m0 (Ndiv2 a) y) m1).
    intro. rewrite H3. simpl in |- *. rewrite (H (Ndiv2 a) y (fun a0:ad => pf (Ndouble a0))).
    rewrite Ndiv2_double. rewrite <- assoc. reflexivity.
    assumption.
    rewrite (MapGet_M2_bit_0_0 A a H2 m0 m1) in H1. assumption.
    simpl in |- *. elim (Ndiscr a). intro H3. elim H3. intro p. elim p. intros p0 H4 H5. rewrite H5 in H2.
    discriminate H2.
    intros p0 H4 H5. rewrite H5. reflexivity.
    intro H4. rewrite H4 in H2. discriminate H2.
    intro H3. rewrite H3. reflexivity.
  Qed.

  Lemma MapFold_Put_disjoint :
   forall (f:ad -> A -> M) (m:Map A) (a:ad) (y:A),
     MapGet A m a = None ->
     MapFold A M neutral op f (MapPut A m a y) =
     op (f a y) (MapFold A M neutral op f m).
  Proof.
    intros. exact (MapFold_Put_disjoint_2 f m a y (fun a0:ad => a0) H).
  Qed.

  Lemma MapFold_Put_behind_disjoint_2 :
   forall (f:ad -> A -> M) (m:Map A) (a:ad) (y:A) (pf:ad -> ad),
     MapGet A m a = None ->
     MapFold1 A M neutral op f pf (MapPut_behind A m a y) =
     op (f (pf a) y) (MapFold1 A M neutral op f pf m).
  Proof.
    intros. cut (eqmap A (MapPut_behind A m a y) (MapPut A m a y)). intro.
    rewrite (MapFold1_ext f _ _ H0 pf). apply MapFold_Put_disjoint_2. assumption.
    apply eqmap_trans with (m' := MapMerge A (M1 A a y) m). apply MapPut_behind_as_Merge.
    apply eqmap_trans with (m' := MapMerge A m (M1 A a y)).
    apply eqmap_trans with (m' := MapDelta A (M1 A a y) m). apply eqmap_sym. apply MapDelta_disjoint.
    unfold MapDisjoint in |- *. unfold in_dom in |- *. simpl in |- *. intros. elim (sumbool_of_bool (Neqb a a0)).
    intro H2. rewrite (Neqb_complete _ _ H2) in H. rewrite H in H1. discriminate H1.
    intro H2. rewrite H2 in H0. discriminate H0.
    apply eqmap_trans with (m' := MapDelta A m (M1 A a y)). apply MapDelta_sym.
    apply MapDelta_disjoint. unfold MapDisjoint in |- *. unfold in_dom in |- *. simpl in |- *. intros.
    elim (sumbool_of_bool (Neqb a a0)). intro H2. rewrite (Neqb_complete _ _ H2) in H.
    rewrite H in H0. discriminate H0.
    intro H2. rewrite H2 in H1. discriminate H1.
    apply eqmap_sym. apply MapPut_as_Merge.
  Qed.

  Lemma MapFold_Put_behind_disjoint :
   forall (f:ad -> A -> M) (m:Map A) (a:ad) (y:A),
     MapGet A m a = None ->
     MapFold A M neutral op f (MapPut_behind A m a y) =
     op (f a y) (MapFold A M neutral op f m).
  Proof.
    intros. exact (MapFold_Put_behind_disjoint_2 f m a y (fun a0:ad => a0) H).
  Qed.

  Lemma MapFold_Merge_disjoint_1 :
   forall (f:ad -> A -> M) (m1 m2:Map A) (pf:ad -> ad),
     MapDisjoint A A m1 m2 ->
     MapFold1 A M neutral op f pf (MapMerge A m1 m2) =
     op (MapFold1 A M neutral op f pf m1) (MapFold1 A M neutral op f pf m2).
  Proof.
    simple induction m1. simpl in |- *. intros. rewrite nleft. reflexivity.
    intros. unfold MapMerge in |- *. apply (MapFold_Put_behind_disjoint_2 f m2 a a0 pf).
    apply in_dom_none. exact (MapDisjoint_M1_l _ _ m2 a a0 H).
    simple induction m2. intros. simpl in |- *. rewrite nright. reflexivity.
    intros. unfold MapMerge in |- *. rewrite (MapFold_Put_disjoint_2 f (M2 A m m0) a a0 pf). apply comm.
    apply in_dom_none. exact (MapDisjoint_M1_r _ _ (M2 A m m0) a a0 H1).
    intros. simpl in |- *. rewrite (H m3 (fun a0:ad => pf (Ndouble a0))).
    rewrite (H0 m4 (fun a0:ad => pf (Ndouble_plus_one a0))).
    cut (forall a b c d:M, op (op a b) (op c d) = op (op a c) (op b d)). intro. apply H4.
    intros. rewrite assoc. rewrite <- (assoc b c d). rewrite (comm b c). rewrite (assoc c b d).
    rewrite assoc. reflexivity.
    exact (MapDisjoint_M2_r _ _ _ _ _ _ H3).
    exact (MapDisjoint_M2_l _ _ _ _ _ _ H3).
  Qed.

  Lemma MapFold_Merge_disjoint :
   forall (f:ad -> A -> M) (m1 m2:Map A),
     MapDisjoint A A m1 m2 ->
     MapFold A M neutral op f (MapMerge A m1 m2) =
     op (MapFold A M neutral op f m1) (MapFold A M neutral op f m2).
  Proof.
    intros. exact (MapFold_Merge_disjoint_1 f m1 m2 (fun a0:ad => a0) H).
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

  Variable absorb : forall c:N, times neutral c = neutral'.
  Variable
    distr :
      forall (a b:M) (c:N), times (op a b) c = op' (times a c) (times b c).

  Lemma MapFold_distr_r_1 :
   forall (f:ad -> A -> M) (m:Map A) (c:N) (pf:ad -> ad),
     times (MapFold1 A M neutral op f pf m) c =
     MapFold1 A M' neutral' op' (fun (a:ad) (y:A) => times (f a y) c) pf m.
  Proof.
    simple induction m. intros. exact (absorb c).
    trivial.
    intros. simpl in |- *. rewrite distr. rewrite H. rewrite H0. reflexivity.
  Qed.

  Lemma MapFold_distr_r :
   forall (f:ad -> A -> M) (m:Map A) (c:N),
     times (MapFold A M neutral op f m) c =
     MapFold A M' neutral' op' (fun (a:ad) (y:A) => times (f a y) c) m.
  Proof.
    intros. exact (MapFold_distr_r_1 f m c (fun a:ad => a)).
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

  Variable absorb : forall c:N, times c neutral = neutral'.
  Variable
    distr :
      forall (a b:M) (c:N), times c (op a b) = op' (times c a) (times c b).

  Lemma MapFold_distr_l :
   forall (f:ad -> A -> M) (m:Map A) (c:N),
     times c (MapFold A M neutral op f m) =
     MapFold A M' neutral' op' (fun (a:ad) (y:A) => times c (f a y)) m.
  Proof.
    intros. apply MapFold_distr_r with (times := fun (a:M) (b:N) => times b a);
  assumption.
  Qed.

End MapFoldDistrL.

Section MapFoldExists.

  Variable A : Set.

  Lemma MapFold_orb_1 :
   forall (f:ad -> A -> bool) (m:Map A) (pf:ad -> ad),
     MapFold1 A bool false orb f pf m =
     match MapSweep1 A f pf m with
     | Some _ => true
     | _ => false
     end.
  Proof.
    simple induction m. trivial.
    intros a y pf. simpl in |- *. unfold MapSweep2 in |- *. case (f (pf a) y); reflexivity.
    intros. simpl in |- *. rewrite (H (fun a0:ad => pf (Ndouble a0))).
    rewrite (H0 (fun a0:ad => pf (Ndouble_plus_one a0))).
    case (MapSweep1 A f (fun a0:ad => pf (Ndouble a0)) m0); reflexivity.
  Qed.

  Lemma MapFold_orb :
   forall (f:ad -> A -> bool) (m:Map A),
     MapFold A bool false orb f m =
     match MapSweep A f m with
     | Some _ => true
     | _ => false
     end.
  Proof.
    intros. exact (MapFold_orb_1 f m (fun a:ad => a)).
  Qed.

End MapFoldExists.

Section DMergeDef.

  Variable A : Set.

  Definition DMerge :=
    MapFold (Map A) (Map A) (M0 A) (MapMerge A) (fun (_:ad) (m:Map A) => m).

  Lemma in_dom_DMerge_1 :
   forall (m:Map (Map A)) (a:ad),
     in_dom A a (DMerge m) =
     match MapSweep _ (fun (_:ad) (m0:Map A) => in_dom A a m0) m with
     | Some _ => true
     | _ => false
     end.
  Proof.
    unfold DMerge in |- *. intros.
    rewrite
     (MapFold_distr_l (Map A) (Map A) (M0 A) (MapMerge A) bool false orb ad
        (in_dom A) (fun c:ad => refl_equal _) (in_dom_merge A))
     .
    apply MapFold_orb.
  Qed.

  Lemma in_dom_DMerge_2 :
   forall (m:Map (Map A)) (a:ad),
     in_dom A a (DMerge m) = true ->
     {b : ad & 
     {m0 : Map A | MapGet _ m b = Some m0 /\ in_dom A a m0 = true}}.
  Proof.
    intros m a. rewrite in_dom_DMerge_1.
    elim
     (option_sum _
        (MapSweep (Map A) (fun (_:ad) (m0:Map A) => in_dom A a m0) m)).
    intro H. elim H. intro r. elim r. intros b m0 H0. intro. split with b. split with m0.
    split. exact (MapSweep_semantics_2 _ _ _ _ _ H0).
    exact (MapSweep_semantics_1 _ _ _ _ _ H0).
    intro H. rewrite H. intro. discriminate H0.
  Qed.

  Lemma in_dom_DMerge_3 :
   forall (m:Map (Map A)) (a b:ad) (m0:Map A),
     MapGet _ m a = Some m0 ->
     in_dom A b m0 = true -> in_dom A b (DMerge m) = true.
  Proof.
    intros m a b m0 H H0. rewrite in_dom_DMerge_1.
    elim
     (MapSweep_semantics_4 _ (fun (_:ad) (m'0:Map A) => in_dom A b m'0) _ _ _
        H H0).
    intros a' H1. elim H1. intros m'0 H2. rewrite H2. reflexivity.
  Qed.

End DMergeDef.
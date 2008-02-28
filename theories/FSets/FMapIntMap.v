(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite sets library.  
 * Authors: Pierre Letouzey and Jean-Christophe Filliâtre 
 * Institution: LRI, CNRS UMR 8623 - Université Paris Sud
 *              91405 Orsay, France *)

(* $Id$ *)

Require Import Bool.
Require Import NArith Ndigits Ndec Nnat. 
Require Import Allmaps.
Require Import OrderedType.
Require Import OrderedTypeEx.
Require Import FMapInterface FMapList.


Set Implicit Arguments.

(** * An implementation of [FMapInterface.S] based on [IntMap] *)

(** Keys are of type [N]. The main functions are directly taken from 
  [IntMap]. Since they have no exact counterpart in [IntMap], functions 
  [fold], [map2] and [equal] are for now obtained by translation 
  to sorted lists. *)

(** [N] is an ordered type, using not the usual order on numbers, 
   but lexicographic ordering on bits (lower bit considered first). *) 

Module NUsualOrderedType <: UsualOrderedType.
  Definition t:=N.
  Definition eq:=@eq N.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Definition lt p q:= Nless p q = true.
 
  Definition lt_trans := Nless_trans.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
  intros; intro.
  rewrite H0 in H.
  red in H.
  rewrite Nless_not_refl in H; discriminate.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
  intros x y.
  destruct (Nless_total x y) as [[H|H]|H].
  apply LT; unfold lt; auto.
  apply GT; unfold lt; auto.
  apply EQ; auto.
  Qed.

End NUsualOrderedType.
 

(** The module of maps over [N] keys based on [IntMap] *)

Module MapIntMap <: S with Module E:=NUsualOrderedType.

  Module E:=NUsualOrderedType.
  Module ME:=OrderedTypeFacts(E).
  Module PE:=KeyOrderedType(E).

  Definition key := N.

  Definition t := Map.

  Section A.
  Variable A:Set.

  Definition empty : t A := M0 A.
 
  Definition is_empty (m : t A) : bool := 
    MapEmptyp _ (MapCanonicalize _ m).

  Definition find (x:key)(m: t A) : option A := MapGet _ m x.

  Definition mem (x:key)(m: t A) : bool := 
    match find x m with 
     | Some _ => true
     | None => false
    end.

  Definition add (x:key)(v:A)(m:t A) : t A := MapPut _ m x v.
  
  Definition remove (x:key)(m:t A) : t A := MapRemove _ m x.

  Definition elements (m : t A) : list (N*A) := alist_of_Map _ m.

  Definition cardinal (m : t A) : nat := MapCard _ m.

  Definition MapsTo (x:key)(v:A)(m:t A) := find x m = Some v.

  Definition In (x:key)(m:t A) := exists e:A, MapsTo x e m.

  Definition Empty m := forall (a : key)(e:A) , ~ MapsTo a e m.

  Definition eq_key (p p':key*A) := E.eq (fst p) (fst p').
      
  Definition eq_key_elt (p p':key*A) := 
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_key (p p':key*A) := E.lt (fst p) (fst p').

  Lemma Empty_alt : forall m, Empty m <-> forall a, find a m = None.
  Proof.
  unfold Empty, MapsTo.
  intuition.
  generalize (H a).
  destruct (find a m); intuition.
  elim (H0 a0); auto.
  rewrite H in H0; discriminate.
  Qed.

  Section Spec. 
  Variable  m m' m'' : t A.
  Variable x y z : key.
  Variable e e' : A.

  Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
  Proof. intros; rewrite <- H; auto. Qed.

  Lemma find_1 : MapsTo x e m -> find x m = Some e.
  Proof. unfold MapsTo; auto. Qed.

  Lemma find_2 : find x m = Some e -> MapsTo x e m.
  Proof. red; auto. Qed.

  Lemma empty_1 : Empty empty.
  Proof.
  rewrite Empty_alt; intros; unfold empty, find; simpl; auto.
  Qed.

  Lemma is_empty_1 : Empty m -> is_empty m = true. 
  Proof.
  unfold Empty, is_empty, find; intros.
  cut (MapCanonicalize _ m = M0 _).
  intros; rewrite H0; simpl; auto.
  apply mapcanon_unique.
  apply mapcanon_exists_2.
  constructor.
  red; red; simpl; intros.
  rewrite <- (mapcanon_exists_1 _ m).
  unfold MapsTo, find in *.
  generalize (H a).
  destruct (MapGet _ m a); auto.
  intros; generalize (H0 a0); destruct 1; auto.
  Qed.  

  Lemma is_empty_2 : is_empty m = true -> Empty m.
  Proof.
  unfold Empty, is_empty, MapsTo, find; intros.
  generalize (MapEmptyp_complete _ _ H); clear H; intros.
  rewrite (mapcanon_exists_1 _ m).
  rewrite H; simpl; auto.
  discriminate.
  Qed.

  Lemma mem_1 : In x m -> mem x m = true.
  Proof.
  unfold In, MapsTo, mem.
  destruct (find x m); auto.
  destruct 1; discriminate.
  Qed.

  Lemma mem_2 : forall m x, mem x m = true -> In x m. 
  Proof.
  unfold In, MapsTo, mem.
  intros.
  destruct (find x0 m0); auto; try discriminate.
  exists a; auto.
  Qed.

  Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
  Proof.
  unfold MapsTo, find, add.
  intro H; rewrite H; clear H.
  rewrite MapPut_semantics.
  rewrite Neqb_correct; auto.
  Qed.

  Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
  unfold MapsTo, find, add.
  intros.
  rewrite MapPut_semantics.
  rewrite H0.
  generalize (Neqb_complete x y).
  destruct (Neqb x y); auto.
  intros.
  elim H; auto.
  apply H1; auto.
  Qed.

  Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
  unfold MapsTo, find, add.
  rewrite MapPut_semantics.
  intro H.
  generalize (Neqb_complete x y).
  destruct (Neqb x y); auto.
  intros; elim H; auto.
  apply H0; auto.
  Qed.

  Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
  Proof. 
  unfold In, MapsTo, find, remove.
  rewrite MapRemove_semantics.
  intro H.
  rewrite H; rewrite Neqb_correct.
  red; destruct 1; discriminate.
  Qed.

  Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
  unfold MapsTo, find, remove.
  rewrite MapRemove_semantics.
  intros.
  rewrite H0.
  generalize (Neqb_complete x y).
  destruct (Neqb x y); auto.
  intros; elim H; apply H1; auto.
  Qed.

  Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
  Proof. 
  unfold MapsTo, find, remove.
  rewrite MapRemove_semantics.
  destruct (Neqb x y); intros; auto.
  discriminate.
  Qed.

  Lemma alist_sorted_sort : forall l, alist_sorted A l=true -> sort lt_key l.
  Proof.
  induction l.
  auto.
  simpl.
  destruct a.
  destruct l.
  auto.
  destruct p.
  intros; destruct (andb_prop _ _ H); auto.
  Qed.

  Lemma elements_3 : sort lt_key (elements m). 
  Proof.
  unfold elements.
  apply alist_sorted_sort.
  apply alist_of_Map_sorts.
  Qed.

  Lemma elements_3w : NoDupA eq_key (elements m). 
  Proof.
  change eq_key with (@PE.eqk A).
  apply PE.Sort_NoDupA; apply elements_3; auto.
  Qed. 

  Lemma elements_1 : 
     MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
  Proof.
  unfold MapsTo, find, elements.
  rewrite InA_alt.
  intro H.
  exists (x,e).
  split.
  red; simpl; unfold E.eq; auto.
  rewrite alist_of_Map_semantics in H.
  generalize H.
  set (l:=alist_of_Map A m); clearbody l; clear.
  induction l; simpl; auto.
  intro; discriminate.
  destruct a; simpl; auto.
  generalize (Neqb_complete a x).
  destruct (Neqb a x); auto.
  left.
  injection H0; auto.
  intros; f_equal; auto.
  Qed.

  Lemma elements_2 : 
     InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
  Proof.
  generalize elements_3.
  unfold MapsTo, find, elements.
  rewrite InA_alt.
  intros H ((e0,a),(H0,H1)).
  red in H0; simpl in H0; unfold E.eq in H0; destruct H0; subst.
  rewrite alist_of_Map_semantics.
  generalize H H1; clear H H1.
  set (l:=alist_of_Map A m); clearbody l; clear.
  induction l; simpl; auto.
  intro; contradiction.
  intros.
  destruct a0; simpl.
  inversion H1. 
  injection H0; intros; subst.
  rewrite Neqb_correct; auto.
  assert (InA eq_key (e0,a) l).
  rewrite InA_alt.
  exists (e0,a); split; auto.
  red; simpl; auto; red; auto.
  generalize (PE.Sort_In_cons_1 H H2).
  unfold PE.ltk; simpl.
  intros H3; generalize (E.lt_not_eq H3).
  generalize (Neqb_complete a0 e0).
  destruct (Neqb a0 e0); auto.
  destruct 2.
  apply H4; auto.
  inversion H; auto.
  Qed.

  Lemma cardinal_1 : forall m, cardinal m = length (elements m).
  Proof. exact (@MapCard_as_length _). Qed.

  Definition Equal m m' := forall y, find y m = find y m'.
  Definition Equiv (eq_elt:A->A->Prop) m m' := 
    (forall k, In k m <-> In k m') /\ 
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').  
  Definition Equivb (cmp: A->A->bool) := Equiv (Cmp cmp).

  (** unfortunately, the [MapFold] of [IntMap] isn't compatible with 
   the FMap interface. We use a naive version for now : *)

  Definition fold (B:Type)(f:key -> A -> B -> B)(m:t A)(i:B) : B := 
    fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.

  Lemma fold_1 :
	forall (B:Type) (i : B) (f : key -> A -> B -> B),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof. auto. Qed.

  End Spec.

  Variable B : Set.

  Fixpoint mapi_aux (pf:N->N)(f : N -> A -> B)(m:t A) { struct m }: t B := 
    match m with 
      | M0 => M0 _ 
      | M1 x y => M1 _ x (f (pf x) y)
      | M2 m0 m1 =>  M2 _ (mapi_aux (fun n => pf (Ndouble n)) f m0)
                                         (mapi_aux (fun n => pf (Ndouble_plus_one n)) f m1)
    end.
    
  Definition mapi := mapi_aux (fun n => n).

  Definition map (f:A->B) := mapi (fun _ => f).
 
  End A.

  Lemma mapi_aux_1 : forall (elt elt':Set)(m: t elt)(pf:N->N)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m -> 
        exists y, E.eq y x /\ MapsTo x (f (pf y) e) (mapi_aux pf f m).
  Proof.
  unfold MapsTo; induction m; simpl; auto.
  inversion 1.

  intros.
  exists x; split; [red; auto|].
  generalize (Neqb_complete a x).
  destruct (Neqb a x); try discriminate.
  injection H; intros; subst; auto.
  rewrite H1; auto.

  intros.
  exists x; split; [red;auto|].
  destruct x; simpl in *.
  destruct (IHm1 (fun n : N => pf (Ndouble n)) _ _ f H) as (y,(Hy,Hy')).
  rewrite Hy in Hy'; simpl in Hy'; auto.
  destruct p; simpl in *.
  destruct (IHm2 (fun n : N => pf (Ndouble_plus_one n)) _ _ f H) as (y,(Hy,Hy')).
  rewrite Hy in Hy'; simpl in Hy'; auto.
  destruct (IHm1 (fun n : N => pf (Ndouble n)) _ _ f H) as (y,(Hy,Hy')).
  rewrite Hy in Hy'; simpl in Hy'; auto.
  destruct (IHm2 (fun n : N => pf (Ndouble_plus_one n)) _ _ f H) as (y,(Hy,Hy')).
  rewrite Hy in Hy'; simpl in Hy'; auto.
  Qed.

  Lemma mapi_1 : forall (elt elt':Set)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m -> 
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof.
  intros elt elt' m; exact (mapi_aux_1 (fun n => n)).
  Qed.

  Lemma mapi_aux_2 : forall (elt elt':Set)(m: t elt)(pf:N->N)(x:key)
        (f:key->elt->elt'), In x (mapi_aux pf f m) -> In x m.
  Proof.
  unfold In, MapsTo.
  induction m; simpl in *.
  intros pf x f (e,He); inversion He.
  intros pf x f (e,He).
  exists a0.
  destruct (Neqb a x); try discriminate; auto.
  intros pf x f (e,He).
  destruct x; [|destruct p]; eauto.
  Qed.

  Lemma mapi_2 : forall (elt elt':Set)(m: t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.
  Proof.
  intros elt elt' m; exact (mapi_aux_2 m (fun n => n)).
  Qed.

  Lemma map_1 : forall (elt elt':Set)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof.
  unfold map; intros.
  destruct (@mapi_1 _ _ m x e (fun _ => f)) as (e',(_,H0)); auto.
  Qed.

  Lemma map_2 : forall (elt elt':Set)(m: t elt)(x:key)(f:elt->elt'), 
        In x (map f m) -> In x m.
  Proof.
  unfold map; intros.
  eapply mapi_2; eauto.
  Qed.

  Module L := FMapList.Raw E.

  (** Not exactly pretty nor perfect, but should suffice as a first naive implem. 
    Anyway, map2 isn't in Ocaml...
  *)

  Definition anti_elements (A:Set)(l:list (key*A)) := L.fold (@add _) l (empty _).

  Definition map2 (A B C:Set)(f:option A->option B -> option C)(m:t A)(m':t B) : t C := 
    anti_elements (L.map2 f (elements m) (elements m')).

  Lemma add_spec : forall (A:Set)(m:t A) x y e, 
    find x (add y e m) = if ME.eq_dec x y then Some e else find x m.
  Proof.
  intros.
  destruct (ME.eq_dec x y).
  apply find_1.
  eapply MapsTo_1 with y; eauto.
  red; auto.
  apply add_1; auto.
  red; auto.
  case_eq (find x m); intros.
  apply find_1.
  apply add_2; unfold E.eq in *; auto.
  case_eq (find x (add y e m)); auto; intros.
  rewrite <- H; symmetry.
  apply find_1; auto.
  apply (@add_3 _ m y x a e); unfold E.eq in *; auto.
  Qed.
  
  Lemma anti_elements_mapsto_aux : forall (A:Set)(l:list (key*A)) m k e,
    NoDupA (eq_key (A:=A)) l -> 
    (forall x, L.PX.In x l -> In x m -> False) -> 
    (MapsTo k e (L.fold (@add _) l m) <-> L.PX.MapsTo k e l \/ MapsTo k e m).
  Proof.
  induction l. 
  simpl; auto.
  intuition.
  inversion H2.
  simpl; destruct a; intros.
  rewrite IHl; clear IHl.
  inversion H; auto.
  intros.
  inversion_clear H.
  assert (~E.eq x k).
   contradict H3.
   destruct H1.
   apply InA_eqA with (x,x0); eauto.
   unfold eq_key, E.eq; eauto.
   unfold eq_key, E.eq; congruence.
  apply (H0 x).
  destruct H1; exists x0; auto.
  revert H2.
  unfold In.
  intros (e',He').
  exists e'; apply (@add_3 _ m k x e' a); unfold E.eq; auto.
  intuition.
  red in H2.
  rewrite add_spec in H2; auto.
  destruct (ME.eq_dec k0 k).
  inversion_clear H2; subst; auto.
  right; apply find_2; auto.
  inversion_clear H2; auto.
  compute in H1; destruct H1.
  subst; right; apply add_1; auto.
  red; auto.
  inversion_clear H.
  destruct (ME.eq_dec k0 k).
  unfold E.eq in *; subst.
  destruct (H0 k); eauto.
  red; eauto.
  right; apply add_2; unfold E.eq in *; auto.
  Qed.
  
  Lemma anti_elements_mapsto : forall (A:Set) l k e, NoDupA (eq_key (A:=A)) l ->
    (MapsTo k e (anti_elements l) <-> L.PX.MapsTo k e l).
  Proof. 
  intros. 
  unfold anti_elements.
  rewrite anti_elements_mapsto_aux; auto; unfold empty; auto.
  inversion 2.
  inversion H2.
  intuition.
  inversion H1.
  Qed.
  
  Lemma find_anti_elements : forall (A:Set)(l: list (key*A)) x, sort (@lt_key _) l -> 
    find x (anti_elements l) = L.find x l.
  Proof.
  intros.
  case_eq (L.find x l); intros.
  apply find_1.
  rewrite anti_elements_mapsto.
  apply L.PX.Sort_NoDupA; auto.
  apply L.find_2; auto.
  case_eq (find x (anti_elements l)); auto; intros.
  rewrite <- H0; symmetry.
  apply L.find_1; auto.
  rewrite <- anti_elements_mapsto.
  apply L.PX.Sort_NoDupA; auto.
  apply find_2; auto.
  Qed.

  Lemma find_elements : forall (A:Set)(m: t A) x,  
    L.find x (elements m) = find x m.
  Proof. 
  intros.
  case_eq (find x m); intros.
  apply L.find_1.
  apply elements_3; auto.
  red; apply elements_1.
  apply find_2; auto.
  case_eq (L.find x (elements m)); auto; intros.
  rewrite <- H; symmetry.
  apply find_1; auto.
  apply elements_2.
  apply L.find_2; auto.
  Qed.
  
  Lemma elements_in : forall (A:Set)(s:t A) x, L.PX.In x (elements s) <-> In x s.
  Proof.
   intros.
   unfold L.PX.In, In.
   firstorder.
   exists x0.
   red; rewrite <- find_elements; auto.
   apply L.find_1; auto.
   apply elements_3.
   exists x0.
   apply L.find_2.
   rewrite find_elements; auto.
  Qed.
  
  Lemma map2_1 : forall (A B C:Set)(m: t A)(m': t B)(x:key)
    (f:option A->option B ->option C), 
    In x m \/ In x m' -> find x (map2 f m m') = f (find x m) (find x m').       
  Proof. 
  unfold map2; intros.
  rewrite find_anti_elements; auto.
  rewrite <- find_elements; auto.
  rewrite <- find_elements; auto.
  apply L.map2_1; auto.
  apply elements_3; auto.
  apply elements_3; auto.
  do 2 rewrite elements_in; auto.
  apply L.map2_sorted; auto.
  apply elements_3; auto.
  apply elements_3; auto.
  Qed.
  
  Lemma map2_2 : forall (A B C: Set)(m: t A)(m': t B)(x:key)
      (f:option A->option B ->option C), 
    In x (map2 f m m') -> In x m \/ In x m'.
  Proof.
  unfold map2; intros.
  do 2 rewrite <- elements_in.
  apply L.map2_2 with (f:=f); auto.
  apply elements_3; auto.
  apply elements_3; auto.
  destruct H.
  exists x0.
  rewrite <- anti_elements_mapsto; auto.
  apply L.PX.Sort_NoDupA; auto.
  apply L.map2_sorted; auto.
  apply elements_3; auto.
  apply elements_3; auto.
  Qed.

  (** same trick for [equal] *)

  Definition equal (A:Set)(cmp:A -> A -> bool)(m m' : t A) : bool := 
    L.equal cmp (elements m) (elements m').
  
  Lemma equal_1 : 
    forall (A:Set)(m: t A)(m': t A)(cmp: A -> A -> bool), 
    Equivb cmp m m' -> equal cmp m m' = true. 
  Proof.
  unfold equal, Equivb, Equiv, Cmp.
  intros.
  apply L.equal_1.
  apply elements_3.
  apply elements_3.
  unfold L.Equivb.
  destruct H.
  split; intros.
  do 2 rewrite elements_in; auto.
  apply (H0 k); 
    red; rewrite <- find_elements; apply L.find_1; auto; 
    apply elements_3.
  Qed.  

  Lemma equal_2 : 
    forall (A:Set)(m: t A)(m': t A)(cmp: A -> A -> bool), 
    equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
  unfold equal, Equivb, Equiv, Cmp.
  intros.
  destruct (L.equal_2 (elements_3 m) (elements_3 m') H); clear H.
  split.
  intros; do 2 rewrite <- elements_in; auto.
  intros; apply (H1 k); 
    apply L.find_2; rewrite find_elements;auto.
  Qed.

End MapIntMap.


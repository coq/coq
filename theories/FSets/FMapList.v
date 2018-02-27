(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Finite map library *)

(** This file proposes an implementation of the non-dependent interface
 [FMapInterface.S] using lists of pairs ordered (increasing) with respect to
 left projection. *)

Require Import FunInd FMapInterface.

Set Implicit Arguments.
Unset Strict Implicit.

Module Raw (X:OrderedType).

Module Import MX := OrderedTypeFacts X.
Module Import PX := KeyOrderedType X.

Definition key := X.t.
Definition t (elt:Type) := list (X.t * elt).

Section Elt.
Variable elt : Type.

Notation eqk := (eqk (elt:=elt)).
Notation eqke := (eqke (elt:=elt)).
Notation ltk := (ltk (elt:=elt)).
Notation MapsTo := (MapsTo (elt:=elt)).
Notation In := (In (elt:=elt)).
Notation Sort := (sort ltk).
Notation Inf := (lelistA (ltk)).

(** * [empty] *)

Definition empty : t elt := nil.

Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

Lemma empty_1 : Empty empty.
Proof.
 unfold Empty,empty.
 intros a e.
 intro abs.
 inversion abs.
Qed.
Hint Resolve empty_1.

Lemma empty_sorted : Sort empty.
Proof.
 unfold empty; auto.
Qed.

(** * [is_empty] *)

Definition is_empty (l : t elt) : bool := if l then true else false.

Lemma is_empty_1 :forall m, Empty m -> is_empty m = true.
Proof.
 unfold Empty, PX.MapsTo.
 intros m.
 case m;auto.
 intros (k,e) l inlist.
 absurd (InA eqke (k, e) ((k, e) :: l));auto.
Qed.

Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
Proof.
 intros m.
 case m;auto.
 intros p l abs.
 inversion abs.
Qed.

(** * [mem] *)

Function mem (k : key) (s : t elt) {struct s} : bool :=
 match s with
  | nil => false
  | (k',_) :: l =>
     match X.compare k k' with
      | LT _ => false
      | EQ _ => true
      | GT _ => mem k l
     end
 end.

Lemma mem_1 : forall m (Hm:Sort m) x, In x m -> mem x m = true.
Proof.
 intros m Hm x; generalize Hm; clear Hm.
 functional induction (mem x m);intros sorted belong1;trivial.

 inversion belong1. inversion H.

 absurd (In x ((k', _x) :: l));try assumption.
 apply Sort_Inf_NotIn with _x;auto.

 apply IHb.
 elim (sort_inv sorted);auto.
 elim (In_inv belong1);auto.
 intro abs.
 absurd (X.eq x k');auto.
Qed.

Lemma mem_2 : forall m (Hm:Sort m) x, mem x m = true -> In x m.
Proof.
 intros m Hm x; generalize Hm; clear Hm; unfold PX.In,PX.MapsTo.
 functional induction (mem x m); intros sorted hyp;try ((inversion hyp);fail).
 exists _x; auto.
 induction IHb; auto.
 exists x0; auto.
 inversion_clear sorted; auto.
Qed.

(** * [find] *)

Function find (k:key) (s: t elt) {struct s} : option elt :=
 match s with
  | nil => None
  | (k',x)::s' =>
     match X.compare k k' with
      | LT _ => None
      | EQ _ => Some x
      | GT _ => find k s'
     end
 end.

Lemma find_2 :  forall m x e, find x m = Some e -> MapsTo x e m.
Proof.
 intros m x. unfold PX.MapsTo.
 functional induction (find x m);simpl;intros e' eqfind; inversion eqfind; auto.
Qed.

Lemma find_1 :  forall m (Hm:Sort m) x e, MapsTo x e m -> find x m = Some e.
Proof.
 intros m Hm x e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction (find x m);simpl; subst; try clear H_eq_1.

 inversion 2.

 inversion_clear 2.
 clear e1;compute in H0; destruct H0;order.
 clear e1;generalize (Sort_In_cons_1 Hm (InA_eqke_eqk H0)); compute; order.

 clear e1;inversion_clear 2.
 compute in H0; destruct H0; intuition congruence.
 generalize (Sort_In_cons_1 Hm (InA_eqke_eqk H0)); compute; order.

 clear e1; do 2 inversion_clear 1; auto.
 compute in H2; destruct H2; order.
Qed.

(** * [add] *)

Function add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
 match s with
  | nil => (k,x) :: nil
  | (k',y) :: l =>
     match X.compare k k' with
      | LT _ => (k,x)::s
      | EQ _ => (k,x)::l
      | GT _ => (k',y) :: add k x l
     end
 end.

Lemma add_1 : forall m x y e, X.eq x y -> MapsTo y e (add x e m).
Proof.
 intros m x y e; generalize y; clear y.
 unfold PX.MapsTo.
 functional induction (add x e m);simpl;auto.
Qed.

Lemma add_2 : forall m x y e e',
  ~ X.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
Proof.
 intros m x  y e e'.
 generalize y e; clear y e; unfold PX.MapsTo.
 functional induction (add x e' m) ;simpl;auto;  clear e0.
 subst;auto.

 intros y' e'' eqky';  inversion_clear 1;  destruct H0; simpl in *.
 order.
 auto.
 auto.
 intros y' e'' eqky'; inversion_clear 1; intuition.
Qed.


Lemma add_3 : forall m x y e e',
  ~ X.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
Proof.
 intros m x y e e'. generalize y e; clear y e; unfold PX.MapsTo.
 functional induction (add x e' m);simpl; intros.
 apply (In_inv_3 H0); compute; auto.
 apply (In_inv_3 H0); compute; auto.
 constructor 2; apply (In_inv_3 H0); compute; auto.
 inversion_clear H0; auto.
Qed.


Lemma add_Inf : forall (m:t elt)(x x':key)(e e':elt),
  Inf (x',e') m -> ltk (x',e') (x,e) -> Inf (x',e') (add x e m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 destruct a as (x'',e'').
 inversion_clear H.
 compute in H0,H1.
 simpl; case (X.compare x x''); intuition.
Qed.
Hint Resolve add_Inf.

Lemma add_sorted : forall m (Hm:Sort m) x e, Sort (add x e m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 destruct a as (x',e').
 simpl; case (X.compare x x'); intuition; inversion_clear Hm; auto.
 constructor; auto.
 apply Inf_eq with (x',e'); auto.
Qed.

(** * [remove] *)

Function remove (k : key) (s : t elt) {struct s} : t elt :=
 match s with
  | nil => nil
  | (k',x) :: l =>
     match X.compare k k' with
      | LT _ => s
      | EQ _ => l
      | GT _ => (k',x) :: remove k l
     end
 end.

Lemma remove_1 : forall m (Hm:Sort m) x y, X.eq x y -> ~ In y (remove x m).
Proof.
 intros m Hm x y; generalize Hm; clear Hm.
 functional induction (remove x m);simpl;intros;subst.

 red; inversion 1; inversion H1.

 apply Sort_Inf_NotIn with x0; auto.
 clear e0;constructor; compute; order.

 clear e0;inversion_clear Hm.
 apply Sort_Inf_NotIn with x0; auto.
 apply Inf_eq with (k',x0);auto; compute; apply X.eq_trans with x; auto.

 clear e0;inversion_clear Hm.
 assert (notin:~ In y (remove x l)) by auto.
 intros (x1,abs).
 inversion_clear abs.
 compute in H2; destruct H2; order.
 apply notin; exists x1; auto.
Qed.


Lemma remove_2 : forall m (Hm:Sort m) x y e,
  ~ X.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
Proof.
 intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction (remove x m);subst;auto;
   match goal with
     | [H: X.compare _ _ = _ |- _ ] => clear H
     | _ => idtac
   end.

 inversion_clear 3; auto.
 compute in H1; destruct H1; order.

 inversion_clear 1; inversion_clear 2; auto.
Qed.

Lemma remove_3 : forall m (Hm:Sort m) x y e,
  MapsTo y e (remove x m) -> MapsTo y e m.
Proof.
 intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction (remove x m);subst;auto.
 inversion_clear 1; inversion_clear 1; auto.
Qed.

Lemma remove_Inf : forall (m:t elt)(Hm : Sort m)(x x':key)(e':elt),
  Inf (x',e') m -> Inf (x',e') (remove x m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 destruct a as (x'',e'').
 inversion_clear H.
 compute in H0.
 simpl; case (X.compare x x''); intuition.
 inversion_clear Hm.
 apply Inf_lt with (x'',e''); auto.
Qed.
Hint Resolve remove_Inf.

Lemma remove_sorted : forall m (Hm:Sort m) x, Sort (remove x m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 destruct a as (x',e').
 simpl; case (X.compare x x'); intuition; inversion_clear Hm; auto.
Qed.

(** * [elements] *)

Definition elements (m: t elt) := m.

Lemma elements_1 : forall m x e,
  MapsTo x e m -> InA eqke (x,e) (elements m).
Proof.
 auto.
Qed.

Lemma elements_2 : forall m x e,
  InA eqke (x,e) (elements m) -> MapsTo x e m.
Proof.
 auto.
Qed.

Lemma elements_3 : forall m (Hm:Sort m), sort ltk (elements m).
Proof.
 auto.
Qed.

Lemma elements_3w : forall m (Hm:Sort m), NoDupA eqk (elements m).
Proof.
 intros.
 apply Sort_NoDupA.
 apply elements_3; auto.
Qed.

(** * [fold] *)

Function fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc:A) {struct m} :  A :=
  match m with
   | nil => acc
   | (k,e)::m' => fold f m' (f k e acc)
  end.

Lemma fold_1 : forall m (A:Type)(i:A)(f:key->elt->A->A),
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
Proof.
 intros; functional induction (fold f m i); auto.
Qed.

(** * [equal] *)

Function equal (cmp:elt->elt->bool)(m m' : t elt) {struct m} : bool :=
  match m, m' with
   | nil, nil => true
   | (x,e)::l, (x',e')::l' =>
      match X.compare x x' with
       | EQ _ => cmp e e' && equal cmp l l'
       | _    => false
      end
   | _, _ => false
  end.

Definition Equivb cmp m m' :=
  (forall k, In k m <-> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Lemma equal_1 : forall m (Hm:Sort m) m' (Hm': Sort m') cmp,
  Equivb cmp m m' -> equal cmp m m' = true.
Proof.
 intros m Hm m' Hm' cmp; generalize Hm Hm'; clear Hm Hm'.
 functional induction (equal cmp m m'); simpl; subst;auto; unfold Equivb;
 intuition; subst.
 match goal with H: X.compare _ _ = _ |- _ => clear H end.
 assert (cmp_e_e':cmp e e' = true).
  apply H1 with x; auto.
 rewrite cmp_e_e'; simpl.
 apply IHb; auto.
 inversion_clear Hm; auto.
 inversion_clear Hm'; auto.
 unfold Equivb; intuition.
 destruct (H0 k).
 assert (In k ((x,e) ::l)).
  destruct H as (e'', hyp); exists e''; auto.
 destruct (In_inv (H2 H4)); auto.
 inversion_clear Hm.
 elim (Sort_Inf_NotIn H6 H7).
 destruct H as (e'', hyp); exists e''; auto.
 apply MapsTo_eq with k; auto; order.
 destruct (H0 k).
 assert (In k ((x',e') ::l')).
  destruct H as (e'', hyp); exists e''; auto.
 destruct (In_inv (H3 H4)); auto.
 inversion_clear Hm'.
 elim (Sort_Inf_NotIn H6 H7).
 destruct H as (e'', hyp); exists e''; auto.
 apply MapsTo_eq with k; auto; order.
 apply H1 with k; destruct (X.eq_dec x k); auto.


 destruct (X.compare x x') as [Hlt|Heq|Hlt]; try contradiction; clear y.
 destruct (H0 x).
 assert (In x ((x',e')::l')).
  apply H; auto.
  exists e; auto.
 destruct (In_inv H3).
 order.
 inversion_clear Hm'.
 assert (Inf (x,e) l').
 apply Inf_lt with (x',e'); auto.
 elim (Sort_Inf_NotIn H5 H7 H4).

 destruct (H0 x').
 assert (In x' ((x,e)::l)).
  apply H2; auto.
  exists e'; auto.
 destruct (In_inv H3).
 order.
 inversion_clear Hm.
 assert (Inf (x',e') l).
  apply Inf_lt with (x,e); auto.
 elim (Sort_Inf_NotIn H5 H7 H4).

 destruct m;
 destruct m';try contradiction.

 clear H1;destruct p as (k,e).
 destruct (H0 k).
 destruct H1.
 exists e; auto.
 inversion H1.

 destruct p as (x,e).
 destruct (H0 x).
 destruct H.
 exists e; auto.
 inversion H.

 destruct p;destruct p0;contradiction.
Qed.


Lemma equal_2 : forall m (Hm:Sort m) m' (Hm:Sort m') cmp,
  equal cmp m m' = true -> Equivb cmp m m'.
Proof.
 intros m Hm m' Hm' cmp; generalize Hm Hm'; clear Hm Hm'.
 functional induction (equal cmp m m'); simpl; subst;auto; unfold Equivb;
  intuition; try discriminate; subst;
  try match goal with H: X.compare _ _ = _ |- _ => clear H end.

 inversion H0.

 inversion_clear Hm;inversion_clear Hm'.
 destruct (andb_prop _ _ H); clear H.
 destruct (IHb H1 H3 H6).
 destruct (In_inv H0).
 exists e'; constructor; split; trivial; apply X.eq_trans with x; auto.
 destruct (H k).
 destruct (H9 H8) as (e'',hyp).
 exists e''; auto.

 inversion_clear Hm;inversion_clear Hm'.
 destruct (andb_prop _ _ H); clear H.
 destruct (IHb H1 H3 H6).
 destruct (In_inv H0).
 exists e; constructor; split; trivial; apply X.eq_trans with x'; auto.
 destruct (H k).
 destruct (H10 H8) as (e'',hyp).
 exists e''; auto.

 inversion_clear Hm;inversion_clear Hm'.
 destruct (andb_prop _ _ H); clear H.
 destruct (IHb H2 H4 H7).
 inversion_clear H0.
 destruct H9; simpl in *; subst.
 inversion_clear H1.
 destruct H9; simpl in *; subst; auto.
 elim (Sort_Inf_NotIn H4 H5).
 exists e'0; apply MapsTo_eq with k; auto; order.
 inversion_clear H1.
 destruct H0; simpl in *; subst; auto.
 elim (Sort_Inf_NotIn H2 H3).
 exists e0; apply MapsTo_eq with k; auto; order.
 apply H8 with k; auto.
Qed.

(** This lemma isn't part of the spec of [Equivb], but is used in [FMapAVL] *)

Lemma equal_cons : forall cmp l1 l2 x y, Sort (x::l1) -> Sort (y::l2) ->
  eqk x y -> cmp (snd x) (snd y) = true ->
  (Equivb cmp l1 l2 <-> Equivb cmp (x :: l1) (y :: l2)).
Proof.
 intros.
 inversion H; subst.
 inversion H0; subst.
 destruct x; destruct y; compute in H1, H2.
 split; intros.
 apply equal_2; auto.
 simpl.
 elim_comp.
 rewrite H2; simpl.
 apply equal_1; auto.
 apply equal_2; auto.
 generalize (equal_1 H H0 H3).
 simpl.
 elim_comp.
 rewrite H2; simpl; auto.
Qed.

Variable elt':Type.

(** * [map] and [mapi] *)

Fixpoint map (f:elt -> elt') (m:t elt) : t elt' :=
  match m with
   | nil => nil
   | (k,e)::m' => (k,f e) :: map f m'
  end.

Fixpoint mapi (f: key -> elt -> elt') (m:t elt) : t elt' :=
  match m with
   | nil => nil
   | (k,e)::m' => (k,f k e) :: mapi f m'
  end.
 
End Elt.
Section Elt2.
(* A new section is necessary for previous definitions to work
   with different [elt], especially [MapsTo]... *)

Variable elt elt' : Type.

(** Specification of [map] *)

Lemma map_1 : forall (m:t elt)(x:key)(e:elt)(f:elt->elt'),
  MapsTo x e m -> MapsTo x (f e) (map f m).
Proof.
 intros m x e f.
 (* functional induction map elt elt' f m.  *) (* Marche pas ??? *)
 induction m.
 inversion 1. 

 destruct a as (x',e').
 simpl.
 inversion_clear 1.  
 constructor 1.
 unfold eqke in *; simpl in *; intuition congruence.
 unfold MapsTo in *; auto.
Qed.

Lemma map_2 : forall (m:t elt)(x:key)(f:elt->elt'),
  In x (map f m) -> In x m.
Proof.
 intros m x f.
 (* functional induction map elt elt' f m. *) (* Marche pas ??? *)
 induction m; simpl.
 intros (e,abs).
 inversion abs.

 destruct a as (x',e).
 intros hyp.
 inversion hyp. clear hyp.
 inversion H; subst; rename x0 into e'.
 exists e; constructor.
 unfold eqke in *; simpl in *; intuition.
 destruct IHm as (e'',hyp).
 exists e'; auto.
 exists e''.
 constructor 2; auto.
Qed.

Lemma map_lelistA : forall (m: t elt)(x:key)(e:elt)(e':elt')(f:elt->elt'),
  lelistA (@ltk elt) (x,e) m ->
  lelistA (@ltk elt') (x,e') (map f m).
Proof.
 induction m; simpl; auto.
 intros.
 destruct a as (x0,e0).
 inversion_clear H; auto.
Qed.

Hint Resolve map_lelistA.

Lemma map_sorted : forall (m: t elt)(Hm : sort (@ltk elt) m)(f:elt -> elt'),
  sort (@ltk elt') (map f m).
Proof.
 induction m; simpl; auto.
 intros.
 destruct a as (x',e').
 inversion_clear Hm.
 constructor; auto.
 exact (map_lelistA _ _ H0).
Qed.

(** Specification of [mapi] *)

Lemma mapi_1 : forall (m:t elt)(x:key)(e:elt)(f:key->elt->elt'),
  MapsTo x e m ->
  exists y, X.eq y x /\ MapsTo x (f y e) (mapi f m).
Proof.
 intros m x e f.
 (* functional induction mapi elt elt' f m. *) (* Marche pas ??? *)
 induction m.
 inversion 1.

 destruct a as (x',e').
 simpl.
 inversion_clear 1.
 exists x'.
 destruct H0; simpl in *.
 split; auto.
 constructor 1.
 unfold eqke in *; simpl in *; intuition congruence.
 destruct IHm as (y, hyp); auto.
 exists y; intuition.
Qed.


Lemma mapi_2 : forall (m:t elt)(x:key)(f:key->elt->elt'),
  In x (mapi f m) -> In x m.
Proof.
 intros m x f.
 (* functional induction mapi elt elt' f m. *) (* Marche pas ??? *)
 induction m; simpl.
 intros (e,abs).
 inversion abs.

 destruct a as (x',e).
 intros hyp.
 inversion hyp. clear hyp.
 inversion H; subst; rename x0 into e'.
 exists e; constructor.
 unfold eqke in *; simpl in *; intuition.
 destruct IHm as (e'',hyp).
 exists e'; auto.
 exists e''.
 constructor 2; auto.
Qed.

Lemma mapi_lelistA : forall (m: t elt)(x:key)(e:elt)(f:key->elt->elt'),
  lelistA (@ltk elt) (x,e) m ->
  lelistA (@ltk elt') (x,f x e) (mapi f m).
Proof.
 induction m; simpl; auto.
 intros.
 destruct a as (x',e').
 inversion_clear H; auto.
Qed.

Hint Resolve mapi_lelistA.

Lemma mapi_sorted : forall m (Hm : sort (@ltk elt) m)(f: key ->elt -> elt'),
  sort (@ltk elt') (mapi f m).
Proof.
 induction m; simpl; auto.
 intros.
 destruct a as (x',e').
 inversion_clear Hm; auto.
Qed.

End Elt2.
Section Elt3.

(** * [map2] *)

Variable elt elt' elt'' : Type.
Variable f : option elt -> option elt' -> option elt''.

Definition option_cons (A:Type)(k:key)(o:option A)(l:list (key*A)) :=
  match o with
   | Some e => (k,e)::l
   | None => l
  end.

Fixpoint map2_l (m : t elt) : t elt'' :=
  match m with
   | nil => nil
   | (k,e)::l => option_cons k (f (Some e) None) (map2_l l)
  end.

Fixpoint map2_r (m' : t elt') : t elt'' :=
  match m' with
   | nil => nil
   | (k,e')::l' => option_cons k (f None (Some e')) (map2_r l')
  end.

Fixpoint map2 (m : t elt) : t elt' -> t elt'' :=
  match m with
   | nil => map2_r
   | (k,e) :: l =>
      fix map2_aux (m' : t elt') : t elt'' :=
        match m' with
         | nil => map2_l m
         | (k',e') :: l' =>
            match X.compare k k' with
             | LT _ => option_cons k (f (Some e) None) (map2 l m')
             | EQ _ => option_cons k (f (Some e) (Some e')) (map2 l l')
             | GT _ => option_cons k' (f None (Some e')) (map2_aux l')
            end
        end
  end.

Notation oee' := (option elt * option elt')%type.

Fixpoint combine (m : t elt) : t elt' -> t oee' :=
  match m with
   | nil => map (fun e' => (None,Some e'))
   | (k,e) :: l =>
      fix combine_aux (m':t elt') : list (key * oee') :=
        match m' with
         | nil => map (fun e => (Some e,None)) m
         | (k',e') :: l' =>
            match X.compare k k' with
             | LT _ => (k,(Some e, None))::combine l m'
             | EQ _ => (k,(Some e, Some e'))::combine l l'
             | GT _ => (k',(None,Some e'))::combine_aux l'
            end
        end
  end.

Definition fold_right_pair (A B C:Type)(f: A->B->C->C)(l:list (A*B))(i:C) :=
  List.fold_right (fun p => f (fst p) (snd p)) i l.

Definition map2_alt m m' :=
  let m0 : t oee' := combine m m' in
  let m1 : t (option elt'') := map (fun p => f (fst p) (snd p)) m0 in
  fold_right_pair (option_cons (A:=elt'')) m1 nil.

Lemma map2_alt_equiv : forall m m', map2_alt m m' = map2 m m'.
Proof.
 unfold map2_alt.
 induction m.
 simpl; auto; intros.
 (* map2_r *)
 induction m'; try destruct a; simpl; auto.
 rewrite IHm'; auto.
 (* fin map2_r *)
 induction m'; destruct a.
 simpl; f_equal.
 (* map2_l *)
 clear IHm.
 induction m; try destruct a; simpl; auto.
 rewrite IHm; auto.
 (* fin map2_l *)
 destruct a0.
 simpl.
 destruct (X.compare t0 t1); simpl; f_equal.
 apply IHm.
 apply IHm.
 apply IHm'.
Qed.

Lemma combine_lelistA :
  forall m m' (x:key)(e:elt)(e':elt')(e'':oee'),
  lelistA (@ltk elt) (x,e) m ->
  lelistA (@ltk elt') (x,e') m' ->
  lelistA (@ltk oee') (x,e'') (combine m m').
Proof.
 induction m.
 intros.
 simpl.
 exact (map_lelistA _ _ H0).
 induction m'.
 intros.
 destruct a.
 replace (combine ((t0, e0) :: m) nil) with
             (map (fun e => (Some e,None (A:=elt'))) ((t0,e0)::m)); auto.
 exact (map_lelistA _ _ H).
 intros.
 simpl.
 destruct a as (k,e0); destruct a0 as (k',e0').
 destruct (X.compare k k').
 inversion_clear H; auto.
 inversion_clear H; auto.
 inversion_clear H0; auto.
Qed.
Hint Resolve combine_lelistA.

Lemma combine_sorted :
  forall m (Hm : sort (@ltk elt) m) m' (Hm' : sort (@ltk elt') m'),
  sort (@ltk oee') (combine m m').
Proof.
 induction m.
 intros; clear Hm.
 simpl.
 apply map_sorted; auto.
 induction m'.
 intros; clear Hm'.
 destruct a.
 replace (combine ((t0, e) :: m) nil) with
             (map (fun e => (Some e,None (A:=elt'))) ((t0,e)::m)); auto.
 apply map_sorted; auto.
 intros.
 simpl.
 destruct a as (k,e); destruct a0 as (k',e').
 destruct (X.compare k k') as [Hlt|Heq|Hlt].
 inversion_clear Hm.
 constructor; auto.
 assert (lelistA (ltk (elt:=elt')) (k, e') ((k',e')::m')) by auto.
 exact (combine_lelistA _ H0 H1).
 inversion_clear Hm; inversion_clear Hm'.
 constructor; auto.
 assert (lelistA (ltk (elt:=elt')) (k, e') m') by (apply Inf_eq with (k',e'); auto).
 exact (combine_lelistA _ H0 H3).
 inversion_clear Hm; inversion_clear Hm'.
 constructor; auto.
 change (lelistA (ltk (elt:=oee')) (k', (None, Some e'))
                 (combine ((k,e)::m) m')).
 assert (lelistA (ltk (elt:=elt)) (k', e) ((k,e)::m)) by auto.
 exact (combine_lelistA _  H3 H2).
Qed.

Lemma map2_sorted :
  forall m (Hm : sort (@ltk elt) m) m' (Hm' : sort (@ltk elt') m'),
  sort (@ltk elt'') (map2 m m').
Proof.
 intros.
 rewrite <- map2_alt_equiv.
 unfold map2_alt.
 assert (H0:=combine_sorted Hm Hm').
 set (l0:=combine m m') in *; clearbody l0.
 set (f':= fun p : oee' => f (fst p) (snd p)).
 assert (H1:=map_sorted (elt' := option elt'') H0 f').
 set (l1:=map f' l0) in *; clearbody l1.
 clear f' f H0 l0 Hm Hm' m m'.
 induction l1.
 simpl; auto.
 inversion_clear H1.
 destruct a; destruct o; auto.
 simpl.
 constructor; auto.
 clear IHl1.
 induction l1.
 simpl; auto.
 destruct a; destruct o; simpl; auto.
 inversion_clear H0; auto.
 inversion_clear H0.
 red in H1; simpl in H1.
 inversion_clear H.
 apply IHl1; auto.
 apply Inf_lt with (t1, None (A:=elt'')); auto.
Qed.

Definition at_least_one (o:option elt)(o':option elt') :=
  match o, o' with
   | None, None => None
   | _, _  => Some (o,o')
  end.

Lemma combine_1 :
  forall m (Hm : sort (@ltk elt) m) m' (Hm' : sort (@ltk elt') m') (x:key),
  find x (combine m m') = at_least_one (find x m) (find x m').
Proof.
 induction m.
 intros.
 simpl.
 induction m'.
 intros; simpl; auto.
 simpl; destruct a.
 simpl; destruct (X.compare x t0); simpl; auto.
 inversion_clear Hm'; auto.
 induction m'.
 (* m' = nil *)
 intros; destruct a; simpl.
 destruct (X.compare x t0) as [Hlt| |Hlt]; simpl; auto.
 inversion_clear Hm; clear H0 Hlt Hm' IHm t0.
 induction m; simpl; auto.
 inversion_clear H.
 destruct a.
 simpl; destruct (X.compare x t0); simpl; auto.
 (* m' <> nil *)
 intros.
 destruct a as (k,e); destruct a0 as (k',e'); simpl.
 inversion Hm; inversion Hm'; subst.
 destruct (X.compare k k'); simpl;
  destruct (X.compare x k);
   elim_comp || destruct (X.compare x k'); simpl; auto.
 rewrite IHm; auto; simpl; elim_comp; auto.
 rewrite IHm; auto; simpl; elim_comp; auto.
 rewrite IHm; auto; simpl; elim_comp; auto.
 change (find x (combine ((k, e) :: m) m') = at_least_one None (find x m')).
 rewrite IHm'; auto.
 simpl find; elim_comp; auto.
 change (find x (combine ((k, e) :: m) m') = Some (Some e, find x m')).
 rewrite IHm'; auto.
 simpl find; elim_comp; auto.
 change (find x (combine ((k, e) :: m) m') =
         at_least_one (find x m) (find x m')).
 rewrite IHm'; auto.
 simpl find; elim_comp; auto.
Qed.

Definition at_least_one_then_f (o:option elt)(o':option elt') :=
  match o, o' with
   | None, None => None
   | _, _  => f o o'
  end.

Lemma map2_0 :
  forall m (Hm : sort (@ltk elt) m) m' (Hm' : sort (@ltk elt') m') (x:key),
  find x (map2 m m') = at_least_one_then_f (find x m) (find x m').
Proof.
 intros.
 rewrite <- map2_alt_equiv.
 unfold map2_alt.
 assert (H:=combine_1 Hm Hm' x).
 assert (H2:=combine_sorted Hm Hm').
 set (f':= fun p : oee' => f (fst p) (snd p)).
 set (m0 := combine m m') in *; clearbody m0.
 set (o:=find x m) in *; clearbody o.
 set (o':=find x m') in *; clearbody o'.
 clear Hm Hm' m m'.
 generalize H; clear H.
 match goal with |- ?m=?n -> ?p=?q =>
   assert ((m=n->p=q)/\(m=None -> p=None)); [|intuition] end.
 induction m0; simpl in *; intuition.
 destruct o; destruct o'; simpl in *; try discriminate; auto.
 destruct a as (k,(oo,oo')); simpl in *.
 inversion_clear H2.
 destruct (X.compare x k) as [Hlt|Heq|Hlt]; simpl in *.
 (* x < k *)
 destruct (f' (oo,oo')); simpl.
 elim_comp.
 destruct o; destruct o'; simpl in *; try discriminate; auto.
 destruct (IHm0 H0) as (H2,_); apply H2; auto.
 rewrite <- H.
 case_eq (find x m0); intros; auto.
 assert (ltk (elt:=oee') (x,(oo,oo')) (k,(oo,oo'))).
  red; auto.
 destruct (Sort_Inf_NotIn H0 (Inf_lt H4 H1)).
 exists p; apply find_2; auto.
 (* x = k *)
 assert (at_least_one_then_f o o' = f oo oo').
  destruct o; destruct o'; simpl in *; inversion_clear H; auto.
 rewrite H2.
 unfold f'; simpl.
 destruct (f oo oo'); simpl.
 elim_comp; auto.
 destruct (IHm0 H0) as (_,H4); apply H4; auto.
 case_eq (find x m0); intros; auto.
 assert (eqk (elt:=oee') (k,(oo,oo')) (x,(oo,oo'))).
  red; auto.
 destruct (Sort_Inf_NotIn H0 (Inf_eq (eqk_sym H5) H1)).
 exists p; apply find_2; auto.
 (* k < x *)
 unfold f'; simpl.
 destruct (f oo oo'); simpl.
 elim_comp; auto.
 destruct (IHm0 H0) as (H3,_); apply H3; auto.
 destruct (IHm0 H0) as (H3,_); apply H3; auto.

 (* None -> None *)
 destruct a as (k,(oo,oo')).
 simpl.
 inversion_clear H2.
 destruct (X.compare x k) as [Hlt|Heq|Hlt].
 (* x < k *)
 unfold f'; simpl.
 destruct (f oo oo'); simpl.
 elim_comp; auto.
 destruct (IHm0 H0) as (_,H4); apply H4; auto.
 case_eq (find x m0); intros; auto.
 assert (ltk (elt:=oee') (x,(oo,oo')) (k,(oo,oo'))).
  red; auto.
 destruct (Sort_Inf_NotIn H0 (Inf_lt H3 H1)).
 exists p; apply find_2; auto.
 (* x = k *)
 discriminate.
 (* k < x *)
 unfold f'; simpl.
 destruct (f oo oo'); simpl.
 elim_comp; auto.
 destruct (IHm0 H0) as (_,H4); apply H4; auto.
 destruct (IHm0 H0) as (_,H4); apply H4; auto.
Qed.

(** Specification of [map2] *)

Lemma map2_1 :
  forall m (Hm : sort (@ltk elt) m) m' (Hm' : sort (@ltk elt') m')(x:key),
  In x m \/ In x m' ->
  find x (map2 m m') = f (find x m) (find x m').
Proof.
 intros.
 rewrite map2_0; auto.
 destruct H as [(e,H)|(e,H)].
 rewrite (find_1 Hm H).
 destruct (find x m'); simpl; auto.
 rewrite (find_1 Hm' H).
 destruct (find x m); simpl; auto.
Qed.

Lemma map2_2 :
  forall m (Hm : sort (@ltk elt) m) m' (Hm' : sort (@ltk elt') m')(x:key),
  In x (map2 m m') -> In x m \/ In x m'.
Proof.
 intros.
 destruct H as (e,H).
 generalize (map2_0 Hm Hm' x).
 rewrite (find_1 (map2_sorted Hm Hm') H).
 generalize (@find_2 _ m x).
 generalize (@find_2 _ m' x).
 destruct (find x m);
   destruct (find x m'); simpl; intros.
 left; exists e0; auto.
 left; exists e0; auto.
 right; exists e0; auto.
 discriminate.
Qed.

End Elt3.
End Raw.

Module Make (X: OrderedType) <: S with Module E := X.
Module Raw := Raw X.
Module E := X.

Definition key := E.t.

Record slist (elt:Type) :=
  {this :> Raw.t elt; sorted : sort (@Raw.PX.ltk elt) this}.
Definition t (elt:Type) : Type := slist elt.

Section Elt.
 Variable elt elt' elt'':Type.

 Implicit Types m : t elt.
 Implicit Types x y : key.
 Implicit Types e : elt.

 Definition empty : t elt := Build_slist (Raw.empty_sorted elt).
 Definition is_empty m : bool := Raw.is_empty m.(this).
 Definition add x e m : t elt := Build_slist (Raw.add_sorted m.(sorted) x e).
 Definition find x m : option elt := Raw.find x m.(this).
 Definition remove x m : t elt := Build_slist (Raw.remove_sorted m.(sorted) x).
 Definition mem x m : bool := Raw.mem x m.(this).
 Definition map f m : t elt' := Build_slist (Raw.map_sorted m.(sorted) f).
 Definition mapi (f:key->elt->elt') m : t elt' := Build_slist (Raw.mapi_sorted m.(sorted) f).
 Definition map2 f m (m':t elt') : t elt'' :=
   Build_slist (Raw.map2_sorted f m.(sorted) m'.(sorted)).
 Definition elements m : list (key*elt) := @Raw.elements elt m.(this).
 Definition cardinal m := length m.(this).
 Definition fold (A:Type)(f:key->elt->A->A) m (i:A) : A := @Raw.fold elt A f m.(this) i.
 Definition equal cmp m m' : bool := @Raw.equal elt cmp m.(this) m'.(this).

 Definition MapsTo x e m : Prop := Raw.PX.MapsTo x e m.(this).
 Definition In x m : Prop := Raw.PX.In x m.(this).
 Definition Empty m : Prop := Raw.Empty m.(this).

 Definition Equal m m' := forall y, find y m = find y m'.
 Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
         (forall k, In k m <-> In k m') /\
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
 Definition Equivb cmp m m' : Prop := @Raw.Equivb elt cmp m.(this) m'.(this).

 Definition eq_key : (key*elt) -> (key*elt) -> Prop := @Raw.PX.eqk elt.
 Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop:= @Raw.PX.eqke elt.
 Definition lt_key : (key*elt) -> (key*elt) -> Prop := @Raw.PX.ltk elt.

 Lemma MapsTo_1 : forall m x y e, E.eq x y -> MapsTo x e m -> MapsTo y e m.
 Proof. intros m; exact (@Raw.PX.MapsTo_eq elt m.(this)). Qed.

 Lemma mem_1 : forall m x, In x m -> mem x m = true.
 Proof. intros m; exact (@Raw.mem_1 elt m.(this) m.(sorted)). Qed.
 Lemma mem_2 : forall m x, mem x m = true -> In x m.
 Proof. intros m; exact (@Raw.mem_2 elt m.(this) m.(sorted)). Qed.

 Lemma empty_1 : Empty empty.
 Proof. exact (@Raw.empty_1 elt). Qed.

 Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
 Proof. intros m; exact (@Raw.is_empty_1 elt m.(this)). Qed.
 Lemma is_empty_2 :  forall m, is_empty m = true -> Empty m.
 Proof. intros m; exact (@Raw.is_empty_2 elt m.(this)). Qed.

 Lemma add_1 : forall m x y e, E.eq x y -> MapsTo y e (add x e m).
 Proof. intros m; exact (@Raw.add_1 elt m.(this)). Qed.
 Lemma add_2 : forall m x y e e', ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
 Proof. intros m; exact (@Raw.add_2 elt m.(this)). Qed.
 Lemma add_3 : forall m x y e e', ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
 Proof. intros m; exact (@Raw.add_3 elt m.(this)). Qed.

 Lemma remove_1 : forall m x y, E.eq x y -> ~ In y (remove x m).
 Proof. intros m; exact (@Raw.remove_1 elt m.(this) m.(sorted)). Qed.
 Lemma remove_2 : forall m x y e, ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
 Proof. intros m; exact (@Raw.remove_2 elt m.(this) m.(sorted)). Qed.
 Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.
 Proof. intros m; exact (@Raw.remove_3 elt m.(this) m.(sorted)). Qed.

 Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e.
 Proof. intros m; exact (@Raw.find_1 elt m.(this) m.(sorted)). Qed.
 Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
 Proof. intros m; exact (@Raw.find_2 elt m.(this)). Qed.

 Lemma elements_1 : forall m x e, MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
 Proof. intros m; exact (@Raw.elements_1 elt m.(this)). Qed.
 Lemma elements_2 : forall m x e, InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
 Proof. intros m; exact (@Raw.elements_2 elt m.(this)). Qed.
 Lemma elements_3 : forall m, sort lt_key (elements m).
 Proof. intros m; exact (@Raw.elements_3 elt m.(this) m.(sorted)). Qed.
 Lemma elements_3w : forall m, NoDupA eq_key (elements m).
 Proof. intros m; exact (@Raw.elements_3w elt m.(this) m.(sorted)). Qed.

 Lemma cardinal_1 : forall m, cardinal m = length (elements m).
 Proof. intros; reflexivity. Qed.

 Lemma fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
 Proof. intros m; exact (@Raw.fold_1 elt m.(this)). Qed.

 Lemma equal_1 : forall m m' cmp, Equivb cmp m m' -> equal cmp m m' = true.
 Proof. intros m m'; exact (@Raw.equal_1 elt m.(this) m.(sorted) m'.(this) m'.(sorted)). Qed.
 Lemma equal_2 : forall m m' cmp, equal cmp m m' = true -> Equivb cmp m m'.
 Proof. intros m m'; exact (@Raw.equal_2 elt m.(this) m.(sorted) m'.(this) m'.(sorted)). Qed.

 End Elt.

 Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
 Proof. intros elt elt' m; exact (@Raw.map_1 elt elt' m.(this)). Qed.
 Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
        In x (map f m) -> In x m.
 Proof. intros elt elt' m; exact (@Raw.map_2 elt elt' m.(this)). Qed.

 Lemma mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m ->
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
 Proof. intros elt elt' m; exact (@Raw.mapi_1 elt elt' m.(this)). Qed.
 Lemma mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.
 Proof. intros elt elt' m; exact (@Raw.mapi_2 elt elt' m.(this)). Qed.

 Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''),
	In x m \/ In x m' ->
        find x (map2 f m m') = f (find x m) (find x m').
 Proof.
 intros elt elt' elt'' m m' x f;
 exact (@Raw.map2_1 elt elt' elt'' f m.(this) m.(sorted) m'.(this) m'.(sorted) x).
 Qed.
 Lemma map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''),
        In x (map2 f m m') -> In x m \/ In x m'.
 Proof.
 intros elt elt' elt'' m m' x f;
 exact (@Raw.map2_2 elt elt' elt'' f m.(this) m.(sorted) m'.(this) m'.(sorted) x).
 Qed.

End Make.

Module Make_ord (X: OrderedType)(D : OrderedType) <:
Sord with Module Data := D
        with Module MapS.E := X.

Module Data := D.
Module MapS := Make(X).
Import MapS.

Module MD := OrderedTypeFacts(D).
Import MD.

Definition t := MapS.t D.t.

Definition cmp e e' := match D.compare e e' with EQ _ => true | _ => false end.

Fixpoint eq_list (m m' : list (X.t * D.t)) : Prop :=
  match m, m' with
   | nil, nil => True
   | (x,e)::l, (x',e')::l' =>
      match X.compare x x' with
       | EQ _ => D.eq e e' /\ eq_list l l'
       | _       => False
      end
   | _, _ => False
  end.

Definition eq m m' := eq_list m.(this) m'.(this).

Fixpoint lt_list (m m' : list (X.t * D.t)) : Prop :=
  match m, m' with
   | nil, nil => False
   | nil, _  => True
   | _, nil  => False
   | (x,e)::l, (x',e')::l' =>
      match X.compare x x' with
       | LT _ => True
       | GT _ => False
       | EQ _ => D.lt e e' \/ (D.eq e e' /\ lt_list l l')
      end
  end.

Definition lt m m' := lt_list m.(this) m'.(this).

Lemma eq_equal : forall m m', eq m m' <-> equal cmp m m' = true.
Proof.
 intros (l,Hl); induction l.
 intros (l',Hl'); unfold eq; simpl.
 destruct l'; unfold equal; simpl; intuition.
 intros (l',Hl'); unfold eq.
 destruct l'.
 destruct a; unfold equal; simpl; intuition.
 destruct a as (x,e).
 destruct p as (x',e').
 unfold equal; simpl.
 destruct (X.compare x x') as [Hlt|Heq|Hlt]; simpl; intuition.
 unfold cmp at 1.
 MD.elim_comp; clear H; simpl.
 inversion_clear Hl.
 inversion_clear Hl'.
 destruct (IHl H (Build_slist H3)).
 unfold equal, eq in H5; simpl in H5; auto.
 destruct (andb_prop _ _ H); clear H.
 generalize H0; unfold cmp.
 MD.elim_comp; auto; intro; discriminate.
 destruct (andb_prop _ _ H); clear H.
 inversion_clear Hl.
 inversion_clear Hl'.
 destruct (IHl H (Build_slist H3)).
 unfold equal, eq in H6; simpl in H6; auto.
Qed.

Lemma eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
Proof.
 intros.
 generalize (@equal_1 D.t m m' cmp).
 generalize (@eq_equal m m').
 intuition.
Qed.

Lemma eq_2 : forall m m', eq m m' -> Equivb cmp m m'.
Proof.
 intros.
 generalize (@equal_2 D.t m m' cmp).
 generalize (@eq_equal m m').
 intuition.
Qed.

Lemma eq_refl : forall m : t, eq m m.
Proof.
 intros (m,Hm); induction m; unfold eq; simpl; auto.
 destruct a.
 destruct (X.compare t0 t0) as [Hlt|Heq|Hlt]; auto.
 apply (MapS.Raw.MX.lt_antirefl Hlt); auto.
 split.
 apply D.eq_refl.
 inversion_clear Hm.
 apply (IHm H).
 apply (MapS.Raw.MX.lt_antirefl Hlt); auto.
Qed.

Lemma eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
Proof.
 intros (m,Hm); induction m;
 intros (m', Hm'); destruct m'; unfold eq; simpl;
 try destruct a as (x,e); try destruct p as (x',e'); auto.
 destruct (X.compare x x')  as [Hlt|Heq|Hlt]; MapS.Raw.MX.elim_comp; intuition.
 inversion_clear Hm; inversion_clear Hm'.
 apply (IHm H0 (Build_slist H4)); auto.
Qed.

Lemma eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
Proof.
 intros (m1,Hm1); induction m1;
 intros (m2, Hm2); destruct m2;
 intros (m3, Hm3); destruct m3; unfold eq; simpl;
 try destruct a as (x,e);
 try destruct p as (x',e');
 try destruct p0 as (x'',e''); try contradiction; auto.
 destruct (X.compare x x') as [Hlt|Heq|Hlt];
  destruct (X.compare x' x'') as [Hlt'|Heq'|Hlt'];
   MapS.Raw.MX.elim_comp; intuition.
 apply D.eq_trans with e'; auto.
 inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
 apply (IHm1 H1 (Build_slist H6) (Build_slist H8)); intuition.
Qed.

Lemma lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
Proof.
 intros (m1,Hm1); induction m1;
 intros (m2, Hm2); destruct m2;
 intros (m3, Hm3); destruct m3; unfold lt; simpl;
 try destruct a as (x,e);
 try destruct p as (x',e');
 try destruct p0 as (x'',e''); try contradiction; auto.
 destruct (X.compare x x') as [Hlt|Heq|Hlt];
  destruct (X.compare x' x'') as [Hlt'|Heq'|Hlt'];
   MapS.Raw.MX.elim_comp; intuition.
 left; apply D.lt_trans with e'; auto.
 left; apply lt_eq with e'; auto.
 left; apply eq_lt with e'; auto.
 right.
 split.
 apply D.eq_trans with e'; auto.
 inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
 apply (IHm1 H2 (Build_slist H6) (Build_slist H8)); intuition.
Qed.

Lemma lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.
Proof.
 intros (m1,Hm1); induction m1;
 intros (m2, Hm2); destruct m2; unfold eq, lt; simpl;
 try destruct a as (x,e);
 try destruct p as (x',e'); try contradiction; auto.
 destruct (X.compare x x') as [Hlt|Heq|Hlt]; auto.
 intuition.
 exact (D.lt_not_eq H0 H1).
 inversion_clear Hm1; inversion_clear Hm2.
 apply (IHm1 H0 (Build_slist H5)); intuition.
Qed.

Ltac cmp_solve := unfold eq, lt; simpl; try Raw.MX.elim_comp; auto.

Definition compare : forall m1 m2, Compare lt eq m1 m2.
Proof.
 intros (m1,Hm1); induction m1;
 intros (m2, Hm2); destruct m2;
  [ apply EQ | apply LT | apply GT | ]; cmp_solve.
 destruct a as (x,e); destruct p as (x',e').
 destruct (X.compare x x');
  [ apply LT | | apply GT ]; cmp_solve.
 destruct (D.compare e e');
  [ apply LT | | apply GT ]; cmp_solve.
 assert (Hm11 : sort (Raw.PX.ltk (elt:=D.t)) m1).
  inversion_clear Hm1; auto.
 assert (Hm22 : sort (Raw.PX.ltk (elt:=D.t)) m2).
  inversion_clear Hm2; auto.
 destruct (IHm1 Hm11 (Build_slist Hm22));
  [ apply LT | apply EQ | apply GT ]; cmp_solve.
Qed.

End Make_ord.

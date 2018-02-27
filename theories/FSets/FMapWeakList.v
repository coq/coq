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
 [FMapInterface.WS] using lists of pairs, unordered but without redundancy. *)

Require Import FunInd FMapInterface.

Set Implicit Arguments.
Unset Strict Implicit.

Module Raw (X:DecidableType).

Module Import PX := KeyDecidableType X.

Definition key := X.t.
Definition t (elt:Type) := list (X.t * elt).

Section Elt.

Variable elt : Type.

Notation eqk := (eqk (elt:=elt)).
Notation eqke := (eqke (elt:=elt)).
Notation MapsTo := (MapsTo (elt:=elt)).
Notation In := (In (elt:=elt)).
Notation NoDupA := (NoDupA eqk).

(** * [empty] *)

Definition empty : t elt := nil.

Definition Empty m := forall (a : key)(e:elt), ~ MapsTo a e m.

Lemma empty_1 : Empty empty.
Proof.
 unfold Empty,empty.
 intros a e.
 intro abs.
 inversion abs.
Qed.

Hint Resolve empty_1.

Lemma empty_NoDup : NoDupA empty.
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
 intros p l inlist.
 destruct p.
 absurd (InA eqke (t0, e) ((t0, e) :: l));auto.
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
   | (k',_) :: l => if X.eq_dec k k' then true else mem k l
  end.

Lemma mem_1 : forall m (Hm:NoDupA m) x, In x m -> mem x m = true.
Proof.
 intros m Hm x; generalize Hm; clear Hm.
 functional induction (mem x m);intros NoDup belong1;trivial.
 inversion belong1. inversion H.
 inversion_clear NoDup.
 inversion_clear belong1.
 inversion_clear H1.
 compute in H2; destruct H2.
 contradiction.
 apply IHb; auto.
 exists x0; auto.
Qed.

Lemma mem_2 : forall m (Hm:NoDupA m) x, mem x m = true -> In x m.
Proof.
 intros m Hm x; generalize Hm; clear Hm; unfold PX.In,PX.MapsTo.
 functional induction (mem x m); intros NoDup hyp; try discriminate.
 exists _x; auto.
 inversion_clear NoDup.
 destruct IHb; auto.
 exists x0; auto.
Qed.

(** * [find] *)

Function find (k:key) (s: t elt) {struct s} : option elt :=
  match s with
   | nil => None
   | (k',x)::s' => if X.eq_dec k k' then Some x else find k s'
  end.

Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
Proof.
 intros m x. unfold PX.MapsTo.
 functional induction (find x m);simpl;intros e' eqfind; inversion eqfind; auto.
Qed.

Lemma find_1 : forall m (Hm:NoDupA m) x e,
  MapsTo x e m -> find x m = Some e.
Proof.
 intros m Hm x e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction (find x m);simpl; subst; try clear H_eq_1.

 inversion 2.

 do 2 inversion_clear 1.
 compute in H2; destruct H2; subst; trivial.
 elim H; apply InA_eqk with (x,e); auto.

 do 2 inversion_clear 1; auto.
 compute in H2; destruct H2; elim _x; auto.
Qed.

(* Not part of the exported specifications, used later for [combine]. *)

Lemma find_eq : forall m (Hm:NoDupA m) x x',
   X.eq x x' -> find x m = find x' m.
Proof.
 induction m; simpl; auto; destruct a; intros.
 inversion_clear Hm.
 rewrite (IHm H1 x x'); auto.
 destruct (X.eq_dec x t0) as [|Hneq]; destruct (X.eq_dec x' t0) as [|?Hneq'];
   trivial.
 elim Hneq'; apply X.eq_trans with x; auto.
 elim Hneq; apply X.eq_trans with x'; auto.
Qed.

(** * [add] *)

Function add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
  match s with
   | nil => (k,x) :: nil
   | (k',y) :: l => if X.eq_dec k k' then (k,x)::l else (k',y)::add k x l
  end.

Lemma add_1 : forall m x y e, X.eq x y -> MapsTo y e (add x e m).
Proof.
 intros m x y e; generalize y; clear y; unfold PX.MapsTo.
 functional induction (add x e m);simpl;auto.
Qed.

Lemma add_2 : forall m x y e e',
  ~ X.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
Proof.
 intros m x  y e e'; generalize y e; clear y e; unfold PX.MapsTo.
 functional induction (add x e' m);simpl;auto.
 intros y' e'' eqky';  inversion_clear 1.
 destruct H0; simpl in *.
 elim eqky'; apply X.eq_trans with k'; auto.
 auto.
 intros y' e'' eqky'; inversion_clear 1; intuition.
Qed.

Lemma add_3 : forall m x y e e',
  ~ X.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
Proof.
 intros m x y e e'. generalize y e; clear y e; unfold PX.MapsTo.
 functional induction (add x e' m);simpl;auto.
 intros; apply (In_inv_3 H0); auto.
 constructor 2; apply (In_inv_3 H0); auto.
 inversion_clear 2; auto.
Qed.

Lemma add_3' : forall m x y e e',
  ~ X.eq x y -> InA eqk (y,e) (add x e' m) -> InA eqk (y,e) m.
Proof.
 intros m x y e e'. generalize y e; clear y e.
 functional induction (add x e' m);simpl;auto.
 inversion_clear 2.
 compute in H1; elim H; auto.
 inversion H1.
 constructor 2; inversion_clear H0; auto.
 compute in H1; elim H; auto.
 inversion_clear 2; auto.
Qed.

Lemma add_NoDup : forall m (Hm:NoDupA m) x e, NoDupA (add x e m).
Proof.
 induction m.
 simpl; constructor; auto; red; inversion 1.
 intros.
 destruct a as (x',e').
 simpl; case (X.eq_dec x x'); inversion_clear Hm; auto.
 constructor; auto.
 contradict H.
 apply InA_eqk with (x,e); auto.
 constructor; auto.
 contradict H; apply add_3' with x e; auto.
Qed.

(* Not part of the exported specifications, used later for [combine]. *)

Lemma add_eq : forall m (Hm:NoDupA m) x a e,
   X.eq x a -> find x (add a e m) = Some e.
Proof.
 intros.
 apply find_1; auto.
 apply add_NoDup; auto.
 apply add_1; auto.
Qed.

Lemma add_not_eq : forall m (Hm:NoDupA m) x a e,
  ~X.eq x a -> find x (add a e m) = find x m.
Proof.
 intros.
 case_eq (find x m); intros.
 apply find_1; auto.
 apply add_NoDup; auto.
 apply add_2; auto.
 apply find_2; auto.
 case_eq (find x (add a e m)); intros; auto.
 rewrite <- H0; symmetry.
 apply find_1; auto.
 apply add_3 with a e; auto.
 apply find_2; auto.
Qed.


(** * [remove] *)

Function remove (k : key) (s : t elt) {struct s} : t elt :=
  match s with
   | nil => nil
   | (k',x) :: l => if X.eq_dec k k' then l else (k',x) :: remove k l
  end.

Lemma remove_1 : forall m (Hm:NoDupA m) x y, X.eq x y -> ~ In y (remove x m).
Proof.
 intros m Hm x y; generalize Hm; clear Hm.
 functional induction (remove x m);simpl;intros;auto.

 red; inversion 1; inversion H1.

 inversion_clear Hm.
 subst.
 contradict H0.
 destruct H0 as (e,H2); unfold PX.MapsTo in H2.
 apply InA_eqk with (y,e); auto.
 compute; apply X.eq_trans with x; auto.

 intro H2.
 destruct H2 as (e,H2); inversion_clear H2.
 compute in H0; destruct H0.
 elim _x; apply X.eq_trans with y; auto.
 inversion_clear Hm.
 elim (IHt0 H2 H).
 exists e; auto.
Qed.

Lemma remove_2 : forall m (Hm:NoDupA m) x y e,
  ~ X.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
Proof.
 intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction (remove x m);auto.
 inversion_clear 3; auto.
 compute in H1; destruct H1.
 elim H; apply X.eq_trans with k'; auto.

 inversion_clear 1; inversion_clear 2; auto.
Qed.

Lemma remove_3 : forall m (Hm:NoDupA m) x y e,
  MapsTo y e (remove x m) -> MapsTo y e m.
Proof.
 intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction (remove x m);auto.
 do 2 inversion_clear 1; auto.
Qed.

Lemma remove_3' : forall m (Hm:NoDupA m) x y e,
  InA eqk (y,e) (remove x m) -> InA eqk (y,e) m.
Proof.
 intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction (remove x m);auto.
 do 2 inversion_clear 1; auto.
Qed.

Lemma remove_NoDup : forall m (Hm:NoDupA m) x, NoDupA (remove x m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 inversion_clear Hm.
 destruct a as (x',e').
 simpl; case (X.eq_dec x x'); auto.
 constructor; auto.
 contradict H; apply remove_3' with x; auto.
Qed.

(** * [elements] *)

Definition elements (m: t elt) := m.

Lemma elements_1 : forall m x e, MapsTo x e m -> InA eqke (x,e) (elements m).
Proof.
 auto.
Qed.

Lemma elements_2 : forall m x e, InA eqke (x,e) (elements m) -> MapsTo x e m.
Proof.
auto.
Qed.

Lemma elements_3w : forall m (Hm:NoDupA m), NoDupA (elements m).
Proof.
 auto.
Qed.

(** * [fold] *)

Function fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc : A) {struct m} :  A :=
  match m with
   | nil => acc
   | (k,e)::m' => fold f m' (f k e acc)
  end.

Lemma fold_1 : forall m (A:Type)(i:A)(f:key->elt->A->A),
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
Proof.
 intros; functional induction (@fold A f m i); auto.
Qed.

(** * [equal] *)

Definition check (cmp : elt -> elt -> bool)(k:key)(e:elt)(m': t elt) :=
  match find k m' with
   | None => false
   | Some e' => cmp e e'
  end.

Definition submap (cmp : elt -> elt -> bool)(m m' : t elt) : bool :=
  fold (fun k e b => andb (check cmp k e m') b) m true.

Definition equal (cmp : elt -> elt -> bool)(m m' : t elt) : bool :=
  andb (submap cmp m m') (submap (fun e' e => cmp e e') m' m).

Definition Submap cmp m m' :=
  (forall k, In k m -> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Definition Equivb cmp m m' :=
  (forall k, In k m <-> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Lemma submap_1 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m') cmp,
  Submap cmp m m' -> submap cmp m m' = true.
Proof.
 unfold Submap, submap.
 induction m.
 simpl; auto.
 destruct a; simpl; intros.
 destruct H.
 inversion_clear Hm.
 assert (H3 : In t0 m').
  apply H; exists e; auto.
 destruct H3 as (e', H3).
 unfold check at 2; rewrite (find_1 Hm' H3).
 rewrite (H0 t0); simpl; auto.
 eapply IHm; auto.
 split; intuition.
 apply H.
 destruct H5 as (e'',H5); exists e''; auto.
 apply H0 with k; auto.
Qed.

Lemma submap_2 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m') cmp,
  submap cmp m m' = true -> Submap cmp m m'.
Proof.
 unfold Submap, submap.
 induction m.
 simpl; auto.
 intuition.
 destruct H0; inversion H0.
 inversion H0.

 destruct a; simpl; intros.
 inversion_clear Hm.
 rewrite andb_b_true in H.
 assert (check cmp t0 e m' = true).
  clear H1 H0 Hm' IHm.
  set (b:=check cmp t0 e m') in *.
  generalize H; clear H; generalize b; clear b.
  induction m; simpl; auto; intros.
  destruct a; simpl in *.
  destruct (andb_prop _ _ (IHm _ H)); auto.
 rewrite H2 in H.
 destruct (IHm H1 m' Hm' cmp H); auto.
 unfold check in H2.
 case_eq (find t0 m'); [intros e' H5 | intros H5];
  rewrite H5 in H2; try discriminate.
 split; intros.
 destruct H6 as (e0,H6); inversion_clear H6.
 compute in H7; destruct H7; subst.
 exists e'.
 apply PX.MapsTo_eq with t0; auto.
 apply find_2; auto.
 apply H3.
 exists e0; auto.
 inversion_clear H6.
 compute in H8; destruct H8; subst.
 rewrite (find_1 Hm' (PX.MapsTo_eq H6 H7)) in H5; congruence.
 apply H4 with k; auto.
Qed.

(** Specification of [equal] *)

Lemma equal_1 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m') cmp,
  Equivb cmp m m' -> equal cmp m m' = true.
Proof.
 unfold Equivb, equal.
 intuition.
 apply andb_true_intro; split; apply submap_1; unfold Submap; firstorder.
Qed.

Lemma equal_2 : forall m (Hm:NoDupA m) m' (Hm':NoDupA m') cmp,
  equal cmp m m' = true -> Equivb cmp m m'.
Proof.
 unfold Equivb, equal.
 intros.
 destruct (andb_prop _ _ H); clear H.
 generalize (submap_2 Hm Hm' H0).
 generalize (submap_2 Hm' Hm H1).
 firstorder.
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
 constructor 2.
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

Lemma map_NoDup : forall m (Hm : NoDupA (@eqk elt) m)(f:elt->elt'),
  NoDupA (@eqk elt') (map f m).
Proof.
 induction m; simpl; auto.
 intros.
 destruct a as (x',e').
 inversion_clear Hm.
 constructor; auto.
 contradict H.
 (* il faut un map_1 avec eqk au lieu de eqke *)
 clear IHm H0.
 induction m; simpl in *; auto.
 inversion H.
 destruct a; inversion H; auto.
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

Lemma mapi_NoDup : forall m (Hm : NoDupA (@eqk elt) m)(f: key->elt->elt'),
  NoDupA (@eqk elt') (mapi f m).
Proof.
 induction m; simpl; auto.
 intros.
 destruct a as (x',e').
 inversion_clear Hm; auto.
 constructor; auto.
 contradict H.
 clear IHm H0.
 induction m; simpl in *; auto.
 inversion_clear H.
 destruct a; inversion_clear H; auto.
Qed.

End Elt2.
Section Elt3.

Variable elt elt' elt'' : Type.

Notation oee' := (option elt * option elt')%type.

Definition combine_l (m:t elt)(m':t elt') : t oee' :=
  mapi (fun k e => (Some e, find k m')) m.

Definition combine_r (m:t elt)(m':t elt') : t oee' :=
  mapi (fun k e' => (find k m, Some e')) m'.

Definition fold_right_pair (A B C:Type)(f:A->B->C->C) :=
  List.fold_right (fun p => f (fst p) (snd p)).

Definition combine (m:t elt)(m':t elt') : t oee' :=
  let l := combine_l m m' in
  let r := combine_r m m' in
  fold_right_pair (add (elt:=oee')) r l.

Lemma fold_right_pair_NoDup :
  forall l r (Hl: NoDupA (eqk (elt:=oee')) l)
    (Hl: NoDupA (eqk (elt:=oee')) r),
    NoDupA (eqk (elt:=oee')) (fold_right_pair (add (elt:=oee')) r l).
Proof.
 induction l; simpl; auto.
 destruct a; simpl; auto.
 inversion_clear 1.
 intros; apply add_NoDup; auto.
Qed.
Hint Resolve fold_right_pair_NoDup.

Lemma combine_NoDup :
  forall m (Hm:NoDupA (@eqk elt) m) m' (Hm':NoDupA (@eqk elt') m'),
  NoDupA (@eqk oee') (combine m m').
Proof.
 unfold combine, combine_r, combine_l.
 intros.
 set (f1 := fun (k : key) (e : elt) => (Some e, find k m')).
 set (f2 := fun (k : key) (e' : elt') => (find k m, Some e')).
 generalize (mapi_NoDup Hm f1).
 generalize (mapi_NoDup Hm' f2).
 set (l := mapi f1 m); clearbody l.
 set (r := mapi f2 m'); clearbody r.
 auto.
Qed.

Definition at_least_left (o:option elt)(o':option elt') :=
  match o with
   | None => None
   | _  => Some (o,o')
  end.

Definition at_least_right (o:option elt)(o':option elt') :=
  match o' with
   | None => None
   | _  => Some (o,o')
  end.

Lemma combine_l_1 :
  forall m (Hm:NoDupA (@eqk elt) m) m' (Hm':NoDupA (@eqk elt') m')(x:key),
  find x (combine_l m m') = at_least_left (find x m) (find x m').
Proof.
 unfold combine_l.
 intros.
 case_eq (find x m); intros.
 simpl.
 apply find_1.
 apply mapi_NoDup; auto.
 destruct (mapi_1 (fun k e => (Some e, find k m')) (find_2 H)) as (y,(H0,H1)).
 rewrite (find_eq Hm' (X.eq_sym H0)); auto.
 simpl.
 case_eq (find x (mapi (fun k e => (Some e, find k m')) m)); intros; auto.
 destruct (@mapi_2 _ _ m x (fun k e => (Some e, find k m'))).
 exists p; apply find_2; auto.
 rewrite (find_1 Hm H1) in H; discriminate.
Qed.

Lemma combine_r_1 :
  forall m (Hm:NoDupA (@eqk elt) m) m' (Hm':NoDupA (@eqk elt') m')(x:key),
  find x (combine_r m m') = at_least_right (find x m) (find x m').
Proof.
 unfold combine_r.
 intros.
 case_eq (find x m'); intros.
 simpl.
 apply find_1.
 apply mapi_NoDup; auto.
 destruct (mapi_1 (fun k e => (find k m, Some e)) (find_2 H)) as (y,(H0,H1)).
 rewrite (find_eq Hm (X.eq_sym H0)); auto.
 simpl.
 case_eq (find x (mapi (fun k e' => (find k m, Some e')) m')); intros; auto.
 destruct (@mapi_2 _ _ m' x (fun k e' => (find k m, Some e'))).
 exists p; apply find_2; auto.
 rewrite (find_1 Hm' H1) in H; discriminate.
Qed.

Definition at_least_one (o:option elt)(o':option elt') :=
  match o, o' with
   | None, None => None
   | _, _  => Some (o,o')
  end.

Lemma combine_1 :
  forall m (Hm:NoDupA (@eqk elt) m) m' (Hm':NoDupA (@eqk elt') m')(x:key),
  find x (combine m m') = at_least_one (find x m) (find x m').
Proof.
 unfold combine.
 intros.
 generalize (combine_r_1 Hm Hm' x).
 generalize (combine_l_1 Hm Hm' x).
 assert (NoDupA (eqk (elt:=oee')) (combine_l m m')).
  unfold combine_l; apply mapi_NoDup; auto.
 assert (NoDupA (eqk (elt:=oee')) (combine_r m m')).
  unfold combine_r; apply mapi_NoDup; auto.
 set (l := combine_l m m') in *; clearbody l.
 set (r := combine_r m m') in *; clearbody r.
 set (o := find x m); clearbody o.
 set (o' := find x m'); clearbody o'.
 clear Hm' Hm m m'.
 induction l.
 destruct o; destruct o'; simpl; intros; discriminate || auto.
 destruct a; simpl in *; intros.
 destruct (X.eq_dec x t0); simpl in *.
 unfold at_least_left in H1.
 destruct o; simpl in *; try discriminate.
 inversion H1; subst.
 apply add_eq; auto.
 inversion_clear H; auto.
 inversion_clear H.
 rewrite <- IHl; auto.
 apply add_not_eq; auto.
Qed.

Variable f : option elt -> option elt' -> option elt''.

Definition option_cons (A:Type)(k:key)(o:option A)(l:list (key*A)) :=
  match o with
   | Some e => (k,e)::l
   | None => l
  end.

Definition map2 m m' :=
  let m0 : t oee' := combine m m' in
  let m1 : t (option elt'') := map (fun p => f (fst p) (snd p)) m0 in
  fold_right_pair (option_cons (A:=elt'')) nil m1.

Lemma map2_NoDup :
  forall m (Hm:NoDupA (@eqk elt) m) m' (Hm':NoDupA (@eqk elt') m'),
  NoDupA (@eqk elt'') (map2 m m').
Proof.
 intros.
 unfold map2.
 assert (H0:=combine_NoDup Hm Hm').
 set (l0:=combine m m') in *; clearbody l0.
 set (f':= fun p : oee' => f (fst p) (snd p)).
 assert (H1:=map_NoDup (elt' := option elt'') H0 f').
 set (l1:=map f' l0) in *; clearbody l1.
 clear f' f H0 l0 Hm Hm' m m'.
 induction l1.
 simpl; auto.
 inversion_clear H1.
 destruct a; destruct o; simpl; auto.
 constructor; auto.
 contradict H.
 clear IHl1.
 induction l1.
 inversion H.
 inversion_clear H0.
 destruct a; destruct o; simpl in *; auto.
 inversion_clear H; auto.
Qed.

Definition at_least_one_then_f (o:option elt)(o':option elt') :=
  match o, o' with
   | None, None => None
   | _, _  => f o o'
  end.

Lemma map2_0 :
  forall m (Hm:NoDupA (@eqk elt) m) m' (Hm':NoDupA (@eqk elt') m')(x:key),
  find x (map2 m m') = at_least_one_then_f (find x m) (find x m').
Proof.
 intros.
 unfold map2.
 assert (H:=combine_1 Hm Hm' x).
 assert (H2:=combine_NoDup Hm Hm').
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
 destruct (X.eq_dec x k) as [|Hneq]; simpl in *.
 (* x = k *)
 assert (at_least_one_then_f o o' = f oo oo').
  destruct o; destruct o'; simpl in *; inversion_clear H; auto.
 rewrite H2.
 unfold f'; simpl.
 destruct (f oo oo'); simpl.
 destruct (X.eq_dec x k) as [|Hneq]; try contradict Hneq; auto.
 destruct (IHm0 H1) as (_,H4); apply H4; auto.
 case_eq (find x m0); intros; auto.
 elim H0.
 apply InA_eqk with (x,p); auto.
 apply InA_eqke_eqk.
 exact (find_2 H3).
 (* k < x *)
 unfold f'; simpl.
 destruct (f oo oo'); simpl.
 destruct (X.eq_dec x k); [ contradict Hneq; auto | auto].
 destruct (IHm0 H1) as (H3,_); apply H3; auto.
 destruct (IHm0 H1) as (H3,_); apply H3; auto.

 (* None -> None *)
 destruct a as (k,(oo,oo')).
 simpl.
 inversion_clear H2.
 destruct (X.eq_dec x k) as [|Hneq].
 (* x = k *)
 discriminate.
 (* k < x *)
 unfold f'; simpl.
 destruct (f oo oo'); simpl.
 destruct (X.eq_dec x k); [ contradict Hneq; auto | auto].
 destruct (IHm0 H1) as (_,H4); apply H4; auto.
 destruct (IHm0 H1) as (_,H4); apply H4; auto.
Qed.

(** Specification of [map2] *)
Lemma map2_1 :
  forall m (Hm:NoDupA (@eqk elt) m) m' (Hm':NoDupA (@eqk elt') m')(x:key),
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
  forall m (Hm:NoDupA (@eqk elt) m) m' (Hm':NoDupA (@eqk elt') m')(x:key),
  In x (map2 m m') -> In x m \/ In x m'.
Proof.
 intros.
 destruct H as (e,H).
 generalize (map2_0 Hm Hm' x).
 rewrite (find_1 (map2_NoDup Hm Hm') H).
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


Module Make (X: DecidableType) <: WS with Module E:=X.
 Module Raw := Raw X.

 Module E := X.
 Definition key := E.t.

 Record slist (elt:Type) :=
  {this :> Raw.t elt; NoDup : NoDupA (@Raw.PX.eqk elt) this}.
 Definition t (elt:Type) := slist elt.

Section Elt.
 Variable elt elt' elt'':Type.

 Implicit Types m : t elt.
 Implicit Types x y : key.
 Implicit Types e : elt.

 Definition empty : t elt := Build_slist (Raw.empty_NoDup elt).
 Definition is_empty m : bool := Raw.is_empty m.(this).
 Definition add x e m : t elt := Build_slist (Raw.add_NoDup m.(NoDup) x e).
 Definition find x m : option elt := Raw.find x m.(this).
 Definition remove x m : t elt := Build_slist (Raw.remove_NoDup m.(NoDup) x).
 Definition mem x m : bool := Raw.mem x m.(this).
 Definition map f m : t elt' := Build_slist (Raw.map_NoDup m.(NoDup) f).
 Definition mapi (f:key->elt->elt') m : t elt' := Build_slist (Raw.mapi_NoDup m.(NoDup) f).
 Definition map2 f m (m':t elt') : t elt'' :=
   Build_slist (Raw.map2_NoDup f m.(NoDup) m'.(NoDup)).
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

 Lemma MapsTo_1 : forall m x y e, E.eq x y -> MapsTo x e m -> MapsTo y e m.
 Proof. intros m; exact (@Raw.PX.MapsTo_eq elt m.(this)). Qed.

 Lemma mem_1 : forall m x, In x m -> mem x m = true.
 Proof. intros m; exact (@Raw.mem_1 elt m.(this) m.(NoDup)). Qed.
 Lemma mem_2 : forall m x, mem x m = true -> In x m.
 Proof. intros m; exact (@Raw.mem_2 elt m.(this) m.(NoDup)). Qed.

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
 Proof. intros m; exact (@Raw.remove_1 elt m.(this) m.(NoDup)). Qed.
 Lemma remove_2 : forall m x y e, ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
 Proof. intros m; exact (@Raw.remove_2 elt m.(this) m.(NoDup)). Qed.
 Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.
 Proof. intros m; exact (@Raw.remove_3 elt m.(this) m.(NoDup)). Qed.

 Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e.
 Proof. intros m; exact (@Raw.find_1 elt m.(this) m.(NoDup)). Qed.
 Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
 Proof. intros m; exact (@Raw.find_2 elt m.(this)). Qed.

 Lemma elements_1 : forall m x e, MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
 Proof. intros m; exact (@Raw.elements_1 elt m.(this)). Qed.
 Lemma elements_2 : forall m x e, InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
 Proof. intros m; exact (@Raw.elements_2 elt m.(this)). Qed.
 Lemma elements_3w : forall m, NoDupA eq_key (elements m).
 Proof. intros m; exact (@Raw.elements_3w elt m.(this) m.(NoDup)). Qed.

 Lemma cardinal_1 : forall m, cardinal m = length (elements m).
 Proof. intros; reflexivity. Qed.

 Lemma fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
 Proof. intros m; exact (@Raw.fold_1 elt m.(this)). Qed.

 Lemma equal_1 : forall m m' cmp, Equivb cmp m m' -> equal cmp m m' = true.
 Proof. intros m m'; exact (@Raw.equal_1 elt m.(this) m.(NoDup) m'.(this) m'.(NoDup)). Qed.
 Lemma equal_2 : forall m m' cmp, equal cmp m m' = true -> Equivb cmp m m'.
 Proof. intros m m'; exact (@Raw.equal_2 elt m.(this) m.(NoDup) m'.(this) m'.(NoDup)). Qed.

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
 exact (@Raw.map2_1 elt elt' elt'' f m.(this) m.(NoDup) m'.(this) m'.(NoDup) x).
 Qed.
 Lemma map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''),
        In x (map2 f m m') -> In x m \/ In x m'.
 Proof.
 intros elt elt' elt'' m m' x f;
 exact (@Raw.map2_2 elt elt' elt'' f m.(this) m.(NoDup) m'.(this) m'.(NoDup) x).
 Qed.

End Make.


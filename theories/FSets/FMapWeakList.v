(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * Finite map library *)  

(** This file proposes an implementation of the non-dependant interface
 [FMapInterface.S] using lists of pairs,  unordered but without redundancy. *)

Require Import FSetInterface. 
Require Import FSetWeakInterface.
Require Import FMapWeakInterface.

Set Implicit Arguments.
Unset Strict Implicit.

Arguments Scope list [type_scope].

Module Raw (XDecidableType).

Module PX = PairDecidableType X.
Import PX.

Definition key = X.t.
Definition t (eltSet) := list (X.t * elt).

Section Elt.

Variable elt  Set.

(* now in PairDecidableType
Definition eqk (p p'key*elt) := X.eq (fst p) (fst p').
Definition eqke (p p'key*elt) := 
          X.eq (fst p) (fst p') /\ (snd p) = (snd p').
*)

Notation eqk = (eqk (elt:=elt)).   
Notation eqke = (eqke (elt:=elt)).
Notation MapsTo = (MapsTo (elt:=elt)).
Notation In = (In (elt:=elt)).
Notation noredunA = (noredunA eqk).

(** * [empty] *)

Definition empty  t elt := nil.

Definition Empty m = forall (a : key)(e:elt), ~ MapsTo a e m.

Lemma empty_1  Empty empty.
Proof.
 unfold Empty,empty.
 intros a e.
 intro abs.
 inversion abs.
Qed.

Hint Resolve empty_1.

Lemma empty_noredun  noredunA empty.
Proof. 
 unfold empty; auto.
Qed.

(** * [is_empty] *)

Definition is_empty (l  t elt) : bool := if l then true else false.

Lemma is_empty_1 forall m, Empty m -> is_empty m = true. 
Proof.
 unfold Empty, PX.MapsTo.
 intros m.
 case m;auto.
 intros p l inlist.
 destruct p.
 absurd (InA eqke (t0, e) ((t0, e) : l));auto.
Qed.

Lemma is_empty_2  forall m, is_empty m = true -> Empty m.
Proof.
 intros m.
 case m;auto.
 intros p l abs.
 inversion abs.
Qed.

(** * [mem] *)

Fixpoint mem (k  key) (s : t elt) {struct s} : bool :=
  match s with
   | nil => false
   | (k',_) : l => if X.eq_dec k k' then true else mem k l
  end.

Lemma mem_1  forall m (Hm:noredunA m) x, In x m -> mem x m = true.
Proof.
 intros m Hm x; generalize Hm; clear Hm.      
 functional induction mem x m;intros noredun belong1;trivial.
 inversion belong1. inversion H.
 inversion_clear noredun.
 inversion_clear belong1.
 inversion_clear H3.
 compute in H4; destruct H4.
 elim H; auto.
 apply H0; auto.
 exists x; auto.
Qed. 

Lemma mem_2  forall m (Hm:noredunA m) x, mem x m = true -> In x m. 
Proof.
 intros m Hm x; generalize Hm; clear Hm; unfold PX.In,PX.MapsTo.
 functional induction mem x m; intros noredun hyp; try discriminate.
 exists e; auto. 
 inversion_clear noredun.
 destruct H0; auto.
 exists x; auto.
Qed.

(** * [find] *)

Fixpoint find (kkey) (s: t elt) {struct s} : option elt :=
  match s with
   | nil => None
   | (k',x):s' => if X.eq_dec k k' then Some x else find k s'
  end.

Lemma find_2  forall m x e, find x m = Some e -> MapsTo x e m.
Proof.
 intros m x. unfold PX.MapsTo.
 functional induction find x m;simpl;intros e' eqfind; inversion eqfind; auto.
Qed.

Lemma find_1  forall m (Hm:noredunA m) x e, 
  MapsTo x e m -> find x m = Some e. 
Proof.
 intros m Hm x e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction find x m;simpl; subst; try clear H_eq_1.

 inversion 2.

 do 2 inversion_clear 1.
 compute in H3; destruct H3; subst; trivial.
 elim H0; apply InA_eqk with (k,e); auto.

 do 2 inversion_clear 1; auto.
 compute in H4; destruct H4; elim H; auto.
Qed.

(* Not part of the exported specifications, used later for [combine]. *)

Lemma find_eq  forall m (Hm:noredunA m) x x', 
   X.eq x x' -> find x m = find x' m.
Proof.
 induction m; simpl; auto; destruct a; intros.
 inversion_clear Hm.
 rewrite (IHm H1 x x'); auto.
 destruct (X.eq_dec x t0); destruct (X.eq_dec x' t0); trivial.
 elim n; apply X.eq_trans with x; auto.
 elim n; apply X.eq_trans with x'; auto.
Qed.

(** * [add] *)

Fixpoint add (k  key) (x : elt) (s : t elt) {struct s} : t elt :=
  match s with
   | nil => (k,x) : nil
   | (k',y) : l => if X.eq_dec k k' then (k,x)::l else (k',y)::add k x l
  end.

Lemma add_1  forall m x y e, X.eq x y -> MapsTo y e (add x e m).
Proof.
 intros m x y e; generalize y; clear y; unfold PX.MapsTo.
 functional induction add x e m;simpl;auto.
Qed.

Lemma add_2  forall m x y e e', 
  ~ X.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
Proof.
 intros m x  y e e'; generalize y e; clear y e; unfold PX.MapsTo.
 functional induction add x e' m;simpl;auto.
 intros y' e' eqky';  inversion_clear 1.
 destruct H1; simpl in *.
 elim eqky'; apply X.eq_trans with k'; auto.
 auto.
 intros y' e' eqky'; inversion_clear 1; intuition.
Qed.
  
Lemma add_3  forall m x y e e',
  ~ X.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
Proof.
 intros m x y e e'. generalize y e; clear y e; unfold PX.MapsTo.
 functional induction add x e' m;simpl;auto.
 intros; apply (In_inv_3 H0); auto.
 constructor 2; apply (In_inv_3 H1); auto.
 inversion_clear 2; auto.
Qed.

Lemma add_3'  forall m x y e e', 
  ~ X.eq x y -> InA eqk (y,e) (add x e' m) -> InA eqk (y,e) m. 
Proof.
 intros m x y e e'. generalize y e; clear y e.
 functional induction add x e' m;simpl;auto.
 inversion_clear 2.
 compute in H1; elim H; auto.
 inversion H1. 
 constructor 2; inversion_clear H1; auto.
 compute in H2; elim H0; auto.
 inversion_clear 2; auto.
Qed.

Lemma add_noredun  forall m (Hm:noredunA m) x e, noredunA (add x e m).
Proof.
 induction m.
 simpl; constructor; auto; red; inversion 1.
 intros.
 destruct a as (x',e').
 simpl; case (X.eq_dec x x'); inversion_clear Hm; auto.
 constructor; auto.
 swap H.
 apply InA_eqk with (x,e); auto.
 constructor; auto.
 swap H; apply add_3' with x e; auto.
Qed.

(* Not part of the exported specifications, used later for [combine]. *)

Lemma add_eq  forall m (Hm:noredunA m) x a e, 
   X.eq x a -> find x (add a e m) = Some e.
Proof.
 intros.
 apply find_1; auto.
 apply add_noredun; auto.
 apply add_1; auto.
Qed.

Lemma add_not_eq  forall m (Hm:noredunA m) x a e, 
  ~X.eq x a -> find x (add a e m) = find x m.
Proof.
 intros.
 case_eq (find x m); intros.
 apply find_1; auto.
 apply add_noredun; auto.
 apply add_2; auto.
 apply find_2; auto.
 case_eq (find x (add a e m)); intros; auto.
 rewrite <- H0; symmetry.
 apply find_1; auto.
 apply add_3 with a e; auto.
 apply find_2; auto.
Qed.


(** * [remove] *)

Fixpoint remove (k  key) (s : t elt) {struct s} : t elt :=
  match s with
   | nil => nil
   | (k',x) : l => if X.eq_dec k k' then l else (k',x) :: remove k l
  end.  

Lemma remove_1  forall m (Hm:noredunA m) x y, X.eq x y -> ~ In y (remove x m).
Proof.
 intros m Hm x y; generalize Hm; clear Hm.
 functional induction remove x m;simpl;intros;auto.

 red; inversion 1; inversion H1.

 inversion_clear Hm.
 subst.
 swap H1.
 destruct H3 as (e,H3); unfold PX.MapsTo in H3.
 apply InA_eqk with (y,e); auto.
 compute; apply X.eq_trans with k; auto.
  
 intro H2.
 destruct H2 as (e,H2); inversion_clear H2.
 compute in H3; destruct H3.
 elim H; apply X.eq_trans with y; auto.
 inversion_clear Hm.
 elim (H0 H4 H1).
 exists e; auto.
Qed.
  
Lemma remove_2  forall m (Hm:noredunA m) x y e, 
  ~ X.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
Proof.
 intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction remove x m;auto.
 inversion_clear 3; auto.
 compute in H2; destruct H2.
 elim H0; apply X.eq_trans with k'; auto.
  
 inversion_clear 1; inversion_clear 2; auto.
Qed.

Lemma remove_3  forall m (Hm:noredunA m) x y e, 
  MapsTo y e (remove x m) -> MapsTo y e m.
Proof.
 intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction remove x m;auto.
 do 2 inversion_clear 1; auto.
Qed.

Lemma remove_3'  forall m (Hm:noredunA m) x y e, 
  InA eqk (y,e) (remove x m) -> InA eqk (y,e) m.
Proof.
 intros m Hm x y e; generalize Hm; clear Hm; unfold PX.MapsTo.
 functional induction remove x m;auto.
 do 2 inversion_clear 1; auto.
Qed.

Lemma remove_noredun  forall m (Hm:noredunA m) x, noredunA (remove x m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 inversion_clear Hm.
 destruct a as (x',e').
 simpl; case (X.eq_dec x x'); auto.
 constructor; auto.
 swap H; apply remove_3' with x; auto.
Qed.  

(** * [elements] *)

Definition elements (m t elt) := m.

Lemma elements_1  forall m x e, MapsTo x e m -> InA eqke (x,e) (elements m).
Proof.
 auto.
Qed.

Lemma elements_2  forall m x e, InA eqke (x,e) (elements m) -> MapsTo x e m.
Proof. 
auto.
Qed.

Lemma elements_3  forall m (Hm:noredunA m), noredunA (elements m). 
Proof. 
 auto.
Qed.

(** * [fold] *)

Fixpoint fold (ASet)(f:key->elt->A->A)(m:t elt) {struct m} : A -> A :=
  fun acc => 
  match m with
   | nil => acc
   | (k,e):m' => fold f m' (f k e acc)
  end.

Lemma fold_1  forall m (A:Set)(i:A)(f:key->elt->A->A),
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
Proof. 
 intros; functional induction fold A f m i; auto.
Qed.

(** * [equal] *)

Definition check (cmp  elt -> elt -> bool)(k:key)(e:elt)(m': t elt) := 
  match find k m' with 
   | None => false
   | Some e' => cmp e e'
  end.

Definition submap (cmp  elt -> elt -> bool)(m m' : t elt) : bool := 
  fold (fun k e b => andb (check cmp k e m') b) m true. 
   
Definition equal (cmp  elt -> elt -> bool)(m m' : t elt) : bool :=
  andb (submap cmp m m') (submap (fun e' e => cmp e e') m' m).

Definition Submap cmp m m' = 
  (forall k, In k m -> In k m') /\ 
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).  

Definition Equal cmp m m' = 
  (forall k, In k m <-> In k m') /\ 
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).  

Lemma submap_1  forall m (Hm:noredunA m) m' (Hm': noredunA m') cmp, 
  Submap cmp m m' -> submap cmp m m' = true. 
Proof.
 unfold Submap, submap.
 induction m.
 simpl; auto.
 destruct a; simpl; intros.
 destruct H.
 inversion_clear Hm.
 assert (H3  In t0 m').
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
   
Lemma submap_2  forall m (Hm:noredunA m) m' (Hm': noredunA m') cmp, 
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
  set (b=check cmp t0 e m') in *.
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

Lemma equal_1  forall m (Hm:noredunA m) m' (Hm': noredunA m') cmp, 
  Equal cmp m m' -> equal cmp m m' = true. 
Proof. 
 unfold Equal, equal.
 intuition.
 apply andb_true_intro; split; apply submap_1; unfold Submap; firstorder.
Qed.

Lemma equal_2  forall m (Hm:noredunA m) m' (Hm':noredunA m') cmp, 
  equal cmp m m' = true -> Equal cmp m m'.
Proof.
 unfold Equal, equal.
 intros.
 destruct (andb_prop _ _ H); clear H.
 generalize (submap_2 Hm Hm' H0).
 generalize (submap_2 Hm' Hm H1).
 firstorder.
Qed. 

Variable elt'Set.

(** * [map] and [mapi] *)
  
Fixpoint map (felt -> elt') (m:t elt) {struct m} : t elt' :=
  match m with
   | nil => nil
   | (k,e):m' => (k,f e) :: map f m'
  end.

Fixpoint mapi (f key -> elt -> elt') (m:t elt) {struct m} : t elt' :=
  match m with
   | nil => nil
   | (k,e):m' => (k,f k e) :: mapi f m'
  end.

End Elt.
Section Elt2. 
(* A new section is necessary for previous definitions to work 
   with different [elt], especially [MapsTo]... *)
  
Variable elt elt'  Set.

(** Specification of [map] *)

Lemma map_1  forall (m:t elt)(x:key)(e:elt)(f:elt->elt'), 
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

Lemma map_2  forall (m:t elt)(x:key)(f:elt->elt'), 
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

Lemma map_noredun  forall m (Hm : noredunA (@eqk elt) m)(f:elt->elt'), 
  noredunA (@eqk elt') (map f m).
Proof.   
 induction m; simpl; auto.
 intros.
 destruct a as (x',e').
 inversion_clear Hm.
 constructor; auto.
 swap H.
 (* il faut un map_1 avec eqk au lieu de eqke *)
 clear IHm H0. 
 induction m; simpl in *; auto.
 inversion H1.
 destruct a; inversion H1; auto.
Qed.      
 
(** Specification of [mapi] *)

Lemma mapi_1  forall (m:t elt)(x:key)(e:elt)(f:key->elt->elt'), 
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

Lemma mapi_2  forall (m:t elt)(x:key)(f:key->elt->elt'), 
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

Lemma mapi_noredun  forall m (Hm : noredunA (@eqk elt) m)(f: key->elt->elt'), 
  noredunA (@eqk elt') (mapi f m).
Proof.
 induction m; simpl; auto.
 intros.
 destruct a as (x',e').
 inversion_clear Hm; auto.
 constructor; auto.
 swap H.
 clear IHm H0.
 induction m; simpl in *; auto.
 inversion_clear H1.
 destruct a; inversion_clear H1; auto.
Qed.

End Elt2. 
Section Elt3.

Variable elt elt' elt''  Set.

Notation oee' = (option elt * option elt')%type.
	
Definition combine_l (mt elt)(m':t elt') : t oee' :=
  mapi (fun k e => (Some e, find k m')) m.	

Definition combine_r (mt elt)(m':t elt') : t oee' :=
  mapi (fun k e' => (find k m, Some e')) m'.	

Definition fold_right_pair (A B CSet)(f:A->B->C->C)(l:list (A*B))(i:C) := 
  List.fold_right (fun p => f (fst p) (snd p)) i l.

Definition combine (mt elt)(m':t elt') : t oee' := 
  let l = combine_l m m' in 
  let r = combine_r m m' in 
  fold_right_pair (add (elt=oee')) l r.

Lemma fold_right_pair_noredun  
  forall l r (Hl noredunA (eqk (elt:=oee')) l) 
    (Hl noredunA (eqk (elt:=oee')) r), 
    noredunA (eqk (elt=oee')) (fold_right_pair (add (elt:=oee')) l r).
Proof.
 induction l; simpl; auto.
 destruct a; simpl; auto.
 inversion_clear 1.
 intros; apply add_noredun; auto.
Qed.
Hint Resolve fold_right_pair_noredun.

Lemma combine_noredun  
  forall m (HmnoredunA (@eqk elt) m) m' (Hm':noredunA (@eqk elt') m'), 
  noredunA (@eqk oee') (combine m m').
Proof.
 unfold combine, combine_r, combine_l.
 intros.
 set (f1 = fun (k : key) (e : elt) => (Some e, find k m')).
 set (f2 = fun (k : key) (e' : elt') => (find k m, Some e')).
 generalize (mapi_noredun Hm f1).
 generalize (mapi_noredun Hm' f2).
 set (l = mapi f1 m); clearbody l.
 set (r = mapi f2 m'); clearbody r.
 auto.
Qed.

Definition at_least_left (ooption elt)(o':option elt') := 
  match o with 
   | None => None 
   | _  => Some (o,o')
  end.

Definition at_least_right (ooption elt)(o':option elt') := 
  match o' with 
   | None => None 
   | _  => Some (o,o')
  end.

Lemma combine_l_1  
  forall m (HmnoredunA (@eqk elt) m) m' (Hm':noredunA (@eqk elt') m')(x:key), 
  find x (combine_l m m') = at_least_left (find x m) (find x m'). 
Proof.
 unfold combine_l.
 intros.
 case_eq (find x m); intros.
 simpl.
 apply find_1.
 apply mapi_noredun; auto.
 destruct (mapi_1 (fun k e => (Some e, find k m')) (find_2 H)) as (y,(H0,H1)).
 rewrite (find_eq Hm' (X.eq_sym H0)); auto.
 simpl.
 case_eq (find x (mapi (fun k e => (Some e, find k m')) m)); intros; auto.
 destruct (@mapi_2 _ _ m x (fun k e => (Some e, find k m'))).
 exists p; apply find_2; auto.
 rewrite (find_1 Hm H1) in H; discriminate.
Qed.

Lemma combine_r_1  
  forall m (HmnoredunA (@eqk elt) m) m' (Hm':noredunA (@eqk elt') m')(x:key), 
  find x (combine_r m m') = at_least_right (find x m) (find x m'). 
Proof.
 unfold combine_r.
 intros.
 case_eq (find x m'); intros.
 simpl.
 apply find_1.
 apply mapi_noredun; auto.
 destruct (mapi_1 (fun k e => (find k m, Some e)) (find_2 H)) as (y,(H0,H1)).
 rewrite (find_eq Hm (X.eq_sym H0)); auto.
 simpl.
 case_eq (find x (mapi (fun k e' => (find k m, Some e')) m')); intros; auto.
 destruct (@mapi_2 _ _ m' x (fun k e' => (find k m, Some e'))).
 exists p; apply find_2; auto.
 rewrite (find_1 Hm' H1) in H; discriminate.
Qed.

Definition at_least_one (ooption elt)(o':option elt') := 
  match o, o' with 
   | None, None => None 
   | _, _  => Some (o,o')
  end.

Lemma combine_1  
  forall m (HmnoredunA (@eqk elt) m) m' (Hm':noredunA (@eqk elt') m')(x:key), 
  find x (combine m m') = at_least_one (find x m) (find x m'). 
Proof.
 unfold combine.
 intros.
 generalize (combine_r_1 Hm Hm' x).
 generalize (combine_l_1 Hm Hm' x).
 assert (noredunA (eqk (elt=oee')) (combine_l m m')).
  unfold combine_l; apply mapi_noredun; auto.
 assert (noredunA (eqk (elt=oee')) (combine_r m m')).
  unfold combine_r; apply mapi_noredun; auto.
 set (l = combine_l m m') in *; clearbody l.
 set (r = combine_r m m') in *; clearbody r.
 set (o = find x m); clearbody o.
 set (o' = find x m'); clearbody o'.
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

Variable f  option elt -> option elt' -> option elt''.

Definition option_cons (ASet)(k:key)(o:option A)(l:list (key*A)) := 
  match o with
   | Some e => (k,e):l
   | None => l
  end.

Definition map2 m m' = 
  let m0  t oee' := combine m m' in 
  let m1  t (option elt'') := map (fun p => f (fst p) (snd p)) m0 in 
  fold_right_pair (option_cons (A=elt'')) m1 nil.

Lemma map2_noredun  
  forall m (HmnoredunA (@eqk elt) m) m' (Hm':noredunA (@eqk elt') m'), 
  noredunA (@eqk elt'') (map2 m m').
Proof.
 intros.
 unfold map2.
 assert (H0=combine_noredun Hm Hm').
 set (l0=combine m m') in *; clearbody l0.
 set (f'= fun p : oee' => f (fst p) (snd p)).
 assert (H1=map_noredun (elt' := option elt'') H0 f').
 set (l1=map f' l0) in *; clearbody l1. 
 clear f' f H0 l0 Hm Hm' m m'.
 induction l1.
 simpl; auto.
 inversion_clear H1.
 destruct a; destruct o; simpl; auto.
 constructor; auto.
 swap H.
 clear IHl1.
 induction l1.
 inversion H1.
 inversion_clear H0.
 destruct a; destruct o; simpl in *; auto.
 inversion_clear  H1; auto.
Qed.

Definition at_least_one_then_f (ooption elt)(o':option elt') := 
  match o, o' with 
   | None, None => None 
   | _, _  => f o o'
  end.

Lemma map2_0  
  forall m (HmnoredunA (@eqk elt) m) m' (Hm':noredunA (@eqk elt') m')(x:key), 
  find x (map2 m m') = at_least_one_then_f (find x m) (find x m'). 
Proof.
 intros.
 unfold map2.
 assert (H=combine_1 Hm Hm' x).
 assert (H2=combine_noredun Hm Hm').
 set (f'= fun p : oee' => f (fst p) (snd p)).
 set (m0 = combine m m') in *; clearbody m0.
 set (o=find x m) in *; clearbody o. 
 set (o'=find x m') in *; clearbody o'.
 clear Hm Hm' m m'.
 generalize H; clear H.
 match goal with |- ?m=?n -> ?p=?q =>
   assert ((m=n->p=q)/\(m=None -> p=None)); [|intuition] end.
 induction m0; simpl in *; intuition.
 destruct o; destruct o'; simpl in *; try discriminate; auto.
 destruct a as (k,(oo,oo')); simpl in *.
 inversion_clear H2.
 destruct (X.eq_dec x k); simpl in *.
 (* x = k *)
 assert (at_least_one_then_f o o' = f oo oo').
  destruct o; destruct o'; simpl in *; inversion_clear H; auto.
 rewrite H2.
 unfold f'; simpl.
 destruct (f oo oo'); simpl. 
 destruct (X.eq_dec x k); try absurd_hyp n; auto.
 destruct (IHm0 H1) as (_,H4); apply H4; auto.
 case_eq (find x m0); intros; auto.
 elim H0.
 apply InA_eqk with (x,p); auto.
 apply InA_eqke_eqk.
 exact (find_2 H3). 
 (* k < x *)
 unfold f'; simpl.
 destruct (f oo oo'); simpl.
 destruct (X.eq_dec x k); [ absurd_hyp n; auto | auto].
 destruct (IHm0 H1) as (H3,_); apply H3; auto.
 destruct (IHm0 H1) as (H3,_); apply H3; auto.

 (* None -> None *)
 destruct a as (k,(oo,oo')).
 simpl.
 inversion_clear H2.
 destruct (X.eq_dec x k).
 (* x = k *)
 discriminate.
 (* k < x *)
 unfold f'; simpl.
 destruct (f oo oo'); simpl.
 destruct (X.eq_dec x k); [ absurd_hyp n; auto | auto].
 destruct (IHm0 H1) as (_,H4); apply H4; auto.
 destruct (IHm0 H1) as (_,H4); apply H4; auto.
Qed.

(** Specification of [map2] *)
Lemma map2_1  
  forall m (HmnoredunA (@eqk elt) m) m' (Hm':noredunA (@eqk elt') m')(x:key),
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
 
Lemma map2_2  
  forall m (HmnoredunA (@eqk elt) m) m' (Hm':noredunA (@eqk elt') m')(x:key), 
  In x (map2 m m') -> In x m \/ In x m'. 
Proof.
 intros.
 destruct H as (e,H).
 generalize (map2_0 Hm Hm' x).
 rewrite (find_1 (map2_noredun Hm Hm') H).
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


Module Make (X DecidableType) <: S with Module E:=X.
 Module Raw = Raw X. 

 Module E = X.
 Definition key = X.t. 

 Record slist (eltSet) : Set :=  
  {this > Raw.t elt; noredun : noredunA (@Raw.PX.eqk elt) this}.
 Definition t (eltSet) := slist elt. 

 Section Elt. 
 Variable elt elt' elt''Set. 

 Implicit Types m  t elt.

 Definition empty = Build_slist (Raw.empty_noredun elt).
 Definition is_empty m = Raw.is_empty m.(this).
 Definition add x e m = Build_slist (Raw.add_noredun m.(noredun) x e).
 Definition find x m = Raw.find x m.(this).
 Definition remove x m = Build_slist (Raw.remove_noredun m.(noredun) x). 
 Definition mem x m = Raw.mem x m.(this).
 Definition map f m  t elt' := Build_slist (Raw.map_noredun m.(noredun) f).
 Definition mapi f m  t elt' := Build_slist (Raw.mapi_noredun m.(noredun) f).
 Definition map2 f m (m't elt') : t elt'' := 
 Build_slist (Raw.map2_noredun f m.(noredun) m'.(noredun)).
 Definition elements m = @Raw.elements elt m.(this).
 Definition fold A f m i = @Raw.fold elt A f m.(this) i.
 Definition equal cmp m m' = @Raw.equal elt cmp m.(this) m'.(this).

 Definition MapsTo x e m = Raw.PX.MapsTo x e m.(this).
 Definition In x m = Raw.PX.In x m.(this).
 Definition Empty m = Raw.Empty m.(this).
 Definition Equal cmp m m' = @Raw.Equal elt cmp m.(this) m'.(this).

 Definition eq_key (p p'key*elt) := X.eq (fst p) (fst p').
 
 Definition eq_key_elt (p p'key*elt) := 
      X.eq (fst p) (fst p') /\ (snd p) = (snd p').

 Definition MapsTo_1 m = @Raw.PX.MapsTo_eq elt m.(this).

 Definition mem_1 m = @Raw.mem_1 elt m.(this) m.(noredun).
 Definition mem_2 m = @Raw.mem_2 elt m.(this) m.(noredun).

 Definition empty_1 = @Raw.empty_1.

 Definition is_empty_1 m = @Raw.is_empty_1 elt m.(this).
 Definition is_empty_2 m = @Raw.is_empty_2 elt m.(this).

 Definition add_1 m = @Raw.add_1 elt m.(this).
 Definition add_2 m = @Raw.add_2 elt m.(this).
 Definition add_3 m = @Raw.add_3 elt m.(this).

 Definition remove_1 m = @Raw.remove_1 elt m.(this) m.(noredun).
 Definition remove_2 m = @Raw.remove_2 elt m.(this) m.(noredun).
 Definition remove_3 m = @Raw.remove_3 elt m.(this) m.(noredun).

 Definition find_1 m = @Raw.find_1 elt m.(this) m.(noredun).
 Definition find_2 m = @Raw.find_2 elt m.(this).

 Definition elements_1 m = @Raw.elements_1 elt m.(this).
 Definition elements_2 m = @Raw.elements_2 elt m.(this).
 Definition elements_3 m = @Raw.elements_3 elt m.(this) m.(noredun).

 Definition fold_1 m = @Raw.fold_1 elt m.(this).

 Definition map_1 m = @Raw.map_1 elt elt' m.(this).
 Definition map_2 m = @Raw.map_2 elt elt' m.(this).

 Definition mapi_1 m = @Raw.mapi_1 elt elt' m.(this).
 Definition mapi_2 m = @Raw.mapi_2 elt elt' m.(this).

 Definition map2_1 m (m't elt') x f := 
  @Raw.map2_1 elt elt' elt'' f m.(this) m.(noredun) m'.(this) m'.(noredun) x.
 Definition map2_2 m (m't elt') x f := 
  @Raw.map2_2 elt elt' elt'' f m.(this) m.(noredun) m'.(this) m'.(noredun) x.

 Definition equal_1 m m' = @Raw.equal_1 elt m.(this) m.(noredun) m'.(this) m'.(noredun).
 Definition equal_2 m m' = @Raw.equal_2 elt m.(this) m.(noredun) m'.(this) m'.(noredun).

 End Elt.
End Make.



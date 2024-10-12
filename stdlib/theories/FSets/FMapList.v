(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Finite map library *)

(** This file proposes an implementation of the non-dependent interface
 [FMapInterface.S] using lists of pairs ordered (increasing) with respect to
 left projection. *)

Require Import FMapInterface.

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
#[local]
Hint Resolve empty_1 : core.

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
 absurd (InA eqke (k, e) ((k, e) :: l)); auto with ordered_type.
Qed.

Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
Proof.
 intros m.
 case m;auto.
 intros p l abs.
 inversion abs.
Qed.

(** * [mem] *)

Fixpoint mem (k : key) (s : t elt) {struct s} : bool :=
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
 intros m Hm; induction m as [|[a m]]; intros x H; simpl in *.
 - destruct H as [? H]; inversion H.
 - apply In_inv in H; destruct H as [H|H].
   + destruct (elim_compare_eq H) as [? Hr]; rewrite Hr; reflexivity.
   + destruct (X.compare x a); [|reflexivity|apply IHm; inversion_clear Hm; auto].
     absurd (In x ((a, m) :: m0)); [|destruct H as [y v]; exists y; constructor 2; auto].
     apply Sort_Inf_NotIn with m; [inversion_clear Hm; auto|].
     constructor; apply l.
Qed.

Lemma mem_2 : forall m (Hm:Sort m) x, mem x m = true -> In x m.
Proof.
 intros m Hm; induction m as [|[a m]]; intros x H; simpl in *.
 - discriminate.
 - destruct X.compare; [discriminate| |].
   + exists m; apply InA_cons_hd; split; auto.
   + inversion_clear Hm; destruct IHm with x as [e He]; auto.
     exists e; apply InA_cons_tl; auto.
Qed.

(** * [find] *)

Fixpoint find (k:key) (s: t elt) {struct s} : option elt :=
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
 induction m as [|[a m]]; intros x e H; simpl in *; [congruence|].
 destruct X.compare; [congruence| |].
 - apply InA_cons_hd; split; compute; congruence.
 - apply InA_cons_tl; apply IHm; auto.
Qed.

Lemma find_1 :  forall m (Hm:Sort m) x e, MapsTo x e m -> find x m = Some e.
Proof.
intros m Hm; induction Hm as [|[a m] l Hm IHHm Hr]; intros x e H; simpl in *.
- inversion H.
- apply InA_cons in H; destruct H as [H|H].
  * unfold eqke in H; simpl in H.
    destruct elim_compare_eq with x a as [H' r]; [tauto|].
    rewrite r; f_equal; symmetry; tauto.
  * destruct elim_compare_gt with x a as [H' r]; [|rewrite r; apply IHHm, H].
    apply InA_eqke_eqk in H.
    apply (Sort_Inf_In Hm Hr H).
Qed.

(** * [add] *)

Fixpoint add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
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
induction m as [|[y e'] m IHm]; simpl.
- auto with ordered_type.
- intros; destruct X.compare; auto with ordered_type.
Qed.

Lemma add_2 : forall m x y e e',
  ~ X.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
Proof.
intros m x y e e' He H; unfold PX.MapsTo in *.
induction m as [|[z e''] m IHm]; simpl.
- auto.
- destruct X.compare as [Hlt|Heq|Hgt]; simpl.
  + auto with ordered_type.
  + apply InA_cons_tl; apply InA_cons in H; destruct H; [|assumption].
    compute in H; intuition order.
  + apply InA_cons in H; destruct H; [now auto with ordered_type|].
    apply InA_cons_tl; apply IHm, H.
Qed.

Lemma add_3 : forall m x y e e',
  ~ X.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
Proof.
intros m x y e e' He H; unfold PX.MapsTo in *.
induction m as [|[z e''] m IHm]; simpl in *.
- apply (In_inv_3 H); auto with ordered_type.
- destruct X.compare as [Hlt|Heq|Hgt]; simpl.
  + apply (In_inv_3 H); auto with ordered_type.
  + constructor 2; apply (In_inv_3 H); auto with ordered_type.
  + inversion_clear H; auto.
Qed.

Lemma add_Inf : forall (m:t elt)(x x':key)(e e':elt),
  Inf (x',e') m -> ltk (x',e') (x,e) -> Inf (x',e') (add x e m).
Proof.
 induction m.
 - simpl; intuition.
 - intros.
   destruct a as (x'',e'').
   inversion_clear H.
   compute in H0,H1.
   simpl; case (X.compare x x''); intuition.
Qed.
#[local]
Hint Resolve add_Inf : core.

Lemma add_sorted : forall m (Hm:Sort m) x e, Sort (add x e m).
Proof.
 induction m.
 - simpl; intuition.
 - intros.
   destruct a as (x',e').
   simpl; case (X.compare x x'); intuition; inversion_clear Hm; auto.
   constructor; auto.
   apply Inf_eq with (x',e'); auto.
Qed.

(** * [remove] *)

Fixpoint remove (k : key) (s : t elt) {struct s} : t elt :=
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
intros m Hm x y He [e H]; revert e H.
induction Hm as [|[a m] l Hm IHHm Hr]; simpl in *; intros e H.
- now inversion H.
- destruct X.compare as [Hlt|Heq|Hgt].
  + apply InA_cons in H; destruct H; [compute in H; destruct H; order|].
    apply InA_eqke_eqk in H; apply (Sort_Inf_In Hm Hr) in H.
    compute in H; order.
  + apply InA_eqke_eqk in H; apply (Sort_Inf_In Hm Hr) in H.
    compute in H; order.
  + apply InA_cons in H; destruct H; [compute in H; destruct H; order|].
    apply (IHHm e), H.
Qed.

Lemma remove_2 : forall m (Hm:Sort m) x y e,
  ~ X.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
Proof.
intros m Hm x y e He H.
induction Hm as [|[a m] l Hm IHHm Hr]; simpl in *.
- now inversion H.
- destruct X.compare as [Hlt|Heq|Hgt].
  + assumption.
  + apply InA_cons in H; destruct H; [compute in H; destruct H; order|].
    apply H.
  + apply InA_cons in H; destruct H.
    * apply InA_cons_hd; assumption.
    * apply InA_cons_tl, IHHm, H.
Qed.

Lemma remove_3 : forall m (Hm:Sort m) x y e,
  MapsTo y e (remove x m) -> MapsTo y e m.
Proof.
intros m Hm x y e H.
induction Hm as [|[a m] l Hm IHHm Hr]; simpl in *.
- now inversion H.
- destruct X.compare as [Hlt|Heq|Hgt].
  + assumption.
  + apply InA_cons_tl, H.
  + apply InA_cons in H; destruct H.
    * apply InA_cons_hd; assumption.
    * apply InA_cons_tl, IHHm, H.
Qed.

Lemma remove_Inf : forall (m:t elt)(Hm : Sort m)(x x':key)(e':elt),
  Inf (x',e') m -> Inf (x',e') (remove x m).
Proof.
 induction m.
 - simpl; intuition.
 - intros.
   destruct a as (x'',e'').
   inversion_clear H.
   compute in H0.
   simpl; case (X.compare x x''); intuition.
   inversion_clear Hm.
   apply Inf_lt with (x'',e''); auto.
Qed.
#[local]
Hint Resolve remove_Inf : core.

Lemma remove_sorted : forall m (Hm:Sort m) x, Sort (remove x m).
Proof.
 induction m.
 - simpl; intuition.
 - intros.
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

Fixpoint fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc:A) {struct m} :  A :=
  match m with
   | nil => acc
   | (k,e)::m' => fold f m' (f k e acc)
  end.

Lemma fold_1 : forall m (A:Type)(i:A)(f:key->elt->A->A),
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
Proof.
induction m as [|[k e] m]; simpl; auto.
Qed.

(** * [equal] *)

Fixpoint equal (cmp:elt->elt->bool)(m m' : t elt) {struct m} : bool :=
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
intros m Hm m' Hm' cmp; revert m' Hm'.
induction Hm as [|[a e] m Hm IHHm Hr]; simpl in *; intros [|[a' e'] m'] Hm' H.
+ reflexivity.
+ destruct H as [H _]; specialize (H a') as [_ H].
  destruct H; [exists e'; constructor; reflexivity|inversion H].
+ destruct H as [H _]; specialize (H a) as [H _].
  destruct H; [exists e; constructor; reflexivity|inversion H].
+ apply Sorted_inv in Hm'; destruct Hm' as [Hm' Hr'].
  destruct (X.compare a a') as [Hlt|Heq|Hgt]; [exfalso| |exfalso].
  - destruct H as [H _]; specialize (H a) as [H _].
    destruct H as [e'' H]; [eexists; constructor; reflexivity|].
    apply InA_cons in H; destruct H as [H|H].
    * apply (gt_not_eq Hlt); symmetry; apply H.
    * apply InA_eqke_eqk, (Sort_Inf_In Hm' Hr') in H.
      compute in H; order.
  - apply andb_true_iff; split.
    * destruct H as [_ H]; apply H with a.
      { apply InA_cons_hd; reflexivity. }
      { apply InA_cons_hd; auto with ordered_type. }
    * apply IHHm; [assumption|]; split.
      { intros k; destruct H as [H _]; specialize (H k).
        split; intros [e'' Hk].
        + destruct H as [H _]; destruct H as [e''' H].
          - exists e''; apply InA_cons_tl; apply Hk.
          - apply InA_cons in H; destruct H as [[H _]|H].
            * assert (Hs := Sort_Inf_In Hm Hr (InA_eqke_eqk Hk)).
              elim (gt_not_eq Hs); simpl; etransitivity; [eassumption|symmetry; assumption].
            * exists e'''; assumption.
        + destruct H as [_ H]; destruct H as [e''' H].
          - exists e''; apply InA_cons_tl; apply Hk.
          - apply InA_cons in H; destruct H as [[H _]|H].
            * assert (Hs := Sort_Inf_In Hm' Hr' (InA_eqke_eqk Hk)).
              elim (gt_not_eq Hs); simpl; etransitivity; eassumption.
            * exists e'''; assumption.
      }
      { intros; destruct H as [_ H]; apply H with k; apply InA_cons_tl; assumption. }
  - destruct H as [H _]; specialize (H a') as [_ H].
    destruct H as [e'' H]; [eexists; constructor; reflexivity|].
    apply InA_cons in H; destruct H as [H|H].
    * apply (gt_not_eq Hgt); symmetry; apply H.
    * apply InA_eqke_eqk, (Sort_Inf_In Hm Hr) in H.
      compute in H; order.
Qed.

Lemma equal_2 : forall m (Hm:Sort m) m' (Hm:Sort m') cmp,
  equal cmp m m' = true -> Equivb cmp m m'.
Proof with auto with ordered_type.
intros m Hm m' Hm' cmp; revert m' Hm'.
induction Hm as [|[a e] m Hm IHHm Hr]; simpl in *; intros [|[a' e'] m'] Hm' H; try congruence.
+ split; [tauto|inversion 1].
+ destruct X.compare as [?|Heq|?]; try congruence.
  apply Sorted_inv in Hm'; destruct Hm' as [Hm' Hr'].
  apply andb_true_iff in H; destruct H as [Hc He]; split.
  - intros k; split; intros [v Hk]; apply InA_cons in Hk; destruct Hk as [Hk|Hk].
    * exists e'; apply InA_cons_hd; split; [|reflexivity].
      transitivity a; [apply Hk|apply Heq].
    * assert (Hi : In k m').
      { apply (IHHm m' Hm' He); exists v; apply Hk. }
      destruct Hi as [w Hw]; exists w; apply InA_cons_tl, Hw.
    * exists e; apply InA_cons_hd; split; [|reflexivity].
      transitivity a'; [apply Hk|symmetry; apply Heq].
    * assert (Hi : In k m).
      { apply (IHHm m' Hm' He); exists v; apply Hk. }
      destruct Hi as [w Hw]; exists w; apply InA_cons_tl, Hw.
  - intros k e1 e2 He1 He2.
    apply InA_cons in He1, He2.
    destruct He1 as [He1|He1]; destruct He2 as [He2|He2].
    * replace e1 with e by (symmetry; apply He1).
      replace e2 with e' by (symmetry; apply He2).
      apply Hc.
    * assert (Hi : In k m).
      { apply (IHHm m' Hm' He); exists e2; apply He2. }
      destruct Hi as [w Hw].
      apply InA_eqke_eqk, (Sort_Inf_In Hm Hr) in Hw.
      destruct He1 as [He1 _].
      elim (eq_not_gt He1); apply Hw.
    * assert (Hi : In k m').
      { apply (IHHm m' Hm' He); exists e1; apply He1. }
      destruct Hi as [w Hw].
      apply InA_eqke_eqk, (Sort_Inf_In Hm' Hr') in Hw.
      destruct He2 as [He2 _].
      elim (eq_not_gt He2); apply Hw.
    * destruct (IHHm m' Hm' He) as [_ IH].
      apply (IH k e1 e2 He1 He2).
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
 - apply equal_2; auto.
   simpl.
   elim_comp.
   rewrite H2; simpl.
   apply equal_1; auto.
 - apply equal_2; auto.
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
 induction m.
 - inversion 1.

 - destruct a as (x',e').
   simpl.
   inversion_clear 1.
   + constructor 1.
     unfold eqke in *; simpl in *; intuition congruence.
   + unfold MapsTo in *; auto.
Qed.

Lemma map_2 : forall (m:t elt)(x:key)(f:elt->elt'),
  In x (map f m) -> In x m.
Proof.
 intros m x f.
 induction m; simpl.
 - intros (e,abs).
   inversion abs.

 - destruct a as (x',e).
   intros hyp.
   inversion hyp. clear hyp.
   inversion H; subst; rename x0 into e'.
   + exists e; constructor.
     unfold eqke in *; simpl in *; intuition.
   + destruct IHm as (e'',hyp).
     * exists e'; auto.
     * exists e''.
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

#[local]
Hint Resolve map_lelistA : core.

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
 induction m.
 - inversion 1.

 - destruct a as (x',e').
   simpl.
   inversion_clear 1.
   + exists x'.
     destruct H0; simpl in *.
     split.
     * auto with ordered_type.
     * constructor 1.
       unfold eqke in *; simpl in *; intuition congruence.
   + destruct IHm as (y, hyp); auto.
     exists y; intuition auto with ordered_type.
Qed.


Lemma mapi_2 : forall (m:t elt)(x:key)(f:key->elt->elt'),
  In x (mapi f m) -> In x m.
Proof.
 intros m x f.
 induction m; simpl.
 - intros (e,abs).
   inversion abs.

 - destruct a as (x',e).
   intros hyp.
   inversion hyp. clear hyp.
   inversion H; subst; rename x0 into e'.
   + exists e; constructor.
     unfold eqke in *; simpl in *; intuition.
   + destruct IHm as (e'',hyp).
     * exists e'; auto.
     * exists e''.
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

#[local]
Hint Resolve mapi_lelistA : core.

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
 - simpl; auto; intros.
   (* map2_r *)
   induction m'; try destruct a; simpl; auto.
   rewrite IHm'; auto.
   (* fin map2_r *)
 - induction m'; destruct a.
   + simpl; f_equal.
     (* map2_l *)
     clear IHm.
     induction m; try destruct a; simpl; auto.
     rewrite IHm; auto.
   (* fin map2_l *)
   + destruct a0.
     simpl.
     destruct (X.compare t0 t1); simpl; f_equal.
     * apply IHm.
     * apply IHm.
     * apply IHm'.
Qed.

Lemma combine_lelistA :
  forall m m' (x:key)(e:elt)(e':elt')(e'':oee'),
  lelistA (@ltk elt) (x,e) m ->
  lelistA (@ltk elt') (x,e') m' ->
  lelistA (@ltk oee') (x,e'') (combine m m').
Proof.
 induction m.
 - intros.
   simpl.
   exact (map_lelistA _ _ H0).
 - induction m'.
   + intros.
     destruct a.
     replace (combine ((t0, e0) :: m) nil) with
       (map (fun e => (Some e,None (A:=elt'))) ((t0,e0)::m)); auto.
     exact (map_lelistA _ _ H).
   + intros.
     simpl.
     destruct a as (k,e0); destruct a0 as (k',e0').
     destruct (X.compare k k').
     * inversion_clear H; auto.
     * inversion_clear H; auto.
     * inversion_clear H0; auto.
Qed.
#[local]
Hint Resolve combine_lelistA : core.

Lemma combine_sorted :
  forall m (Hm : sort (@ltk elt) m) m' (Hm' : sort (@ltk elt') m'),
  sort (@ltk oee') (combine m m').
Proof.
 induction m.
 - intros; clear Hm.
   simpl.
   apply map_sorted; auto.
 - induction m'.
   + intros; clear Hm'.
     destruct a.
     replace (combine ((t0, e) :: m) nil) with
       (map (fun e => (Some e,None (A:=elt'))) ((t0,e)::m)); auto.
     apply map_sorted; auto.
   + intros.
     simpl.
     destruct a as (k,e); destruct a0 as (k',e').
     destruct (X.compare k k') as [Hlt|Heq|Hlt].
     * inversion_clear Hm.
       constructor; auto.
       assert (lelistA (ltk (elt:=elt')) (k, e') ((k',e')::m')) by auto.
       exact (combine_lelistA _ H0 H1).
     * inversion_clear Hm; inversion_clear Hm'.
       constructor; auto.
       assert (lelistA (ltk (elt:=elt')) (k, e') m') by (apply Inf_eq with (k',e'); auto).
       exact (combine_lelistA _ H0 H3).
     * inversion_clear Hm; inversion_clear Hm'.
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
 - simpl; auto.
 - inversion_clear H1.
   destruct a; destruct o; auto.
   simpl.
   constructor; auto.
   clear IHl1.
   induction l1.
   + simpl; auto.
   + destruct a; destruct o; simpl; auto.
     * inversion_clear H0; auto.
     * inversion_clear H0.
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
 - intros.
   simpl.
   induction m'.
   + intros; simpl; auto.
   + simpl; destruct a.
     simpl; destruct (X.compare x t0); simpl; auto.
     inversion_clear Hm'; auto.
 - induction m'.
   + (* m' = nil *)
     intros; destruct a; simpl.
     destruct (X.compare x t0) as [Hlt| |Hlt]; simpl; auto.
     inversion_clear Hm; clear H0 Hlt Hm' IHm t0.
     induction m; simpl; auto.
     inversion_clear H.
     destruct a.
     simpl; destruct (X.compare x t0); simpl; auto.
   + (* m' <> nil *)
     intros.
     destruct a as (k,e); destruct a0 as (k',e'); simpl.
     inversion Hm; inversion Hm'; subst.
     destruct (X.compare k k'); simpl;
       destruct (X.compare x k);
       elim_comp || destruct (X.compare x k'); simpl; auto.
     * rewrite IHm; auto; simpl; elim_comp; auto.
     * rewrite IHm; auto; simpl; elim_comp; auto.
     * rewrite IHm; auto; simpl; elim_comp; auto.
     * change (find x (combine ((k, e) :: m) m') = at_least_one None (find x m')).
       rewrite IHm'; auto.
       simpl find; elim_comp; auto.
     * change (find x (combine ((k, e) :: m) m') = Some (Some e, find x m')).
       rewrite IHm'; auto.
       simpl find; elim_comp; auto.
     * change (find x (combine ((k, e) :: m) m') =
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
 - destruct o; destruct o'; simpl in *; try discriminate; auto.
 - destruct a as (k,(oo,oo')); simpl in *.
   inversion_clear H2.
   destruct (X.compare x k) as [Hlt|Heq|Hlt]; simpl in *.
   + (* x < k *)
     destruct (f' (oo,oo')); simpl.
     * elim_comp.
       destruct o; destruct o'; simpl in *; try discriminate; auto.
     * destruct (IHm0 H0) as (H2,_); apply H2; auto.
       rewrite <- H.
       case_eq (find x m0); intros; auto.
       assert (ltk (elt:=oee') (x,(oo,oo')) (k,(oo,oo'))).
       -- red; auto.
       -- destruct (Sort_Inf_NotIn H0 (Inf_lt H4 H1)).
          exists p; apply find_2; auto.
   + (* x = k *)
     assert (at_least_one_then_f o o' = f oo oo').
     * destruct o; destruct o'; simpl in *; inversion_clear H; auto.
     * rewrite H2.
       unfold f'; simpl.
       destruct (f oo oo'); simpl.
       -- elim_comp; auto.
       -- destruct (IHm0 H0) as (_,H4); apply H4; auto.
          case_eq (find x m0); intros; auto.
          assert (eqk (elt:=oee') (k,(oo,oo')) (x,(oo,oo'))).
          ++ red; auto with ordered_type.
          ++ destruct (Sort_Inf_NotIn H0 (Inf_eq (eqk_sym H5) H1)).
             exists p; apply find_2; auto.
   + (* k < x *)
     unfold f'; simpl.
     destruct (f oo oo'); simpl.
     * elim_comp; auto.
       destruct (IHm0 H0) as (H3,_); apply H3; auto.
     * destruct (IHm0 H0) as (H3,_); apply H3; auto.

 - (* None -> None *)
   destruct a as (k,(oo,oo')).
   simpl.
   inversion_clear H2.
   destruct (X.compare x k) as [Hlt|Heq|Hlt].
   + (* x < k *)
     unfold f'; simpl.
     destruct (f oo oo'); simpl.
     * elim_comp; auto.
     * destruct (IHm0 H0) as (_,H4); apply H4; auto.
       case_eq (find x m0); intros; auto.
       assert (ltk (elt:=oee') (x,(oo,oo')) (k,(oo,oo'))).
       -- red; auto.
       -- destruct (Sort_Inf_NotIn H0 (Inf_lt H3 H1)).
          exists p; apply find_2; auto.
   + (* x = k *)
     discriminate.
   + (* k < x *)
     unfold f'; simpl.
     destruct (f oo oo'); simpl.
     * elim_comp; auto.
       destruct (IHm0 H0) as (_,H4); apply H4; auto.
     * destruct (IHm0 H0) as (_,H4); apply H4; auto.
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
 - rewrite (find_1 Hm H).
   destruct (find x m'); simpl; auto.
 - rewrite (find_1 Hm' H).
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
 - left; exists e0; auto.
 - left; exists e0; auto.
 - right; exists e0; auto.
 - discriminate.
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
 Definition is_empty m : bool := Raw.is_empty (this m).
 Definition add x e m : t elt := Build_slist (Raw.add_sorted (sorted m) x e).
 Definition find x m : option elt := Raw.find x (this m).
 Definition remove x m : t elt := Build_slist (Raw.remove_sorted (sorted m) x).
 Definition mem x m : bool := Raw.mem x (this m).
 Definition map f m : t elt' := Build_slist (Raw.map_sorted (sorted m) f).
 Definition mapi (f:key->elt->elt') m : t elt' := Build_slist (Raw.mapi_sorted (sorted m) f).
 Definition map2 f m (m':t elt') : t elt'' :=
   Build_slist (Raw.map2_sorted f (sorted m) (sorted m')).
 Definition elements m : list (key*elt) := @Raw.elements elt (this m).
 Definition cardinal m := length (this m).
 Definition fold (A:Type)(f:key->elt->A->A) m (i:A) : A := @Raw.fold elt A f (this m) i.
 Definition equal cmp m m' : bool := @Raw.equal elt cmp (this m) (this m').

 Definition MapsTo x e m : Prop := Raw.PX.MapsTo x e (this m).
 Definition In x m : Prop := Raw.PX.In x (this m).
 Definition Empty m : Prop := Raw.Empty (this m).

 Definition Equal m m' := forall y, find y m = find y m'.
 Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
         (forall k, In k m <-> In k m') /\
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
 Definition Equivb cmp m m' : Prop := @Raw.Equivb elt cmp (this m) (this m').

 Definition eq_key : (key*elt) -> (key*elt) -> Prop := @Raw.PX.eqk elt.
 Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop:= @Raw.PX.eqke elt.
 Definition lt_key : (key*elt) -> (key*elt) -> Prop := @Raw.PX.ltk elt.

 Lemma MapsTo_1 : forall m x y e, E.eq x y -> MapsTo x e m -> MapsTo y e m.
 Proof. intros m; exact (@Raw.PX.MapsTo_eq elt (this m)). Qed.

 Lemma mem_1 : forall m x, In x m -> mem x m = true.
 Proof. intros m; exact (@Raw.mem_1 elt (this m) (sorted m)). Qed.
 Lemma mem_2 : forall m x, mem x m = true -> In x m.
 Proof. intros m; exact (@Raw.mem_2 elt (this m) (sorted m)). Qed.

 Lemma empty_1 : Empty empty.
 Proof. exact (@Raw.empty_1 elt). Qed.

 Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
 Proof. intros m; exact (@Raw.is_empty_1 elt (this m)). Qed.
 Lemma is_empty_2 :  forall m, is_empty m = true -> Empty m.
 Proof. intros m; exact (@Raw.is_empty_2 elt (this m)). Qed.

 Lemma add_1 : forall m x y e, E.eq x y -> MapsTo y e (add x e m).
 Proof. intros m; exact (@Raw.add_1 elt (this m)). Qed.
 Lemma add_2 : forall m x y e e', ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
 Proof. intros m; exact (@Raw.add_2 elt (this m)). Qed.
 Lemma add_3 : forall m x y e e', ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
 Proof. intros m; exact (@Raw.add_3 elt (this m)). Qed.

 Lemma remove_1 : forall m x y, E.eq x y -> ~ In y (remove x m).
 Proof. intros m; exact (@Raw.remove_1 elt (this m) (sorted m)). Qed.
 Lemma remove_2 : forall m x y e, ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
 Proof. intros m; exact (@Raw.remove_2 elt (this m) (sorted m)). Qed.
 Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.
 Proof. intros m; exact (@Raw.remove_3 elt (this m) (sorted m)). Qed.

 Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e.
 Proof. intros m; exact (@Raw.find_1 elt (this m) (sorted m)). Qed.
 Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
 Proof. intros m; exact (@Raw.find_2 elt (this m)). Qed.

 Lemma elements_1 : forall m x e, MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
 Proof. intros m; exact (@Raw.elements_1 elt (this m)). Qed.
 Lemma elements_2 : forall m x e, InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
 Proof. intros m; exact (@Raw.elements_2 elt (this m)). Qed.
 Lemma elements_3 : forall m, sort lt_key (elements m).
 Proof. intros m; exact (@Raw.elements_3 elt (this m) (sorted m)). Qed.
 Lemma elements_3w : forall m, NoDupA eq_key (elements m).
 Proof. intros m; exact (@Raw.elements_3w elt (this m) (sorted m)). Qed.

 Lemma cardinal_1 : forall m, cardinal m = length (elements m).
 Proof. intros; reflexivity. Qed.

 Lemma fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
 Proof. intros m; exact (@Raw.fold_1 elt (this m)). Qed.

 Lemma equal_1 : forall m m' cmp, Equivb cmp m m' -> equal cmp m m' = true.
 Proof. intros m m'; exact (@Raw.equal_1 elt (this m) (sorted m) (this m') (sorted m')). Qed.
 Lemma equal_2 : forall m m' cmp, equal cmp m m' = true -> Equivb cmp m m'.
 Proof. intros m m'; exact (@Raw.equal_2 elt (this m) (sorted m) (this m') (sorted m')). Qed.

 End Elt.

 Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
 Proof. intros elt elt' m; exact (@Raw.map_1 elt elt' (this m)). Qed.
 Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
        In x (map f m) -> In x m.
 Proof. intros elt elt' m; exact (@Raw.map_2 elt elt' (this m)). Qed.

 Lemma mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m ->
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
 Proof. intros elt elt' m; exact (@Raw.mapi_1 elt elt' (this m)). Qed.
 Lemma mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.
 Proof. intros elt elt' m; exact (@Raw.mapi_2 elt elt' (this m)). Qed.

 Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
        (x:key)(f:option elt->option elt'->option elt''),
        In x m \/ In x m' ->
        find x (map2 f m m') = f (find x m) (find x m').
 Proof.
 intros elt elt' elt'' m m' x f;
 exact (@Raw.map2_1 elt elt' elt'' f (this m) (sorted m) (this m') (sorted m') x).
 Qed.
 Lemma map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
        (x:key)(f:option elt->option elt'->option elt''),
        In x (map2 f m m') -> In x m \/ In x m'.
 Proof.
 intros elt elt' elt'' m m' x f;
 exact (@Raw.map2_2 elt elt' elt'' f (this m) (sorted m) (this m') (sorted m') x).
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

Definition eq m m' := eq_list (this m) (this m').

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

Definition lt m m' := lt_list (this m) (this m').

Lemma eq_equal : forall m m', eq m m' <-> equal cmp m m' = true.
Proof.
  intros (l,Hl); induction l.
  - intros (l',Hl'); unfold eq; simpl.
    destruct l'; unfold equal; simpl; intuition auto with bool.
  - intros (l',Hl'); unfold eq.
    destruct l'.
    + destruct a; unfold equal; simpl; intuition auto with bool.
    + destruct a as (x,e).
      destruct p as (x',e').
      unfold equal; simpl.
      destruct (X.compare x x') as [Hlt|Heq|Hlt]; simpl; intuition auto with bool.
      * unfold cmp at 1.
        MD.elim_comp; clear H; simpl.
        inversion_clear Hl.
        inversion_clear Hl'.
        destruct (IHl H (Build_slist H3)).
        unfold equal, eq in H5; simpl in H5; auto.
      * destruct (andb_prop _ _ H); clear H.
        generalize H0; unfold cmp.
        MD.elim_comp; auto; intro; discriminate.
      * destruct (andb_prop _ _ H); clear H.
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
 - apply (MapS.Raw.MX.lt_antirefl Hlt); auto.
 - split.
   + apply D.eq_refl.
   + inversion_clear Hm.
     apply (IHm H).
 - apply (MapS.Raw.MX.lt_antirefl Hlt); auto.
Qed.

Lemma eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
Proof.
 intros (m,Hm); induction m;
 intros (m', Hm'); destruct m'; unfold eq; simpl;
 try destruct a as (x,e); try destruct p as (x',e'); auto.
 destruct (X.compare x x')  as [Hlt|Heq|Hlt]; MapS.Raw.MX.elim_comp; intuition auto with ordered_type.
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
 - apply D.eq_trans with e'; auto.
 - inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
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
 - left; apply D.lt_trans with e'; auto.
 - left; apply lt_eq with e'; auto.
 - left; apply eq_lt with e'; auto.
 - right.
   split.
   + apply D.eq_trans with e'; auto.
   + inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
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
 - exact (D.lt_not_eq H0 H1).
 - inversion_clear Hm1; inversion_clear Hm2.
   apply (IHm1 H0 (Build_slist H5)); intuition.
Qed.

Ltac cmp_solve := unfold eq, lt; simpl; try Raw.MX.elim_comp; auto with ordered_type.

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
 - inversion_clear Hm1; auto.
 - assert (Hm22 : sort (Raw.PX.ltk (elt:=D.t)) m2).
   { inversion_clear Hm2; auto. }
   destruct (IHm1 Hm11 (Build_slist Hm22));
     [ apply LT | apply EQ | apply GT ]; cmp_solve.
Qed.

End Make_ord.

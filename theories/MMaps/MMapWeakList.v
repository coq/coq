(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Finite map library *)

(** This file proposes an implementation of the non-dependant interface
 [MMapInterface.WS] using lists of pairs, unordered but without redundancy. *)

Require Import MMapInterface EqualitiesFacts.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma Some_iff {A} (a a' : A) : Some a = Some a' <-> a = a'.
Proof. split; congruence. Qed.

Module Raw (X:DecidableType).

Module Import PX := KeyDecidableType X.

Definition key := X.t.
Definition t (elt:Type) := list (X.t * elt).

Ltac dec := match goal with
 | |- context [ X.eq_dec ?x ?x ] =>
   let E := fresh "E" in destruct (X.eq_dec x x) as [E|E]; [ | now elim E]
 | H : X.eq ?x ?y |- context [ X.eq_dec ?x ?y ] =>
   let E := fresh "E" in destruct (X.eq_dec x y) as [_|E]; [ | now elim E]
 | H : ~X.eq ?x ?y |- context [ X.eq_dec ?x ?y ] =>
   let E := fresh "E" in destruct (X.eq_dec x y) as [E|_]; [ now elim H | ]
 | |- context [ X.eq_dec ?x ?y ] =>
   let E := fresh "E" in destruct (X.eq_dec x y) as [E|E]
end.

Section Elt.

Variable elt : Type.
Notation NoDupA := (@NoDupA _ eqk).

(** * [find] *)

Fixpoint find (k:key) (s: t elt) : option elt :=
  match s with
   | nil => None
   | (k',x)::s' => if X.eq_dec k k' then Some x else find k s'
  end.

Lemma find_spec : forall m (Hm:NoDupA m) x e,
  find x m = Some e <-> MapsTo x e m.
Proof.
 unfold PX.MapsTo.
 induction m as [ | (k,e) m IH]; simpl.
 - split; inversion 1.
 - intros Hm k' e'. rewrite InA_cons.
   change (eqke (k',e') (k,e)) with (X.eq k' k /\ e' = e).
   inversion_clear Hm. dec.
   + rewrite Some_iff; intuition.
     elim H. apply InA_eqk with (k',e'); auto.
   + rewrite IH; intuition.
Qed.

(** * [mem] *)

Fixpoint mem (k : key) (s : t elt) : bool :=
  match s with
   | nil => false
   | (k',_) :: l => if X.eq_dec k k' then true else mem k l
  end.

Lemma mem_spec : forall m (Hm:NoDupA m) x, mem x m = true <-> In x m.
Proof.
 induction m as [ | (k,e) m IH]; simpl; intros Hm x.
 - split. discriminate. inversion_clear 1. inversion H0.
 - inversion_clear Hm. rewrite PX.In_cons; simpl.
   rewrite <- IH by trivial.
   dec; intuition.
Qed.

(** * [empty] *)

Definition empty : t elt := nil.

Lemma empty_spec x : find x empty = None.
Proof.
 reflexivity.
Qed.

Lemma empty_NoDup : NoDupA empty.
Proof.
 unfold empty; auto.
Qed.

(** * [is_empty] *)

Definition is_empty (l : t elt) : bool := if l then true else false.

Lemma is_empty_spec m : is_empty m = true <-> forall x, find x m = None.
Proof.
 destruct m; simpl; intuition; try discriminate.
 specialize (H a).
 revert H. now dec.
Qed.

(* Not part of the exported specifications, used later for [merge]. *)

Lemma find_eq : forall m (Hm:NoDupA m) x x',
   X.eq x x' -> find x m = find x' m.
Proof.
 induction m; simpl; auto; destruct a; intros.
 inversion_clear Hm.
 rewrite (IHm H1 x x'); auto.
 dec; dec; trivial.
 elim E0. now transitivity x.
 elim E. now transitivity x'.
Qed.

(** * [add] *)

Fixpoint add (k : key) (x : elt) (s : t elt) : t elt :=
  match s with
   | nil => (k,x) :: nil
   | (k',y) :: l => if X.eq_dec k k' then (k,x)::l else (k',y)::add k x l
  end.

Lemma add_spec1 m x e : find x (add x e m) = Some e.
Proof.
 induction m as [ | (k,e') m IH]; simpl.
 - now dec.
 - dec; simpl; now dec.
Qed.

Lemma add_spec2 m x y e : ~X.eq x y -> find y (add x e m) = find y m.
Proof.
 intros N.
 assert (N' : ~X.eq y x) by now contradict N.
 induction m as [ | (k,e') m IH]; simpl.
 - dec; trivial.
 - repeat (dec; simpl); trivial. elim N. now transitivity k.
Qed.

Lemma add_InA : forall m x y e e',
  ~ X.eq x y -> InA eqk (y,e) (add x e' m) -> InA eqk (y,e) m.
Proof.
 induction m as [ | (k,e') m IH]; simpl; intros.
 - inversion_clear H0. elim H. symmetry; apply H1. inversion_clear H1.
 - revert H0; dec; rewrite !InA_cons.
   + rewrite E. intuition.
   + intuition. right; eapply IH; eauto.
Qed.

Lemma add_NoDup : forall m (Hm:NoDupA m) x e, NoDupA (add x e m).
Proof.
 induction m as [ | (k,e') m IH]; simpl; intros Hm x e.
 - constructor; auto. now inversion 1.
 - inversion_clear Hm. dec; constructor; auto.
   + contradict H. apply InA_eqk with (x,e); auto.
   + contradict H; apply add_InA with x e; auto.
Qed.

(** * [remove] *)

Fixpoint remove (k : key) (s : t elt) : t elt :=
  match s with
   | nil => nil
   | (k',x) :: l => if X.eq_dec k k' then l else (k',x) :: remove k l
  end.

Lemma remove_spec1 m (Hm: NoDupA m) x : find x (remove x m) = None.
Proof.
 induction m as [ | (k,e') m IH]; simpl; trivial.
 inversion_clear Hm.
 repeat (dec; simpl); auto.
 destruct (find x m) eqn:F; trivial.
 apply find_spec in F; trivial.
 elim H. apply InA_eqk with (x,e); auto.
Qed.

Lemma remove_spec2 m (Hm: NoDupA m) x y : ~X.eq x y ->
  find y (remove x m) = find y m.
Proof.
 induction m as [ | (k,e') m IH]; simpl; trivial; intros E.
 inversion_clear Hm.
 repeat (dec; simpl); auto.
 elim E. now transitivity k.
Qed.

Lemma remove_InA : forall m (Hm:NoDupA m) x y e,
  InA eqk (y,e) (remove x m) -> InA eqk (y,e) m.
Proof.
 induction m as [ | (k,e') m IH]; simpl; trivial; intros.
 inversion_clear Hm.
 revert H; dec; rewrite !InA_cons; intuition.
 right; eapply H; eauto.
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
 contradict H; apply remove_InA with x; auto.
Qed.

(** * [bindings] *)

Definition bindings (m: t elt) := m.

Lemma bindings_spec1 m x e : InA eqke (x,e) (bindings m) <-> MapsTo x e m.
Proof.
 reflexivity.
Qed.

Lemma bindings_spec2w m (Hm:NoDupA m) : NoDupA (bindings m).
Proof.
 trivial.
Qed.

(** * [fold] *)

Fixpoint fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc : A) :  A :=
  match m with
   | nil => acc
   | (k,e)::m' => fold f m' (f k e acc)
  end.

Lemma fold_spec : forall m (A:Type)(i:A)(f:key->elt->A->A),
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
Proof.
 induction m as [ | (k,e) m IH]; simpl; auto.
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

Definition Submap (cmp:elt->elt->bool) m m' :=
  (forall k, In k m -> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Definition Equivb (cmp:elt->elt->bool) m m' :=
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
 { apply H; exists e; auto with *. }
 destruct H3 as (e', H3).
 assert (H4 : find t0 m' = Some e') by now apply find_spec.
 unfold check at 2. rewrite H4.
 rewrite (H0 t0); simpl; auto with *.
 eapply IHm; auto.
 split; intuition.
 apply H.
 destruct H6 as (e'',H6); exists e''; auto.
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
 apply PX.MapsTo_eq with t0; auto with *.
 apply find_spec; auto.
 apply H3.
 exists e0; auto.
 inversion_clear H6.
 compute in H8; destruct H8; subst.
 assert (H8 : MapsTo t0 e'0 m'). { eapply PX.MapsTo_eq; eauto. }
 apply find_spec in H8; trivial. congruence.
 apply H4 with k; auto.
Qed.

(** Specification of [equal] *)

Lemma equal_spec : forall m (Hm:NoDupA m) m' (Hm': NoDupA m') cmp,
  equal cmp m m' = true <-> Equivb cmp m m'.
Proof.
 unfold Equivb, equal.
 split.
 - intros.
   destruct (andb_prop _ _ H); clear H.
   generalize (submap_2 Hm Hm' H0).
   generalize (submap_2 Hm' Hm H1).
   firstorder.
 - intuition.
   apply andb_true_intro; split; apply submap_1; unfold Submap; firstorder.
Qed.
End Elt.
Section Elt2.
Variable elt elt' : Type.

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

(** Specification of [map] *)

Lemma map_spec (f:elt->elt')(m:t elt)(x:key) :
  find x (map f m) = option_map f (find x m).
Proof.
 induction m as [ | (k,e) m IH]; simpl; trivial.
 dec; simpl; trivial.
Qed.

Lemma map_NoDup m (Hm : NoDupA (@eqk elt) m)(f:elt->elt') :
  NoDupA (@eqk elt') (map f m).
Proof.
 induction m; simpl; auto.
 intros.
 destruct a as (x',e').
 inversion_clear Hm.
 constructor; auto.
 contradict H.
 clear IHm H0.
 induction m; simpl in *; auto.
 inversion H.
 destruct a; inversion H; auto.
Qed.

(** Specification of [mapi] *)

Lemma mapi_spec (f:key->elt->elt')(m:t elt)(x:key) :
  exists y, X.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).
Proof.
 induction m as [ | (k,e) m IH]; simpl; trivial.
 - now exists x.
 - dec; simpl.
   + now exists k.
   + destruct IH as (y,(Hy,H)). now exists y.
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

Lemma mapfst_InA {elt}(m:t elt) x :
 InA X.eq x (List.map fst m) <-> In x m.
Proof.
 induction m as [| (k,e) m IH]; simpl; auto.
 - split; inversion 1. inversion H0.
 - rewrite InA_cons, In_cons. simpl. now rewrite IH.
Qed.

Lemma mapfst_NoDup {elt}(m:t elt) :
 NoDupA X.eq (List.map fst m) <-> NoDupA eqk m.
Proof.
 induction m as [| (k,e) m IH]; simpl.
 - split; constructor.
 - split; inversion_clear 1; constructor; try apply IH; trivial.
   + contradict H0. rewrite mapfst_InA. eapply In_alt'; eauto.
   + rewrite mapfst_InA. contradict H0. now apply In_alt'.
Qed.

Lemma filter_NoDup f (m:list key) :
 NoDupA X.eq m -> NoDupA X.eq (List.filter f m).
Proof.
 induction 1; simpl.
 - constructor.
 - destruct (f x); trivial. constructor; trivial.
   contradict H. rewrite InA_alt in *. destruct H as (y,(Hy,H)).
   exists y; split; trivial. now rewrite filter_In in H.
Qed.

Lemma NoDupA_unique_repr (l:list key) x y :
 NoDupA X.eq l -> X.eq x y -> List.In x l -> List.In y l -> x = y.
Proof.
 intros H E Hx Hy.
 induction H; simpl in *.
 - inversion Hx.
 - intuition; subst; trivial.
   elim H. apply InA_alt. now exists y.
   elim H. apply InA_alt. now exists x.
Qed.

Section Elt3.

Variable elt elt' elt'' : Type.

Definition restrict (m:t elt)(k:key) :=
 match find k m with
 | None => true
 | Some _ => false
 end.

Definition domains (m:t elt)(m':t elt') :=
 List.map fst m ++ List.filter (restrict m) (List.map fst m').

Lemma domains_InA m m' (Hm : NoDupA eqk m) x :
 InA X.eq x (domains m m') <-> In x m \/ In x m'.
Proof.
 unfold domains.
 assert (Proper (X.eq==>eq) (restrict m)).
 { intros k k' Hk. unfold restrict. now rewrite (find_eq Hm Hk). }
 rewrite InA_app_iff, filter_InA, !mapfst_InA; intuition.
 unfold restrict.
 destruct (find x m) eqn:F.
 - left. apply find_spec in F; trivial. now exists e.
 - now right.
Qed.

Lemma domains_NoDup m m' : NoDupA eqk m -> NoDupA eqk m' ->
 NoDupA X.eq (domains m m').
Proof.
 intros Hm Hm'. unfold domains.
 apply NoDupA_app; auto with *.
 - now apply mapfst_NoDup.
 - now apply filter_NoDup, mapfst_NoDup.
 - intros x.
   rewrite mapfst_InA. intros (e,H).
   apply find_spec in H; trivial.
   rewrite InA_alt. intros (y,(Hy,H')).
   rewrite (find_eq Hm Hy) in H.
   rewrite filter_In in H'. destruct H' as (_,H').
   unfold restrict in H'. now rewrite H in H'.
Qed.

Fixpoint fold_keys (f:key->option elt'') l :=
  match l with
    | nil => nil
    | k::l =>
      match f k with
        | Some e => (k,e)::fold_keys f l
        | None => fold_keys f l
      end
  end.

Lemma fold_keys_In f l x e :
  List.In (x,e) (fold_keys f l) <-> List.In x l /\ f x = Some e.
Proof.
 induction l as [|k l IH]; simpl.
 - intuition.
 - destruct (f k) eqn:F; simpl; rewrite IH; clear IH; intuition;
   try left; congruence.
Qed.

Lemma fold_keys_NoDup f l :
  NoDupA X.eq l -> NoDupA eqk (fold_keys f l).
Proof.
 induction 1; simpl.
 - constructor.
 - destruct (f x); trivial.
   constructor; trivial. contradict H.
   apply InA_alt in H. destruct H as ((k,e'),(E,H)).
   rewrite fold_keys_In in H.
   apply InA_alt. exists k. now split.
Qed.

Variable f : key -> option elt -> option elt' -> option elt''.

Definition merge m m' : t elt'' :=
 fold_keys (fun k => f k (find k m) (find k m')) (domains m m').

Lemma merge_NoDup m (Hm:NoDupA (@eqk elt) m) m' (Hm':NoDupA (@eqk elt') m') :
  NoDupA (@eqk elt'') (merge m m').
Proof.
 now apply fold_keys_NoDup, domains_NoDup.
Qed.

Lemma merge_spec1 m (Hm:NoDupA eqk m) m' (Hm':NoDupA eqk m') x :
  In x m \/ In x m' ->
  exists y:key, X.eq y x /\
                find x (merge m m') = f y (find x m) (find x m').
Proof.
 assert (Hmm' : NoDupA eqk (merge m m')) by now apply merge_NoDup.
 rewrite <- domains_InA; trivial.
 rewrite InA_alt. intros (y,(Hy,H)).
 exists y; split; [easy|].
 rewrite (find_eq Hm Hy), (find_eq Hm' Hy).
 destruct (f y (find y m) (find y m')) eqn:F.
 - apply find_spec; trivial.
   red. apply InA_alt. exists (y,e). split. now split.
   unfold merge. apply fold_keys_In. now split.
 - destruct (find x (merge m m')) eqn:F'; trivial.
   rewrite <- F; clear F. symmetry.
   apply find_spec in F'; trivial.
   red in F'. rewrite InA_alt in F'.
   destruct F' as ((y',e'),(E,F')).
   unfold merge in F'; rewrite fold_keys_In in F'.
   destruct F' as (H',F').
   compute in E; destruct E as (Hy',<-).
   replace y with y'; trivial.
   apply (@NoDupA_unique_repr (domains m m')); auto.
   now apply domains_NoDup.
   now transitivity x.
Qed.

Lemma merge_spec2 m (Hm:NoDupA eqk m) m' (Hm':NoDupA eqk m') x :
  In x (merge m m') -> In x m \/ In x m'.
Proof.
 rewrite <- domains_InA; trivial.
 intros (e,H). red in H. rewrite InA_alt in H. destruct H as ((k,e'),(E,H)).
 unfold merge in H; rewrite fold_keys_In in H. destruct H as (H,_).
 apply InA_alt. exists k. split; trivial. now destruct E.
Qed.

End Elt3.
End Raw.


Module Make (X: DecidableType) <: WS with Module E:=X.
 Module Raw := Raw X.

 Module E := X.
 Definition key := E.t.
 Definition eq_key {elt} := @Raw.PX.eqk elt.
 Definition eq_key_elt {elt} := @Raw.PX.eqke elt.

 Record t_ (elt:Type) := Mk
  {this :> Raw.t elt;
   nodup : NoDupA Raw.PX.eqk this}.
 Definition t := t_.

 Definition empty {elt} : t elt := Mk (Raw.empty_NoDup elt).

Section Elt.
 Variable elt elt' elt'':Type.
 Implicit Types m : t elt.
 Implicit Types x y : key.
 Implicit Types e : elt.

 Definition find x m : option elt := Raw.find x m.(this).
 Definition mem x m : bool := Raw.mem x m.(this).
 Definition is_empty m : bool := Raw.is_empty m.(this).
 Definition add x e m : t elt := Mk (Raw.add_NoDup m.(nodup) x e).
 Definition remove x m : t elt := Mk (Raw.remove_NoDup m.(nodup) x).
 Definition map f m : t elt' := Mk (Raw.map_NoDup m.(nodup) f).
 Definition mapi (f:key->elt->elt') m : t elt' :=
   Mk (Raw.mapi_NoDup m.(nodup) f).
 Definition merge f m (m':t elt') : t elt'' :=
   Mk (Raw.merge_NoDup f m.(nodup) m'.(nodup)).
 Definition bindings m : list (key*elt) := Raw.bindings m.(this).
 Definition cardinal m := length m.(this).
 Definition fold {A}(f:key->elt->A->A) m (i:A) : A := Raw.fold f m.(this) i.
 Definition equal cmp m m' : bool := Raw.equal cmp m.(this) m'.(this).
 Definition MapsTo x e m : Prop := Raw.PX.MapsTo x e m.(this).
 Definition In x m : Prop := Raw.PX.In x m.(this).

 Definition Equal m m' := forall y, find y m = find y m'.
 Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
         (forall k, In k m <-> In k m') /\
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
 Definition Equivb cmp m m' : Prop := Raw.Equivb cmp m.(this) m'.(this).

 Instance MapsTo_compat :
   Proper (E.eq==>Logic.eq==>Logic.eq==>iff) MapsTo.
 Proof.
   intros x x' Hx e e' <- m m' <-. unfold MapsTo. now rewrite Hx.
 Qed.

 Lemma find_spec m : forall x e, find x m = Some e <-> MapsTo x e m.
 Proof. exact (Raw.find_spec m.(nodup)). Qed.

 Lemma mem_spec m : forall x, mem x m = true <-> In x m.
 Proof. exact (Raw.mem_spec m.(nodup)). Qed.

 Lemma empty_spec : forall x, find x empty = None.
 Proof. exact (Raw.empty_spec _). Qed.

 Lemma is_empty_spec m : is_empty m = true <-> (forall x, find x m = None).
 Proof. exact (Raw.is_empty_spec m.(this)). Qed.

 Lemma add_spec1 m : forall x e, find x (add x e m) = Some e.
 Proof. exact (Raw.add_spec1 m.(this)). Qed.
 Lemma add_spec2 m : forall x y e, ~E.eq x y -> find y (add x e m) = find y m.
 Proof. exact (Raw.add_spec2 m.(this)). Qed.

 Lemma remove_spec1 m : forall x, find x (remove x m) = None.
 Proof. exact (Raw.remove_spec1 m.(nodup)). Qed.
 Lemma remove_spec2 m : forall x y, ~E.eq x y -> find y (remove x m) = find y m.
 Proof. exact (Raw.remove_spec2 m.(nodup)). Qed.

 Lemma bindings_spec1 m : forall x e,
   InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
 Proof. exact (Raw.bindings_spec1 m.(this)). Qed.
 Lemma bindings_spec2w m : NoDupA eq_key (bindings m).
 Proof. exact (Raw.bindings_spec2w m.(nodup)). Qed.

 Lemma cardinal_spec m : cardinal m = length (bindings m).
 Proof. reflexivity. Qed.

 Lemma fold_spec m : forall (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
 Proof. exact (Raw.fold_spec m.(this)). Qed.

 Lemma equal_spec m m' : forall cmp, equal cmp m m' = true <-> Equivb cmp m m'.
 Proof. exact (Raw.equal_spec m.(nodup) m'.(nodup)). Qed.

End Elt.

 Lemma map_spec {elt elt'} (f:elt->elt') m :
   forall x, find x (map f m) = option_map f (find x m).
 Proof. exact (Raw.map_spec f m.(this)). Qed.

 Lemma mapi_spec {elt elt'} (f:key->elt->elt') m :
   forall x, exists y,
     E.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).
 Proof. exact (Raw.mapi_spec f m.(this)). Qed.

 Lemma merge_spec1 {elt elt' elt''}
  (f:key->option elt->option elt'->option elt'') m m' :
  forall x,
   In x m \/ In x m' ->
   exists y, E.eq y x /\ find x (merge f m m') = f y (find x m) (find x m').
 Proof. exact (Raw.merge_spec1 f m.(nodup) m'.(nodup)). Qed.

 Lemma merge_spec2 {elt elt' elt''}
  (f:key->option elt->option elt'->option elt'') m m' :
  forall x,
   In x (merge f m m') -> In x m \/ In x m'.
 Proof. exact (Raw.merge_spec2 m.(nodup) m'.(nodup)). Qed.

End Make.

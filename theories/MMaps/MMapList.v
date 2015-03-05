(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Finite map library *)

(** This file proposes an implementation of the non-dependant interface
 [MMapInterface.S] using lists of pairs ordered (increasing) with respect to
 left projection. *)

Require Import MMapInterface OrdersFacts OrdersLists.

Set Implicit Arguments.
Unset Strict Implicit.

Module Raw (X:OrderedType).

Module Import MX := OrderedTypeFacts X.
Module Import PX := KeyOrderedType X.

Definition key := X.t.
Definition t (elt:Type) := list (X.t * elt).

Local Notation Sort := (sort ltk).
Local Notation Inf := (lelistA (ltk)).

Section Elt.
Variable elt : Type.

Ltac SortLt :=
 match goal with
   | H1 : Sort ?m, H2:Inf (?k',?e') ?m, H3:In ?k ?m |- _  =>
     assert (X.lt k' k);
     [let e := fresh "e" in destruct H3 as (e,H3);
      change (ltk (k',e') (k,e));
      apply (Sort_Inf_In H1 H2 (InA_eqke_eqk H3)) | ]
   | H1:Sort ?m, H2:Inf (?k',?e') ?m, H3:MapsTo ?k ?e ?m |- _  =>
     assert (X.lt k' k);
     [change (ltk (k',e') (k,e));
      apply (Sort_Inf_In H1 H2 (InA_eqke_eqk H3)) | ]
   | H1:Sort ?m, H2:Inf (?k',?e') ?m, H3:InA eqke (?k,?e) ?m |- _  =>
     assert (X.lt k' k);
     [change (ltk (k',e') (k,e));
      apply (Sort_Inf_In H1 H2 (InA_eqke_eqk H3)) | ]
 end.

(** * [find] *)

Fixpoint find (k:key) (m: t elt) : option elt :=
 match m with
  | nil => None
  | (k',x)::m' =>
     match X.compare k k' with
      | Lt => None
      | Eq => Some x
      | Gt => find k m'
     end
 end.

Lemma find_spec m (Hm:Sort m) x e :
 find x m = Some e <-> MapsTo x e m.
Proof.
 induction m as [|(k,e') m IH]; simpl.
 - split. discriminate. inversion 1.
 - inversion_clear Hm.
   unfold MapsTo in *. rewrite InA_cons, eqke_def.
   case X.compare_spec; intros.
   + split. injection 1 as ->; auto.
     intros [(_,<-)|IN]; trivial. SortLt. MX.order.
   + split. discriminate.
     intros [(E,<-)|IN]; trivial; try SortLt; MX.order.
   + rewrite IH; trivial. split; auto.
     intros [(E,<-)|IN]; trivial. MX.order.
Qed.

(** * [mem] *)

Fixpoint mem (k : key) (m : t elt) : bool :=
 match m with
  | nil => false
  | (k',_) :: l =>
     match X.compare k k' with
      | Lt => false
      | Eq => true
      | Gt => mem k l
     end
 end.

Lemma mem_spec m (Hm:Sort m) x : mem x m = true <-> In x m.
Proof.
 induction m as [|(k,e') m IH]; simpl.
 - split. discriminate. inversion 1. inversion_clear H0.
 - inversion_clear Hm.
   rewrite In_cons; simpl.
   case X.compare_spec; intros.
   + intuition.
   + split. discriminate. intros [E|(e,IN)]. MX.order.
     SortLt. MX.order.
   + rewrite IH; trivial. split; auto. intros [E|IN]; trivial.
     MX.order.
Qed.

(** * [empty] *)

Definition empty : t elt := nil.

Lemma empty_spec x : find x empty = None.
Proof.
 reflexivity.
Qed.

Lemma empty_sorted : Sort empty.
Proof.
 unfold empty; auto.
Qed.

(** * [is_empty] *)

Definition is_empty (l : t elt) : bool := if l then true else false.

Lemma is_empty_spec m :
 is_empty m = true <-> forall x, find x m = None.
Proof.
 destruct m as [|(k,e) m]; simpl; split; trivial; try discriminate.
 intros H. specialize (H k). now rewrite compare_refl in H.
Qed.

(** * [add] *)

Fixpoint add (k : key) (x : elt) (s : t elt) : t elt :=
 match s with
  | nil => (k,x) :: nil
  | (k',y) :: l =>
     match X.compare k k' with
      | Lt => (k,x)::s
      | Eq => (k,x)::l
      | Gt => (k',y) :: add k x l
     end
 end.

Lemma add_spec1 m x e : find x (add x e m) = Some e.
Proof.
 induction m as [|(k,e') m IH]; simpl.
 - now rewrite compare_refl.
 - case X.compare_spec; simpl; rewrite ?compare_refl; trivial.
   rewrite <- compare_gt_iff. now intros ->.
Qed.

Lemma add_spec2 m x y e : ~X.eq x y -> find y (add x e m) = find y m.
Proof.
 induction m as [|(k,e') m IH]; simpl.
 - case X.compare_spec; trivial; MX.order.
 - case X.compare_spec; simpl; intros; trivial.
   + rewrite <-H. case X.compare_spec; trivial; MX.order.
   + do 2 (case X.compare_spec; trivial; try MX.order).
   + now rewrite IH.
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
 simpl; case X.compare; intuition.
Qed.
Hint Resolve add_Inf.

Lemma add_sorted : forall m (Hm:Sort m) x e, Sort (add x e m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 destruct a as (x',e').
 simpl; case (X.compare_spec x x'); intuition; inversion_clear Hm; auto.
 constructor; auto.
 apply Inf_eq with (x',e'); auto.
Qed.

(** * [remove] *)

Fixpoint remove (k : key) (s : t elt) : t elt :=
 match s with
  | nil => nil
  | (k',x) :: l =>
     match X.compare k k' with
      | Lt => s
      | Eq => l
      | Gt => (k',x) :: remove k l
     end
 end.

Lemma remove_spec1 m (Hm:Sort m) x : find x (remove x m) = None.
Proof.
 induction m as [|(k,e') m IH]; simpl; trivial.
 inversion_clear Hm.
 case X.compare_spec; simpl.
 - intros E. rewrite <- E in H0.
   apply Sort_Inf_NotIn in H0; trivial. unfold In in H0.
   setoid_rewrite <- find_spec in H0; trivial.
   destruct (find x m); trivial.
   elim H0; now exists e.
 - rewrite <- compare_lt_iff. now intros ->.
 - rewrite <- compare_gt_iff. intros ->; auto.
Qed.

Lemma remove_spec2 m (Hm:Sort m) x y :
  ~X.eq x y -> find y (remove x m) = find y m.
Proof.
 induction m as [|(k,e') m IH]; simpl; trivial.
 inversion_clear Hm.
 case X.compare_spec; simpl; intros E E'; try rewrite IH; auto.
 case X.compare_spec; simpl; trivial; try MX.order.
 intros. rewrite <- E in H0,H1. clear E E'.
 destruct (find y m) eqn:F; trivial.
 apply find_spec in F; trivial.
 SortLt. MX.order.
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
 simpl; case X.compare; intuition.
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
 simpl; case X.compare_spec; intuition; inversion_clear Hm; auto.
Qed.

(** * [bindings] *)

Definition bindings (m: t elt) := m.

Lemma bindings_spec1 m x e :
  InA eqke (x,e) (bindings m) <-> MapsTo x e m.
Proof.
 reflexivity.
Qed.

Lemma bindings_spec2 m (Hm:Sort m) : sort ltk (bindings m).
Proof.
 auto.
Qed.

Lemma bindings_spec2w m (Hm:Sort m) : NoDupA eqk (bindings m).
Proof.
 now apply Sort_NoDupA.
Qed.

(** * [fold] *)

Fixpoint fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc:A) :  A :=
  match m with
   | nil => acc
   | (k,e)::m' => fold f m' (f k e acc)
  end.

Lemma fold_spec m : forall (A:Type)(i:A)(f:key->elt->A->A),
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
Proof.
 induction m as [|(k,e) m IH]; simpl; auto.
Qed.

(** * [equal] *)

Fixpoint equal (cmp:elt->elt->bool)(m m' : t elt) : bool :=
  match m, m' with
   | nil, nil => true
   | (x,e)::l, (x',e')::l' =>
      match X.compare x x' with
       | Eq => cmp e e' && equal cmp l l'
       | _  => false
      end
   | _, _ => false
  end.

Definition Equivb (cmp:elt->elt->bool) m m' :=
  (forall k, In k m <-> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Lemma equal_1 : forall m (Hm:Sort m) m' (Hm': Sort m') cmp,
  Equivb cmp m m' -> equal cmp m m' = true.
Proof.
 induction m as [|(k,e) m IH]; destruct m' as [|(k',e') m']; simpl.
 - trivial.
 - intros _ cmp (H,_).
   exfalso. apply (@In_nil elt k'). rewrite H, In_cons. now left.
 - intros _ cmp (H,_).
   exfalso. apply (@In_nil elt k). rewrite <- H, In_cons. now left.
 - intros Hm' cmp E.
   inversion_clear Hm; inversion_clear Hm'.
   case X.compare_spec; intros E'.
   + apply andb_true_intro; split.
     * eapply E; eauto. apply InA_cons; now left.
     * apply IH; clear IH; trivial.
       destruct E as (E1,E2). split.
       { intros x. clear E2.
         split; intros; SortLt.
         specialize (E1 x); rewrite 2 In_cons in E1; simpl in E1.
         destruct E1 as ([E1|E1],_); eauto. MX.order.
         specialize (E1 x); rewrite 2 In_cons in E1; simpl in E1.
         destruct E1 as (_,[E1|E1]); eauto. MX.order. }
       { intros x xe xe' Hx HX'. eapply E2; eauto. }
   + assert (IN : In k ((k',e')::m')).
     { apply E. apply In_cons; now left. }
     apply In_cons in IN. simpl in IN. destruct IN as [?|IN]. MX.order.
     SortLt. MX.order.
   + assert (IN : In k' ((k,e)::m)).
     { apply E. apply In_cons; now left. }
     apply In_cons in IN. simpl in IN. destruct IN as [?|IN]. MX.order.
     SortLt. MX.order.
Qed.

Lemma equal_2 m (Hm:Sort m) m' (Hm':Sort m') cmp :
  equal cmp m m' = true -> Equivb cmp m m'.
Proof.
 revert m' Hm'.
 induction m as [|(k,e) m IH]; destruct m' as [|(k',e') m']; simpl;
  try discriminate.
 - split. reflexivity. inversion 1.
 - intros Hm'. case X.compare_spec; try discriminate.
   rewrite andb_true_iff. intros E (C,EQ).
   inversion_clear Hm; inversion_clear Hm'.
   apply IH in EQ; trivial.
   destruct EQ as (E1,E2).
   split.
   + intros x. rewrite 2 In_cons; simpl. rewrite <- E1.
     intuition; now left; MX.order.
   + intros x ex ex'. unfold MapsTo in *. rewrite 2 InA_cons, 2 eqke_def.
     intuition; subst.
     * trivial.
     * SortLt. MX.order.
     * SortLt. MX.order.
     * eapply E2; eauto.
Qed.

Lemma equal_spec m (Hm:Sort m) m' (Hm':Sort m') cmp :
  equal cmp m m' = true <-> Equivb cmp m m'.
Proof.
 split. now apply equal_2. now apply equal_1.
Qed.

(** This lemma isn't part of the spec of [Equivb], but is used in [MMapAVL] *)

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
 case X.compare_spec; intros; try MX.order.
 rewrite H2; simpl.
 apply equal_1; auto.
 apply equal_2; auto.
 generalize (equal_1 H H0 H3).
 simpl.
 case X.compare_spec; try discriminate.
 rewrite andb_true_iff. intuition.
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
Arguments find {elt} k m.
Section Elt2.
Variable elt elt' : Type.

(** Specification of [map] *)

Lemma map_spec (f:elt->elt') m x :
 find x (map f m) = option_map f (find x m).
Proof.
 induction m as [|(k,e) m IH]; simpl; trivial.
 now case X.compare_spec.
Qed.

Lemma map_Inf (f:elt->elt') m x e e' :
  Inf (x,e) m -> Inf (x,e') (map f m).
Proof.
 induction m as [|(x0,e0) m IH]; simpl; auto.
 inversion_clear 1; auto.
Qed.
Hint Resolve map_Inf.

Lemma map_sorted (f:elt->elt')(m: t elt)(Hm : Sort m) :
  Sort (map f m).
Proof.
 induction m as [|(x,e) m IH]; simpl; auto.
 inversion_clear Hm. constructor; eauto.
Qed.

(** Specification of [mapi] *)

Lemma mapi_spec (f:key->elt->elt') m x :
  exists y, X.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).
Proof.
 induction m as [|(k,e) m IH]; simpl.
 - now exists x.
 - elim X.compare_spec; intros; simpl.
   + now exists k.
   + now exists x.
   + apply IH.
Qed.

Lemma mapi_Inf (f:key->elt->elt') m x e :
  Inf (x,e) m -> Inf (x,f x e) (mapi f m).
Proof.
 induction m as [|(x0,e0) m IH]; simpl; auto.
 inversion_clear 1; auto.
Qed.
Hint Resolve mapi_Inf.

Lemma mapi_sorted (f:key->elt->elt') m (Hm : Sort m) :
  Sort (mapi f m).
Proof.
 induction m as [|(x,e) m IH]; simpl; auto.
 inversion_clear Hm; auto.
Qed.

End Elt2.
Section Elt3.

(** * [merge] *)

Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.

Definition option_cons {A}(k:key)(o:option A)(l:list (key*A)) :=
  match o with
   | Some e => (k,e)::l
   | None => l
  end.

Fixpoint merge_l (m : t elt) : t elt'' :=
  match m with
   | nil => nil
   | (k,e)::l => option_cons k (f k (Some e) None) (merge_l l)
  end.

Fixpoint merge_r (m' : t elt') : t elt'' :=
  match m' with
   | nil => nil
   | (k,e')::l' => option_cons k (f k None (Some e')) (merge_r l')
  end.

Fixpoint merge (m : t elt) : t elt' -> t elt'' :=
  match m with
   | nil => merge_r
   | (k,e) :: l =>
      fix merge_aux (m' : t elt') : t elt'' :=
        match m' with
         | nil => merge_l m
         | (k',e') :: l' =>
            match X.compare k k' with
             | Lt => option_cons k (f k (Some e) None) (merge l m')
             | Eq => option_cons k (f k (Some e) (Some e')) (merge l l')
             | Gt => option_cons k' (f k' None (Some e')) (merge_aux l')
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
             | Lt => (k,(Some e, None))::combine l m'
             | Eq => (k,(Some e, Some e'))::combine l l'
             | Gt => (k',(None,Some e'))::combine_aux l'
            end
        end
  end.

Definition fold_right_pair {A B C}(f: A->B->C->C)(l:list (A*B))(i:C) :=
  List.fold_right (fun p => f (fst p) (snd p)) i l.

Definition merge' m m' :=
  let m0 : t oee' := combine m m' in
  let m1 : t (option elt'') := mapi (fun k p => f k (fst p) (snd p)) m0 in
  fold_right_pair (option_cons (A:=elt'')) m1 nil.

Lemma merge_equiv : forall m m', merge' m m' = merge m m'.
Proof.
 unfold merge'.
 induction m as [|(k,e) m IHm]; intros.
 - (* merge_r *)
   simpl.
   induction m' as [|(k',e') m' IHm']; simpl; rewrite ?IHm'; auto.
 - induction m' as [|(k',e') m' IHm']; simpl.
   + f_equal.
     (* merge_l *)
     clear k e IHm.
     induction m as [|(k,e) m IHm]; simpl; rewrite ?IHm; auto.
   + elim X.compare_spec; intros; simpl; f_equal.
     * apply IHm.
     * apply IHm.
     * apply IHm'.
Qed.

Lemma combine_Inf :
  forall m m' (x:key)(e:elt)(e':elt')(e'':oee'),
  Inf (x,e) m ->
  Inf (x,e') m' ->
  Inf (x,e'') (combine m m').
Proof.
 induction m.
 - intros. simpl. eapply map_Inf; eauto.
 - induction m'; intros.
   + destruct a.
     replace (combine ((t0, e0) :: m) nil) with
      (map (fun e => (Some e,None (A:=elt'))) ((t0,e0)::m)); auto.
     eapply map_Inf; eauto.
   + simpl.
     destruct a as (k,e0); destruct a0 as (k',e0').
     elim X.compare_spec.
     * inversion_clear H; auto.
     * inversion_clear H; auto.
     * inversion_clear H0; auto.
Qed.
Hint Resolve combine_Inf.

Lemma combine_sorted m (Hm : Sort m) m' (Hm' : Sort m') :
  Sort (combine m m').
Proof.
 revert m' Hm'.
 induction m.
 - intros; clear Hm. simpl. apply map_sorted; auto.
 - induction m'; intros.
   + clear Hm'.
     destruct a.
     replace (combine ((t0, e) :: m) nil) with
      (map (fun e => (Some e,None (A:=elt'))) ((t0,e)::m)); auto.
     apply map_sorted; auto.
   + simpl.
     destruct a as (k,e); destruct a0 as (k',e').
     inversion_clear Hm; inversion_clear Hm'.
     case X.compare_spec; [intros Heq| intros Hlt| intros Hlt];
      constructor; auto.
     * assert (Inf (k, e') m') by (apply Inf_eq with (k',e'); auto).
       exact (combine_Inf _ H0 H3).
     * assert (Inf (k, e') ((k',e')::m')) by auto.
       exact (combine_Inf _ H0 H3).
     * assert (Inf (k', e) ((k,e)::m)) by auto.
       exact (combine_Inf _  H3 H2).
Qed.

Lemma merge_sorted m (Hm : Sort m) m' (Hm' : Sort m') :
  Sort (merge m m').
Proof.
 intros.
 rewrite <- merge_equiv.
 unfold merge'.
 assert (Hmm':=combine_sorted Hm Hm').
 set (l0:=combine m m') in *; clearbody l0.
 set (f':= fun k p => f k (fst p) (snd p)).
 assert (H1:=mapi_sorted f' Hmm').
 set (l1:=mapi f' l0) in *; clearbody l1.
 clear f' f Hmm' l0 Hm Hm' m m'.
 (* Sort fold_right_pair *)
 induction l1.
 - simpl; auto.
 - inversion_clear H1.
   destruct a; destruct o; auto.
   simpl.
   constructor; auto.
   clear IHl1.
   (* Inf fold_right_pair *)
   induction l1.
   + simpl; auto.
   + destruct a; destruct o; simpl; auto.
     * inversion_clear H0; auto.
     * inversion_clear H0. inversion_clear H.
       compute in H1.
       apply IHl1; auto.
       apply Inf_lt with (t1, None); auto.
Qed.

Definition at_least_one (o:option elt)(o':option elt') :=
  match o, o' with
   | None, None => None
   | _, _  => Some (o,o')
  end.

Lemma combine_spec m (Hm : Sort m) m' (Hm' : Sort m') (x:key) :
  find x (combine m m') = at_least_one (find x m) (find x m').
Proof.
 revert m' Hm'.
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
 destruct (X.compare_spec x t0) as [ |Hlt|Hlt]; simpl; auto.
 inversion_clear Hm; clear H0 Hlt Hm' IHm t0.
 induction m; simpl; auto.
 inversion_clear H.
 destruct a.
 simpl; destruct (X.compare x t0); simpl; auto.
 (* m' <> nil *)
 intros.
 destruct a as (k,e); destruct a0 as (k',e'); simpl.
 inversion Hm; inversion Hm'; subst.
 destruct (X.compare_spec k k'); simpl;
  destruct (X.compare_spec x k);
   MX.order || destruct (X.compare_spec x k');
               simpl; try MX.order; auto.
 - rewrite IHm; auto; simpl. elim X.compare_spec; auto; MX.order.
 - rewrite IHm; auto; simpl. elim X.compare_spec; auto; MX.order.
 - rewrite IHm; auto; simpl. elim X.compare_spec; auto; MX.order.
 - change (find x (combine ((k, e) :: m) m') = Some (Some e, find x m')).
   rewrite IHm'; auto; simpl. elim X.compare_spec; auto; MX.order.
 - change (find x (combine ((k, e) :: m) m') = at_least_one None (find x m')).
   rewrite IHm'; auto; simpl. elim X.compare_spec; auto; MX.order.
 - change (find x (combine ((k, e) :: m) m') =
         at_least_one (find x m) (find x m')).
   rewrite IHm'; auto; simpl. elim X.compare_spec; auto; MX.order.
Qed.

Definition at_least_one_then_f k (o:option elt)(o':option elt') :=
  match o, o' with
   | None, None => None
   | _, _  => f k o o'
  end.

Lemma merge_spec0 m (Hm : Sort m) m' (Hm' : Sort m') (x:key) :
  exists y, X.eq y x /\
  find x (merge m m') = at_least_one_then_f y (find x m) (find x m').
Proof.
 intros.
 rewrite <- merge_equiv.
 unfold merge'.
 assert (H:=combine_spec Hm Hm' x).
 assert (H2:=combine_sorted Hm Hm').
 set (f':= fun k p => f k (fst p) (snd p)).
 set (m0 := combine m m') in *; clearbody m0.
 set (o:=find x m) in *; clearbody o.
 set (o':=find x m') in *; clearbody o'.
 clear Hm Hm' m m'. revert H.
 match goal with |- ?G =>
   assert (G/\(find x m0 = None ->
               find x (fold_right_pair option_cons (mapi f' m0) nil) = None));
    [|intuition] end.
 induction m0; simpl in *; intuition.
 - exists x; split; [easy|].
   destruct o; destruct o'; simpl in *; try discriminate; auto.
 - destruct a as (k,(oo,oo')); simpl in *.
   inversion_clear H2.
   destruct (X.compare_spec x k) as [Heq|Hlt|Hlt]; simpl in *.
   + (* x = k *)
     exists k; split; [easy|].
     assert (at_least_one_then_f k o o' = f k oo oo').
     { destruct o; destruct o'; simpl in *; inversion_clear H; auto. }
     rewrite H2.
     unfold f'; simpl.
     destruct (f k oo oo'); simpl.
     * elim X.compare_spec; trivial; try MX.order.
     * destruct (IHm0 H0) as (_,H4); apply H4; auto.
       case_eq (find x m0); intros; auto.
       assert (eqk (elt:=oee') (k,(oo,oo')) (x,(oo,oo'))).
       now compute.
       symmetry in H5.
       destruct (Sort_Inf_NotIn H0 (Inf_eq H5 H1)).
       exists p; apply find_spec; auto.
   + (* x < k *)
     destruct (f' k (oo,oo')); simpl.
     * elim X.compare_spec; trivial; try MX.order.
       destruct o; destruct o'; simpl in *; try discriminate; auto.
       now exists x.
     * apply IHm0; trivial.
       rewrite <- H.
       case_eq (find x m0); intros; auto.
       assert (ltk (elt:=oee') (x,(oo,oo')) (k,(oo,oo'))).
       red; auto.
       destruct (Sort_Inf_NotIn H0 (Inf_lt H3 H1)).
       exists p; apply find_spec; auto.
   + (* k < x *)
     unfold f'; simpl.
     destruct (f k oo oo'); simpl.
     * elim X.compare_spec; trivial; try MX.order.
       intros. apply IHm0; auto.
     * apply IHm0; auto.

 - (* None -> None *)
   destruct a as (k,(oo,oo')).
   simpl.
   inversion_clear H2.
   destruct (X.compare_spec x k) as [Hlt|Heq|Hlt]; try discriminate.
   + (* x < k *)
     unfold f'; simpl.
     destruct (f k oo oo'); simpl.
     elim X.compare_spec; trivial; try MX.order. intros.
     apply IHm0; auto.
     case_eq (find x m0); intros; auto.
     assert (ltk (elt:=oee') (x,(oo,oo')) (k,(oo,oo'))).
     now compute.
     destruct (Sort_Inf_NotIn H0 (Inf_lt H3 H1)).
     exists p; apply find_spec; auto.
   + (* k < x *)
     unfold f'; simpl.
     destruct (f k oo oo'); simpl.
     elim X.compare_spec; trivial; try MX.order. intros.
     apply IHm0; auto.
     apply IHm0; auto.
Qed.

(** Specification of [merge] *)

Lemma merge_spec1 m (Hm : Sort m) m' (Hm' : Sort m')(x:key) :
  In x m \/ In x m' ->
  exists y, X.eq y x /\
    find x (merge m m') = f y (find x m) (find x m').
Proof.
 intros.
 destruct (merge_spec0 Hm Hm' x) as (y,(Hy,H')).
 exists y; split; [easy|]. rewrite H'.
 destruct H as [(e,H)|(e,H)];
  apply find_spec in H; trivial; rewrite H; simpl; auto.
 now destruct (find x m).
Qed.

Lemma merge_spec2 m (Hm : Sort m) m' (Hm' : Sort m')(x:key) :
  In x (merge m m') -> In x m \/ In x m'.
Proof.
 intros.
 destruct H as (e,H).
 apply find_spec in H; auto using merge_sorted.
 destruct (merge_spec0 Hm Hm' x) as (y,(Hy,H')).
 rewrite H in H'.
 destruct (find x m) eqn:F.
 - apply find_spec in F; eauto.
 - destruct (find x m') eqn:F'.
   + apply find_spec in F'; eauto.
   + simpl in H'. discriminate.
Qed.

End Elt3.
End Raw.

Module Make (X: OrderedType) <: S with Module E := X.
Module Raw := Raw X.
Module E := X.

Definition key := E.t.
Definition eq_key {elt} := @Raw.PX.eqk elt.
Definition eq_key_elt {elt} := @Raw.PX.eqke elt.
Definition lt_key {elt} := @Raw.PX.ltk elt.

Record t_ (elt:Type) := Mk
  {this :> Raw.t elt;
   sorted : sort Raw.PX.ltk this}.
Definition t := t_.

Definition empty {elt} := Mk (Raw.empty_sorted elt).

Section Elt.
 Variable elt elt' elt'':Type.

 Implicit Types m : t elt.
 Implicit Types x y : key.
 Implicit Types e : elt.

 Definition is_empty m : bool := Raw.is_empty m.(this).
 Definition add x e m : t elt := Mk (Raw.add_sorted m.(sorted) x e).
 Definition find x m : option elt := Raw.find x m.(this).
 Definition remove x m : t elt := Mk (Raw.remove_sorted m.(sorted) x).
 Definition mem x m : bool := Raw.mem x m.(this).
 Definition map f m : t elt' := Mk (Raw.map_sorted f m.(sorted)).
 Definition mapi (f:key->elt->elt') m : t elt' :=
   Mk (Raw.mapi_sorted f m.(sorted)).
 Definition merge f m (m':t elt') : t elt'' :=
   Mk (Raw.merge_sorted f m.(sorted) m'.(sorted)).
 Definition bindings m : list (key*elt) := Raw.bindings m.(this).
 Definition cardinal m := length m.(this).
 Definition fold {A:Type}(f:key->elt->A->A) m (i:A) : A :=
   Raw.fold f m.(this) i.
 Definition equal cmp m m' : bool := Raw.equal cmp m.(this) m'.(this).

 Definition MapsTo x e m : Prop := Raw.PX.MapsTo x e m.(this).
 Definition In x m : Prop := Raw.PX.In x m.(this).

 Definition Equal m m' := forall y, find y m = find y m'.
 Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
         (forall k, In k m <-> In k m') /\
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
 Definition Equivb cmp m m' : Prop := @Raw.Equivb elt cmp m.(this) m'.(this).

 Instance MapsTo_compat :
   Proper (E.eq==>Logic.eq==>Logic.eq==>iff) MapsTo.
 Proof.
   intros x x' Hx e e' <- m m' <-. unfold MapsTo. now rewrite Hx.
 Qed.

 Lemma find_spec m : forall x e, find x m = Some e <-> MapsTo x e m.
 Proof. exact (Raw.find_spec m.(sorted)). Qed.

 Lemma mem_spec m : forall x, mem x m = true <-> In x m.
 Proof. exact (Raw.mem_spec m.(sorted)). Qed.

 Lemma empty_spec : forall x, find x empty = None.
 Proof. exact (Raw.empty_spec _). Qed.

 Lemma is_empty_spec m : is_empty m = true <-> (forall x, find x m = None).
 Proof. exact (Raw.is_empty_spec m.(this)). Qed.

 Lemma add_spec1 m : forall x e, find x (add x e m) = Some e.
 Proof. exact (Raw.add_spec1 m.(this)). Qed.
 Lemma add_spec2 m : forall x y e, ~E.eq x y -> find y (add x e m) = find y m.
 Proof. exact (Raw.add_spec2 m.(this)). Qed.

 Lemma remove_spec1 m : forall x, find x (remove x m) = None.
 Proof. exact (Raw.remove_spec1 m.(sorted)). Qed.
 Lemma remove_spec2 m : forall x y, ~E.eq x y -> find y (remove x m) = find y m.
 Proof. exact (Raw.remove_spec2 m.(sorted)). Qed.

 Lemma bindings_spec1 m : forall x e,
   InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
 Proof. exact (Raw.bindings_spec1 m.(this)). Qed.
 Lemma bindings_spec2w m : NoDupA eq_key (bindings m).
 Proof. exact (Raw.bindings_spec2w m.(sorted)). Qed.
 Lemma bindings_spec2 m : sort lt_key (bindings m).
 Proof. exact (Raw.bindings_spec2 m.(sorted)). Qed.

 Lemma cardinal_spec m : cardinal m = length (bindings m).
 Proof. reflexivity. Qed.

 Lemma fold_spec m : forall (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
 Proof. exact (Raw.fold_spec m.(this)). Qed.

 Lemma equal_spec m m' : forall cmp, equal cmp m m' = true <-> Equivb cmp m m'.
 Proof. exact (Raw.equal_spec m.(sorted) m'.(sorted)). Qed.

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
 Proof. exact (Raw.merge_spec1 f m.(sorted) m'.(sorted)). Qed.

 Lemma merge_spec2 {elt elt' elt''}
  (f:key->option elt->option elt'->option elt'') m m' :
  forall x,
   In x (merge f m m') -> In x m \/ In x m'.
 Proof. exact (Raw.merge_spec2 m.(sorted) m'.(sorted)). Qed.

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

Definition cmp e e' :=
  match D.compare e e' with Eq => true | _ => false end.

Fixpoint eq_list (m m' : list (X.t * D.t)) : Prop :=
  match m, m' with
   | nil, nil => True
   | (x,e)::l, (x',e')::l' =>
      match X.compare x x' with
       | Eq => D.eq e e' /\ eq_list l l'
       | _  => False
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
       | Lt => True
       | Gt => False
       | Eq => D.lt e e' \/ (D.eq e e' /\ lt_list l l')
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
 destruct (X.compare_spec x x') as [Hlt|Heq|Hlt]; simpl; intuition.
 unfold cmp at 1.
 elim D.compare_spec; try MD.order; simpl.
 inversion_clear Hl.
 inversion_clear Hl'.
 destruct (IHl H (Mk H3)).
 unfold equal, eq in H5; simpl in H5; auto.
 destruct (andb_prop _ _ H); clear H.
 generalize H0; unfold cmp.
 elim D.compare_spec; try MD.order; simpl; try discriminate.
 destruct (andb_prop _ _ H); clear H.
 inversion_clear Hl.
 inversion_clear Hl'.
 destruct (IHl H (Mk H3)).
 unfold equal, eq in H6; simpl in H6; auto.
Qed.

Lemma eq_spec m m' : eq m m' <-> Equivb cmp m m'.
Proof.
 now rewrite eq_equal, equal_spec.
Qed.

Lemma eq_refl : forall m : t, eq m m.
Proof.
 intros (m,Hm); induction m; unfold eq; simpl; auto.
 destruct a.
 destruct (X.compare_spec t0 t0) as [Hlt|Heq|Hlt]; auto.
 - split. reflexivity. inversion_clear Hm. apply (IHm H).
 - MapS.Raw.MX.order.
 - MapS.Raw.MX.order.
Qed.

Lemma eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
Proof.
 intros (m,Hm); induction m;
 intros (m', Hm'); destruct m'; unfold eq; simpl;
 try destruct a as (x,e); try destruct p as (x',e'); auto.
 destruct (X.compare_spec x x')  as [Hlt|Heq|Hlt];
  elim X.compare_spec; try MapS.Raw.MX.order; intuition.
 inversion_clear Hm; inversion_clear Hm'.
 apply (IHm H0 (Mk H4)); auto.
Qed.

Lemma eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
Proof.
 intros (m1,Hm1); induction m1;
 intros (m2, Hm2); destruct m2;
 intros (m3, Hm3); destruct m3; unfold eq; simpl;
 try destruct a as (x,e);
 try destruct p as (x',e');
 try destruct p0 as (x'',e''); try contradiction; auto.
 destruct (X.compare_spec x x') as [Hlt|Heq|Hlt];
  destruct (X.compare_spec x' x'') as [Hlt'|Heq'|Hlt'];
   elim X.compare_spec; try MapS.Raw.MX.order; intuition.
 now transitivity e'.
 inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
 apply (IHm1 H1 (Mk H6) (Mk H8)); intuition.
Qed.

Instance eq_equiv : Equivalence eq.
Proof. split; [exact eq_refl|exact eq_sym|exact eq_trans]. Qed.

Lemma lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
Proof.
 intros (m1,Hm1); induction m1;
 intros (m2, Hm2); destruct m2;
 intros (m3, Hm3); destruct m3; unfold lt; simpl;
 try destruct a as (x,e);
 try destruct p as (x',e');
 try destruct p0 as (x'',e''); try contradiction; auto.
 destruct (X.compare_spec x x') as [Hlt|Heq|Hlt];
  destruct (X.compare_spec x' x'') as [Hlt'|Heq'|Hlt'];
   elim X.compare_spec; try MapS.Raw.MX.order; intuition.
 left; transitivity e'; auto.
 left; MD.order.
 left; MD.order.
 right.
 split.
 transitivity e'; auto.
 inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
 apply (IHm1 H2 (Mk H6) (Mk H8)); intuition.
Qed.

Lemma lt_irrefl : forall m, ~ lt m m.
Proof.
 intros (m,Hm); induction m; unfold lt; simpl; auto.
 destruct a.
 destruct (X.compare_spec t0 t0) as [Hlt|Heq|Hlt]; auto.
 - intuition. MD.order. inversion_clear Hm. now apply (IHm H0).
 - MapS.Raw.MX.order.
Qed.

Instance lt_strorder : StrictOrder lt.
Proof. split; [exact lt_irrefl|exact lt_trans]. Qed.

Lemma lt_compat1 : forall m1 m1' m2, eq m1 m1' -> lt m1 m2 -> lt m1' m2.
Proof.
 intros (m1,Hm1); induction m1;
 intros (m1',Hm1'); destruct m1';
 intros (m2,Hm2); destruct m2; unfold eq, lt;
 try destruct a as (x,e);
 try destruct p as (x',e');
 try destruct p0 as (x'',e''); try contradiction; simpl; auto.
 destruct (X.compare_spec x x') as [Hlt|Heq|Hlt];
  destruct (X.compare_spec x' x'') as [Hlt'|Heq'|Hlt'];
   elim X.compare_spec; try MapS.Raw.MX.order; intuition.
 left; MD.order.
 right.
 split.
 MD.order.
 inversion_clear Hm1; inversion_clear Hm1'; inversion_clear Hm2.
 apply (IHm1 H0 (Mk H6) (Mk H8)); intuition.
Qed.

Lemma lt_compat2 : forall m1 m2 m2', eq m2 m2' -> lt m1 m2 -> lt m1 m2'.
Proof.
 intros (m1,Hm1); induction m1;
 intros (m2,Hm2); destruct m2;
 intros (m2',Hm2'); destruct m2'; unfold eq, lt;
 try destruct a as (x,e);
 try destruct p as (x',e');
 try destruct p0 as (x'',e''); try contradiction; simpl; auto.
 destruct (X.compare_spec x x') as [Hlt|Heq|Hlt];
  destruct (X.compare_spec x' x'') as [Hlt'|Heq'|Hlt'];
   elim X.compare_spec; try MapS.Raw.MX.order; intuition.
 left; MD.order.
 right.
 split.
 MD.order.
 inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm2'.
 apply (IHm1 H0 (Mk H6) (Mk H8)); intuition.
Qed.

Instance lt_compat : Proper (eq==>eq==>iff) lt.
Proof.
 intros m1 m1' H1 m2 m2' H2. split; intros.
 now apply (lt_compat2 H2), (lt_compat1 H1).
 symmetry in H1, H2.
 now apply (lt_compat2 H2), (lt_compat1 H1).
Qed.

Ltac cmp_solve :=
  unfold eq, lt; simpl; elim X.compare_spec; try Raw.MX.order; auto.

Fixpoint compare_list m1 m2 := match m1, m2 with
| nil, nil => Eq
| nil, _ => Lt
| _, nil => Gt
| (k1,e1)::m1, (k2,e2)::m2 =>
  match X.compare k1 k2 with
  | Lt => Lt
  | Gt => Gt
  | Eq => match D.compare e1 e2 with
          | Lt => Lt
          | Gt => Gt
          | Eq => compare_list m1 m2
          end
  end
end.

Definition compare m1 m2 := compare_list m1.(this) m2.(this).

Lemma compare_spec : forall m1 m2, CompSpec eq lt m1 m2 (compare m1 m2).
Proof.
 unfold CompSpec.
 intros (m1,Hm1)(m2,Hm2). unfold compare, eq, lt; simpl.
 revert m2 Hm2.
 induction m1 as [|(k1,e1) m1 IH1]; destruct m2 as [|(k2,e2) m2];
  try constructor; simpl; intros; auto.
 elim X.compare_spec; simpl; try constructor; auto; intros.
 elim D.compare_spec; simpl; try constructor; auto; intros.
 inversion_clear Hm1; inversion_clear Hm2.
 destruct (IH1 H1 _ H3); simpl; try constructor; auto.
 elim X.compare_spec; try Raw.MX.order. right. now split.
 elim X.compare_spec; try Raw.MX.order. now left.
 elim X.compare_spec; try Raw.MX.order; auto.
Qed.

End Make_ord.

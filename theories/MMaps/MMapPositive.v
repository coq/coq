(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * MMapPositive : an implementation of MMapInterface for [positive] keys. *)

Require Import Bool PeanoNat BinPos Orders OrdersEx OrdersLists MMapInterface.

Set Implicit Arguments.
Local Open Scope lazy_bool_scope.
Local Open Scope positive_scope.
Local Unset Elimination Schemes.

(** This file is an adaptation to the [MMap] framework of a work by
  Xavier Leroy and Sandrine Blazy (used for building certified compilers).
  Keys are of type [positive], and maps are binary trees: the sequence
  of binary digits of a positive number corresponds to a path in such a tree.
  This is quite similar to the [IntMap] library, except that no path
  compression is implemented, and that the current file is simple enough to be
  self-contained. *)

(** Reverses the positive [y] and concatenate it with [x] *)

Fixpoint rev_append (y x : positive) : positive :=
  match y with
    | 1 => x
    | y~1 => rev_append y x~1
    | y~0 => rev_append y x~0
  end.
Local Infix "@" := rev_append (at level 60).
Definition rev x := x@1.

(** The module of maps over positive keys *)

Module PositiveMap <: S with Module E:=PositiveOrderedTypeBits.

  Module E:=PositiveOrderedTypeBits.
  Module ME:=KeyOrderedType E.

  Definition key := positive : Type.

  Definition eq_key {A} (p p':key*A) := E.eq (fst p) (fst p').

  Definition eq_key_elt {A} (p p':key*A) :=
    E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_key {A} (p p':key*A) := E.lt (fst p) (fst p').

  Instance eqk_equiv {A} : Equivalence (@eq_key A) := _.
  Instance eqke_equiv {A} : Equivalence (@eq_key_elt A) := _.
  Instance ltk_strorder {A} : StrictOrder (@lt_key A) := _.

  Inductive tree (A : Type) :=
    | Leaf : tree A
    | Node : tree A -> option A -> tree A -> tree A.

  Arguments Leaf {A}.

  Scheme tree_ind := Induction for tree Sort Prop.

  Definition t := tree.

  Definition empty {A} : t A := Leaf.

  Section A.
  Variable A:Type.

  Fixpoint is_empty (m : t A) : bool :=
   match m with
    | Leaf => true
    | Node l None r => (is_empty l) &&& (is_empty r)
    | _ => false
   end.

  Fixpoint find (i : key) (m : t A) : option A :=
    match m with
    | Leaf => None
    | Node l o r =>
        match i with
        | xH => o
        | xO ii => find ii l
        | xI ii => find ii r
        end
    end.

  Fixpoint mem (i : key) (m : t A) : bool :=
    match m with
    | Leaf => false
    | Node l o r =>
        match i with
        | xH => match o with None => false | _ => true end
        | xO ii => mem ii l
        | xI ii => mem ii r
        end
    end.

  Fixpoint add (i : key) (v : A) (m : t A) : t A :=
    match m with
    | Leaf =>
        match i with
        | xH => Node Leaf (Some v) Leaf
        | xO ii => Node (add ii v Leaf) None Leaf
        | xI ii => Node Leaf None (add ii v Leaf)
        end
    | Node l o r =>
        match i with
        | xH => Node l (Some v) r
        | xO ii => Node (add ii v l) o r
        | xI ii => Node l o (add ii v r)
        end
    end.

  (** helper function to avoid creating empty trees that are not leaves *)

  Definition node (l : t A) (o: option A) (r : t A) : t A :=
    match o,l,r with
      | None,Leaf,Leaf => Leaf
      | _,_,_ => Node l o r
    end.

  Fixpoint remove (i : key) (m : t A) : t A :=
    match m with
    | Leaf => Leaf
    | Node l o r =>
      match i with
      | xH => node l None r
      | xO ii => node (remove ii l) o r
      | xI ii => node l o (remove ii r)
      end
    end.

  (** [bindings] *)

  Fixpoint xbindings (m : t A) (i : positive) (a: list (key*A)) :=
    match m with
      | Leaf => a
      | Node l None r => xbindings l i~0 (xbindings r i~1 a)
      | Node l (Some e) r => xbindings l i~0 ((rev i,e) :: xbindings r i~1 a)
    end.

  Definition bindings (m : t A) := xbindings m 1 nil.

  (** [cardinal] *)

  Fixpoint cardinal (m : t A) : nat :=
    match m with
      | Leaf => 0%nat
      | Node l None r => (cardinal l + cardinal r)%nat
      | Node l (Some _) r => S (cardinal l + cardinal r)
    end.

  (** Specification proofs *)

  Definition MapsTo (i:key)(v:A)(m:t A) := find i m = Some v.
  Definition In (i:key)(m:t A) := exists e:A, MapsTo i e m.

  Lemma MapsTo_compat : Proper (E.eq==>eq==>eq==>iff) MapsTo.
  Proof.
   intros k k' Hk e e' He m m' Hm. red in Hk. now subst.
  Qed.

  Lemma find_spec m x e : find x m = Some e <-> MapsTo x e m.
  Proof. reflexivity. Qed.

  Lemma mem_find :
    forall m x, mem x m = match find x m with None => false | _ => true end.
  Proof.
  induction m; destruct x; simpl; auto.
  Qed.

  Lemma mem_spec : forall m x, mem x m = true <-> In x m.
  Proof.
  unfold In, MapsTo; intros m x; rewrite mem_find.
  split.
  - destruct (find x m).
    exists a; auto.
    intros; discriminate.
  - destruct 1 as (e0,H0); rewrite H0; auto.
  Qed.

  Lemma gleaf : forall (i : key), find i Leaf = None.
  Proof. destruct i; simpl; auto. Qed.

  Theorem empty_spec:
    forall (i: key), find i empty = None.
  Proof. exact gleaf. Qed.

  Lemma is_empty_spec m :
   is_empty m = true <-> forall k, find k m = None.
  Proof.
  induction m; simpl.
  - intuition. apply empty_spec.
  - destruct o. split; try discriminate.
    intros H. now specialize (H xH).
    rewrite <- andb_lazy_alt, andb_true_iff, IHm1, IHm2.
    clear IHm1 IHm2.
    split.
    + intros (H1,H2) k. destruct k; simpl; auto.
    + intros H; split; intros k. apply (H (xO k)). apply (H (xI k)).
  Qed.

  Theorem add_spec1:
    forall (m: t A) (i: key) (x: A), find i (add i x m) = Some x.
  Proof.
    intros m i; revert m.
    induction i; destruct m; simpl; auto.
  Qed.

  Theorem add_spec2:
    forall (m: t A) (i j: key) (x: A),
    i <> j -> find j (add i x m) = find j m.
  Proof.
    intros m i j; revert m i.
    induction j; destruct i, m; simpl; intros;
     rewrite ?IHj, ?gleaf; auto; try congruence.
  Qed.

  Lemma rleaf : forall (i : key), remove i Leaf = Leaf.
  Proof. destruct i; simpl; auto. Qed.

  Lemma gnode l o r i : find i (node l o r) = find i (Node l o r).
  Proof.
   destruct o,l,r; simpl; trivial.
   destruct i; simpl; now rewrite ?gleaf.
  Qed.

  Opaque node.

  Theorem remove_spec1:
    forall (m: t A)(i: key), find i (remove i m) = None.
  Proof.
    induction m; simpl.
    - intros; rewrite rleaf. apply gleaf.
    - destruct i; simpl remove; rewrite gnode; simpl; auto.
  Qed.

  Theorem remove_spec2:
    forall (m: t A)(i j: key),
    i <> j -> find j (remove i m) = find j m.
  Proof.
    induction m; simpl; intros.
    - now rewrite rleaf.
    - destruct i; simpl; rewrite gnode; destruct j; simpl; trivial;
      try apply IHm1; try apply IHm2; congruence.
  Qed.

  Local Notation InL := (InA eq_key_elt).

  Lemma xbindings_spec: forall m j acc k e,
    InL (k,e) (xbindings m j acc) <->
    InL (k,e) acc \/ exists x, k=(j@x) /\ find x m = Some e.
  Proof.
    induction m as [|l IHl o r IHr]; simpl.
    - intros. split; intro H.
      + now left.
      + destruct H as [H|[x [_ H]]]. assumption.
        now rewrite gleaf in H.
    - intros j acc k e. case o as [e'|];
      rewrite IHl, ?InA_cons, IHr; clear IHl IHr; split.
      + intros [[H|[H|H]]|H]; auto.
        * unfold eq_key_elt, E.eq, fst, snd in H. destruct H as (->,<-).
          right. now exists 1.
        * destruct H as (x,(->,H)). right. now exists x~1.
        * destruct H as (x,(->,H)). right. now exists x~0.
      + intros [H|H]; auto.
        destruct H as (x,(->,H)).
        destruct x; simpl in *.
        * left. right. right. now exists x.
        * right. now exists x.
        * left. left. injection H as ->. reflexivity.
      + intros [[H|H]|H]; auto.
        * destruct H as (x,(->,H)). right. now exists x~1.
        * destruct H as (x,(->,H)). right. now exists x~0.
      + intros [H|H]; auto.
        destruct H as (x,(->,H)).
        destruct x; simpl in *.
        * left. right. now exists x.
        * right. now exists x.
        * discriminate.
  Qed.

  Lemma lt_rev_append: forall j x y, E.lt x y -> E.lt (j@x) (j@y).
  Proof. induction j; intros; simpl; auto. Qed.

  Lemma xbindings_sort m j acc :
    sort lt_key acc ->
    (forall x p, In x m -> InL p acc -> E.lt (j@x) (fst p)) ->
    sort lt_key (xbindings m j acc).
  Proof.
    revert j acc.
    induction m as [|l IHl o r IHr]; simpl; trivial.
    intros j acc Hacc Hsacc. destruct o as [e|].
    - apply IHl;[constructor;[apply IHr; [apply Hacc|]|]|].
      + intros. now apply Hsacc.
      + case_eq (xbindings r j~1 acc); [constructor|].
        intros (z,e') q H. constructor.
        assert (H': InL (z,e') (xbindings r j~1 acc)).
        { rewrite H. now constructor. }
        clear H q. rewrite xbindings_spec in H'.
        destruct H' as [H'|H'].
        * apply (Hsacc 1 (z,e')); trivial. now exists e.
        * destruct H' as (x,(->,H)).
          red. simpl. now apply lt_rev_append.
      + intros x (y,e') Hx Hy. inversion_clear Hy.
        rewrite H. simpl. now apply lt_rev_append.
        rewrite xbindings_spec in H.
        destruct H as [H|H].
        * now apply Hsacc.
        * destruct H as (z,(->,H)). simpl.
          now apply lt_rev_append.
    - apply IHl; [apply IHr; [apply Hacc|]|].
      + intros. now apply Hsacc.
      + intros x (y,e') Hx H. rewrite xbindings_spec in H.
        destruct H as [H|H].
        * now apply Hsacc.
        * destruct H as (z,(->,H)). simpl.
          now apply lt_rev_append.
  Qed.

  Lemma bindings_spec1 m k e :
    InA eq_key_elt (k,e) (bindings m) <-> MapsTo k e m.
  Proof.
   unfold bindings, MapsTo. rewrite xbindings_spec.
   split; [ intros [H|(y & H & H')] | intros IN ].
   - inversion H.
   - simpl in *. now subst.
   - right. now exists k.
  Qed.

  Lemma bindings_spec2 m : sort lt_key (bindings m).
  Proof.
    unfold bindings.
    apply xbindings_sort. constructor. inversion 2.
  Qed.

  Lemma bindings_spec2w m : NoDupA eq_key (bindings m).
  Proof.
    apply ME.Sort_NoDupA.
    apply bindings_spec2.
  Qed.

  Lemma xbindings_length m j acc :
    length (xbindings m j acc) = (cardinal m + length acc)%nat.
  Proof.
   revert j acc.
   induction m; simpl; trivial; intros.
   destruct o; simpl; rewrite IHm1; simpl; rewrite IHm2;
    now rewrite ?Nat.add_succ_r, Nat.add_assoc.
  Qed.

  Lemma cardinal_spec m : cardinal m = length (bindings m).
  Proof.
   unfold bindings. rewrite xbindings_length. simpl.
   symmetry. apply Nat.add_0_r.
  Qed.

  (** [map] and [mapi] *)

  Variable B : Type.

  Section Mapi.

    Variable f : key -> option A -> option B.

    Fixpoint xmapi (m : t A) (i : key) : t B :=
       match m with
        | Leaf => Leaf
        | Node l o r => Node (xmapi l (i~0))
                             (f (rev i) o)
                             (xmapi r (i~1))
       end.

  End Mapi.

  Definition mapi (f : key -> A -> B) m :=
    xmapi (fun k => option_map (f k)) m 1.

  Definition map (f : A -> B) m := mapi (fun _ => f) m.

  End A.

  Lemma xgmapi:
    forall (A B: Type) (f: key -> option A -> option B) (i j : key) (m: t A),
      (forall k, f k None = None) ->
      find i (xmapi f m j) = f (j@i) (find i m).
  Proof.
  induction i; intros; destruct m; simpl; rewrite ?IHi; auto.
  Qed.

  Theorem mapi_spec0 :
    forall (A B: Type) (f: key -> A -> B) (i: key) (m: t A),
    find i (mapi f m) = option_map (f i) (find i m).
  Proof.
  intros. unfold mapi. rewrite xgmapi; simpl; auto.
  Qed.

  Lemma mapi_spec :
    forall (A B: Type) (f: key -> A -> B) (m: t A) (i:key),
    exists j, E.eq j i /\
     find i (mapi f m) = option_map (f j) (find i m).
  Proof.
   intros.
   exists i. split. reflexivity. apply mapi_spec0.
  Qed.

  Lemma map_spec :
    forall (elt elt':Type)(f:elt->elt')(m: t elt)(x:key),
    find x (map f m) = option_map f (find x m).
  Proof.
  intros; unfold map. apply mapi_spec0.
  Qed.

  Section merge.
  Variable A B C : Type.
  Variable f : key -> option A -> option B -> option C.

  Fixpoint xmerge (m1 : t A)(m2 : t B)(i:positive) : t C :=
    match m1 with
    | Leaf => xmapi (fun k => f k None) m2 i
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xmapi (fun k o => f k o None) m1 i
        | Node l2 o2 r2 =>
          Node (xmerge l1 l2 (i~0))
               (f (rev i) o1 o2)
               (xmerge r1 r2 (i~1))
        end
    end.

  Lemma xgmerge: forall (i j: key)(m1:t A)(m2: t B),
      (forall i, f i None None = None) ->
      find i (xmerge m1 m2 j) = f (j@i) (find i m1) (find i m2).
  Proof.
    induction i; intros; destruct m1; destruct m2; simpl; auto;
    rewrite ?xgmapi, ?IHi; simpl; auto.
  Qed.

  End merge.

  Definition merge {A B C}(f:key->option A->option B->option C) m1 m2 :=
   xmerge
     (fun k o1 o2 => match o1,o2 with
       | None,None => None
       | _, _ => f k o1 o2
      end)
     m1 m2 xH.

  Lemma merge_spec1 {A B C}(f:key->option A->option B->option C) :
    forall m m' x,
    In x m \/ In x m' ->
    exists y, E.eq y x /\
     find x (merge f m m') = f y (find x m) (find x m').
  Proof.
  intros. exists x. split. reflexivity.
  unfold merge.
  rewrite xgmerge; simpl; auto.
  rewrite <- 2 mem_spec, 2 mem_find in H.
  destruct (find x m); simpl; auto.
  destruct (find x m'); simpl; auto. intuition discriminate.
  Qed.

  Lemma merge_spec2 {A B C}(f:key->option A->option B->option C) :
    forall m m' x, In x (merge f m m') -> In x m \/ In x m'.
  Proof.
  intros.
  rewrite <-mem_spec, mem_find in H.
  unfold merge in H.
  rewrite xgmerge in H; simpl; auto.
  rewrite <- 2 mem_spec, 2 mem_find.
  destruct (find x m); simpl in *; auto.
  destruct (find x m'); simpl in *; auto.
  Qed.

  Section Fold.

    Variables A B : Type.
    Variable f : key -> A -> B -> B.

    (** the additional argument, [i], records the current path, in
       reverse order (this should be more efficient: we reverse this argument
       only at present nodes only, rather than at each node of the tree).
       we also use this convention in all functions below
     *)

    Fixpoint xfold (m : t A) (v : B) (i : key) :=
      match m with
        | Leaf => v
        | Node l (Some x) r =>
          xfold r (f (rev i) x (xfold l v i~0)) i~1
        | Node l None r =>
          xfold r (xfold l v i~0) i~1
      end.
    Definition fold m i := xfold m i 1.

  End Fold.

  Lemma fold_spec :
    forall {A}(m:t A){B}(i : B) (f : key -> A -> B -> B),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
  Proof.
    unfold fold, bindings. intros A m B i f. revert m i.
    set (f' := fun a p => f (fst p) (snd p) a).
    assert (H: forall m i j acc,
      fold_left f' acc (xfold f m i j) =
      fold_left f' (xbindings m j acc) i).
    { induction m as [|l IHl o r IHr]; intros; trivial.
      destruct o; simpl; now rewrite IHr, <- IHl. }
    intros. exact (H m i 1 nil).
  Qed.

  Fixpoint equal (A:Type)(cmp : A -> A -> bool)(m1 m2 : t A) : bool :=
    match m1, m2 with
      | Leaf, _ => is_empty m2
      | _, Leaf => is_empty m1
      | Node l1 o1 r1, Node l2 o2 r2 =>
           (match o1, o2 with
             | None, None => true
             | Some v1, Some v2 => cmp v1 v2
             | _, _ => false
            end)
           &&& equal cmp l1 l2 &&& equal cmp r1 r2
     end.

  Definition Equal (A:Type)(m m':t A) :=
    forall y, find y m = find y m'.
  Definition Equiv (A:Type)(eq_elt:A->A->Prop) m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
  Definition Equivb (A:Type)(cmp: A->A->bool) := Equiv (Cmp cmp).

  Lemma equal_1 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    Equivb cmp m m' -> equal cmp m m' = true.
  Proof.
  induction m.
  - (* m = Leaf *)
    destruct 1 as (E,_); simpl.
    apply is_empty_spec; intros k.
    destruct (find k m') eqn:F; trivial.
    assert (H : In k m') by now exists a.
    rewrite <- E in H.
    destruct H as (x,H). red in H. now rewrite gleaf in H.
  - (* m = Node *)
    destruct m'.
    + (* m' = Leaf *)
      destruct 1 as (E,_); simpl.
      destruct o.
      * assert (H : In xH (@Leaf A)).
        { rewrite <- E. now exists a. }
        destruct H as (e,H). now red in H.
      * apply andb_true_intro; split; apply is_empty_spec; intros k.
        destruct (find k m1) eqn:F; trivial.
        assert (H : In (xO k) (@Leaf A)).
        { rewrite <- E. exists a; auto. }
        destruct H as (x,H). red in H. now rewrite gleaf in H.
        destruct (find k m2) eqn:F; trivial.
        assert (H : In (xI k) (@Leaf A)).
        { rewrite <- E. exists a; auto. }
        destruct H as (x,H). red in H. now rewrite gleaf in H.
    + (* m' = Node *)
      destruct 1.
      assert (Equivb cmp m1 m'1).
      { split.
        intros k; generalize (H (xO k)); unfold In, MapsTo; simpl; auto.
        intros k e e'; generalize (H0 (xO k) e e'); unfold In, MapsTo; simpl; auto. }
      assert (Equivb cmp m2 m'2).
      { split.
        intros k; generalize (H (xI k)); unfold In, MapsTo; simpl; auto.
        intros k e e'; generalize (H0 (xI k) e e'); unfold In, MapsTo; simpl; auto. }
      simpl.
      destruct o; destruct o0; simpl.
      repeat (apply andb_true_intro; split); auto.
      apply (H0 xH); red; auto.
      generalize (H xH); unfold In, MapsTo; simpl; intuition.
      destruct H4; try discriminate; eauto.
      generalize (H xH); unfold In, MapsTo; simpl; intuition.
      destruct H5; try discriminate; eauto.
      apply andb_true_intro; split; auto.
  Qed.

  Lemma equal_2 : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
  induction m.
  (* m = Leaf *)
  simpl.
  split; intros.
  split.
  destruct 1; red in H0; destruct k; discriminate.
  rewrite is_empty_spec in H.
  intros (e,H'). red in H'. now rewrite H in H'.
  red in H0; destruct k; discriminate.
  (* m = Node *)
  destruct m'.
  (* m' = Leaf *)
  simpl.
  destruct o; intros; try discriminate.
  destruct (andb_prop _ _ H); clear H.
  split; intros.
  split; unfold In, MapsTo; destruct 1.
  destruct k; simpl in *; try discriminate.
  rewrite is_empty_spec in H1.
  now rewrite H1 in H.
  rewrite is_empty_spec in H0.
  now rewrite H0 in H.
  destruct k; simpl in *; discriminate.
  unfold In, MapsTo; destruct k; simpl in *; discriminate.
  (* m' = Node *)
  destruct o; destruct o0; simpl; intros; try discriminate.
  destruct (andb_prop _ _ H); clear H.
  destruct (andb_prop _ _ H0); clear H0.
  destruct (IHm1 _ _ H2); clear H2 IHm1.
  destruct (IHm2 _ _ H1); clear H1 IHm2.
  split; intros.
  destruct k; unfold In, MapsTo in *; simpl; auto.
  split; eauto.
  destruct k; unfold In, MapsTo in *; simpl in *.
  eapply H4; eauto.
  eapply H3; eauto.
  congruence.
  destruct (andb_prop _ _ H); clear H.
  destruct (IHm1 _ _ H0); clear H0 IHm1.
  destruct (IHm2 _ _ H1); clear H1 IHm2.
  split; intros.
  destruct k; unfold In, MapsTo in *; simpl; auto.
  split; eauto.
  destruct k; unfold In, MapsTo in *; simpl in *.
  eapply H3; eauto.
  eapply H2; eauto.
  try discriminate.
  Qed.

  Lemma equal_spec : forall (A:Type)(m m':t A)(cmp:A->A->bool),
    equal cmp m m' = true <-> Equivb cmp m m'.
  Proof.
    split. apply equal_2. apply equal_1.
  Qed.

End PositiveMap.

(** Here come some additional facts about this implementation.
  Most are facts that cannot be derivable from the general interface. *)

Module PositiveMapAdditionalFacts.
  Import PositiveMap.

  (* Derivable from the Map interface *)
  Theorem gsspec {A} i j x (m: t A) :
    find i (add j x m) = if E.eq_dec i j then Some x else find i m.
  Proof.
    destruct (E.eq_dec i j) as [->|];
    [ apply add_spec1 | apply add_spec2; auto ].
  Qed.

   (* Not derivable from the Map interface *)
  Theorem gsident {A} i (m:t A) v :
    find i m = Some v -> add i v m = m.
  Proof.
    revert m.
    induction i; destruct m; simpl in *; try congruence.
    - intro H; now rewrite (IHi m2 H).
    - intro H; now rewrite (IHi m1 H).
  Qed.

  Lemma xmapi_ext {A B}(f g: key -> option A -> option B) :
    (forall k (o : option A), f k o = g k o) ->
    forall m i, xmapi f m i = xmapi g m i.
  Proof.
    induction m; intros; simpl; auto. now f_equal.
  Qed.

  Theorem xmerge_commut{A B C}
    (f: key -> option A -> option B -> option C)
    (g: key -> option B -> option A -> option C) :
    (forall k o1 o2, f k o1 o2 = g k o2 o1) ->
    forall m1 m2 i, xmerge f m1 m2 i = xmerge g m2 m1 i.
  Proof.
    intros E.
    induction m1; destruct m2; intros i; simpl; trivial; f_equal;
    try apply IHm1_1; try apply IHm1_2; try apply xmapi_ext;
    intros; apply E.
  Qed.

  Theorem merge_commut{A B C}
    (f: key -> option A -> option B -> option C)
    (g: key -> option B -> option A -> option C) :
    (forall k o1 o2, f k o1 o2 = g k o2 o1) ->
    forall m1 m2, merge f m1 m2 = merge g m2 m1.
  Proof.
    intros E m1 m2.
    unfold merge. apply xmerge_commut.
    intros k [x1|] [x2|]; trivial.
  Qed.

End PositiveMapAdditionalFacts.

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Efficient implementation of [MSetInterface.S] for positive keys,
    inspired from the [FMapPositive] module.

   This module was adapted by Alexandre Ren, Damien Pous, and Thomas
   Braibant (2010, LIG, CNRS, UMR 5217), from the [FMapPositive]
   module of Pierre Letouzey and Jean-Christophe Filliâtre, which in
   turn comes from the [FMap] framework of a work by Xavier Leroy and
   Sandrine Blazy (used for building certified compilers).
*)

Require Import Bool BinPos Orders OrdersEx MSetInterface.

Set Implicit Arguments.
Local Open Scope lazy_bool_scope.
Local Open Scope positive_scope.
Local Unset Elimination Schemes.

Module PositiveSet <: S with Module E:=PositiveOrderedTypeBits.

  Module E:=PositiveOrderedTypeBits.

  Definition elt := positive : Type.

  Inductive tree :=
    | Leaf : tree
    | Node : tree -> bool -> tree -> tree.

  Scheme tree_ind := Induction for tree Sort Prop.

  Definition t := tree : Type.

  Definition empty : t := Leaf.

  Fixpoint is_empty (m : t) : bool :=
   match m with
    | Leaf => true
    | Node l b r => negb b &&& is_empty l &&& is_empty r
   end.

  Fixpoint mem (i : positive) (m : t) {struct m} : bool :=
    match m with
    | Leaf => false
    | Node l o r =>
        match i with
        | 1 => o
        | i~0 => mem i l
        | i~1 => mem i r
        end
    end.

  Fixpoint add (i : positive) (m : t) : t :=
    match m with
    | Leaf =>
        match i with
        | 1 => Node Leaf true Leaf
        | i~0 => Node (add i Leaf) false Leaf
        | i~1 => Node Leaf false (add i Leaf)
        end
    | Node l o r =>
        match i with
        | 1 => Node l true r
        | i~0 => Node (add i l) o r
        | i~1 => Node l o (add i r)
        end
    end.

  Definition singleton i := add i empty.

  (** helper function to avoid creating empty trees that are not leaves *)

  Definition node (l : t) (b: bool) (r : t) : t :=
    if b then Node l b r else
     match l,r with
       | Leaf,Leaf => Leaf
       | _,_ => Node l false r end.

  Fixpoint remove (i : positive) (m : t) {struct m} : t :=
    match m with
      | Leaf => Leaf
      | Node l o r =>
        match i with
          | 1 => node l false r
          | i~0 => node (remove i l) o r
          | i~1 => node l o (remove i r)
        end
    end.

  Fixpoint union (m m': t) : t :=
    match m with
      | Leaf => m'
      | Node l o r =>
        match m' with
          | Leaf => m
          | Node l' o' r' => Node (union l l') (o||o') (union r r')
        end
    end.

  Fixpoint inter (m m': t) : t :=
    match m with
      | Leaf => Leaf
      | Node l o r =>
        match m' with
          | Leaf => Leaf
          | Node l' o' r' => node (inter l l') (o&&o') (inter r r')
        end
    end.

  Fixpoint diff (m m': t) : t :=
    match m with
      | Leaf => Leaf
      | Node l o r =>
        match m' with
          | Leaf => m
          | Node l' o' r' => node (diff l l') (o&&negb o') (diff r r')
        end
    end.

  Fixpoint equal (m m': t): bool :=
    match m with
      | Leaf => is_empty m'
      | Node l o r =>
        match m' with
          | Leaf => is_empty m
          | Node l' o' r' => eqb o o' &&& equal l l' &&& equal r r'
        end
    end.

  Fixpoint subset (m m': t): bool :=
    match m with
      | Leaf => true
      | Node l o r =>
        match m' with
          | Leaf => is_empty m
          | Node l' o' r' => (negb o ||| o') &&& subset l l' &&& subset r r'
        end
    end.

  (** reverses [y] and concatenate it with [x] *)

  Fixpoint rev_append (y x : elt) : elt :=
    match y with
      | 1 => x
      | y~1 => rev_append y x~1
      | y~0 => rev_append y x~0
    end.
  Infix "@" := rev_append (at level 60).
  Definition rev x := x@1.

  Section Fold.

    Variables B : Type.
    Variable f : positive -> B -> B.

    (** the additional argument, [i], records the current path, in
       reverse order (this should be more efficient: we reverse this argument
       only at present nodes only, rather than at each node of the tree).
       we also use this convention in all functions below
     *)

    Fixpoint xfold (m : t) (v : B) (i : positive) :=
      match m with
        | Leaf => v
        | Node l true r =>
          xfold r (f (rev i) (xfold l v i~0)) i~1
        | Node l false r =>
          xfold r (xfold l v i~0) i~1
      end.
    Definition fold m i := xfold m i 1.

  End Fold.

  Section Quantifiers.

    Variable f : positive -> bool.

    Fixpoint xforall (m : t) (i : positive) :=
      match m with
        | Leaf => true
        | Node l o r =>
          (negb o ||| f (rev i)) &&& xforall r i~1 &&& xforall l i~0
      end.
    Definition for_all m := xforall m 1.

    Fixpoint xexists (m : t) (i : positive) :=
      match m with
        | Leaf => false
        | Node l o r => (o &&& f (rev i)) ||| xexists r i~1 ||| xexists l i~0
      end.
    Definition exists_ m := xexists m 1.

    Fixpoint xfilter (m : t) (i : positive) : t :=
      match m with
        | Leaf => Leaf
        | Node l o r => node (xfilter l i~0) (o &&& f (rev i)) (xfilter r i~1)
      end.
    Definition filter m := xfilter m 1.

    Fixpoint xpartition (m : t) (i : positive) : t * t :=
      match m with
        | Leaf => (Leaf,Leaf)
        | Node l o r =>
          let (lt,lf) := xpartition l i~0 in
          let (rt,rf) := xpartition r i~1 in
             if o then
               let fi := f (rev i) in
                 (node lt fi rt, node lf (negb fi) rf)
             else
                 (node lt false rt, node lf false rf)
      end.
    Definition partition m := xpartition m 1.

  End Quantifiers.

  (** uses [a] to accumulate values rather than doing a lot of concatenations *)

  Fixpoint xelements (m : t) (i : positive) (a: list positive) :=
    match m with
      | Leaf => a
      | Node l false r => xelements l i~0 (xelements r i~1 a)
      | Node l true r => xelements l i~0 (rev i :: xelements r i~1 a)
    end.

  Definition elements (m : t) := xelements m 1 nil.

  Fixpoint cardinal (m : t) : nat :=
    match m with
      | Leaf => O
      | Node l false r => (cardinal l + cardinal r)%nat
      | Node l true r => S (cardinal l + cardinal r)
    end.

  (** would it be more efficient to use a path like in the above functions ? *)

  Fixpoint choose (m: t) : option elt :=
    match m with
      | Leaf => None
      | Node l o r => if o then Some 1 else
        match choose l with
          | None => option_map xI (choose r)
          | Some i => Some i~0
        end
    end.

  Fixpoint min_elt (m: t) : option elt :=
    match m with
      | Leaf => None
      | Node l o r =>
        match min_elt l with
          | None => if o then Some 1 else option_map xI (min_elt r)
          | Some i => Some i~0
        end
    end.

  Fixpoint max_elt (m: t) : option elt :=
    match m with
      | Leaf => None
      | Node l o r =>
        match max_elt r with
          | None => if o then Some 1 else option_map xO (max_elt l)
          | Some i => Some i~1
        end
    end.

  (** lexicographic product, defined using a notation to keep things lazy *)

  Notation lex u v := match u with Eq => v | Lt => Lt | Gt => Gt end.

  Definition compare_bool a b :=
    match a,b with
      | false, true => Lt
      | true, false => Gt
      | _,_ => Eq
    end.

  Fixpoint compare (m m': t): comparison :=
    match m,m' with
      | Leaf,_ => if is_empty m' then Eq else Lt
      | _,Leaf => if is_empty m then Eq else Gt
      | Node l o r,Node l' o' r' =>
        lex (compare_bool o o') (lex (compare l l') (compare r r'))
    end.


  Definition In i t := mem i t = true.
  Definition Equal s s' := forall a : elt, In a  s <-> In a  s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Notation "s  [=]  t" := (Equal s t) (at level 70, no associativity).
  Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).

  Definition eq := Equal.
  Definition lt m m' := compare m m' = Lt.

  (** Specification of [In] *)

  Instance In_compat : Proper (E.eq==>Logic.eq==>iff) In.
  Proof.
   intros s s' Hs x x' Hx. rewrite Hs, Hx; intuition.
  Qed.

  (** Specification of [eq] *)

  Local Instance eq_equiv : Equivalence eq.
  Proof. firstorder. Qed.

  (** Specification of [mem] *)

  Lemma mem_spec: forall s x, mem x s = true <-> In x s.
  Proof. unfold In. intuition. Qed.

  (** Additional lemmas for mem  *)

  Lemma mem_Leaf: forall x, mem x Leaf = false.
  Proof. destruct x; trivial. Qed.

  (** Specification of [empty] *)

  Lemma empty_spec : Empty empty.
  Proof. unfold Empty, In. intro. rewrite mem_Leaf. discriminate. Qed.

  (** Specification of node  *)

  Lemma mem_node: forall x l o r, mem x (node l o r) = mem x (Node l o r).
  Proof.
    intros x l o r.
    case o; trivial.
    destruct l; trivial.
    destruct r; trivial.
    destruct x; reflexivity.
  Qed.
  Local Opaque node.

  (** Specification of [is_empty] *)

  Lemma is_empty_spec: forall s, is_empty s = true <-> Empty s.
  Proof.
    unfold Empty, In.
    induction s as [|l IHl o r IHr]; simpl.
      firstorder.
      rewrite <- 2andb_lazy_alt, 2andb_true_iff, IHl, IHr. clear IHl IHr.
      destruct o; simpl; split.
        intuition discriminate.
        intro H. elim (H 1). reflexivity.
        intros H [a|a|]; apply H || intro; discriminate.
        intro H. split. split. reflexivity.
          intro a. apply (H a~0).
          intro a. apply (H a~1).
  Qed.

  (** Specification of [subset] *)

  Lemma subset_Leaf_s: forall s, Leaf [<=] s.
  Proof. intros s i Hi. apply empty_spec in Hi. elim Hi. Qed.

  Lemma subset_spec: forall s s', subset s s' = true <-> s [<=] s'.
  Proof.
    induction s as [|l IHl o r IHr]; intros [|l' o' r']; simpl.
      split; intros. apply subset_Leaf_s. reflexivity.

      split; intros. apply subset_Leaf_s. reflexivity.

      rewrite <- 2andb_lazy_alt, 2andb_true_iff, 2is_empty_spec.
      destruct o; simpl.
        split.
          intuition discriminate.
          intro H. elim (@empty_spec 1). apply H. reflexivity.
        split; intro H.
          destruct H as [[_ Hl] Hr].
          intros [i|i|] Hi.
            elim (Hr i Hi).
            elim (Hl i Hi).
            discriminate.
          split. split. reflexivity.
          unfold Empty. intros a H1. apply (@empty_spec (a~0)), H. assumption.
          unfold Empty. intros a H1. apply (@empty_spec (a~1)), H. assumption.

      rewrite <- 2andb_lazy_alt, 2andb_true_iff, IHl, IHr. clear.
      destruct o; simpl.
       split; intro H.
         destruct H as [[Ho' Hl] Hr]. rewrite Ho'.
          intros i Hi. destruct i.
            apply (Hr i). assumption.
            apply (Hl i). assumption.
            assumption.
         split. split.
          destruct o'; trivial.
          specialize (H 1). unfold In in H. simpl in H. apply H. reflexivity.
          intros i Hi. apply (H i~0). apply Hi.
          intros i Hi. apply (H i~1). apply Hi.
       split; intros.
         intros i Hi. destruct i; destruct H as [[H Hl] Hr].
           apply (Hr i). assumption.
           apply (Hl i). assumption.
            discriminate Hi.
         split. split. reflexivity.
           intros i Hi. apply (H i~0). apply Hi.
           intros i Hi. apply (H i~1). apply Hi.
  Qed.

  (** Specification of [equal] (via subset) *)

  Lemma equal_subset: forall s s', equal s s' = subset s s' && subset s' s.
  Proof.
    induction s as [|l IHl o r IHr]; intros [|l' o' r']; simpl; trivial.
      destruct o. reflexivity. rewrite andb_comm. reflexivity.
      rewrite <- 6andb_lazy_alt. rewrite eq_iff_eq_true.
       rewrite 7andb_true_iff, eqb_true_iff.
      rewrite IHl, IHr, 2andb_true_iff. clear IHl IHr. intuition subst.
       destruct o'; reflexivity.
       destruct o'; reflexivity.
       destruct o; auto. destruct o'; trivial.
  Qed.

  Lemma equal_spec: forall s s', equal s s' = true <-> Equal s s'.
  Proof.
    intros. rewrite equal_subset. rewrite andb_true_iff.
    rewrite 2subset_spec. unfold Equal, Subset. firstorder.
  Qed.

  Lemma eq_dec : forall s s', { eq s s' } + { ~ eq s s' }.
  Proof.
    unfold eq.
    intros. case_eq (equal s s'); intro H.
     left. apply equal_spec, H.
     right. rewrite <- equal_spec. congruence.
  Defined.

  (** (Specified) definition of [compare] *)

  Lemma lex_Opp: forall u v u' v', u = CompOpp u' -> v = CompOpp v' ->
    lex u v = CompOpp (lex u' v').
  Proof. intros ? ? u' ? -> ->. case u'; reflexivity. Qed.

  Lemma compare_bool_inv: forall b b',
    compare_bool b b' = CompOpp (compare_bool b' b).
  Proof. intros [|] [|]; reflexivity. Qed.

  Lemma compare_inv: forall s s', compare s s' = CompOpp (compare s' s).
  Proof.
    induction s as [|l IHl o r IHr]; destruct s' as [|l' o' r']; trivial.
    unfold compare. case is_empty; reflexivity.
    unfold compare. case is_empty; reflexivity.
    simpl. rewrite compare_bool_inv.
     case compare_bool; simpl; trivial; apply lex_Opp; auto.
  Qed.

  Lemma lex_Eq: forall u v, lex u v = Eq <-> u=Eq /\ v=Eq.
  Proof. intros u v; destruct u; intuition discriminate. Qed.

  Lemma compare_bool_Eq: forall b1 b2,
    compare_bool b1 b2 = Eq <-> eqb b1 b2 = true.
  Proof. intros [|] [|]; intuition discriminate. Qed.

  Lemma compare_equal: forall s s', compare s s' = Eq <-> equal s s' = true.
  Proof.
    induction s as [|l IHl o r IHr]; destruct s' as [|l' o' r'].
     simpl. tauto.
     unfold compare, equal. case is_empty; intuition discriminate.
     unfold compare, equal. case is_empty; intuition discriminate.
     simpl. rewrite <- 2andb_lazy_alt, 2andb_true_iff.
     rewrite <- IHl, <- IHr, <- compare_bool_Eq. clear IHl IHr.
     rewrite and_assoc. rewrite <- 2lex_Eq. reflexivity.
  Qed.


  Lemma compare_gt: forall s s', compare s s' = Gt -> lt s' s.
  Proof.
    unfold lt. intros s s'. rewrite compare_inv.
     case compare; trivial; intros; discriminate.
  Qed.

  Lemma compare_eq: forall s s', compare s s' = Eq -> eq s s'.
  Proof.
    unfold eq. intros s s'. rewrite compare_equal, equal_spec. trivial.
  Qed.

  Lemma compare_spec : forall s s' : t, CompSpec eq lt s s' (compare s s').
  Proof.
    intros. case_eq (compare s s'); intro H; constructor.
    apply compare_eq, H.
    assumption.
    apply compare_gt, H.
  Qed.

  Section lt_spec.

  Inductive ct: comparison -> comparison -> comparison -> Prop :=
  | ct_xxx: forall x, ct x  x  x
  | ct_xex: forall x, ct x  Eq x
  | ct_exx: forall x, ct Eq x  x
  | ct_glx: forall x, ct Gt Lt x
  | ct_lgx: forall x, ct Lt Gt x.

  Lemma ct_cxe: forall x, ct (CompOpp x) x Eq.
  Proof. destruct x; constructor. Qed.

  Lemma ct_xce: forall x, ct x (CompOpp x) Eq.
  Proof. destruct x; constructor. Qed.

  Lemma ct_lxl: forall x, ct Lt x Lt.
  Proof. destruct x; constructor. Qed.

  Lemma ct_gxg: forall x, ct Gt x Gt.
  Proof. destruct x; constructor. Qed.

  Lemma ct_xll: forall x, ct x Lt Lt.
  Proof. destruct x; constructor. Qed.

  Lemma ct_xgg: forall x, ct x Gt Gt.
  Proof. destruct x; constructor. Qed.

  Local Hint Constructors ct: ct.
  Local Hint Resolve ct_cxe ct_xce ct_lxl ct_xll ct_gxg ct_xgg: ct.
  Ltac ct := trivial with ct.

  Lemma ct_lex: forall u v w u' v' w',
    ct u v w -> ct u' v' w' -> ct (lex u u') (lex v v') (lex w w').
  Proof.
    intros u v w u' v' w' H H'.
    inversion_clear H; inversion_clear H'; ct; destruct w; ct; destruct w'; ct.
  Qed.

  Lemma ct_compare_bool:
    forall a b c, ct (compare_bool a b) (compare_bool b c) (compare_bool a c).
  Proof.
    intros [|] [|] [|]; constructor.
  Qed.

  Lemma compare_x_Leaf: forall s,
    compare s Leaf = if is_empty s then Eq else Gt.
  Proof.
    intros. rewrite compare_inv. simpl. case (is_empty s); reflexivity.
  Qed.

  Lemma compare_empty_x: forall a, is_empty a = true ->
    forall b, compare a b = if is_empty b then Eq else Lt.
  Proof.
    induction a as [|l IHl o r IHr]; trivial.
    destruct o. intro; discriminate.
    simpl is_empty. rewrite <- andb_lazy_alt, andb_true_iff.
    intros [Hl Hr].
    destruct b as [|l' [|] r']; simpl compare; trivial.
     rewrite Hl, Hr. trivial.
     rewrite (IHl Hl), (IHr Hr). simpl.
     case (is_empty l'); case (is_empty r'); trivial.
  Qed.

  Lemma compare_x_empty: forall a, is_empty a = true ->
    forall b, compare b a = if is_empty b then Eq else Gt.
  Proof.
    setoid_rewrite <- compare_x_Leaf.
    intros. rewrite 2(compare_inv b), (compare_empty_x _ H). reflexivity.
  Qed.

  Lemma ct_compare:
    forall a b c, ct (compare a b) (compare b c) (compare a c).
  Proof.
    induction a as [|l IHl o r IHr]; intros s' s''.
     destruct s' as [|l' o' r']; destruct s'' as [|l'' o'' r'']; ct.
      rewrite compare_inv. ct.
      unfold compare at 1. case_eq (is_empty (Node l' o' r')); intro H'.
       rewrite (compare_empty_x _ H'). ct.
       unfold compare at 2. case_eq (is_empty (Node l'' o'' r'')); intro H''.
        rewrite (compare_x_empty _ H''), H'. ct.
        ct.

     destruct s' as [|l' o' r']; destruct s'' as [|l'' o'' r''].
      ct.
      unfold compare at 2. rewrite compare_x_Leaf.
      case_eq (is_empty (Node l o r)); intro H.
       rewrite (compare_empty_x _ H). ct.
       case_eq (is_empty (Node l'' o'' r'')); intro H''.
        rewrite (compare_x_empty _ H''), H. ct.
        ct.

      rewrite 2 compare_x_Leaf.
      case_eq (is_empty (Node l o r)); intro H.
       rewrite compare_inv, (compare_x_empty _ H). ct.
       case_eq (is_empty (Node l' o' r')); intro H'.
        rewrite (compare_x_empty _ H'), H. ct.
        ct.

      simpl compare. apply ct_lex. apply ct_compare_bool.
       apply ct_lex; trivial.
  Qed.

  End lt_spec.

  Instance lt_strorder : StrictOrder lt.
  Proof.
   unfold lt. split.
   intros x H.
   assert (compare x x = Eq).
    apply compare_equal, equal_spec. reflexivity.
   congruence.
   intros a b c. assert (H := ct_compare a b c).
    inversion_clear H; trivial; intros; discriminate.
  Qed.

  Local Instance compare_compat_1 : Proper (eq==>Logic.eq==>Logic.eq) compare.
  Proof.
   intros x x' Hx y y' Hy. subst y'.
   unfold eq in *. rewrite <- equal_spec, <- compare_equal in *.
   assert (C:=ct_compare x x' y). rewrite Hx in C. inversion C; auto.
  Qed.

  Instance compare_compat : Proper (eq==>eq==>Logic.eq) compare.
  Proof.
   intros x x' Hx y y' Hy. rewrite Hx.
   rewrite compare_inv, Hy, <- compare_inv. reflexivity.
  Qed.

  Local Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
   intros x x' Hx y y' Hy. unfold lt. rewrite Hx, Hy. intuition.
  Qed.

  (** Specification of [add] *)

  Lemma add_spec: forall s x y, In y (add x s) <-> y=x \/ In y s.
  Proof.
    unfold In. intros s x y; revert x y s.
    induction x; intros [y|y|] [|l o r]; simpl mem;
    try (rewrite IHx; clear IHx); rewrite ?mem_Leaf; intuition congruence.
  Qed.

  (** Specification of [remove] *)

  Lemma remove_spec: forall s x y, In y (remove x s) <-> In y s /\ y<>x.
  Proof.
    unfold In. intros s x y; revert x y s.
    induction x; intros [y|y|] [|l o r]; simpl remove; rewrite ?mem_node;
     simpl mem; try (rewrite IHx; clear IHx); rewrite ?mem_Leaf;
     intuition congruence.
  Qed.

  (** Specification of [singleton] *)

  Lemma singleton_spec : forall x y, In y (singleton x) <-> y=x.
  Proof.
    unfold singleton. intros x y. rewrite add_spec. intuition.
    unfold In in *. rewrite mem_Leaf in *. discriminate.
  Qed.

  (** Specification of [union] *)

  Lemma union_spec: forall s s' x, In x (union s s') <-> In x s \/ In x s'.
  Proof.
    unfold In. intros s s' x; revert x s s'.
    induction x; destruct s; destruct s'; simpl union; simpl mem;
      try (rewrite IHx; clear IHx); try intuition congruence.
      apply orb_true_iff.
  Qed.

  (** Specification of [inter] *)

  Lemma inter_spec: forall s s' x, In x (inter s s') <-> In x s /\ In x s'.
  Proof.
    unfold In. intros s s' x; revert x s s'.
    induction x; destruct s; destruct s'; simpl inter; rewrite ?mem_node;
     simpl mem; try (rewrite IHx; clear IHx); try intuition congruence.
     apply andb_true_iff.
  Qed.

  (** Specification of [diff] *)

  Lemma diff_spec: forall s s' x, In x (diff s s') <-> In x s /\ ~ In x s'.
  Proof.
    unfold In. intros s s' x; revert x s s'.
    induction x; destruct s; destruct s' as [|l' o' r']; simpl diff;
     rewrite ?mem_node; simpl mem;
      try (rewrite IHx; clear IHx); try intuition congruence.
      rewrite andb_true_iff. destruct o'; intuition discriminate.
  Qed.

  (** Specification of [fold] *)

  Lemma fold_spec: forall s (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof.
    unfold fold, elements. intros s A i f. revert s i.
    set (f' := fun a e => f e a).
    assert (H: forall s i j acc,
      fold_left f' acc (xfold f s i j) =
      fold_left f' (xelements s j acc) i).

    induction s as [|l IHl o r IHr]; intros; trivial.
      destruct o; simpl xelements; simpl xfold.
        rewrite IHr, <- IHl. reflexivity.
        rewrite IHr. apply IHl.

    intros. exact (H s i 1 nil).
  Qed.

  (** Specification of [cardinal] *)

  Lemma cardinal_spec: forall s, cardinal s = length (elements s).
  Proof.
    unfold elements.
    assert (H: forall s j acc,
                (cardinal s + length acc)%nat = length (xelements s j acc)).

    induction s as [|l IHl b r IHr]; intros j acc; simpl; trivial. destruct b.
      rewrite <- IHl. simpl. rewrite <- IHr.
       rewrite <- plus_n_Sm, Plus.plus_assoc. reflexivity.
      rewrite <- IHl, <- IHr. rewrite Plus.plus_assoc. reflexivity.

    intros. rewrite <- H. simpl. rewrite Plus.plus_comm. reflexivity.
  Qed.

  (** Specification of [filter] *)

  Lemma xfilter_spec: forall f s x i,
    In x (xfilter f s i) <-> In x s /\ f (i@x) = true.
  Proof.
    intro f. unfold In.
    induction s as [|l IHl o r IHr]; intros x i; simpl xfilter.
     rewrite mem_Leaf. intuition discriminate.
     rewrite mem_node. destruct x; simpl.
       rewrite IHr. reflexivity.
       rewrite IHl. reflexivity.
       rewrite <- andb_lazy_alt. apply andb_true_iff.
  Qed.

  Lemma filter_spec: forall s x f, @compat_bool elt E.eq f ->
    (In x (filter f s) <-> In x s /\ f x = true).
  Proof. intros. apply xfilter_spec. Qed.

  (** Specification of [for_all] *)

  Lemma xforall_spec: forall f s i,
    xforall f s i = true <-> For_all (fun x => f (i@x) = true) s.
  Proof.
    unfold For_all, In. intro f.
    induction s as [|l IHl o r IHr]; intros i; simpl.
    intuition discriminate.
     rewrite <- 2andb_lazy_alt, <- orb_lazy_alt, 2 andb_true_iff.
     rewrite IHl, IHr. clear IHl IHr.
      split.
       intros [[Hi Hr] Hl] x. destruct x; simpl; intro H.
        apply Hr, H.
        apply Hl, H.
        rewrite H in Hi. assumption.
       intro H; intuition.
        specialize (H 1). destruct o. apply H. reflexivity. reflexivity.
        apply H. assumption.
        apply H. assumption.
  Qed.

  Lemma for_all_spec: forall s f, @compat_bool elt E.eq f ->
    (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof. intros. apply xforall_spec. Qed.

  (** Specification of [exists] *)

  Lemma xexists_spec: forall f s i,
    xexists f s i = true <-> Exists (fun x => f (i@x) = true) s.
  Proof.
    unfold Exists, In. intro f.
    induction s as [|l IHl o r IHr]; intros i; simpl.
     firstorder.
     rewrite <- 2orb_lazy_alt, 2orb_true_iff, <- andb_lazy_alt, andb_true_iff.
     rewrite IHl, IHr. clear IHl IHr.
      split.
       intros [[Hi|[x Hr]]|[x Hl]].
        exists 1. exact Hi.
        exists x~1. exact Hr.
        exists x~0. exact Hl.
       intros [[x|x|] H]; eauto.
  Qed.

  Lemma exists_spec : forall s f, @compat_bool elt E.eq f ->
    (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof. intros. apply xexists_spec. Qed.


  (** Specification of [partition] *)

  Lemma partition_filter : forall s f,
    partition f s = (filter f s, filter (fun x => negb (f x)) s).
  Proof.
    unfold partition, filter. intros s f. generalize 1 as j.
    induction s as [|l IHl o r IHr]; intro j.
      reflexivity.
      destruct o; simpl; rewrite IHl, IHr; reflexivity.
  Qed.

  Lemma partition_spec1 : forall s f, @compat_bool elt E.eq f ->
      Equal (fst (partition f s)) (filter f s).
  Proof. intros. rewrite partition_filter. reflexivity. Qed.

  Lemma partition_spec2 : forall s f, @compat_bool elt E.eq f ->
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof. intros. rewrite partition_filter. reflexivity. Qed.


  (** Specification of [elements] *)

  Notation InL := (InA E.eq).

  Lemma xelements_spec: forall s j acc y,
    InL y (xelements s j acc)
    <->
    InL y acc \/ exists x, y=(j@x) /\ mem x s = true.
  Proof.
    induction s as [|l IHl o r IHr]; simpl.
      intros. split; intro H.
        left. assumption.
        destruct H as [H|[x [Hx Hx']]]. assumption. discriminate.

      intros j acc y. case o.
        rewrite IHl. rewrite InA_cons. rewrite IHr. clear IHl IHr. split.
          intros [[H|[H|[x [-> H]]]]|[x [-> H]]]; eauto.
            right. exists x~1. auto.
            right. exists x~0. auto.
          intros [H|[x [-> H]]].
            eauto.
            destruct x.
              left. right. right. exists x; auto.
              right. exists x; auto.
              left. left. reflexivity.

        rewrite IHl, IHr. clear IHl IHr. split.
          intros [[H|[x [-> H]]]|[x [-> H]]].
            eauto.
            right. exists x~1. auto.
            right. exists x~0. auto.
          intros [H|[x [-> H]]].
            eauto.
            destruct x.
              left. right.  exists x; auto.
              right. exists x; auto.
              discriminate.
  Qed.

  Lemma elements_spec1: forall s x, InL x (elements s) <-> In x s.
  Proof.
   unfold elements. intros. rewrite xelements_spec.
   split; [ intros [A|(y & B & C)] | intros IN ].
   inversion A. simpl in *. congruence.
   right. exists x. auto.
  Qed.

  Lemma lt_rev_append: forall j x y, E.lt x y -> E.lt (j@x) (j@y).
  Proof. induction j; intros; simpl; auto. Qed.

  Lemma elements_spec2: forall s, sort E.lt (elements s).
  Proof.
    unfold elements.
    assert (H: forall s j acc,
      sort E.lt acc ->
      (forall x y, In x s ->  InL y acc -> E.lt (j@x) y) ->
      sort E.lt (xelements s j acc)).

    induction s as [|l IHl o r IHr]; simpl; trivial.
    intros j acc Hacc Hsacc. destruct o.
      apply IHl. constructor.
       apply IHr. apply Hacc.
       intros x y Hx Hy. apply Hsacc; assumption.
       case_eq (xelements r j~1 acc). constructor.
       intros z q H. constructor.
       assert (H': InL z (xelements r j~1 acc)).
        rewrite H. constructor. reflexivity.
       clear H q. rewrite xelements_spec in H'. destruct H' as [Hy|[x [-> Hx]]].
         apply (Hsacc 1 z); trivial. reflexivity.
         simpl. apply lt_rev_append. exact I.
       intros x y Hx Hy. inversion_clear Hy.
         rewrite H. simpl. apply lt_rev_append. exact I.
         rewrite xelements_spec in H. destruct H as [Hy|[z [-> Hy]]].
           apply Hsacc; assumption.
           simpl. apply lt_rev_append. exact I.

      apply IHl. apply IHr. apply Hacc.
       intros x y Hx Hy. apply Hsacc; assumption.
       intros x y Hx Hy. rewrite xelements_spec in Hy.
        destruct Hy as [Hy|[z [-> Hy]]].
         apply Hsacc; assumption.
         simpl. apply lt_rev_append. exact I.

    intros. apply H. constructor.
      intros x y _ H'. inversion H'.
  Qed.

  Lemma elements_spec2w: forall s, NoDupA E.eq (elements s).
  Proof.
    intro. apply SortA_NoDupA with E.lt; auto with *.
    apply elements_spec2.
  Qed.


  (** Specification of [choose] *)

  Lemma choose_spec1: forall s x, choose s = Some x -> In x s.
  Proof.
    induction s as [| l IHl o r IHr]; simpl.
      intros. discriminate.
      destruct o.
        intros x H. injection H; intros; subst. reflexivity.
        revert IHl. case choose.
          intros p Hp x H. injection H as <-. apply Hp.
           reflexivity.
          intros _ x. revert IHr. case choose.
            intros p Hp H. injection H as <-. apply Hp.
            reflexivity.
            intros. discriminate.
  Qed.

  Lemma choose_spec2: forall s, choose s = None -> Empty s.
  Proof.
    unfold Empty, In. intros s H.
    induction s as [|l IHl o r IHr].
      intro. apply empty_spec.
      destruct o.
        discriminate.
        simpl in H. destruct (choose l).
          discriminate.
          destruct (choose r).
            discriminate.
            intros [a|a|].
              apply IHr. reflexivity.
              apply IHl. reflexivity.
              discriminate.
  Qed.

  Lemma choose_empty: forall s, is_empty s = true -> choose s = None.
  Proof.
    intros s Hs. case_eq (choose s); trivial.
    intros p Hp. apply choose_spec1 in Hp. apply is_empty_spec in Hs.
     elim (Hs _ Hp).
  Qed.

  Lemma choose_spec3': forall s s', Equal s s' -> choose s = choose s'.
  Proof.
    setoid_rewrite <- equal_spec.
    induction s as [|l IHl o r IHr].
      intros. symmetry. apply choose_empty. assumption.

      destruct s' as [|l' o' r'].
        generalize (Node l o r) as s. simpl. intros. apply choose_empty.
        rewrite equal_spec in H. symmetry in H. rewrite <- equal_spec in H.
        assumption.

        simpl. rewrite <- 2andb_lazy_alt, 2andb_true_iff, eqb_true_iff.
        intros [[<- Hl] Hr]. rewrite (IHl _ Hl), (IHr _ Hr). reflexivity.
  Qed.

  Lemma choose_spec3: forall s s' x y,
    choose s = Some x -> choose s' = Some y -> Equal s s' -> E.eq x y.
  Proof. intros s s' x y Hx Hy H. apply choose_spec3' in H. congruence. Qed.


  (** Specification of [min_elt] *)

  Lemma min_elt_spec1: forall s x, min_elt s = Some x -> In x s.
  Proof.
   unfold In.
   induction s as [| l IHl o r IHr]; simpl.
     intros. discriminate.
     intros x. destruct (min_elt l); intros.
       injection H as <-. apply IHl. reflexivity.
       destruct o; simpl.
         injection H as <-. reflexivity.
         destruct (min_elt r); simpl in *.
           injection H as <-. apply IHr. reflexivity.
           discriminate.
  Qed.

  Lemma min_elt_spec3: forall s, min_elt s = None -> Empty s.
  Proof.
    unfold Empty, In. intros s H.
    induction s as [|l IHl o r IHr].
      intro. apply empty_spec.
      intros [a|a|].
        apply IHr. revert H. clear. simpl. destruct (min_elt r); trivial.
          case min_elt; intros; try discriminate. destruct o; discriminate.
        apply IHl. revert H. clear. simpl. destruct (min_elt l); trivial.
         intro; discriminate.
        revert H. clear. simpl. case min_elt; intros; try discriminate.
         destruct o; discriminate.
  Qed.

  Lemma min_elt_spec2: forall s x y, min_elt s = Some x -> In y s -> ~ E.lt y x.
  Proof.
    unfold In.
    induction s as [|l IHl o r IHr]; intros x y H H'.
      discriminate.
      simpl in H. case_eq (min_elt l).
        intros p Hp. rewrite Hp in H. injection H as <-.
        destruct y as [z|z|]; simpl; intro; trivial. apply (IHl p z); trivial.
        intro Hp; rewrite Hp in H. apply min_elt_spec3 in Hp.
        destruct o.
          injection H as <-. intros Hl.
          destruct y as [z|z|]; simpl; trivial. elim (Hp _ H').

          destruct (min_elt r).
            injection H as <-.
            destruct y as [z|z|].
              apply (IHr e z); trivial.
              elim (Hp _ H').
              discriminate.
            discriminate.
  Qed.


  (** Specification of [max_elt] *)

  Lemma max_elt_spec1: forall s x, max_elt s = Some x -> In x s.
  Proof.
   unfold In.
   induction s as [| l IHl o r IHr]; simpl.
     intros. discriminate.
     intros x. destruct (max_elt r); intros.
       injection H as <-. apply IHr. reflexivity.
       destruct o; simpl.
         injection H as <-. reflexivity.
         destruct (max_elt l); simpl in *.
           injection H as <-. apply IHl. reflexivity.
           discriminate.
  Qed.

  Lemma max_elt_spec3: forall s, max_elt s = None -> Empty s.
  Proof.
    unfold Empty, In. intros s H.
    induction s as [|l IHl o r IHr].
      intro. apply empty_spec.
      intros [a|a|].
        apply IHr. revert H. clear. simpl. destruct (max_elt r); trivial.
         intro; discriminate.
        apply IHl. revert H. clear. simpl. destruct (max_elt l); trivial.
          case max_elt; intros; try discriminate. destruct o; discriminate.
        revert H. clear. simpl. case max_elt; intros; try discriminate.
         destruct o; discriminate.
  Qed.

  Lemma max_elt_spec2: forall s x y, max_elt s = Some x -> In y s -> ~ E.lt x y.
  Proof.
    unfold In.
    induction s as [|l IHl o r IHr]; intros x y H H'.
      discriminate.
      simpl in H. case_eq (max_elt r).
        intros p Hp. rewrite Hp in H. injection H as <-.
        destruct y as [z|z|]; simpl; intro; trivial. apply (IHr p z); trivial.
        intro Hp; rewrite Hp in H. apply max_elt_spec3 in Hp.
        destruct o.
          injection H as <-. intros Hl.
          destruct y as [z|z|]; simpl; trivial. elim (Hp _ H').

          destruct (max_elt l).
            injection H as <-.
            destruct y as [z|z|].
              elim (Hp _ H').
              apply (IHl e z); trivial.
              discriminate.
            discriminate.
  Qed.

End PositiveSet.

(* -*- coding: utf-8 -*- *)
(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * MSetAVL : Implementation of MSetInterface via AVL trees *)

(** This module implements finite sets using AVL trees.
    It follows the implementation from Ocaml's standard library,

    All operations given here expect and produce well-balanced trees
    (in the ocaml sense: heigths of subtrees shouldn't differ by more
    than 2), and hence has low complexities (e.g. add is logarithmic
    in the size of the set). But proving these balancing preservations
    is in fact not necessary for ensuring correct operational behavior
    and hence fulfilling the MSet interface. As a consequence,
    balancing results are not part of this file anymore, they can
    now be found in [MSetFullAVL].

    Four operations ([union], [subset], [compare] and [equal]) have
    been slightly adapted in order to have only structural recursive
    calls. The precise ocaml versions of these operations have also
    been formalized (thanks to Function+measure), see [ocaml_union],
    [ocaml_subset], [ocaml_compare] and [ocaml_equal] in
    [MSetFullAVL]. The structural variants compute faster in Coq,
    whereas the other variants produce nicer and/or (slightly) faster
    code after extraction.
*)

Require Import MSetInterface ZArith Int.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Ops : the pure functions *)

Module Ops (Import I:Int)(X:OrderedType) <: WOps X.
Local Open Scope Int_scope.
Local Open Scope lazy_bool_scope.

Definition elt := X.t.

(** ** Trees

   The fourth field of [Node] is the height of the tree *)

Inductive tree :=
  | Leaf : tree
  | Node : tree -> X.t -> tree -> int -> tree.

Definition t := tree.

(** ** Basic functions on trees: height and cardinal *)

Definition height (s : t) : int :=
  match s with
  | Leaf => 0
  | Node _ _ _ h => h
  end.

Fixpoint cardinal (s : t) : nat :=
  match s with
   | Leaf => 0%nat
   | Node l _ r _ => S (cardinal l + cardinal r)
  end.

(** ** Empty Set *)

Definition empty := Leaf.

(** ** Emptyness test *)

Definition is_empty s :=
  match s with Leaf => true | _ => false end.

(** ** Appartness *)

(** The [mem] function is deciding appartness. It exploits the
    binary search tree invariant to achieve logarithmic complexity. *)

Fixpoint mem x s :=
   match s with
     |  Leaf => false
     |  Node l y r _ => match X.compare x y with
             | Lt => mem x l
             | Eq => true
             | Gt => mem x r
         end
   end.

(** ** Singleton set *)

Definition singleton x := Node Leaf x Leaf 1.

(** ** Helper functions *)

(** [create l x r] creates a node, assuming [l] and [r]
    to be balanced and [|height l - height r| <= 2]. *)

Definition create l x r :=
   Node l x r (max (height l) (height r) + 1).

(** [bal l x r] acts as [create], but performs one step of
    rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

Definition assert_false := create.

Definition bal l x r :=
  let hl := height l in
  let hr := height r in
  if gt_le_dec hl (hr+2) then
    match l with
     | Leaf => assert_false l x r
     | Node ll lx lr _ =>
       if ge_lt_dec (height ll) (height lr) then
         create ll lx (create lr x r)
       else
         match lr with
          | Leaf => assert_false l x r
          | Node lrl lrx lrr _ =>
              create (create ll lx lrl) lrx (create lrr x r)
         end
    end
  else
    if gt_le_dec hr (hl+2) then
      match r with
       | Leaf => assert_false l x r
       | Node rl rx rr _ =>
         if ge_lt_dec (height rr) (height rl) then
            create (create l x rl) rx rr
         else
           match rl with
            | Leaf => assert_false l x r
            | Node rll rlx rlr _ =>
                create (create l x rll) rlx (create rlr rx rr)
           end
      end
    else
      create l x r.

(** ** Insertion *)

Fixpoint add x s := match s with
   | Leaf => Node Leaf x Leaf 1
   | Node l y r h =>
      match X.compare x y with
         | Lt => bal (add x l) y r
         | Eq => Node l y r h
         | Gt => bal l y (add x r)
      end
  end.

(** ** Join

    Same as [bal] but does not assume anything regarding heights
    of [l] and [r].
*)

Fixpoint join l : elt -> t -> t :=
  match l with
    | Leaf => add
    | Node ll lx lr lh => fun x =>
       fix join_aux (r:t) : t := match r with
          | Leaf =>  add x l
          | Node rl rx rr rh =>
               if gt_le_dec lh (rh+2) then bal ll lx (join lr x r)
               else if gt_le_dec rh (lh+2) then bal (join_aux rl) rx rr
               else create l x r
          end
  end.

(** ** Extraction of minimum element

  Morally, [remove_min] is to be applied to a non-empty tree
  [t = Node l x r h]. Since we can't deal here with [assert false]
  for [t=Leaf], we pre-unpack [t] (and forget about [h]).
*)

Fixpoint remove_min l x r : t*elt :=
  match l with
    | Leaf => (r,x)
    | Node ll lx lr lh =>
       let (l',m) := remove_min ll lx lr in (bal l' x r, m)
  end.

(** ** Merging two trees

  [merge t1 t2] builds the union of [t1] and [t2] assuming all elements
  of [t1] to be smaller than all elements of [t2], and
  [|height t1 - height t2| <= 2].
*)

Definition merge s1 s2 :=  match s1,s2 with
  | Leaf, _ => s2
  | _, Leaf => s1
  | _, Node l2 x2 r2 h2 =>
        let (s2',m) := remove_min l2 x2 r2 in bal s1 m s2'
end.

(** ** Deletion *)

Fixpoint remove x s := match s with
  | Leaf => Leaf
  | Node l y r h =>
      match X.compare x y with
         | Lt => bal (remove x l) y r
         | Eq => merge l r
         | Gt => bal l  y (remove x r)
      end
   end.

(** ** Minimum element *)

Fixpoint min_elt s := match s with
   | Leaf => None
   | Node Leaf y _  _ => Some y
   | Node l _ _ _ => min_elt l
end.

(** ** Maximum element *)

Fixpoint max_elt s := match s with
   | Leaf => None
   | Node _ y Leaf  _ => Some y
   | Node _ _ r _ => max_elt r
end.

(** ** Any element *)

Definition choose := min_elt.

(** ** Concatenation

    Same as [merge] but does not assume anything about heights.
*)

Definition concat s1 s2 :=
   match s1, s2 with
      | Leaf, _ => s2
      | _, Leaf => s1
      | _, Node l2 x2 r2 _ =>
            let (s2',m) := remove_min l2 x2 r2 in
            join s1 m s2'
   end.

(** ** Splitting

    [split x s] returns a triple [(l, present, r)] where
    - [l] is the set of elements of [s] that are [< x]
    - [r] is the set of elements of [s] that are [> x]
    - [present] is [true] if and only if [s] contains  [x].
*)

Record triple := mktriple { t_left:t; t_in:bool; t_right:t }.
Notation "<< l , b , r >>" := (mktriple l b r) (at level 9).

Fixpoint split x s : triple := match s with
  | Leaf => << Leaf, false, Leaf >>
  | Node l y r h =>
     match X.compare x y with
      | Lt => let (ll,b,rl) := split x l in << ll, b, join rl y r >>
      | Eq => << l, true, r >>
      | Gt => let (rl,b,rr) := split x r in << join l y rl, b, rr >>
     end
 end.

(** ** Intersection *)

Fixpoint inter s1 s2 := match s1, s2 with
    | Leaf, _ => Leaf
    | _, Leaf => Leaf
    | Node l1 x1 r1 h1, _ =>
            let (l2',pres,r2') := split x1 s2 in
            if pres then join (inter l1 l2') x1 (inter r1 r2')
            else concat (inter l1 l2') (inter r1 r2')
    end.

(** ** Difference *)

Fixpoint diff s1 s2 := match s1, s2 with
 | Leaf, _ => Leaf
 | _, Leaf => s1
 | Node l1 x1 r1 h1, _ =>
    let (l2',pres,r2') := split x1 s2 in
    if pres then concat (diff l1 l2') (diff r1 r2')
    else join (diff l1 l2') x1 (diff r1 r2')
end.

(** ** Union *)

(** In ocaml, heights of [s1] and [s2] are compared each time in order
   to recursively perform the split on the smaller set.
   Unfortunately, this leads to a non-structural algorithm. The
   following code is a simplification of the ocaml version: no
   comparison of heights. It might be slightly slower, but
   experimentally all the tests I've made in ocaml have shown this
   potential slowdown to be non-significant. Anyway, the exact code
   of ocaml has also been formalized thanks to Function+measure, see
   [ocaml_union] in [MSetFullAVL].
*)

Fixpoint union s1 s2 :=
 match s1, s2 with
  | Leaf, _ => s2
  | _, Leaf => s1
  | Node l1 x1 r1 h1, _ =>
     let (l2',_,r2') := split x1 s2 in
     join (union l1 l2') x1 (union r1 r2')
 end.

(** ** Elements *)

(** [elements_tree_aux acc t] catenates the elements of [t] in infix
    order to the list [acc] *)

Fixpoint elements_aux (acc : list X.t) (s : t) : list X.t :=
  match s with
   | Leaf => acc
   | Node l x r _ => elements_aux (x :: elements_aux acc r) l
  end.

(** then [elements] is an instanciation with an empty [acc] *)

Definition elements := elements_aux nil.

(** ** Filter *)

Fixpoint filter_acc (f:elt->bool) acc s := match s with
  | Leaf => acc
  | Node l x r h =>
     filter_acc f (filter_acc f (if f x then add x acc else acc) l) r
 end.

Definition filter f := filter_acc f Leaf.


(** ** Partition *)

Fixpoint partition_acc (f:elt->bool)(acc : t*t)(s : t) : t*t :=
  match s with
   | Leaf => acc
   | Node l x r _ =>
      let (acct,accf) := acc in
      partition_acc f
        (partition_acc f
           (if f x then (add x acct, accf) else (acct, add x accf)) l) r
  end.

Definition partition f := partition_acc f (Leaf,Leaf).

(** ** [for_all] and [exists] *)

Fixpoint for_all (f:elt->bool) s := match s with
  | Leaf => true
  | Node l x r _ => f x &&& for_all f l &&& for_all f r
end.

Fixpoint exists_ (f:elt->bool) s := match s with
  | Leaf => false
  | Node l x r _ => f x ||| exists_ f l ||| exists_ f r
end.

(** ** Fold *)

Fixpoint fold (A : Type) (f : elt -> A -> A)(s : t) : A -> A :=
 fun a => match s with
  | Leaf => a
  | Node l x r _ => fold f r (f x (fold f l a))
 end.
Implicit Arguments fold [A].


(** ** Subset *)

(** In ocaml, recursive calls are made on "half-trees" such as
   (Node l1 x1 Leaf _) and (Node Leaf x1 r1 _). Instead of these
   non-structural calls, we propose here two specialized functions for
   these situations. This version should be almost as efficient as
   the one of ocaml (closures as arguments may slow things a bit),
   it is simply less compact. The exact ocaml version has also been
   formalized (thanks to Function+measure), see [ocaml_subset] in
   [MSetFullAVL].
 *)

Fixpoint subsetl (subset_l1:t->bool) x1 s2 : bool :=
 match s2 with
  | Leaf => false
  | Node l2 x2 r2 h2 =>
     match X.compare x1 x2 with
      | Eq => subset_l1 l2
      | Lt => subsetl subset_l1 x1 l2
      | Gt => mem x1 r2 &&& subset_l1 s2
     end
 end.

Fixpoint subsetr (subset_r1:t->bool) x1 s2 : bool :=
 match s2 with
  | Leaf => false
  | Node l2 x2 r2 h2 =>
     match X.compare x1 x2 with
      | Eq => subset_r1 r2
      | Lt => mem x1 l2 &&& subset_r1 s2
      | Gt => subsetr subset_r1 x1 r2
     end
 end.

Fixpoint subset s1 s2 : bool := match s1, s2 with
  | Leaf, _ => true
  | Node _ _ _ _, Leaf => false
  | Node l1 x1 r1 h1, Node l2 x2 r2 h2 =>
     match X.compare x1 x2 with
      | Eq => subset l1 l2 &&& subset r1 r2
      | Lt => subsetl (subset l1) x1 l2 &&& subset r1 s2
      | Gt => subsetr (subset r1) x1 r2 &&& subset l1 s2
     end
 end.

(** ** A new comparison algorithm suggested by Xavier Leroy

    Transformation in C.P.S. suggested by Benjamin Grégoire.
    The original ocaml code (with non-structural recursive calls)
    has also been formalized (thanks to Function+measure), see
    [ocaml_compare] in [MSetFullAVL]. The following code with
    continuations computes dramatically faster in Coq, and
    should be almost as efficient after extraction.
*)

(** Enumeration of the elements of a tree *)

Inductive enumeration :=
 | End : enumeration
 | More : elt -> t -> enumeration -> enumeration.


(** [cons t e] adds the elements of tree [t] on the head of
    enumeration [e]. *)

Fixpoint cons s e : enumeration :=
 match s with
  | Leaf => e
  | Node l x r h => cons l (More x r e)
 end.

(** One step of comparison of elements *)

Definition compare_more x1 (cont:enumeration->comparison) e2 :=
 match e2 with
 | End => Gt
 | More x2 r2 e2 =>
     match X.compare x1 x2 with
      | Eq => cont (cons r2 e2)
      | Lt => Lt
      | Gt => Gt
     end
 end.

(** Comparison of left tree, middle element, then right tree *)

Fixpoint compare_cont s1 (cont:enumeration->comparison) e2 :=
 match s1 with
  | Leaf => cont e2
  | Node l1 x1 r1 _ =>
     compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2
  end.

(** Initial continuation *)

Definition compare_end e2 :=
 match e2 with End => Eq | _ => Lt end.

(** The complete comparison *)

Definition compare s1 s2 := compare_cont s1 compare_end (cons s2 End).

(** ** Equality test *)

Definition equal s1 s2 : bool :=
 match compare s1 s2 with
  | Eq => true
  | _ => false
 end.

End Ops.



(** * MakeRaw

   Functor of pure functions + a posteriori proofs of invariant
   preservation *)

Module MakeRaw (Import I:Int)(X:OrderedType) <: RawSets X.
Include Ops I X.

(** * Invariants *)

(** ** Occurrence in a tree *)

Inductive InT (x : elt) : tree -> Prop :=
  | IsRoot : forall l r h y, X.eq x y -> InT x (Node l y r h)
  | InLeft : forall l r h y, InT x l -> InT x (Node l y r h)
  | InRight : forall l r h y, InT x r -> InT x (Node l y r h).

Definition In := InT.

(** ** Some shortcuts *)

Definition Equal s s' := forall a : elt, InT a s <-> InT a s'.
Definition Subset s s' := forall a : elt, InT a s -> InT a s'.
Definition Empty s := forall a : elt, ~ InT a s.
Definition For_all (P : elt -> Prop) s := forall x, InT x s -> P x.
Definition Exists (P : elt -> Prop) s := exists x, InT x s /\ P x.

(** ** Binary search trees *)

(** [lt_tree x s]: all elements in [s] are smaller than [x]
   (resp. greater for [gt_tree]) *)

Definition lt_tree x s := forall y, InT y s -> X.lt y x.
Definition gt_tree x s := forall y, InT y s -> X.lt x y.

(** [bst t] : [t] is a binary search tree *)

Inductive bst : tree -> Prop :=
  | BSLeaf : bst Leaf
  | BSNode : forall x l r h, bst l -> bst r ->
     lt_tree x l -> gt_tree x r -> bst (Node l x r h).

(** [bst] is the (decidable) invariant our trees will have to satisfy. *)

Definition IsOk := bst.

Class Ok (s:t) : Prop := { ok : bst s }.

Instance bst_Ok s (Hs : bst s) : Ok s := Hs.

Fixpoint ltb_tree x s :=
 match s with
  | Leaf => true
  | Node l y r _ =>
     match X.compare x y with
      | Gt => ltb_tree x l && ltb_tree x r
      | _ => false
     end
 end.

Fixpoint gtb_tree x s :=
 match s with
  | Leaf => true
  | Node l y r _ =>
     match X.compare x y with
      | Lt => gtb_tree x l && gtb_tree x r
      | _ => false
     end
 end.

Fixpoint isok s :=
 match s with
  | Leaf => true
  | Node l x r _ => isok l && isok r && ltb_tree x l && gtb_tree x r
 end.


(** * Correctness proofs *)

(* Module Proofs. *)
 Module Import MX := OrderedTypeFacts X.
 Hint Resolve MX.lt_trans.

(** * Automation and dedicated tactics *)

Hint Unfold In.
Hint Constructors InT bst.
Hint Unfold lt_tree gt_tree.
Hint Resolve @ok.
Hint Constructors Ok.

Tactic Notation "factornode" ident(l) ident(x) ident(r) ident(h)
 "as" ident(s) :=
 set (s:=Node l x r h) in *; clearbody s; clear l x r h.

(** Automatic treatment of [Ok] hypothesis *)

Ltac inv_ok := match goal with
 | H:Ok (Node _ _ _ _) |- _ => apply @ok in H; inversion_clear H; inv_ok
 | H:Ok Leaf |- _ => clear H; inv_ok
 | H:bst _ |- _ => generalize (Build_Ok H); clear H; intro H; inv_ok
 | _ => idtac
end.

(** A tactic to repeat [inversion_clear] on all hyps of the
    form [(f (Node _ _ _ _))] *)

Ltac is_tree_constr c :=
  match c with
   | Leaf => idtac
   | Node _ _ _ _ => idtac
   | _ => fail
  end.

Ltac invtree f :=
  match goal with
     | H:f ?s |- _ => is_tree_constr s; inversion_clear H; invtree f
     | H:f _ ?s |- _ => is_tree_constr s; inversion_clear H; invtree f
     | H:f _ _ ?s |- _ => is_tree_constr s; inversion_clear H; invtree f
     | _ => idtac
  end.

Ltac inv := inv_ok; invtree InT.

Ltac intuition_in := repeat progress (intuition; inv).

(** Helper tactic concerning order of elements. *)

Ltac order := match goal with
 | U: lt_tree _ ?s, V: InT _ ?s |- _ => generalize (U _ V); clear U; order
 | U: gt_tree _ ?s, V: InT _ ?s |- _ => generalize (U _ V); clear U; order
 | _ => MX.order
end.


(** [isok] is indeed a decision procedure for [Ok] *)

Lemma ltb_tree_iff : forall x s, lt_tree x s <-> ltb_tree x s = true.
Proof.
 induction s as [|l IHl y r IHr h]; simpl.
 unfold lt_tree; intuition_in.
 elim_compare x y.
 split; intros; try discriminate. assert (X.lt y x) by auto. order.
 split; intros; try discriminate. assert (X.lt y x) by auto. order.
 rewrite !andb_true_iff, <-IHl, <-IHr.
  unfold lt_tree; intuition_in; order.
Qed.

Lemma gtb_tree_iff : forall x s, gt_tree x s <-> gtb_tree x s = true.
Proof.
 induction s as [|l IHl y r IHr h]; simpl.
 unfold gt_tree; intuition_in.
 elim_compare x y.
 split; intros; try discriminate. assert (X.lt x y) by auto. order.
 rewrite !andb_true_iff, <-IHl, <-IHr.
  unfold gt_tree; intuition_in; order.
 split; intros; try discriminate. assert (X.lt x y) by auto. order.
Qed.

Lemma isok_iff : forall s, Ok s <-> isok s = true.
Proof.
 induction s as [|l IHl y r IHr h]; simpl.
 intuition_in.
 rewrite !andb_true_iff, <- IHl, <-IHr, <- ltb_tree_iff, <- gtb_tree_iff.
 intuition_in.
Qed.

Instance isok_Ok s : isok s = true -> Ok s | 10.
Proof. intros; apply <- isok_iff; auto. Qed.


(** * Basic results about [In], [lt_tree], [gt_tree], [height] *)

(** [In] is compatible with [X.eq] *)

Lemma In_1 :
 forall s x y, X.eq x y -> InT x s -> InT y s.
Proof.
 induction s; simpl; intuition_in; eauto 3. (** TODO: why 5 is so slow ? *)
Qed.
Hint Immediate In_1.

Instance In_compat : Proper (X.eq==>eq==>iff) InT.
Proof.
apply proper_sym_impl_iff_2; auto with *.
repeat red; intros; subst. apply In_1 with x; auto.
Qed.

Lemma In_node_iff :
 forall l x r h y,
  InT y (Node l x r h) <-> InT y l \/ X.eq y x \/ InT y r.
Proof.
 intuition_in.
Qed.

(** Results about [lt_tree] and [gt_tree] *)

Lemma lt_leaf : forall x : elt, lt_tree x Leaf.
Proof.
 red; inversion 1.
Qed.

Lemma gt_leaf : forall x : elt, gt_tree x Leaf.
Proof.
 red; inversion 1.
Qed.

Lemma lt_tree_node :
 forall (x y : elt) (l r : tree) (h : int),
 lt_tree x l -> lt_tree x r -> X.lt y x -> lt_tree x (Node l y r h).
Proof.
 unfold lt_tree; intuition_in; order.
Qed.

Lemma gt_tree_node :
 forall (x y : elt) (l r : tree) (h : int),
 gt_tree x l -> gt_tree x r -> X.lt x y -> gt_tree x (Node l y r h).
Proof.
 unfold gt_tree; intuition_in; order.
Qed.

Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

Lemma lt_tree_not_in :
 forall (x : elt) (t : tree), lt_tree x t -> ~ InT x t.
Proof.
 intros; intro; order.
Qed.

Lemma lt_tree_trans :
 forall x y, X.lt x y -> forall t, lt_tree x t -> lt_tree y t.
Proof.
 eauto.
Qed.

Lemma gt_tree_not_in :
 forall (x : elt) (t : tree), gt_tree x t -> ~ InT x t.
Proof.
 intros; intro; order.
Qed.

Lemma gt_tree_trans :
 forall x y, X.lt y x -> forall t, gt_tree x t -> gt_tree y t.
Proof.
 eauto.
Qed.

Hint Resolve lt_tree_not_in lt_tree_trans gt_tree_not_in gt_tree_trans.

(** * Inductions principles for some of the set operators *)

Functional Scheme bal_ind := Induction for bal Sort Prop.
Functional Scheme remove_min_ind := Induction for remove_min Sort Prop.
Functional Scheme merge_ind := Induction for merge Sort Prop.
Functional Scheme min_elt_ind := Induction for min_elt Sort Prop.
Functional Scheme max_elt_ind := Induction for max_elt Sort Prop.
Functional Scheme concat_ind := Induction for concat Sort Prop.
Functional Scheme inter_ind := Induction for inter Sort Prop.
Functional Scheme diff_ind := Induction for diff Sort Prop.
Functional Scheme union_ind := Induction for union Sort Prop.

Ltac induct s x :=
 induction s as [|l IHl x' r IHr h]; simpl; intros;
 [|elim_compare x x'; intros; inv].


(** * Notations and helper lemma about pairs and triples *)

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.
Notation "t #l" := (t_left t) (at level 9, format "t '#l'") : pair_scope.
Notation "t #b" := (t_in t) (at level 9, format "t '#b'") : pair_scope.
Notation "t #r" := (t_right t) (at level 9, format "t '#r'") : pair_scope.

Open Local Scope pair_scope.


(** * Empty set *)

Lemma empty_spec : Empty empty.
Proof.
 intro; intro.
 inversion H.
Qed.

Instance empty_ok : Ok empty.
Proof.
 auto.
Qed.

(** * Emptyness test *)

Lemma is_empty_spec : forall s, is_empty s = true <-> Empty s.
Proof.
 destruct s as [|r x l h]; simpl; auto.
 split; auto. red; red; intros; inv.
 split; auto. try discriminate. intro H; elim (H x); auto.
Qed.

(** * Appartness *)

Lemma mem_spec : forall s x `{Ok s}, mem x s = true <-> InT x s.
Proof.
 split.
 induct s x; auto; try discriminate.
 induct s x; intuition_in; order.
Qed.


(** * Singleton set *)

Lemma singleton_spec : forall x y, InT y (singleton x) <-> X.eq y x.
Proof.
 unfold singleton; intuition_in.
Qed.

Instance singleton_ok x : Ok (singleton x).
Proof.
 unfold singleton; auto.
Qed.



(** * Helper functions *)

Lemma create_spec :
 forall l x r y,  InT y (create l x r) <-> X.eq y x \/ InT y l \/ InT y r.
Proof.
 unfold create; split; [ inversion_clear 1 | ]; intuition.
Qed.

Instance create_ok l x r `(Ok l, Ok r, lt_tree x l, gt_tree x r) :
 Ok (create l x r).
Proof.
 unfold create; auto.
Qed.

Lemma bal_spec : forall l x r y,
 InT y (bal l x r) <-> X.eq y x \/ InT y l \/ InT y r.
Proof.
 intros l x r; functional induction bal l x r; intros; try clear e0;
 rewrite !create_spec; intuition_in.
Qed.

Instance bal_ok l x r `(Ok l, Ok r, lt_tree x l, gt_tree x r) :
 Ok (bal l x r).
Proof.
 intros l x r; functional induction bal l x r; intros;
 inv; repeat apply create_ok; auto; unfold create;
 (apply lt_tree_node || apply gt_tree_node); auto;
 (eapply lt_tree_trans || eapply gt_tree_trans); eauto.
Qed.


(** * Insertion *)

Lemma add_spec' : forall s x y,
 InT y (add x s) <-> X.eq y x \/ InT y s.
Proof.
 induct s x; try rewrite ?bal_spec, ?IHl, ?IHr; intuition_in.
 setoid_replace y with x'; eauto.
Qed.

Lemma add_spec : forall s x y `{Ok s},
 InT y (add x s) <-> X.eq y x \/ InT y s.
Proof. intros; apply add_spec'. Qed.

Instance add_ok s x `(Ok s) : Ok (add x s).
Proof.
 induct s x; auto; apply bal_ok; auto;
  intros y; rewrite add_spec'; intuition; order.
Qed.


Open Scope Int_scope.

(** * Join *)

(* Function/Functional Scheme can't deal with internal fix.
   Let's do its job by hand: *)

Ltac join_tac :=
 intro l; induction l as [| ll _ lx lr Hlr lh];
   [ | intros x r; induction r as [| rl Hrl rx rr _ rh]; unfold join;
     [ | destruct (gt_le_dec lh (rh+2));
       [ match goal with |- context b [ bal ?a ?b ?c] =>
           replace (bal a b c)
           with (bal ll lx (join lr x (Node rl rx rr rh))); [ | auto]
         end
       | destruct (gt_le_dec rh (lh+2));
         [ match goal with |- context b [ bal ?a ?b ?c] =>
             replace (bal a b c)
             with (bal (join (Node ll lx lr lh) x rl) rx rr); [ | auto]
           end
         | ] ] ] ]; intros.

Lemma join_spec : forall l x r y,
 InT y (join l x r) <-> X.eq y x \/ InT y l \/ InT y r.
Proof.
 join_tac.
 simpl.
 rewrite add_spec'; intuition_in.
 rewrite add_spec'; intuition_in.
 rewrite bal_spec, Hlr; clear Hlr Hrl; intuition_in.
 rewrite bal_spec, Hrl; clear Hlr Hrl; intuition_in.
 apply create_spec.
Qed.

Instance join_ok l x r `(Ok l, Ok r, lt_tree x l, gt_tree x r) :
 Ok (join l x r).
Proof.
 join_tac; auto with *; inv; apply bal_ok; auto;
 clear Hrl Hlr z; intro; intros; rewrite join_spec in *.
 intuition; [ setoid_replace y with x | ]; eauto.
 intuition; [ setoid_replace y with x | ]; eauto.
Qed.


(** * Extraction of minimum element *)

Lemma remove_min_spec : forall l x r h y,
 InT y (Node l x r h) <->
  X.eq y (remove_min l x r)#2 \/ InT y (remove_min l x r)#1.
Proof.
 intros l x r; functional induction (remove_min l x r); simpl in *; intros.
 intuition_in.
 rewrite bal_spec, In_node_iff, IHp, e0; simpl; intuition.
Qed.

Instance remove_min_ok l x r h `(Ok (Node l x r h)) :
 Ok (remove_min l x r)#1.
Proof.
 intros l x r; functional induction (remove_min l x r); simpl; intros.
 inv; auto.
 assert (O : Ok (Node ll lx lr _x)) by (inv; auto).
 assert (L : lt_tree x (Node ll lx lr _x)) by (inv; auto).
 specialize IHp with (1:=O); rewrite e0 in IHp; auto; simpl in *.
 apply bal_ok; auto.
 inv; auto.
 intro y; specialize (L y).
 rewrite remove_min_spec, e0 in L; simpl in L; intuition.
 inv; auto.
Qed.

Lemma remove_min_gt_tree : forall l x r h `{Ok (Node l x r h)},
 gt_tree (remove_min l x r)#2 (remove_min l x r)#1.
Proof.
 intros l x r; functional induction (remove_min l x r); simpl; intros.
 inv; auto.
 assert (O : Ok (Node ll lx lr _x)) by (inv; auto).
 assert (L : lt_tree x (Node ll lx lr _x)) by (inv; auto).
 specialize IHp with (1:=O); rewrite e0 in IHp; simpl in IHp.
 intro y; rewrite bal_spec; intuition;
  specialize (L m); rewrite remove_min_spec, e0 in L; simpl in L;
   [setoid_replace y with x|inv]; eauto.
Qed.
Hint Resolve remove_min_gt_tree.



(** * Merging two trees *)

Lemma merge_spec : forall s1 s2 y,
 InT y (merge s1 s2) <-> InT y s1 \/ InT y s2.
Proof.
 intros s1 s2; functional induction (merge s1 s2); intros;
 try factornode _x _x0 _x1 _x2 as s1.
 intuition_in.
 intuition_in.
 rewrite bal_spec, remove_min_spec, e1; simpl; intuition.
Qed.

Instance merge_ok s1 s2 `(Ok s1, Ok s2)
 `(forall y1 y2 : elt, InT y1 s1 -> InT y2 s2 -> X.lt y1 y2) :
 Ok (merge s1 s2).
Proof.
 intros s1 s2; functional induction (merge s1 s2); intros; auto;
 try factornode _x _x0 _x1 _x2 as s1.
 apply bal_ok; auto.
 change s2' with ((s2',m)#1); rewrite <-e1; eauto with *.
 intros y Hy.
 apply H1; auto.
 rewrite remove_min_spec, e1; simpl; auto.
 change (gt_tree (s2',m)#2 (s2',m)#1); rewrite <-e1; eauto.
Qed.



(** * Deletion *)

Lemma remove_spec : forall s x y `{Ok s},
 (InT y (remove x s) <-> InT y s /\ ~ X.eq y x).
Proof.
 induct s x.
 intuition_in.
 rewrite merge_spec; intuition; [order|order|intuition_in].
 elim H6; eauto.
 rewrite bal_spec, IHl; clear IHl IHr; intuition; [order|order|intuition_in].
 rewrite bal_spec, IHr; clear IHl IHr; intuition; [order|order|intuition_in].
Qed.

Instance remove_ok s x `(Ok s) : Ok (remove x s).
Proof.
 induct s x.
 auto.
 (* EQ *)
 apply merge_ok; eauto.
 (* LT *)
 apply bal_ok; auto.
 intro z; rewrite remove_spec; auto; destruct 1; eauto.
 (* GT *)
 apply bal_ok; auto.
 intro z; rewrite remove_spec; auto; destruct 1; eauto.
Qed.


(** * Minimum element *)

Lemma min_elt_spec1 : forall s x, min_elt s = Some x -> InT x s.
Proof.
 intro s; functional induction (min_elt s); auto; inversion 1; auto.
Qed.

Lemma min_elt_spec2 : forall s x y `{Ok s},
 min_elt s = Some x -> InT y s -> ~ X.lt y x.
Proof.
 intro s; functional induction (min_elt s);
 try rename _x1 into l1, _x2 into x1, _x3 into r1, _x4 into h1.
 discriminate.
 intros x y0 U V W.
 inversion V; clear V; subst.
 inv; order.
 intros; inv; auto.
 assert (X.lt x y) by (apply H4; apply min_elt_spec1; auto).
 order.
 assert (X.lt x1 y) by auto.
 assert (~X.lt x1 x) by auto.
 order.
Qed.

Lemma min_elt_spec3 : forall s, min_elt s = None -> Empty s.
Proof.
 intro s; functional induction (min_elt s).
 red; red; inversion 2.
 inversion 1.
 intro H0.
 destruct (IHo H0 _x2); auto.
Qed.



(** * Maximum element *)

Lemma max_elt_spec1 : forall s x, max_elt s = Some x -> InT x s.
Proof.
 intro s; functional induction (max_elt s); auto; inversion 1; auto.
Qed.

Lemma max_elt_spec2 : forall s x y `{Ok s},
 max_elt s = Some x -> InT y s -> ~ X.lt x y.
Proof.
 intro s; functional induction (max_elt s);
 try rename _x1 into l1, _x2 into x1, _x3 into r1, _x4 into h1.
 discriminate.
 intros x y0 U V W.
 inversion V; clear V; subst.
 inv; order.
 intros; inv; auto.
 assert (X.lt y x1) by auto.
 assert (~ X.lt x x1) by auto.
 order.
 assert (X.lt y x) by (apply H5; apply max_elt_spec1; auto).
 order.
Qed.

Lemma max_elt_spec3 : forall s, max_elt s = None -> Empty s.
Proof.
 intro s; functional induction (max_elt s).
 red; auto.
 inversion 1.
 intros H0; destruct (IHo H0 _x2); auto.
Qed.



(** * Any element *)

Lemma choose_spec1 : forall s x, choose s = Some x -> InT x s.
Proof.
 exact min_elt_spec1.
Qed.

Lemma choose_spec2 : forall s, choose s = None -> Empty s.
Proof.
 exact min_elt_spec3.
Qed.

Lemma choose_spec3 : forall s s' x x' `{Ok s, Ok s'},
  choose s = Some x -> choose s' = Some x' ->
  Equal s s' -> X.eq x x'.
Proof.
 unfold choose, Equal; intros s s' x x' Hb Hb' Hx Hx' H.
 assert (~X.lt x x').
  apply min_elt_spec2 with s'; auto.
  rewrite <-H; auto using min_elt_spec1.
 assert (~X.lt x' x).
  apply min_elt_spec2 with s; auto.
  rewrite H; auto using min_elt_spec1.
 elim_compare x x'; intuition.
Qed.


(** * Concatenation *)

Lemma concat_spec : forall s1 s2 y,
 InT y (concat s1 s2) <-> InT y s1 \/ InT y s2.
Proof.
 intros s1 s2; functional induction (concat s1 s2); intros;
 try factornode _x _x0 _x1 _x2 as s1.
 intuition_in.
 intuition_in.
 rewrite join_spec, remove_min_spec, e1; simpl; intuition.
Qed.

Instance concat_ok s1 s2 `(Ok s1, Ok s2)
 `(forall y1 y2 : elt, InT y1 s1 -> InT y2 s2 -> X.lt y1 y2) :
 Ok (concat s1 s2).
Proof.
 intros s1 s2; functional induction (concat s1 s2); intros; auto;
 try factornode _x _x0 _x1 _x2 as s1.
 apply join_ok; auto.
 change (Ok (s2',m)#1); rewrite <-e1; eauto with *.
 intros y Hy.
 apply H1; auto.
 rewrite remove_min_spec, e1; simpl; auto.
 change (gt_tree (s2',m)#2 (s2',m)#1); rewrite <-e1; eauto.
Qed.



(** * Splitting *)

Lemma split_spec1 : forall s x y `{Ok s},
 (InT y (split x s)#l <-> InT y s /\ X.lt y x).
Proof.
 induct s x.
 intuition_in.
 intuition_in; order.
 specialize (IHl x y).
 destruct (split x l); simpl in *. rewrite IHl; intuition_in; order.
 specialize (IHr x y).
 destruct (split x r); simpl in *. rewrite join_spec, IHr; intuition_in; order.
Qed.

Lemma split_spec2 : forall s x y `{Ok s},
 (InT y (split x s)#r <-> InT y s /\ X.lt x y).
Proof.
 induct s x.
 intuition_in.
 intuition_in; order.
 specialize (IHl x y).
 destruct (split x l); simpl in *. rewrite join_spec, IHl; intuition_in; order.
 specialize (IHr x y).
 destruct (split x r); simpl in *. rewrite IHr; intuition_in; order.
Qed.

Lemma split_spec3 : forall s x `{Ok s},
 ((split x s)#b = true <-> InT x s).
Proof.
 induct s x.
 intuition_in; try discriminate.
 intuition.
 specialize (IHl x).
 destruct (split x l); simpl in *. rewrite IHl; intuition_in; order.
 specialize (IHr x).
 destruct (split x r); simpl in *. rewrite IHr; intuition_in; order.
Qed.

Lemma split_ok s x `{Ok s} : Ok (split x s)#l /\ Ok (split x s)#r.
Proof.
 induct s x; simpl; auto.
 specialize (IHl x).
 generalize (fun y => @split_spec2 _ x y H1).
 destruct (split x l); simpl in *; intuition. apply join_ok; auto.
 intros y; rewrite H; intuition.
 specialize (IHr x).
 generalize (fun y => @split_spec1 _ x y H2).
 destruct (split x r); simpl in *; intuition. apply join_ok; auto.
 intros y; rewrite H; intuition.
Qed.

Instance split_ok1 s x `(Ok s) : Ok (split x s)#l.
Proof. intros; destruct (@split_ok s x); auto. Qed.

Instance split_ok2 s x `(Ok s) : Ok (split x s)#r.
Proof. intros; destruct (@split_ok s x); auto. Qed.


(** * Intersection *)

Ltac destruct_split := match goal with
 | H : split ?x ?s = << ?u, ?v, ?w >> |- _ =>
   assert ((split x s)#l = u) by (rewrite H; auto);
   assert ((split x s)#b = v) by (rewrite H; auto);
   assert ((split x s)#r = w) by (rewrite H; auto);
   clear H; subst u w
 end.

Lemma inter_spec_ok : forall s1 s2 `{Ok s1, Ok s2},
 Ok (inter s1 s2) /\ (forall y, InT y (inter s1 s2) <-> InT y s1 /\ InT y s2).
Proof.
 intros s1 s2; functional induction inter s1 s2; intros B1 B2;
 [intuition_in|intuition_in | | ];
 factornode _x0 _x1 _x2 _x3 as s2; destruct_split; inv;
 destruct IHt0 as (IHo1,IHi1), IHt1 as (IHo2,IHi2); auto with *;
 split; intros.
 (* Ok join *)
 apply join_ok; auto with *; intro y; rewrite ?IHi1, ?IHi2; intuition.
 (* InT join *)
 rewrite join_spec, IHi1, IHi2, split_spec1, split_spec2; intuition_in.
 setoid_replace y with x1; auto. rewrite <- split_spec3; auto.
 (* Ok concat *)
 apply concat_ok; auto with *; intros y1 y2; rewrite IHi1, IHi2; intuition; order.
 (* InT concat *)
 rewrite concat_spec, IHi1, IHi2, split_spec1, split_spec2; auto.
 intuition_in.
 absurd (InT x1 s2).
  rewrite <- split_spec3; auto; congruence.
  setoid_replace x1 with y; auto.
Qed.

Lemma inter_spec : forall s1 s2 y `{Ok s1, Ok s2},
 (InT y (inter s1 s2) <-> InT y s1 /\ InT y s2).
Proof. intros; destruct (@inter_spec_ok s1 s2); auto. Qed.

Instance inter_ok s1 s2 `(Ok s1, Ok s2) : Ok (inter s1 s2).
Proof. intros; destruct (@inter_spec_ok s1 s2); auto. Qed.


(** * Difference *)

Lemma diff_spec_ok : forall s1 s2 `{Ok s1, Ok s2},
 Ok (diff s1 s2) /\ (forall y, InT y (diff s1 s2) <-> InT y s1 /\ ~InT y s2).
Proof.
 intros s1 s2; functional induction diff s1 s2; intros B1 B2;
 [intuition_in|intuition_in | | ];
 factornode _x0 _x1 _x2 _x3 as s2; destruct_split; inv;
 destruct IHt0 as (IHb1,IHi1), IHt1 as (IHb2,IHi2); auto with *;
 split; intros.
 (* Ok concat *)
 apply concat_ok; auto; intros y1 y2; rewrite IHi1, IHi2; intuition; order.
 (* InT concat *)
 rewrite concat_spec, IHi1, IHi2, split_spec1, split_spec2; intuition_in.
 absurd (InT x1 s2).
  setoid_replace x1 with y; auto.
  rewrite <- split_spec3; auto; congruence.
 (* Ok join *)
 apply join_ok; auto; intro y; rewrite ?IHi1, ?IHi2; intuition.
 (* InT join *)
 rewrite join_spec, IHi1, IHi2, split_spec1, split_spec2; auto with *.
 intuition_in.
 absurd (InT x1 s2); auto.
  rewrite <- split_spec3; auto; congruence.
  setoid_replace x1 with y; auto.
Qed.

Lemma diff_spec : forall s1 s2 y `{Ok s1, Ok s2},
 (InT y (diff s1 s2) <-> InT y s1 /\ ~InT y s2).
Proof. intros; destruct (@diff_spec_ok s1 s2); auto. Qed.

Instance diff_ok s1 s2 `(Ok s1, Ok s2) : Ok (diff s1 s2).
Proof. intros; destruct (@diff_spec_ok s1 s2); auto. Qed.


(** * Union *)

Lemma union_spec : forall s1 s2 y `{Ok s1, Ok s2},
 (InT y (union s1 s2) <-> InT y s1 \/ InT y s2).
Proof.
 intros s1 s2; functional induction union s1 s2; intros y B1 B2.
 intuition_in.
 intuition_in.
 factornode _x0 _x1 _x2 _x3 as s2; destruct_split; inv.
 rewrite join_spec, IHt0, IHt1, split_spec1, split_spec2; auto with *.
 elim_compare y x1; intuition_in.
Qed.

Instance union_ok s1 s2 `(Ok s1, Ok s2) : Ok (union s1 s2).
Proof.
 intros s1 s2; functional induction union s1 s2; intros B1 B2; auto.
 factornode _x0 _x1 _x2 _x3 as s2; destruct_split; inv.
 apply join_ok; auto with *.
 intro y; rewrite union_spec, split_spec1; intuition_in.
 intro y; rewrite union_spec, split_spec2; intuition_in.
Qed.


(** * Elements *)

Lemma elements_spec1' : forall s acc x,
 InA X.eq x (elements_aux acc s) <-> InT x s \/ InA X.eq x acc.
Proof.
 induction s as [ | l Hl x r Hr h ]; simpl; auto.
 intuition.
 inversion H0.
 intros.
 rewrite Hl.
 destruct (Hr acc x0); clear Hl Hr.
 intuition; inversion_clear H3; intuition.
Qed.

Lemma elements_spec1 : forall s x, InA X.eq x (elements s) <-> InT x s.
Proof.
 intros; generalize (elements_spec1' s nil x); intuition.
 inversion_clear H0.
Qed.

Lemma elements_spec2' : forall s acc `{Ok s}, sort X.lt acc ->
 (forall x y : elt, InA X.eq x acc -> InT y s -> X.lt y x) ->
 sort X.lt (elements_aux acc s).
Proof.
 induction s as [ | l Hl y r Hr h]; simpl; intuition.
 inv.
 apply Hl; auto.
 constructor.
 apply Hr; auto.
 eapply InA_InfA; eauto with *.
 intros.
 destruct (elements_spec1' r acc y0); intuition.
 intros.
 inversion_clear H.
 order.
 destruct (elements_spec1' r acc x); intuition eauto.
Qed.

Lemma elements_spec2 : forall s `(Ok s), sort X.lt (elements s).
Proof.
 intros; unfold elements; apply elements_spec2'; auto.
 intros; inversion H0.
Qed.
Hint Resolve elements_spec2.

Lemma elements_spec2w : forall s `(Ok s), NoDupA X.eq (elements s).
Proof.
 intros. eapply SortA_NoDupA; eauto with *.
Qed.

Lemma elements_aux_cardinal :
 forall s acc, (length acc + cardinal s)%nat = length (elements_aux acc s).
Proof.
 simple induction s; simpl in |- *; intuition.
 rewrite <- H.
 simpl in |- *.
 rewrite <- H0; omega.
Qed.

Lemma elements_cardinal : forall s : tree, cardinal s = length (elements s).
Proof.
 exact (fun s => elements_aux_cardinal s nil).
Qed.

Definition cardinal_spec (s:t)(Hs:Ok s) := elements_cardinal s.

Lemma elements_app :
 forall s acc, elements_aux acc s = elements s ++ acc.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1, IHs2.
 unfold elements; simpl.
 rewrite 2 IHs1, IHs2, <- !app_nil_end, !app_ass; auto.
Qed.

Lemma elements_node :
 forall l x r h acc,
 elements l ++ x :: elements r ++ acc =
 elements (Node l x r h) ++ acc.
Proof.
 unfold elements; simpl; intros; auto.
 rewrite !elements_app, <- !app_nil_end, !app_ass; auto.
Qed.


(** * Filter *)

Lemma filter_spec' : forall s x acc f,
 Proper (X.eq==>eq) f ->
 (InT x (filter_acc f acc s) <-> InT x acc \/ InT x s /\ f x = true).
Proof.
 induction s; simpl; intros.
 intuition_in.
 rewrite IHs2, IHs1 by (destruct (f t0); auto).
 case_eq (f t0); intros.
 rewrite add_spec'; auto.
 intuition_in.
 rewrite (H _ _ H2).
 intuition.
 intuition_in.
 rewrite (H _ _ H2) in H3.
 rewrite H0 in H3; discriminate.
Qed.

Instance filter_ok' s acc f `(Ok s, Ok acc) :
 Ok (filter_acc f acc s).
Proof.
 induction s; simpl; auto.
 intros. inv.
 destruct (f t0); auto with *.
Qed.

Lemma filter_spec : forall s x f,
 Proper (X.eq==>eq) f ->
 (InT x (filter f s) <-> InT x s /\ f x = true).
Proof.
 unfold filter; intros; rewrite filter_spec'; intuition_in.
Qed.

Instance filter_ok s f `(Ok s) : Ok (filter f s).
Proof.
 unfold filter; intros; apply filter_ok'; auto.
Qed.


(** * Partition *)

Lemma partition_spec1' : forall s acc f,
 Proper (X.eq==>eq) f -> forall x : elt,
 InT x (partition_acc f acc s)#1 <->
 InT x acc#1 \/ InT x s /\ f x = true.
Proof.
 induction s; simpl; intros.
 intuition_in.
 destruct acc as [acct accf]; simpl in *.
 rewrite IHs2 by
  (destruct (f t0); auto; apply partition_acc_avl_1; simpl; auto).
 rewrite IHs1 by (destruct (f t0); simpl; auto).
 case_eq (f t0); simpl; intros.
 rewrite add_spec'; auto.
 intuition_in.
 rewrite (H _ _ H2).
 intuition.
 intuition_in.
 rewrite (H _ _ H2) in H3.
 rewrite H0 in H3; discriminate.
Qed.

Lemma partition_spec2' : forall s acc f,
 Proper (X.eq==>eq) f -> forall x : elt,
 InT x (partition_acc f acc s)#2 <->
 InT x acc#2 \/ InT x s /\ f x = false.
Proof.
 induction s; simpl; intros.
 intuition_in.
 destruct acc as [acct accf]; simpl in *.
 rewrite IHs2 by
  (destruct (f t0); auto; apply partition_acc_avl_2; simpl; auto).
 rewrite IHs1 by (destruct (f t0); simpl; auto).
 case_eq (f t0); simpl; intros.
 intuition.
 intuition_in.
 rewrite (H _ _ H2) in H3.
 rewrite H0 in H3; discriminate.
 rewrite add_spec'; auto.
 intuition_in.
 rewrite (H _ _ H2).
 intuition.
Qed.

Lemma partition_spec1 : forall s f,
 Proper (X.eq==>eq) f ->
 Equal (partition f s)#1 (filter f s).
Proof.
 unfold partition; intros s f P x.
 rewrite partition_spec1', filter_spec; simpl; intuition_in.
Qed.

Lemma partition_spec2 : forall s f,
 Proper (X.eq==>eq) f ->
 Equal (partition f s)#2 (filter (fun x => negb (f x)) s).
Proof.
 unfold partition; intros s f P x.
 rewrite partition_spec2', filter_spec; simpl; intuition_in.
 rewrite H1; auto.
 right; split; auto.
 rewrite negb_true_iff in H1; auto.
 intros u v H; rewrite H; auto.
Qed.

Instance partition_ok1' s acc f `(Ok s, Ok acc#1) :
 Ok (partition_acc f acc s)#1.
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros. inv.
 destruct (f t0); auto.
 apply IHs2; simpl; auto.
 apply IHs1; simpl; auto with *.
Qed.

Instance partition_ok2' s acc f `(Ok s, Ok acc#2) :
 Ok (partition_acc f acc s)#2.
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros. inv.
 destruct (f t0); auto.
 apply IHs2; simpl; auto.
 apply IHs1; simpl; auto with *.
Qed.

Instance partition_ok1 s f `(Ok s) : Ok (partition f s)#1.
Proof. intros; apply partition_ok1'; auto. Qed.

Instance partition_ok2 s f `(Ok s) : Ok (partition f s)#2.
Proof. intros; apply partition_ok2'; auto. Qed.



(** * [for_all] and [exists] *)

Lemma for_all_spec : forall s f, Proper (X.eq==>eq) f ->
 (for_all f s = true <-> For_all (fun x => f x = true) s).
Proof.
 split.
 induction s; simpl; auto; intros; red; intros; inv.
 destruct (andb_prop _ _ H0); auto.
 destruct (andb_prop _ _ H1); eauto.
 apply IHs1; auto.
 destruct (andb_prop _ _ H0); auto.
 destruct (andb_prop _ _ H1); auto.
 apply IHs2; auto.
 destruct (andb_prop _ _ H0); auto.
 (* <- *)
 induction s; simpl; auto.
 intros.
 rewrite IHs1; try red; auto.
 rewrite IHs2; try red; auto.
 generalize (H0 t0).
 destruct (f t0); simpl; auto.
Qed.

Lemma exists_spec : forall s f, Proper (X.eq==>eq) f ->
 (exists_ f s = true <-> Exists (fun x => f x = true) s).
Proof.
 split.
 induction s; simpl; intros; rewrite <- ?orb_lazy_alt in *.
 discriminate.
 destruct (orb_true_elim _ _ H0) as [H1|H1].
 destruct (orb_true_elim _ _ H1) as [H2|H2].
 exists t0; auto.
 destruct (IHs1 H2); auto; exists x; intuition.
 destruct (IHs2 H1); auto; exists x; intuition.
 (* <- *)
 induction s; simpl; destruct 1 as (x,(U,V)); inv; rewrite <- ?orb_lazy_alt.
 rewrite (H _ _ (MX.eq_sym H0)); rewrite V; auto.
 apply orb_true_intro; left.
 apply orb_true_intro; right; apply IHs1; auto; exists x; auto.
 apply orb_true_intro; right; apply IHs2; auto; exists x; auto.
Qed.


(** * Fold *)

Lemma fold_spec' :
 forall (A : Type) (f : elt -> A -> A) (s : tree) (i : A) (acc : list elt),
 fold_left (flip f) (elements_aux acc s) i = fold_left (flip f) acc (fold f s i).
Proof.
 induction s as [|l IHl x r IHr h]; simpl; intros; auto.
 rewrite IHl.
 simpl. unfold flip at 2.
 apply IHr.
Qed.

Lemma fold_spec :
 forall (s:t) (A : Type) (i : A) (f : elt -> A -> A),
 fold f s i = fold_left (flip f) (elements s) i.
Proof.
 unfold elements.
 induction s as [|l IHl x r IHr h]; simpl; intros; auto.
 rewrite fold_spec'.
 rewrite IHr.
 simpl; auto.
Qed.


(** * Subset *)

Lemma subsetl_spec : forall subset_l1 l1 x1 h1 s2
 `{Ok (Node l1 x1 Leaf h1), Ok s2},
 (forall s `{Ok s}, (subset_l1 s = true <-> Subset l1 s)) ->
 (subsetl subset_l1 x1 s2 = true <-> Subset (Node l1 x1 Leaf h1) s2 ).
Proof.
 induction s2 as [|l2 IHl2 x2 r2 IHr2 h2]; simpl; intros.
 unfold Subset; intuition; try discriminate.
 assert (H': InT x1 Leaf) by auto; inversion H'.
 specialize (IHl2 H).
 specialize (IHr2 H).
 inv.
 elim_compare x1 x2.

 rewrite H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (X.eq a x2) by order; intuition_in.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

 rewrite IHl2 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

 rewrite <-andb_lazy_alt, andb_true_iff, H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 constructor 3. setoid_replace a with x1; auto. rewrite <- mem_spec; auto.
 rewrite mem_spec; auto.
 assert (InT x1 (Node l2 x2 r2 h2)) by auto; intuition_in; order.
Qed.


Lemma subsetr_spec : forall subset_r1 r1 x1 h1 s2,
 bst (Node Leaf x1 r1 h1) -> bst s2 ->
 (forall s, bst s -> (subset_r1 s = true <-> Subset r1 s)) ->
 (subsetr subset_r1 x1 s2 = true <-> Subset (Node Leaf x1 r1 h1) s2).
Proof.
 induction s2 as [|l2 IHl2 x2 r2 IHr2 h2]; simpl; intros.
 unfold Subset; intuition; try discriminate.
 assert (H': InT x1 Leaf) by auto; inversion H'.
 specialize (IHl2 H).
 specialize (IHr2 H).
 inv.
 elim_compare x1 x2.

 rewrite H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (X.eq a x2) by order; intuition_in.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

 rewrite <-andb_lazy_alt, andb_true_iff, H1 by auto;  clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 constructor 2. setoid_replace a with x1; auto. rewrite <- mem_spec; auto.
 rewrite mem_spec; auto.
 assert (InT x1 (Node l2 x2 r2 h2)) by auto; intuition_in; order.

 rewrite IHr2 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
Qed.

Lemma subset_spec : forall s1 s2 `{Ok s1, Ok s2},
 (subset s1 s2 = true <-> Subset s1 s2).
Proof.
 induction s1 as [|l1 IHl1 x1 r1 IHr1 h1]; simpl; intros.
 unfold Subset; intuition_in.
 destruct s2 as [|l2 x2 r2 h2]; simpl; intros.
 unfold Subset; intuition_in; try discriminate.
 assert (H': InT x1 Leaf) by auto; inversion H'.
 inv.
 elim_compare x1 x2.

 rewrite <-andb_lazy_alt, andb_true_iff, IHl1, IHr1 by auto.
 clear IHl1 IHr1.
 unfold Subset; intuition_in.
 assert (X.eq a x2) by order; intuition_in.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

 rewrite <-andb_lazy_alt, andb_true_iff, IHr1 by auto.
 rewrite (@subsetl_spec (subset l1) l1 x1 h1) by auto.
 clear IHl1 IHr1.
 unfold Subset; intuition_in.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

 rewrite <-andb_lazy_alt, andb_true_iff, IHl1 by auto.
 rewrite (@subsetr_spec (subset r1) r1 x1 h1) by auto.
 clear IHl1 IHr1.
 unfold Subset; intuition_in.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (InT a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
Qed.


(** * Comparison *)

(** ** Relations [eq] and [lt] over trees *)

Module L := MakeListOrdering X.

Definition eq := Equal.
Instance eq_equiv : Equivalence eq.
Proof. firstorder. Qed.

Lemma eq_Leq : forall s s', eq s s' <-> L.eq (elements s) (elements s').
Proof.
 unfold eq, Equal, L.eq; intros.
 setoid_rewrite elements_spec1; firstorder.
Qed.

Definition lt (s1 s2 : t) : Prop :=
 exists s1', exists s2', Ok s1' /\ Ok s2' /\ eq s1 s1' /\ eq s2 s2'
   /\ L.lt (elements s1') (elements s2').

Instance lt_strorder : StrictOrder lt.
Proof.
 split.
 intros s (s1 & s2 & B1 & B2 & E1 & E2 & L).
 assert (eqlistA X.eq (elements s1) (elements s2)).
  apply SortA_equivlistA_eqlistA with (ltA:=X.lt); auto with *.
  rewrite <- eq_Leq. transitivity s; auto. symmetry; auto.
 rewrite H in L.
 apply (StrictOrder_Irreflexive (elements s2)); auto.
 intros s1 s2 s3 (s1' & s2' & B1 & B2 & E1 & E2 & L12)
                 (s2'' & s3' & B2' & B3 & E2' & E3 & L23).
 exists s1', s3'; do 4 (split; trivial).
 assert (eqlistA X.eq (elements s2') (elements s2'')).
  apply SortA_equivlistA_eqlistA with (ltA:=X.lt); auto with *.
  rewrite <- eq_Leq. transitivity s2; auto. symmetry; auto.
 transitivity (elements s2'); auto.
 rewrite H; auto.
Qed.

Instance lt_compat : Proper (eq==>eq==>iff) lt.
Proof.
 intros s1 s2 E12 s3 s4 E34. split.
 intros (s1' & s3' & B1 & B3 & E1 & E3 & LT).
 exists s1', s3'; do 2 (split; trivial).
  split. transitivity s1; auto. symmetry; auto.
  split; auto. transitivity s3; auto. symmetry; auto.
 intros (s1' & s3' & B1 & B3 & E1 & E3 & LT).
 exists s1', s3'; do 2 (split; trivial).
  split. transitivity s2; auto.
  split; auto. transitivity s4; auto.
Qed.


(** * Proof of the comparison algorithm *)

(** [flatten_e e] returns the list of elements of [e] i.e. the list
    of elements actually compared *)

Fixpoint flatten_e (e : enumeration) : list elt := match e with
  | End => nil
  | More x t r => x :: elements t ++ flatten_e r
 end.

Lemma flatten_e_elements :
 forall l x r h e,
 elements l ++ flatten_e (More x r e) = elements (Node l x r h) ++ flatten_e e.
Proof.
 intros; simpl; apply elements_node.
Qed.

Lemma cons_1 : forall s e,
  flatten_e (cons s e) = elements s ++ flatten_e e.
Proof.
 induction s; simpl; auto; intros.
 rewrite IHs1; apply flatten_e_elements.
Qed.

Hint Unfold flip.

(** Correctness of this comparison *)

Definition Cmp c x y := CompSpec L.eq L.lt x y c.

Hint Unfold Cmp.

Lemma compare_end_Cmp :
 forall e2, Cmp (compare_end e2) nil (flatten_e e2).
Proof.
 destruct e2; simpl; constructor; auto. reflexivity.
Qed.

Lemma compare_more_Cmp : forall x1 cont x2 r2 e2 l,
  Cmp (cont (cons r2 e2)) l (elements r2 ++ flatten_e e2) ->
   Cmp (compare_more x1 cont (More x2 r2 e2)) (x1::l)
      (flatten_e (More x2 r2 e2)).
Proof.
 simpl; intros; elim_compare x1 x2; simpl; auto.
Qed.

Lemma compare_cont_Cmp : forall s1 cont e2 l,
 (forall e, Cmp (cont e) l (flatten_e e)) ->
 Cmp (compare_cont s1 cont e2) (elements s1 ++ l) (flatten_e e2).
Proof.
 induction s1 as [|l1 Hl1 x1 r1 Hr1 h1]; simpl; intros; auto.
 rewrite <- elements_node; simpl.
 apply Hl1; auto. clear e2. intros [|x2 r2 e2].
 simpl; auto.
 apply compare_more_Cmp.
 rewrite <- cons_1; auto.
Qed.

Lemma compare_Cmp : forall s1 s2,
 Cmp (compare s1 s2) (elements s1) (elements s2).
Proof.
 intros; unfold compare.
 rewrite (app_nil_end (elements s1)).
 replace (elements s2) with (flatten_e (cons s2 End)) by
  (rewrite cons_1; simpl; rewrite <- app_nil_end; auto).
 apply compare_cont_Cmp; auto.
 intros.
 apply compare_end_Cmp; auto.
Qed.

Lemma compare_spec : forall s1 s2 `{Ok s1, Ok s2},
 CompSpec eq lt s1 s2 (compare s1 s2).
Proof.
 intros.
 destruct (compare_Cmp s1 s2); constructor.
 rewrite eq_Leq; auto.
 intros; exists s1, s2; repeat split; auto.
 intros; exists s2, s1; repeat split; auto.
Qed.


(** * Equality test *)

Lemma equal_spec : forall s1 s2 `{Ok s1, Ok s2},
 equal s1 s2 = true <-> eq s1 s2.
Proof.
unfold equal; intros s1 s2 B1 B2.
destruct (@compare_spec s1 s2 B1 B2) as [H|H|H];
 split; intros H'; auto; try discriminate.
rewrite H' in H. elim (StrictOrder_Irreflexive s2); auto.
rewrite H' in H. elim (StrictOrder_Irreflexive s2); auto.
Qed.

End MakeRaw.



(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of binary search trees.
   They also happen to be well-balanced, but this has no influence
   on the correctness of operations, so we won't state this here,
   see [MSetFullAVL] if you need more than just the MSet interface.
*)

Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.
 Module Raw := MakeRaw I X.
 Include Raw2Sets X Raw.
End IntMake.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (X: OrderedType) <: S with Module E := X
 :=IntMake(Z_as_Int)(X).

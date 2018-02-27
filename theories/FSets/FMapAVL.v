(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Finite map library.  *)

(** * FMapAVL *)

(** This module implements maps using AVL trees.
    It follows the implementation from Ocaml's standard library.

    See the comments at the beginning of FSetAVL for more details.
*)

Require Import FunInd FMapInterface FMapList ZArith Int.

Set Implicit Arguments.
Unset Strict Implicit.

(** Notations and helper lemma about pairs *)

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

(** * The Raw functor

   Functor of pure functions + separate proofs of invariant
   preservation *)

Module Raw (Import I:Int)(X: OrderedType).
Local Open Scope pair_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope Int_scope.
Local Notation int := I.t.

Definition key := X.t.
Hint Transparent key.

(** * Trees *)

Section Elt.

Variable elt : Type.

(** * Trees

   The fifth field of [Node] is the height of the tree *)

Inductive tree :=
  | Leaf : tree
  | Node : tree -> key -> elt -> tree -> int -> tree.

Notation t := tree.

(** * Basic functions on trees: height and cardinal *)

Definition height (m : t) : int :=
  match m with
  | Leaf => 0
  | Node _ _ _ _ h => h
  end.

Fixpoint cardinal (m : t) : nat :=
  match m with
   | Leaf => 0%nat
   | Node l _ _ r _ => S (cardinal l + cardinal r)
  end.

(** * Empty Map *)

Definition empty := Leaf.

(** * Emptyness test *)

Definition is_empty m := match m with Leaf => true | _ => false end.

(** * Membership *)

(** The [mem] function is deciding membership. It exploits the [bst] property
    to achieve logarithmic complexity. *)

Fixpoint mem x m : bool :=
   match m with
     |  Leaf => false
     |  Node l y _ r _ => match X.compare x y with
             | LT _ => mem x l
             | EQ _ => true
             | GT _ => mem x r
         end
   end.

Fixpoint find x m : option elt :=
   match m with
     |  Leaf => None
     |  Node l y d r _ => match X.compare x y with
             | LT _ => find x l
             | EQ _ => Some d
             | GT _ => find x r
         end
   end.

(** * Helper functions *)

(** [create l x r] creates a node, assuming [l] and [r]
    to be balanced and [|height l - height r| <= 2]. *)

Definition create l x e r :=
   Node l x e r (max (height l) (height r) + 1).

(** [bal l x e r] acts as [create], but performs one step of
    rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

Definition assert_false := create.

Fixpoint bal l x d r :=
  let hl := height l in
  let hr := height r in
  if gt_le_dec hl (hr+2) then
    match l with
     | Leaf => assert_false l x d r
     | Node ll lx ld lr _ =>
       if ge_lt_dec (height ll) (height lr) then
         create ll lx ld (create lr x d r)
       else
         match lr with
          | Leaf => assert_false l x d r
          | Node lrl lrx lrd lrr _ =>
              create (create ll lx ld lrl) lrx lrd (create lrr x d r)
         end
    end
  else
    if gt_le_dec hr (hl+2) then
      match r with
       | Leaf => assert_false l x d r
       | Node rl rx rd rr _ =>
         if ge_lt_dec (height rr) (height rl) then
            create (create l x d rl) rx rd rr
         else
           match rl with
            | Leaf => assert_false l x d r
            | Node rll rlx rld rlr _ =>
                create (create l x d rll) rlx rld (create rlr rx rd rr)
           end
      end
    else
      create l x d r.

(** * Insertion *)

Fixpoint add x d m :=
  match m with
   | Leaf => Node Leaf x d Leaf 1
   | Node l y d' r h =>
      match X.compare x y with
         | LT _ => bal (add x d l) y d' r
         | EQ _ => Node l y d r h
         | GT _ => bal l y d' (add x d r)
      end
  end.

(** * Extraction of minimum binding

  Morally, [remove_min] is to be applied to a non-empty tree
  [t = Node l x e r h]. Since we can't deal here with [assert false]
  for [t=Leaf], we pre-unpack [t] (and forget about [h]).
*)

Fixpoint remove_min l x d r : t*(key*elt) :=
  match l with
    | Leaf => (r,(x,d))
    | Node ll lx ld lr lh =>
       let (l',m) := remove_min ll lx ld lr in
       (bal l' x d r, m)
  end.

(** * Merging two trees

  [merge t1 t2] builds the union of [t1] and [t2] assuming all elements
  of [t1] to be smaller than all elements of [t2], and
  [|height t1 - height t2| <= 2].
*)

Fixpoint merge s1 s2 :=  match s1,s2 with
  | Leaf, _ => s2
  | _, Leaf => s1
  | _, Node l2 x2 d2 r2 h2 =>
    match remove_min l2 x2 d2 r2 with
      (s2',(x,d)) => bal s1 x d s2'
    end
end.

(** * Deletion *)

Fixpoint remove x m := match m with
  | Leaf => Leaf
  | Node l y d r h =>
      match X.compare x y with
         | LT _ => bal (remove x l) y d r
         | EQ _ => merge l r
         | GT _ => bal l y d (remove x r)
      end
   end.

(** * join

    Same as [bal] but does not assume anything regarding heights of [l]
    and [r].
*)

Fixpoint join l : key -> elt -> t -> t :=
  match l with
    | Leaf => add
    | Node ll lx ld lr lh => fun x d =>
       fix join_aux (r:t) : t := match r with
          | Leaf =>  add x d l
          | Node rl rx rd rr rh =>
               if gt_le_dec lh (rh+2) then bal ll lx ld (join lr x d r)
               else if gt_le_dec rh (lh+2) then bal (join_aux rl) rx rd rr
               else create l x d r
          end
  end.

(** * Splitting

    [split x m] returns a triple [(l, o, r)] where
    - [l] is the set of elements of [m] that are [< x]
    - [r] is the set of elements of [m] that are [> x]
    - [o] is the result of [find x m].
*)

Record triple := mktriple { t_left:t; t_opt:option elt; t_right:t }.
Notation "<< l , b , r >>" := (mktriple l b r) (at level 9).

Fixpoint split x m : triple := match m with
  | Leaf => << Leaf, None, Leaf >>
  | Node l y d r h =>
     match X.compare x y with
      | LT _ => let (ll,o,rl) := split x l in << ll, o, join rl y d r >>
      | EQ _ => << l, Some d, r >>
      | GT _ => let (rl,o,rr) := split x r in << join l y d rl, o, rr >>
     end
 end.

(** * Concatenation

   Same as [merge] but does not assume anything about heights.
*)

Definition concat m1 m2 :=
   match m1, m2 with
      | Leaf, _ => m2
      | _ , Leaf => m1
      | _, Node l2 x2 d2 r2 _ =>
            let (m2',xd) := remove_min l2 x2 d2 r2 in
            join m1 xd#1 xd#2 m2'
   end.

(** * Elements *)

(** [elements_tree_aux acc t] catenates the elements of [t] in infix
    order to the list [acc] *)

Fixpoint elements_aux (acc : list (key*elt)) m : list (key*elt) :=
  match m with
   | Leaf => acc
   | Node l x d r _ => elements_aux ((x,d) :: elements_aux acc r) l
  end.

(** then [elements] is an instantiation with an empty [acc] *)

Definition elements := elements_aux nil.

(** * Fold *)

Fixpoint fold (A : Type) (f : key -> elt -> A -> A) (m : t) : A -> A :=
 fun a => match m with
  | Leaf => a
  | Node l x d r _ => fold f r (f x d (fold f l a))
 end.

(** * Comparison *)

Variable cmp : elt->elt->bool.

(** ** Enumeration of the elements of a tree *)

Inductive enumeration :=
 | End : enumeration
 | More : key -> elt -> t -> enumeration -> enumeration.

(** [cons m e] adds the elements of tree [m] on the head of
    enumeration [e]. *)

Fixpoint cons m e : enumeration :=
 match m with
  | Leaf => e
  | Node l x d r h => cons l (More x d r e)
 end.

(** One step of comparison of elements *)

Definition equal_more x1 d1 (cont:enumeration->bool) e2 :=
 match e2 with
 | End => false
 | More x2 d2 r2 e2 =>
     match X.compare x1 x2 with
      | EQ _ => cmp d1 d2 &&& cont (cons r2 e2)
      | _ => false
     end
 end.

(** Comparison of left tree, middle element, then right tree *)

Fixpoint equal_cont m1 (cont:enumeration->bool) e2 :=
 match m1 with
  | Leaf => cont e2
  | Node l1 x1 d1 r1 _ =>
     equal_cont l1 (equal_more x1 d1 (equal_cont r1 cont)) e2
  end.

(** Initial continuation *)

Definition equal_end e2 := match e2 with End => true | _ => false end.

(** The complete comparison *)

Definition equal m1 m2 := equal_cont m1 equal_end (cons m2 End).

End Elt.
Notation t := tree.
Notation "<< l , b , r >>" := (mktriple l b r) (at level 9).
Notation "t #l" := (t_left t) (at level 9, format "t '#l'").
Notation "t #o" := (t_opt t) (at level 9, format "t '#o'").
Notation "t #r" := (t_right t) (at level 9, format "t '#r'").


(** * Map *)

Fixpoint map (elt elt' : Type)(f : elt -> elt')(m : t elt) : t elt' :=
  match m with
   | Leaf _   => Leaf _
   | Node l x d r h => Node (map f l) x (f d) (map f r) h
  end.

(* * Mapi *)

Fixpoint mapi (elt elt' : Type)(f : key -> elt -> elt')(m : t elt) : t elt' :=
  match m with
   | Leaf _ => Leaf _
   | Node l x d r h => Node (mapi f l) x (f x d) (mapi f r) h
  end.

(** * Map with removal *)

Fixpoint map_option (elt elt' : Type)(f : key -> elt -> option elt')(m : t elt)
  : t elt' :=
  match m with
   | Leaf _ => Leaf _
   | Node l x d r h =>
      match f x d with
       | Some d' => join (map_option f l) x d' (map_option f r)
       | None => concat (map_option f l) (map_option f r)
      end
  end.

(** * Optimized map2

  Suggestion by B. Gregoire: a [map2] function with specialized
  arguments that allows bypassing some tree traversal. Instead of one
  [f0] of type [key -> option elt -> option elt' -> option elt''],
  we ask here for:
  - [f] which is a specialisation of [f0] when first option isn't [None]
  - [mapl] treats a [tree elt] with [f0] when second option is [None]
  - [mapr] treats a [tree elt'] with [f0] when first option is [None]

  The idea is that [mapl] and [mapr] can be instantaneous (e.g.
  the identity or some constant function).
*)

Section Map2_opt.
Variable elt elt' elt'' : Type.
Variable f : key -> elt -> option elt' -> option elt''.
Variable mapl : t elt -> t elt''.
Variable mapr : t elt' -> t elt''.

Fixpoint map2_opt m1 m2 :=
 match m1, m2 with
  | Leaf _, _ => mapr m2
  | _, Leaf _ => mapl m1
  | Node l1 x1 d1 r1 h1, _ =>
     let (l2',o2,r2') := split x1 m2 in
     match f x1 d1 o2 with
      | Some e => join (map2_opt l1 l2') x1 e (map2_opt r1 r2')
      | None => concat (map2_opt l1 l2') (map2_opt r1 r2')
     end
 end.

End Map2_opt.

(** * Map2

    The [map2] function of the Map interface can be implemented
    via [map2_opt] and [map_option].
*)

Section Map2.
Variable elt elt' elt'' : Type.
Variable f : option elt -> option elt' -> option elt''.

Definition map2 : t elt -> t elt' -> t elt'' :=
 map2_opt
   (fun _ d o => f (Some d) o)
   (map_option (fun _ d => f (Some d) None))
   (map_option (fun _ d' => f None (Some d'))).

End Map2.



(** * Invariants *)

Section Invariants.
Variable elt : Type.

(** ** Occurrence in a tree *)

Inductive MapsTo (x : key)(e : elt) : t elt -> Prop :=
  | MapsRoot : forall l r h y,
      X.eq x y -> MapsTo x e (Node l y e r h)
  | MapsLeft : forall l r h y e',
      MapsTo x e l -> MapsTo x e (Node l y e' r h)
  | MapsRight : forall l r h y e',
      MapsTo x e r -> MapsTo x e (Node l y e' r h).

Inductive In (x : key) : t elt -> Prop :=
  | InRoot : forall l r h y e,
      X.eq x y -> In x (Node l y e r h)
  | InLeft : forall l r h y e',
      In x l -> In x (Node l y e' r h)
  | InRight : forall l r h y e',
      In x r -> In x (Node l y e' r h).

Definition In0 k m := exists e:elt, MapsTo k e m.

(** ** Binary search trees *)

(** [lt_tree x s]: all elements in [s] are smaller than [x]
   (resp. greater for [gt_tree]) *)

Definition lt_tree x m := forall y, In y m -> X.lt y x.
Definition gt_tree x m := forall y, In y m -> X.lt x y.

(** [bst t] : [t] is a binary search tree *)

Inductive bst : t elt -> Prop :=
  | BSLeaf : bst (Leaf _)
  | BSNode : forall x e l r h, bst l -> bst r ->
     lt_tree x l -> gt_tree x r -> bst (Node l x e r h).

End Invariants.


(** * Correctness proofs, isolated in a sub-module *)

Module Proofs.
 Module MX := OrderedTypeFacts X.
 Module PX := KeyOrderedType X.
 Module L := FMapList.Raw X.

Functional Scheme mem_ind := Induction for mem Sort Prop.
Functional Scheme find_ind := Induction for find Sort Prop.
Functional Scheme bal_ind := Induction for bal Sort Prop.
Functional Scheme add_ind := Induction for add Sort Prop.
Functional Scheme remove_min_ind := Induction for remove_min Sort Prop.
Functional Scheme merge_ind := Induction for merge Sort Prop.
Functional Scheme remove_ind := Induction for remove Sort Prop.
Functional Scheme concat_ind := Induction for concat Sort Prop.
Functional Scheme split_ind := Induction for split Sort Prop.
Functional Scheme map_option_ind := Induction for map_option Sort Prop.
Functional Scheme map2_opt_ind := Induction for map2_opt Sort Prop.

(** * Automation and dedicated tactics. *)

Hint Constructors tree MapsTo In bst.
Hint Unfold lt_tree gt_tree.

Tactic Notation "factornode" ident(l) ident(x) ident(d) ident(r) ident(h)
 "as" ident(s) :=
 set (s:=Node l x d r h) in *; clearbody s; clear l x d r h.

(** A tactic for cleaning hypothesis after use of functional induction. *)

Ltac clearf :=
 match goal with
  | H : (@Logic.eq (Compare _ _ _ _) _ _) |- _ => clear H; clearf
  | H : (@Logic.eq (sumbool _ _) _ _) |- _ => clear H; clearf
  | _ => idtac
 end.

(** A tactic to repeat [inversion_clear] on all hyps of the
    form [(f (Node ...))] *)

Ltac inv f :=
  match goal with
     | H:f (Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ (Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ _ (Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ _ _ (Leaf _) |- _ => inversion_clear H; inv f
     | H:f (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ _ _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | _ => idtac
  end.

Ltac inv_all f :=
  match goal with
   | H: f _ |- _ => inversion_clear H; inv f
   | H: f _ _ |- _ => inversion_clear H; inv f
   | H: f _ _ _ |- _ => inversion_clear H; inv f
   | H: f _ _ _ _ |- _ => inversion_clear H; inv f
   | _ => idtac
  end.

(** Helper tactic concerning order of elements. *)

Ltac order := match goal with
 | U: lt_tree _ ?s, V: In _ ?s |- _ => generalize (U _ V); clear U; order
 | U: gt_tree _ ?s, V: In _ ?s |- _ => generalize (U _ V); clear U; order
 | _ => MX.order
end.

Ltac intuition_in := repeat (intuition; inv In; inv MapsTo).

(* Function/Functional Scheme can't deal with internal fix.
   Let's do its job by hand: *)

Ltac join_tac :=
 intros l; induction l as [| ll _ lx ld lr Hlr lh];
   [ | intros x d r; induction r as [| rl Hrl rx rd rr _ rh]; unfold join;
     [ | destruct (gt_le_dec lh (rh+2)) as [GT|LE];
       [ match goal with |- context [ bal ?u ?v ?w ?z ] =>
           replace (bal u v w z)
           with (bal ll lx ld (join lr x d (Node rl rx rd rr rh))); [ | auto]
         end
       | destruct (gt_le_dec rh (lh+2)) as [GT'|LE'];
         [ match goal with |- context [ bal ?u ?v ?w ?z ] =>
             replace (bal u v w z)
             with (bal (join (Node ll lx ld lr lh) x d rl) rx rd rr); [ | auto]
           end
         | ] ] ] ]; intros.

Section Elt.
Variable elt:Type.
Implicit Types m r : t elt.

(** * Basic results about [MapsTo], [In], [lt_tree], [gt_tree], [height] *)

(** Facts about [MapsTo] and [In]. *)

Lemma MapsTo_In : forall k e m, MapsTo k e m -> In k m.
Proof.
 induction 1; auto.
Qed.
Hint Resolve MapsTo_In.

Lemma In_MapsTo : forall k m, In k m -> exists e, MapsTo k e m.
Proof.
 induction 1; try destruct IHIn as (e,He); exists e; auto.
Qed.

Lemma In_alt : forall k m, In0 k m <-> In k m.
Proof.
 split.
 intros (e,H); eauto.
 unfold In0; apply In_MapsTo; auto.
Qed.

Lemma MapsTo_1 :
 forall m x y e, X.eq x y -> MapsTo x e m -> MapsTo y e m.
Proof.
 induction m; simpl; intuition_in; eauto.
Qed.
Hint Immediate MapsTo_1.

Lemma In_1 :
 forall m x y, X.eq x y -> In x m -> In y m.
Proof.
 intros m x y; induction m; simpl; intuition_in; eauto.
Qed.

Lemma In_node_iff :
 forall l x e r h y,
  In y (Node l x e r h) <-> In y l \/ X.eq y x \/ In y r.
Proof.
 intuition_in.
Qed.

(** Results about [lt_tree] and [gt_tree] *)

Lemma lt_leaf : forall x, lt_tree x (Leaf elt).
Proof.
 unfold lt_tree; intros; intuition_in.
Qed.

Lemma gt_leaf : forall x, gt_tree x (Leaf elt).
Proof.
  unfold gt_tree; intros; intuition_in.
Qed.

Lemma lt_tree_node : forall x y l r e h,
 lt_tree x l -> lt_tree x r -> X.lt y x -> lt_tree x (Node l y e r h).
Proof.
 unfold lt_tree in *; intuition_in; order.
Qed.

Lemma gt_tree_node : forall x y l r e h,
 gt_tree x l -> gt_tree x r -> X.lt x y -> gt_tree x (Node l y e r h).
Proof.
 unfold gt_tree in *; intuition_in; order.
Qed.

Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

Lemma lt_left : forall x y l r e h,
 lt_tree x (Node l y e r h) -> lt_tree x l.
Proof.
 intuition_in.
Qed.

Lemma lt_right : forall x y l r e h,
 lt_tree x (Node l y e r h) -> lt_tree x r.
Proof.
 intuition_in.
Qed.

Lemma gt_left : forall x y l r e h,
 gt_tree x (Node l y e r h) -> gt_tree x l.
Proof.
 intuition_in.
Qed.

Lemma gt_right : forall x y l r e h,
 gt_tree x (Node l y e r h) -> gt_tree x r.
Proof.
 intuition_in.
Qed.

Hint Resolve lt_left lt_right gt_left gt_right.

Lemma lt_tree_not_in :
 forall x m, lt_tree x m -> ~ In x m.
Proof.
 intros; intro; generalize (H _ H0); order.
Qed.

Lemma lt_tree_trans :
 forall x y, X.lt x y -> forall m, lt_tree x m -> lt_tree y m.
Proof.
 eauto.
Qed.

Lemma gt_tree_not_in :
 forall x m, gt_tree x m -> ~ In x m.
Proof.
 intros; intro; generalize (H _ H0); order.
Qed.

Lemma gt_tree_trans :
 forall x y, X.lt y x -> forall m, gt_tree x m -> gt_tree y m.
Proof.
 eauto.
Qed.

Hint Resolve lt_tree_not_in lt_tree_trans gt_tree_not_in gt_tree_trans.

(** * Empty map *)

Definition Empty m := forall (a:key)(e:elt) , ~ MapsTo a e m.

Lemma empty_bst : bst (empty elt).
Proof.
 unfold empty; auto.
Qed.

Lemma empty_1 : Empty (empty elt).
Proof.
 unfold empty, Empty; intuition_in.
Qed.

(** * Emptyness test *)

Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
Proof.
 destruct m as [|r x e l h]; simpl; auto.
 intro H; elim (H x e); auto.
Qed.

Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
Proof.
 destruct m; simpl; intros; try discriminate; red; intuition_in.
Qed.

(** * Membership *)

Lemma mem_1 : forall m x, bst m -> In x m -> mem x m = true.
Proof.
 intros m x; functional induction (mem x m); auto; intros; clearf;
  inv bst; intuition_in; order.
Qed.

Lemma mem_2 : forall m x, mem x m = true -> In x m.
Proof.
 intros m x; functional induction (mem x m); auto; intros; discriminate.
Qed.

Lemma find_1 : forall m x e, bst m -> MapsTo x e m -> find x m = Some e.
Proof.
 intros m x; functional induction (find x m); auto; intros; clearf;
  inv bst; intuition_in; simpl; auto;
 try solve [order | absurd (X.lt x y); eauto | absurd (X.lt y x); eauto].
Qed.

Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
Proof.
 intros m x; functional induction (find x m); subst; intros; clearf;
  try discriminate.
 constructor 2; auto.
 inversion H; auto.
 constructor 3; auto.
Qed.

Lemma find_iff : forall m x e, bst m ->
 (find x m = Some e <-> MapsTo x e m).
Proof.
 split; auto using find_1, find_2.
Qed.

Lemma find_in : forall m x, find x m <> None -> In x m.
Proof.
 intros.
 case_eq (find x m); [intros|congruence].
 apply MapsTo_In with e; apply find_2; auto.
Qed.

Lemma in_find : forall m x, bst m -> In x m -> find x m <> None.
Proof.
 intros.
 destruct (In_MapsTo H0) as (d,Hd).
 rewrite (find_1 H Hd); discriminate.
Qed.

Lemma find_in_iff : forall m x, bst m ->
 (find x m <> None <-> In x m).
Proof.
 split; auto using find_in, in_find.
Qed.

Lemma not_find_iff : forall m x, bst m ->
 (find x m = None <-> ~In x m).
Proof.
 split; intros.
 red; intros.
 elim (in_find H H1 H0).
 case_eq (find x m); [ intros | auto ].
 elim H0; apply find_in; congruence.
Qed.

Lemma find_find : forall m m' x,
 find x m = find x m' <->
 (forall d, find x m = Some d <-> find x m' = Some d).
Proof.
 intros; destruct (find x m); destruct (find x m'); split; intros;
  try split; try congruence.
 rewrite H; auto.
 symmetry; rewrite <- H; auto.
 rewrite H; auto.
Qed.

Lemma find_mapsto_equiv : forall m m' x, bst m -> bst m' ->
 (find x m = find x m' <->
  (forall d, MapsTo x d m <-> MapsTo x d m')).
Proof.
 intros m m' x Hm Hm'.
 rewrite find_find.
 split; intros H d; specialize H with d.
 rewrite <- 2 find_iff; auto.
 rewrite 2 find_iff; auto.
Qed.

Lemma find_in_equiv : forall m m' x, bst m -> bst m' ->
 find x m = find x m' ->
 (In x m <-> In x m').
Proof.
 split; intros; apply find_in; [ rewrite <- H1 | rewrite H1 ];
  apply in_find; auto.
Qed.

(** * Helper functions *)

Lemma create_bst :
 forall l x e r, bst l -> bst r -> lt_tree x l -> gt_tree x r ->
 bst (create l x e r).
Proof.
 unfold create; auto.
Qed.
Hint Resolve create_bst.

Lemma create_in :
 forall l x e r y,
  In y (create l x e r) <-> X.eq y x \/ In y l \/ In y r.
Proof.
 unfold create; split; [ inversion_clear 1 | ]; intuition.
Qed.

Lemma bal_bst : forall l x e r, bst l -> bst r ->
 lt_tree x l -> gt_tree x r -> bst (bal l x e r).
Proof.
 intros l x e r; functional induction (bal l x e r); intros; clearf;
 inv bst; repeat apply create_bst; auto; unfold create; try constructor;
 (apply lt_tree_node || apply gt_tree_node); auto;
 (eapply lt_tree_trans || eapply gt_tree_trans); eauto. 
Qed.
Hint Resolve bal_bst.

Lemma bal_in : forall l x e r y,
 In y (bal l x e r) <-> X.eq y x \/ In y l \/ In y r.
Proof.
 intros l x e r; functional induction (bal l x e r); intros; clearf;
 rewrite !create_in; intuition_in.
Qed.

Lemma bal_mapsto : forall l x e r y e',
 MapsTo y e' (bal l x e r) <-> MapsTo y e' (create l x e r).
Proof.
 intros l x e r; functional induction (bal l x e r); intros; clearf;
 unfold assert_false, create; intuition_in.
Qed.

Lemma bal_find : forall l x e r y,
 bst l -> bst r -> lt_tree x l -> gt_tree x r ->
 find y (bal l x e r) = find y (create l x e r).
Proof.
 intros; rewrite find_mapsto_equiv; auto; intros; apply bal_mapsto.
Qed.

(** * Insertion *)

Lemma add_in : forall m x y e,
 In y (add x e m) <-> X.eq y x \/ In y m.
Proof.
 intros m x y e; functional induction (add x e m); auto; intros;
 try (rewrite bal_in, IHt); intuition_in.
 apply In_1 with x; auto.
Qed.

Lemma add_bst : forall m x e, bst m -> bst (add x e m).
Proof.
 intros m x e; functional induction (add x e m); intros;
  inv bst; try apply bal_bst; auto;
  intro z; rewrite add_in; intuition.
 apply MX.eq_lt with x; auto.
 apply MX.lt_eq with x; auto.
Qed.
Hint Resolve add_bst.

Lemma add_1 : forall m x y e, X.eq x y -> MapsTo y e (add x e m).
Proof.
 intros m x y e; functional induction (add x e m);
   intros; inv bst; try rewrite bal_mapsto; unfold create; eauto.
Qed.

Lemma add_2 : forall m x y e e', ~X.eq x y ->
 MapsTo y e m -> MapsTo y e (add x e' m).
Proof.
 intros m x y e e'; induction m; simpl; auto.
 destruct (X.compare x k);
 intros; inv bst; try rewrite bal_mapsto; unfold create; auto;
   inv MapsTo; auto; order.
Qed.

Lemma add_3 : forall m x y e e', ~X.eq x y ->
 MapsTo y e (add x e' m) -> MapsTo y e m.
Proof.
 intros m x y e e'; induction m; simpl; auto.
 intros; inv MapsTo; auto; order.
 destruct (X.compare x k); intro;
  try rewrite bal_mapsto; auto; unfold create; intros; inv MapsTo; auto;
  order.
Qed.

Lemma add_find : forall m x y e, bst m ->
 find y (add x e m) =
  match X.compare y x with EQ _ => Some e | _ => find y m end.
Proof.
 intros.
 assert (~X.eq x y -> find y (add x e m) = find y m).
  intros; rewrite find_mapsto_equiv; auto.
  split; eauto using add_2, add_3.
 destruct X.compare; try (apply H0; order).
 auto using find_1, add_1.
Qed.

(** * Extraction of minimum binding *)

Lemma remove_min_in : forall l x e r h y,
 In y (Node l x e r h) <->
  X.eq y (remove_min l x e r)#2#1 \/ In y (remove_min l x e r)#1.
Proof.
 intros l x e r; functional induction (remove_min l x e r); simpl in *; intros.
 intuition_in.
 rewrite e0 in *; simpl; intros.
 rewrite bal_in, In_node_iff, IHp; intuition.
Qed.

Lemma remove_min_mapsto : forall l x e r h y e',
  MapsTo y e' (Node l x e r h) <->
   ((X.eq y (remove_min l x e r)#2#1) /\ e' = (remove_min l x e r)#2#2)
    \/ MapsTo y e' (remove_min l x e r)#1.
Proof.
 intros l x e r; functional induction (remove_min l x e r); simpl in *; intros.
 intuition_in; subst; auto.
 rewrite e0 in *; simpl; intros.
 rewrite bal_mapsto; auto; unfold create.
 simpl in *;destruct (IHp _x y e').
 intuition.
 inversion_clear H1; intuition.
 inversion_clear H3; intuition.
Qed.

Lemma remove_min_bst : forall l x e r h,
 bst (Node l x e r h) -> bst (remove_min l x e r)#1.
Proof.
 intros l x e r; functional induction (remove_min l x e r); simpl in *; intros.
 inv bst; auto.
 inversion_clear H; inversion_clear H0.
 apply bal_bst; auto.
 rewrite e0 in *; simpl in *; apply (IHp _x); auto.
 intro; intros.
 generalize (remove_min_in ll lx ld lr _x y).
 rewrite e0; simpl in *.
 destruct 1.
 apply H2; intuition.
Qed.
Hint Resolve remove_min_bst.

Lemma remove_min_gt_tree : forall l x e r h,
 bst (Node l x e r h) ->
 gt_tree (remove_min l x e r)#2#1 (remove_min l x e r)#1.
Proof.
 intros l x e r; functional induction (remove_min l x e r); simpl in *; intros.
 inv bst; auto.
 inversion_clear H.
 intro; intro.
 rewrite e0 in *;simpl in *.
 generalize (IHp _x H0).
 generalize (remove_min_in ll lx ld lr _x m#1).
 rewrite e0; simpl; intros.
 rewrite (bal_in l' x d r y) in H.
 assert (In m#1 (Node ll lx ld lr _x)) by (rewrite H4; auto); clear H4.
 assert (X.lt m#1 x) by order.
 decompose [or] H; order.
Qed.
Hint Resolve remove_min_gt_tree.

Lemma remove_min_find : forall l x e r h y,
 bst (Node l x e r h) ->
 find y (Node l x e r h) =
   match X.compare y (remove_min l x e r)#2#1 with
    | LT _ => None
    | EQ _ => Some (remove_min l x e r)#2#2
    | GT _ => find y (remove_min l x e r)#1
   end.
Proof.
 intros.
 destruct X.compare.
 rewrite not_find_iff; auto.
 rewrite remove_min_in; red; destruct 1 as [H'|H']; [ order | ].
 generalize (remove_min_gt_tree H H'); order.
 apply find_1; auto.
 rewrite remove_min_mapsto; auto.
 rewrite find_mapsto_equiv; eauto; intros.
 rewrite remove_min_mapsto; intuition; order.
Qed.

(** * Merging two trees *)

Lemma merge_in : forall m1 m2 y, bst m1 -> bst m2 ->
 (In y (merge m1 m2) <-> In y m1 \/ In y m2).
Proof.
 intros m1 m2; functional induction (merge m1 m2);intros;
  try factornode _x _x0 _x1 _x2 _x3 as m1.
 intuition_in.
 intuition_in.
 rewrite bal_in, remove_min_in, e1; simpl; intuition.
Qed.

Lemma merge_mapsto : forall m1 m2 y e, bst m1 -> bst m2 ->
  (MapsTo y e (merge m1 m2) <-> MapsTo y e m1 \/ MapsTo y e m2).
Proof.
 intros m1 m2; functional induction (merge m1 m2); intros;
  try factornode _x _x0 _x1 _x2 _x3 as m1.
 intuition_in.
 intuition_in.
 rewrite bal_mapsto, remove_min_mapsto, e1; simpl; auto.
 unfold create.
 intuition; subst; auto.
 inversion_clear H1; intuition.
Qed.

Lemma merge_bst : forall m1 m2, bst m1 -> bst m2 ->
 (forall y1 y2 : key, In y1 m1 -> In y2 m2 -> X.lt y1 y2) ->
 bst (merge m1 m2).
Proof.
 intros m1 m2; functional induction (merge m1 m2); intros; auto;
 try factornode _x _x0 _x1 _x2 _x3 as m1.
 apply bal_bst; auto.
 generalize (remove_min_bst H0); rewrite e1; simpl in *; auto.
 intro; intro.
 apply H1; auto.
 generalize (remove_min_in l2 x2 d2 r2 _x4 x); rewrite e1; simpl; intuition.
 generalize (remove_min_gt_tree H0); rewrite e1; simpl; auto.
Qed.

(** * Deletion *)

Lemma remove_in : forall m x y, bst m ->
 (In y (remove x m) <-> ~ X.eq y x /\ In y m).
Proof.
 intros m x; functional induction (remove x m); simpl; intros.
 intuition_in.
 (* LT *)
 inv bst; clear e0.
 rewrite bal_in; auto.
 generalize (IHt y0 H0); intuition; [ order | order | intuition_in ].
 (* EQ *)
 inv bst; clear e0.
 rewrite merge_in; intuition; [ order | order | intuition_in ].
 elim H4; eauto.
 (* GT *)
 inv bst; clear e0.
 rewrite bal_in; auto.
 generalize (IHt y0 H1); intuition; [ order | order | intuition_in ].
Qed.

Lemma remove_bst : forall m x, bst m -> bst (remove x m).
Proof.
 intros m x; functional induction (remove x m); simpl; intros.
 auto.
 (* LT *)
 inv bst.
 apply bal_bst; auto.
 intro; intro.
 rewrite (remove_in x y0 H0) in H; auto.
 destruct H; eauto.
 (* EQ *)
 inv bst.
 apply merge_bst; eauto.
 (* GT *)
 inv bst.
 apply bal_bst; auto.
 intro; intro.
 rewrite (remove_in x y0 H1) in H; auto.
 destruct H; eauto.
Qed.

Lemma remove_1 : forall m x y, bst m -> X.eq x y -> ~ In y (remove x m).
Proof.
 intros; rewrite remove_in; intuition.
Qed.

Lemma remove_2 : forall m x y e, bst m -> ~X.eq x y ->
 MapsTo y e m -> MapsTo y e (remove x m).
Proof.
 intros m x y e; induction m; simpl; auto.
 destruct (X.compare x k);
   intros; inv bst; try rewrite bal_mapsto; unfold create; auto;
   try solve [inv MapsTo; auto].
 rewrite merge_mapsto; auto.
 inv MapsTo; auto; order.
Qed.

Lemma remove_3 : forall m x y e, bst m ->
 MapsTo y e (remove x m) -> MapsTo y e m.
Proof.
 intros m x y e; induction m; simpl; auto.
 destruct (X.compare x k); intros Bs; inv bst;
  try rewrite bal_mapsto; auto; unfold create.
  intros; inv MapsTo; auto.
  rewrite merge_mapsto; intuition.
  intros; inv MapsTo; auto.
Qed.

(** * join *)

Lemma join_in : forall l x d r y,
 In y (join l x d r) <-> X.eq y x \/ In y l \/ In y r.
Proof.
 join_tac.
 simpl.
 rewrite add_in; intuition_in.
 rewrite add_in; intuition_in.
 rewrite bal_in, Hlr; clear Hlr Hrl; intuition_in.
 rewrite bal_in, Hrl; clear Hlr Hrl; intuition_in.
 apply create_in.
Qed.

Lemma join_bst : forall l x d r, bst l -> bst r ->
 lt_tree x l -> gt_tree x r -> bst (join l x d r).
Proof.
 join_tac; auto; try (simpl; auto; fail); inv bst; apply bal_bst; auto;
 clear Hrl Hlr; intro; intros; rewrite join_in in *.
 intuition; [ apply MX.lt_eq with x | ]; eauto.
 intuition; [ apply MX.eq_lt with x | ]; eauto.
Qed.
Hint Resolve join_bst.

Lemma join_find : forall l x d r y,
 bst l -> bst r -> lt_tree x l -> gt_tree x r ->
 find y (join l x d r) = find y (create l x d r).
Proof.
 join_tac; auto; inv bst;
  simpl (join (Leaf elt));
  try (assert (X.lt lx x) by auto);
  try (assert (X.lt x rx) by auto);
  rewrite ?add_find, ?bal_find; auto.

 simpl; destruct X.compare; auto.
 rewrite not_find_iff; auto; intro; order.

 simpl; repeat (destruct X.compare; auto); try (order; fail).
 rewrite not_find_iff by auto; intro.
 assert (X.lt y x) by auto; order.

 simpl; rewrite Hlr; simpl; auto.
 repeat (destruct X.compare; auto); order.
 intros u Hu; rewrite join_in in Hu.
  destruct Hu as [Hu|[Hu|Hu]]; try generalize (H2 _ Hu); order.

 simpl; rewrite Hrl; simpl; auto.
 repeat (destruct X.compare; auto); order.
 intros u Hu; rewrite join_in in Hu.
  destruct Hu as [Hu|[Hu|Hu]]; order.
Qed.

(** * split *)

Lemma split_in_1 : forall m x, bst m -> forall y,
 (In y (split x m)#l <-> In y m /\ X.lt y x).
Proof.
 intros m x; functional induction (split x m); simpl; intros;
  inv bst; try clear e0.
 intuition_in.
 rewrite e1 in IHt; simpl in IHt; rewrite IHt; intuition_in; order.
 intuition_in; order.
 rewrite join_in.
 rewrite e1 in IHt; simpl in IHt; rewrite IHt; intuition_in; order.
Qed.

Lemma split_in_2 : forall m x, bst m -> forall y,
 (In y (split x m)#r <-> In y m /\ X.lt x y).
Proof.
 intros m x; functional induction (split x m); subst; simpl; intros;
  inv bst; try clear e0.
 intuition_in.
 rewrite join_in.
 rewrite e1 in IHt; simpl in IHt; rewrite IHt; intuition_in; order.
 intuition_in; order.
 rewrite e1 in IHt; simpl in IHt; rewrite IHt; intuition_in; order.
Qed.

Lemma split_in_3 : forall m x, bst m ->
 (split x m)#o = find x m.
Proof.
 intros m x; functional induction (split x m); subst; simpl; auto;
  intros; inv bst; try clear e0;
  destruct X.compare; try order; trivial; rewrite <- IHt, e1; auto.
Qed.

Lemma split_bst : forall m x, bst m ->
 bst (split x m)#l /\ bst (split x m)#r.
Proof.
 intros m x; functional induction (split x m); subst; simpl; intros;
  inv bst; try clear e0; try rewrite e1 in *; simpl in *; intuition;
  apply join_bst; auto.
 intros y0.
 generalize (split_in_2 x H0 y0); rewrite e1; simpl; intuition.
 intros y0.
 generalize (split_in_1 x H1 y0); rewrite e1; simpl; intuition.
Qed.

Lemma split_lt_tree : forall m x, bst m -> lt_tree x (split x m)#l.
Proof.
 intros m x B y Hy; rewrite split_in_1 in Hy; intuition.
Qed.

Lemma split_gt_tree : forall m x, bst m -> gt_tree x (split x m)#r.
Proof.
 intros m x B y Hy; rewrite split_in_2 in Hy; intuition.
Qed.

Lemma split_find : forall m x y, bst m ->
 find y m = match X.compare y x with
              | LT _ => find y (split x m)#l
              | EQ _ => (split x m)#o
              | GT _ => find y (split x m)#r
            end.
Proof.
 intros m x; functional induction (split x m); subst; simpl; intros;
  inv bst; try clear e0; try rewrite e1 in *; simpl in *;
  [ destruct X.compare; auto | .. ];
  try match goal with E:split ?x ?t = _, B:bst ?t |- _ =>
      generalize (split_in_1 x B)(split_in_2 x B)(split_bst x B);
       rewrite E; simpl; destruct 3 end.

 rewrite join_find, IHt; auto; clear IHt; simpl.
 repeat (destruct X.compare; auto); order.
 intro y1; rewrite H4; intuition.

 repeat (destruct X.compare; auto); order.

 rewrite join_find, IHt; auto; clear IHt; simpl.
 repeat (destruct X.compare; auto); order.
 intros y1; rewrite H; intuition.
Qed.

(** * Concatenation *)

Lemma concat_in : forall m1 m2 y,
 In y (concat m1 m2) <-> In y m1 \/ In y m2.
Proof.
 intros m1 m2; functional induction (concat m1 m2); intros;
  try factornode _x _x0 _x1 _x2 _x3 as m1.
 intuition_in.
 intuition_in.
 rewrite join_in, remove_min_in, e1; simpl; intuition.
Qed.

Lemma concat_bst : forall m1 m2, bst m1 -> bst m2 ->
 (forall y1 y2, In y1 m1 -> In y2 m2 -> X.lt y1 y2) ->
 bst (concat m1 m2).
Proof.
 intros m1 m2; functional induction (concat m1 m2); intros; auto;
 try factornode _x _x0 _x1 _x2 _x3 as m1.
 apply join_bst; auto.
 change (bst (m2',xd)#1). rewrite <-e1; eauto.
 intros y Hy.
 apply H1; auto.
 rewrite remove_min_in, e1; simpl; auto.
 change (gt_tree (m2',xd)#2#1 (m2',xd)#1). rewrite <-e1; eauto.
Qed.
Hint Resolve concat_bst.

Lemma concat_find : forall m1 m2 y, bst m1 -> bst m2 ->
 (forall y1 y2, In y1 m1 -> In y2 m2 -> X.lt y1 y2) ->
 find y (concat m1 m2) =
  match find y m2 with Some d => Some d | None => find y m1 end.
Proof.
 intros m1 m2; functional induction (concat m1 m2); intros; auto;
 try factornode _x _x0 _x1 _x2 _x3 as m1.
 simpl; destruct (find y m2); auto.

 generalize (remove_min_find y H0)(remove_min_in l2 x2 d2 r2 _x4)
  (remove_min_bst H0)(remove_min_gt_tree H0);
  rewrite e1; simpl fst; simpl snd; intros.

 inv bst.
 rewrite H2, join_find; auto; clear H2.
 simpl; destruct X.compare as [Hlt| |Hlt]; simpl; auto.
 destruct (find y m2'); auto.
 symmetry; rewrite not_find_iff; auto; intro.
 apply (MX.lt_not_gt Hlt); apply H1; auto; rewrite H3; auto.

 intros z Hz; apply H1; auto; rewrite H3; auto.
Qed.


(** * Elements *)

Notation eqk := (PX.eqk (elt:= elt)).
Notation eqke := (PX.eqke (elt:= elt)).
Notation ltk := (PX.ltk (elt:= elt)).

Lemma elements_aux_mapsto : forall (s:t elt) acc x e,
 InA eqke (x,e) (elements_aux acc s) <-> MapsTo x e s \/ InA eqke (x,e) acc.
Proof.
 induction s as [ | l Hl x e r Hr h ]; simpl; auto.
 intuition.
 inversion H0.
 intros.
 rewrite Hl.
 destruct (Hr acc x0 e0); clear Hl Hr.
 intuition; inversion_clear H3; intuition.
 destruct H0; simpl in *; subst; intuition.
Qed.

Lemma elements_mapsto : forall (s:t elt) x e, InA eqke (x,e) (elements s) <-> MapsTo x e s.
Proof.
 intros; generalize (elements_aux_mapsto s nil x e); intuition.
 inversion_clear H0.
Qed.

Lemma elements_in : forall (s:t elt) x, L.PX.In x (elements s) <-> In x s.
Proof.
 intros.
 unfold L.PX.In.
 rewrite <- In_alt; unfold In0.
 firstorder.
 exists x0.
 rewrite <- elements_mapsto; auto.
 exists x0.
 unfold L.PX.MapsTo; rewrite elements_mapsto; auto.
Qed.

Lemma elements_aux_sort : forall (s:t elt) acc, bst s -> sort ltk acc ->
 (forall x e y, InA eqke (x,e) acc -> In y s -> X.lt y x) ->
 sort ltk (elements_aux acc s).
Proof.
 induction s as [ | l Hl y e r Hr h]; simpl; intuition.
 inv bst.
 apply Hl; auto.
 constructor.
 apply Hr; eauto.
 apply InA_InfA with (eqA:=eqke); auto with *. intros (y',e') H6.
 destruct (elements_aux_mapsto r acc y' e'); intuition.
 red; simpl; eauto.
 red; simpl; eauto.
 intros.
 inversion_clear H.
 destruct H7; simpl in *.
 order.
 destruct (elements_aux_mapsto r acc x e0); intuition eauto. 
Qed.

Lemma elements_sort : forall s : t elt, bst s -> sort ltk (elements s).
Proof.
 intros; unfold elements; apply elements_aux_sort; auto.
 intros; inversion H0.
Qed.
Hint Resolve elements_sort.

Lemma elements_nodup : forall s : t elt, bst s -> NoDupA eqk (elements s).
Proof.
 intros; apply PX.Sort_NoDupA; auto.
Qed.

Lemma elements_aux_cardinal :
 forall (m:t elt) acc, (length acc + cardinal m)%nat = length (elements_aux acc m).
Proof.
 simple induction m; simpl; intuition.
 rewrite <- H; simpl.
 rewrite <- H0; omega.
Qed.

Lemma elements_cardinal : forall (m:t elt), cardinal m = length (elements m).
Proof.
 exact (fun m => elements_aux_cardinal m nil).
Qed.

Lemma elements_app :
 forall (s:t elt) acc, elements_aux acc s = elements s ++ acc.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1, IHs2.
 unfold elements; simpl.
 rewrite 2 IHs1, IHs2, !app_nil_r, !app_ass; auto.
Qed.

Lemma elements_node :
 forall (t1 t2:t elt) x e z l,
 elements t1 ++ (x,e) :: elements t2 ++ l =
 elements (Node t1 x e t2 z) ++ l.
Proof.
 unfold elements; simpl; intros.
 rewrite !elements_app, !app_nil_r, !app_ass; auto.
Qed.

(** * Fold *)

Definition fold' (A : Type) (f : key -> elt -> A -> A)(s : t elt) :=
  L.fold f (elements s).

Lemma fold_equiv_aux :
 forall (A : Type) (s : t elt) (f : key -> elt -> A -> A) (a : A) acc,
 L.fold f (elements_aux acc s) a = L.fold f acc (fold f s a).
Proof.
 simple induction s.
 simpl; intuition.
 simpl; intros.
 rewrite H.
 simpl.
 apply H0.
Qed.

Lemma fold_equiv :
 forall (A : Type) (s : t elt) (f : key -> elt -> A -> A) (a : A),
 fold f s a = fold' f s a.
Proof.
 unfold fold', elements.
 simple induction s; simpl; auto; intros.
 rewrite fold_equiv_aux.
 rewrite H0.
 simpl; auto.
Qed.

Lemma fold_1 :
 forall (s:t elt)(Hs:bst s)(A : Type)(i:A)(f : key -> elt -> A -> A),
 fold f s i = fold_left (fun a p => f p#1 p#2 a) (elements s) i.
Proof.
 intros.
 rewrite fold_equiv.
 unfold fold'.
 rewrite L.fold_1.
 unfold L.elements; auto.
Qed.

(** * Comparison *)

(** [flatten_e e] returns the list of elements of the enumeration [e]
    i.e. the list of elements actually compared *)

Fixpoint flatten_e (e : enumeration elt) : list (key*elt) := match e with
  | End _ => nil
  | More x e t r => (x,e) :: elements t ++ flatten_e r
 end.

Lemma flatten_e_elements :
 forall (l:t elt) r x d z e,
 elements l ++ flatten_e (More x d r e) =
 elements (Node l x d r z) ++ flatten_e e.
Proof.
 intros; apply elements_node.
Qed.

Lemma cons_1 : forall (s:t elt) e,
  flatten_e (cons s e) = elements s ++ flatten_e e.
Proof.
  induction s; auto; intros.
  simpl flatten_e; rewrite IHs1; apply flatten_e_elements; auto.
Qed.

(** Proof of correction for the comparison *)

Variable cmp : elt->elt->bool.

Definition IfEq b l1 l2 := L.equal cmp l1 l2 = b.

Lemma cons_IfEq : forall b x1 x2 d1 d2 l1 l2,
  X.eq x1 x2 -> cmp d1 d2 = true ->
  IfEq b l1 l2 ->
    IfEq b ((x1,d1)::l1) ((x2,d2)::l2).
Proof.
 unfold IfEq; destruct b; simpl; intros; destruct X.compare; simpl;
  try rewrite H0; auto; order.
Qed.

Lemma equal_end_IfEq : forall e2,
  IfEq (equal_end e2) nil (flatten_e e2).
Proof.
 destruct e2; red; auto.
Qed.

Lemma equal_more_IfEq :
 forall x1 d1 (cont:enumeration elt -> bool) x2 d2 r2 e2 l,
  IfEq (cont (cons r2 e2)) l (elements r2 ++ flatten_e e2) ->
    IfEq (equal_more cmp x1 d1 cont (More x2 d2 r2 e2)) ((x1,d1)::l)
       (flatten_e (More x2 d2 r2 e2)).
Proof.
 unfold IfEq; simpl; intros; destruct X.compare; simpl; auto.
 rewrite <-andb_lazy_alt; f_equal; auto.
Qed.

Lemma equal_cont_IfEq : forall m1 cont e2 l,
  (forall e, IfEq (cont e) l (flatten_e e)) ->
  IfEq (equal_cont cmp m1 cont e2) (elements m1 ++ l) (flatten_e e2).
Proof.
 induction m1 as [|l1 Hl1 x1 d1 r1 Hr1 h1]; intros; auto.
 rewrite <- elements_node; simpl.
 apply Hl1; auto.
 clear e2; intros [|x2 d2 r2 e2].
 simpl; red; auto.
 apply equal_more_IfEq.
 rewrite <- cons_1; auto.
Qed.

Lemma equal_IfEq : forall (m1 m2:t elt),
  IfEq (equal cmp m1 m2) (elements m1) (elements m2).
Proof.
 intros; unfold equal.
 rewrite <- (app_nil_r (elements m1)).
 replace (elements m2) with (flatten_e (cons m2 (End _)))
  by (rewrite cons_1; simpl; rewrite app_nil_r; auto).
 apply equal_cont_IfEq.
 intros.
 apply equal_end_IfEq; auto.
Qed.

Definition Equivb m m' :=
  (forall k, In k m <-> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Lemma Equivb_elements : forall s s',
 Equivb s s' <-> L.Equivb cmp (elements s) (elements s').
Proof.
unfold Equivb, L.Equivb; split; split; intros.
do 2 rewrite elements_in; firstorder.
destruct H.
apply (H2 k); rewrite <- elements_mapsto; auto.
do 2 rewrite <- elements_in; firstorder.
destruct H.
apply (H2 k); unfold L.PX.MapsTo; rewrite elements_mapsto; auto.
Qed.

Lemma equal_Equivb : forall (s s': t elt), bst s -> bst s' ->
  (equal cmp s s' = true <-> Equivb s s').
Proof.
 intros s s' B B'.
 rewrite Equivb_elements, <- equal_IfEq.
 split; [apply L.equal_2|apply L.equal_1]; auto.
Qed.

End Elt.

Section Map.
Variable elt elt' : Type.
Variable f : elt -> elt'.

Lemma map_1 : forall (m: t elt)(x:key)(e:elt),
    MapsTo x e m -> MapsTo x (f e) (map f m).
Proof.
induction m; simpl; inversion_clear 1; auto.
Qed.

Lemma map_2 : forall (m: t elt)(x:key),
    In x (map f m) -> In x m.
Proof.
induction m; simpl; inversion_clear 1; auto.
Qed.

Lemma map_bst : forall m, bst m -> bst (map f m).
Proof.
induction m; simpl; auto.
inversion_clear 1; constructor; auto;
 red; auto using map_2.
Qed.

End Map.
Section Mapi.
Variable elt elt' : Type.
Variable f : key -> elt -> elt'.

Lemma mapi_1 : forall (m: tree elt)(x:key)(e:elt),
    MapsTo x e m -> exists y, X.eq y x /\ MapsTo x (f y e) (mapi f m).
Proof.
induction m; simpl; inversion_clear 1; auto.
exists k; auto.
destruct (IHm1 _ _ H0).
exists x0; intuition.
destruct (IHm2 _ _ H0).
exists x0; intuition.
Qed.

Lemma mapi_2 : forall (m: t elt)(x:key),
    In x (mapi f m) -> In x m.
Proof.
induction m; simpl; inversion_clear 1; auto.
Qed.

Lemma mapi_bst : forall m, bst m -> bst (mapi f m).
Proof.
induction m; simpl; auto.
inversion_clear 1; constructor; auto;
 red; auto using mapi_2.
Qed.

End Mapi.

Section Map_option.
Variable elt elt' : Type.
Variable f : key -> elt -> option elt'.
Hypothesis f_compat : forall x x' d, X.eq x x' -> f x d = f x' d.

Lemma map_option_2 : forall (m:t elt)(x:key),
 In x (map_option f m) -> exists d, MapsTo x d m /\ f x d <> None.
Proof.
intros m; functional induction (map_option f m); simpl; auto; intros.
inversion H.
rewrite join_in in H; destruct H as [H|[H|H]].
exists d; split; auto; rewrite (f_compat d H), e0; discriminate.
destruct (IHt _ H) as (d0 & ? & ?); exists d0; auto.
destruct (IHt0 _ H) as (d0 & ? & ?); exists d0; auto.
rewrite concat_in in H; destruct H as [H|H].
destruct (IHt _ H) as (d0 & ? & ?); exists d0; auto.
destruct (IHt0 _ H) as (d0 & ? & ?); exists d0; auto.
Qed.

Lemma map_option_bst : forall m, bst m -> bst (map_option f m).
Proof.
intros m; functional induction (map_option f m); simpl; auto; intros;
 inv bst.
apply join_bst; auto; intros y H;
 destruct (map_option_2 H) as (d0 & ? & ?); eauto using MapsTo_In.
apply concat_bst; auto; intros y y' H H'.
destruct (map_option_2 H) as (d0 & ? & ?).
destruct (map_option_2 H') as (d0' & ? & ?).
eapply X.lt_trans with x; eauto using MapsTo_In.
Qed.
Hint Resolve map_option_bst.

Ltac nonify e :=
 replace e with (@None elt) by
  (symmetry; rewrite not_find_iff; auto; intro; order).

Lemma map_option_find : forall (m:t elt)(x:key),
 bst m ->
 find x (map_option f m) =
  match (find x m) with Some d => f x d | None => None end.
Proof.
intros m; functional induction (map_option f m); simpl; auto; intros;
 inv bst; rewrite join_find || rewrite concat_find; auto; simpl;
 try destruct X.compare as [Hlt|Heq|Hlt]; simpl; auto.
rewrite (f_compat d Heq); auto.
intros y H;
 destruct (map_option_2 H) as (? & ? & ?); eauto using MapsTo_In.
intros y H;
 destruct (map_option_2 H) as (? & ? & ?); eauto using MapsTo_In.

rewrite <- IHt, IHt0; auto; nonify (find x0 r); auto.
rewrite IHt, IHt0; auto; nonify (find x0 r); nonify (find x0 l); auto.
rewrite (f_compat d Heq); auto.
rewrite <- IHt0, IHt; auto; nonify (find x0 l); auto.
 destruct (find x0 (map_option f r)); auto.

intros y y' H H'.
destruct (map_option_2 H) as (? & ? & ?).
destruct (map_option_2 H') as (? & ? & ?).
eapply X.lt_trans with x; eauto using MapsTo_In.
Qed.

End Map_option.

Section Map2_opt.
Variable elt elt' elt'' : Type.
Variable f0 : key -> option elt -> option elt' -> option elt''.
Variable f : key -> elt -> option elt' -> option elt''.
Variable mapl : t elt -> t elt''.
Variable mapr : t elt' -> t elt''.
Hypothesis f0_f : forall x d o, f x d o = f0 x (Some d) o.
Hypothesis mapl_bst : forall m, bst m -> bst (mapl m).
Hypothesis mapr_bst : forall m', bst m' -> bst (mapr m').
Hypothesis mapl_f0 : forall x m, bst m ->
 find x (mapl m) =
  match find x m with Some d => f0 x (Some d) None | None => None end.
Hypothesis mapr_f0 : forall x m', bst m' ->
 find x (mapr m') =
  match find x m' with Some d' => f0 x None (Some d') | None => None end.
Hypothesis f0_compat : forall x x' o o', X.eq x x' -> f0 x o o' = f0 x' o o'.

Notation map2_opt := (map2_opt f mapl mapr).

Lemma map2_opt_2 : forall m m' y, bst m -> bst m' ->
  In y (map2_opt m m') -> In y m \/ In y m'.
Proof.
intros m m'; functional induction (map2_opt m m'); intros;
 auto; try factornode _x0 _x1 _x2 _x3 _x4 as m2;
 try (generalize (split_in_1 x1 H0 y)(split_in_2 x1 H0 y)
      (split_bst x1 H0); rewrite e1; simpl; destruct 3; inv bst).

right; apply find_in.
generalize (in_find (mapr_bst H0) H1); rewrite mapr_f0; auto.
destruct (find y m2); auto; intros; discriminate.

factornode l1 x1 d1 r1 _x as m1.
left; apply find_in.
generalize (in_find (mapl_bst H) H1); rewrite mapl_f0; auto.
destruct (find y m1); auto; intros; discriminate.

rewrite join_in in H1; destruct H1 as [H'|[H'|H']]; auto.
destruct (IHt1 y H6 H4 H'); intuition.
destruct (IHt0 y H7 H5 H'); intuition.

rewrite concat_in in H1; destruct H1 as [H'|H']; auto.
destruct (IHt1 y H6 H4 H'); intuition.
destruct (IHt0 y H7 H5 H'); intuition.
Qed.

Lemma map2_opt_bst : forall m m', bst m -> bst m' ->
 bst (map2_opt m m').
Proof.
intros m m'; functional induction (map2_opt m m'); intros;
 auto; try factornode _x0 _x1 _x2 _x3 _x4 as m2; inv bst;
 generalize (split_in_1 x1 H0)(split_in_2 x1 H0)(split_bst x1 H0);
  rewrite e1; simpl in *; destruct 3.

apply join_bst; auto.
intros y Hy; specialize H with y.
destruct (map2_opt_2 H1 H6 Hy); intuition.
intros y Hy; specialize H5 with y.
destruct (map2_opt_2 H2 H7 Hy); intuition.

apply concat_bst; auto.
intros y y' Hy Hy'; specialize H with y; specialize H5 with y'.
apply X.lt_trans with x1.
destruct (map2_opt_2 H1 H6 Hy); intuition.
destruct (map2_opt_2 H2 H7 Hy'); intuition.
Qed.
Hint Resolve map2_opt_bst.

Ltac map2_aux :=
 match goal with
  | H : In ?x _ \/ In ?x ?m,
    H' : find ?x ?m = find ?x ?m', B:bst ?m, B':bst ?m' |- _ =>
    destruct H; [ intuition_in; order |
                  rewrite <-(find_in_equiv B B' H'); auto ]
 end.

Ltac nonify t :=
 match t with (find ?y (map2_opt ?m ?m')) =>
 replace t with (@None elt'');
 [ | symmetry; rewrite not_find_iff; auto; intro;
     destruct (@map2_opt_2 m m' y); auto; order ]
 end.

Lemma map2_opt_1 : forall m m' y, bst m -> bst m' ->
 In y m \/ In y m' ->
 find y (map2_opt m m') = f0 y (find y m) (find y m').
Proof.
intros m m'; functional induction (map2_opt m m'); intros;
 auto; try factornode _x0 _x1 _x2 _x3 _x4 as m2;
 try (generalize (split_in_1 x1 H0)(split_in_2 x1 H0)
       (split_in_3 x1 H0)(split_bst x1 H0)(split_find x1 y H0)
       (split_lt_tree (x:=x1) H0)(split_gt_tree (x:=x1) H0);
       rewrite e1; simpl in *; destruct 4; intros; inv bst;
      subst o2; rewrite H7, ?join_find, ?concat_find; auto).

simpl; destruct H1; [ inversion_clear H1 | ].
rewrite mapr_f0; auto.
generalize (in_find H0 H1); destruct (find y m2); intuition.

factornode l1 x1 d1 r1 _x as m1.
destruct H1; [ | inversion_clear H1 ].
rewrite mapl_f0; auto.
generalize (in_find H H1); destruct (find y m1); intuition.

simpl; destruct X.compare; auto.
apply IHt1; auto; map2_aux.
rewrite (@f0_compat y x1), <- f0_f; auto.
apply IHt0; auto; map2_aux.
intros z Hz; destruct (@map2_opt_2 l1 l2' z); auto.
intros z Hz; destruct (@map2_opt_2 r1 r2' z); auto.

destruct X.compare.
nonify (find y (map2_opt r1 r2')).
apply IHt1; auto; map2_aux.
nonify (find y (map2_opt r1 r2')).
nonify (find y (map2_opt l1 l2')).
rewrite (@f0_compat y x1), <- f0_f; auto.
nonify (find y (map2_opt l1 l2')).
rewrite IHt0; auto; [ | map2_aux ].
destruct (f0 y (find y r1) (find y r2')); auto.
intros y1 y2 Hy1 Hy2; apply X.lt_trans with x1.
 destruct (@map2_opt_2 l1 l2' y1); auto.
 destruct (@map2_opt_2 r1 r2' y2); auto.
Qed.

End Map2_opt.

Section Map2.
Variable elt elt' elt'' : Type.
Variable f : option elt -> option elt' -> option elt''.

Lemma map2_bst : forall m m', bst m -> bst m' -> bst (map2 f m m').
Proof.
unfold map2; intros.
apply map2_opt_bst with (fun _ => f); auto using map_option_bst;
 intros; rewrite map_option_find; auto.
Qed.

Lemma map2_1 : forall m m' y, bst m -> bst m' ->
  In y m \/ In y m' -> find y (map2 f m m') = f (find y m) (find y m').
Proof.
unfold map2; intros.
rewrite (map2_opt_1 (f0:=fun _ => f));
 auto using map_option_bst; intros; rewrite map_option_find; auto.
Qed.

Lemma map2_2 : forall m m' y, bst m -> bst m' ->
  In y (map2 f m m') -> In y m \/ In y m'.
Proof.
unfold map2; intros.
eapply map2_opt_2 with (f0:=fun _ => f); try eassumption; trivial; intros.
 apply map_option_bst; auto.
 apply map_option_bst; auto.
 rewrite map_option_find; auto.
 rewrite map_option_find; auto.
Qed.

End Map2.
End Proofs.
End Raw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of balanced binary search trees. *)

Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.

 Module E := X.
 Module Raw := Raw I X.
 Import Raw.Proofs.

 Record bst (elt:Type) :=
  Bst {this :> Raw.tree elt; is_bst : Raw.bst this}.

 Definition t := bst.
 Definition key := E.t.

 Section Elt.
 Variable elt elt' elt'': Type.

 Implicit Types m : t elt.
 Implicit Types x y : key.
 Implicit Types e : elt.

 Definition empty : t elt := Bst (empty_bst elt).
 Definition is_empty m : bool := Raw.is_empty m.(this).
 Definition add x e m : t elt := Bst (add_bst x e m.(is_bst)).
 Definition remove x m : t elt := Bst (remove_bst x m.(is_bst)).
 Definition mem x m : bool := Raw.mem x m.(this).
 Definition find x m : option elt := Raw.find x m.(this).
 Definition map f m : t elt' := Bst (map_bst f m.(is_bst)).
 Definition mapi (f:key->elt->elt') m : t elt' :=
  Bst (mapi_bst f m.(is_bst)).
 Definition map2 f m (m':t elt') : t elt'' :=
  Bst (map2_bst f m.(is_bst) m'.(is_bst)).
 Definition elements m : list (key*elt) := Raw.elements m.(this).
 Definition cardinal m := Raw.cardinal m.(this).
 Definition fold (A:Type) (f:key->elt->A->A) m i := Raw.fold (A:=A) f m.(this) i.
 Definition equal cmp m m' : bool := Raw.equal cmp m.(this) m'.(this).

 Definition MapsTo x e m : Prop := Raw.MapsTo x e m.(this).
 Definition In x m : Prop := Raw.In0 x m.(this).
 Definition Empty m : Prop := Empty m.(this).

 Definition eq_key : (key*elt) -> (key*elt) -> Prop := @PX.eqk elt.
 Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop := @PX.eqke elt.
 Definition lt_key : (key*elt) -> (key*elt) -> Prop := @PX.ltk elt.

 Lemma MapsTo_1 : forall m x y e, E.eq x y -> MapsTo x e m -> MapsTo y e m.
 Proof. intros m; exact (@MapsTo_1 _ m.(this)). Qed.

 Lemma mem_1 : forall m x, In x m -> mem x m = true.
 Proof.
 unfold In, mem; intros m x; rewrite In_alt; simpl; apply mem_1; auto.
 apply m.(is_bst).
 Qed.

 Lemma mem_2 : forall m x, mem x m = true -> In x m.
 Proof.
 unfold In, mem; intros m x; rewrite In_alt; simpl; apply mem_2; auto.
 Qed.

 Lemma empty_1 : Empty empty.
 Proof. exact (@empty_1 elt). Qed.

 Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
 Proof. intros m; exact (@is_empty_1 _ m.(this)). Qed.
 Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
 Proof. intros m; exact (@is_empty_2 _ m.(this)). Qed.

 Lemma add_1 : forall m x y e, E.eq x y -> MapsTo y e (add x e m).
 Proof. intros m x y e; exact (@add_1 elt _ x y e). Qed.
 Lemma add_2 : forall m x y e e', ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
 Proof. intros m x y e e'; exact (@add_2 elt _ x y e e'). Qed.
 Lemma add_3 : forall m x y e e', ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
 Proof. intros m x y e e'; exact (@add_3 elt _ x y e e'). Qed.

 Lemma remove_1 : forall m x y, E.eq x y -> ~ In y (remove x m).
 Proof.
 unfold In, remove; intros m x y; rewrite In_alt; simpl; apply remove_1; auto.
 apply m.(is_bst).
 Qed.
 Lemma remove_2 : forall m x y e, ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
 Proof. intros m x y e; exact (@remove_2 elt _ x y e m.(is_bst)). Qed.
 Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.
 Proof. intros m x y e; exact (@remove_3 elt _ x y e m.(is_bst)). Qed.


 Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e.
 Proof. intros m x e; exact (@find_1 elt _ x e m.(is_bst)). Qed.
 Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
 Proof. intros m; exact (@find_2 elt m.(this)). Qed.

 Lemma fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
 Proof. intros m; exact (@fold_1 elt m.(this) m.(is_bst)). Qed.

 Lemma elements_1 : forall m x e,
   MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
 Proof.
 intros; unfold elements, MapsTo, eq_key_elt; rewrite elements_mapsto; auto.
 Qed.

 Lemma elements_2 : forall m x e,
   InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
 Proof.
 intros; unfold elements, MapsTo, eq_key_elt; rewrite <- elements_mapsto; auto.
 Qed.

 Lemma elements_3 : forall m, sort lt_key (elements m).
 Proof. intros m; exact (@elements_sort elt m.(this) m.(is_bst)). Qed.

 Lemma elements_3w : forall m, NoDupA eq_key (elements m).
 Proof. intros m; exact (@elements_nodup elt m.(this) m.(is_bst)). Qed.

 Lemma cardinal_1 : forall m, cardinal m = length (elements m).
 Proof. intro m; exact (@elements_cardinal elt m.(this)). Qed.

 Definition Equal m m' := forall y, find y m = find y m'.
 Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
   (forall k, In k m <-> In k m') /\
   (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
 Definition Equivb cmp := Equiv (Cmp cmp).

 Lemma Equivb_Equivb : forall cmp m m',
  Equivb cmp m m' <-> Raw.Proofs.Equivb cmp m m'.
 Proof.
 intros; unfold Equivb, Equiv, Raw.Proofs.Equivb, In. intuition. 
 generalize (H0 k); do 2 rewrite In_alt; intuition.
 generalize (H0 k); do 2 rewrite In_alt; intuition.
 generalize (H0 k); do 2 rewrite <- In_alt; intuition.
 generalize (H0 k); do 2 rewrite <- In_alt; intuition.
 Qed.

 Lemma equal_1 : forall m m' cmp,
   Equivb cmp m m' -> equal cmp m m' = true.
 Proof.
 unfold equal; intros (m,b) (m',b') cmp; rewrite Equivb_Equivb;
  intros; simpl in *; rewrite equal_Equivb; auto.
 Qed.

 Lemma equal_2 : forall m m' cmp,
   equal cmp m m' = true -> Equivb cmp m m'.
 Proof.
 unfold equal; intros (m,b) (m',b') cmp; rewrite Equivb_Equivb;
  intros; simpl in *; rewrite <-equal_Equivb; auto.
 Qed.

 End Elt.

 Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
 Proof. intros elt elt' m x e f; exact (@map_1 elt elt' f m.(this) x e). Qed.

 Lemma map_2 : forall (elt elt':Type)(m:t elt)(x:key)(f:elt->elt'), In x (map f m) -> In x m.
 Proof.
 intros elt elt' m x f; do 2 unfold In in *; do 2 rewrite In_alt; simpl.
 apply map_2; auto.
 Qed.

 Lemma mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m ->
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
 Proof. intros elt elt' m x e f; exact (@mapi_1 elt elt' f m.(this) x e). Qed.
 Lemma mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.
 Proof.
 intros elt elt' m x f; unfold In in *; do 2 rewrite In_alt; simpl; apply mapi_2; auto.
 Qed.

 Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In x m \/ In x m' ->
    find x (map2 f m m') = f (find x m) (find x m').
 Proof.
 unfold find, map2, In; intros elt elt' elt'' m m' x f.
 do 2 rewrite In_alt; intros; simpl; apply map2_1; auto.
 apply m.(is_bst).
 apply m'.(is_bst).
 Qed.

 Lemma map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
     (x:key)(f:option elt->option elt'->option elt''),
     In x (map2 f m m') -> In x m \/ In x m'.
 Proof.
 unfold In, map2; intros elt elt' elt'' m m' x f.
 do 3 rewrite In_alt; intros; simpl in *; eapply map2_2; eauto.
 apply m.(is_bst).
 apply m'.(is_bst).
 Qed.

End IntMake.


Module IntMake_ord (I:Int)(X: OrderedType)(D : OrderedType) <:
    Sord with Module Data := D
         with Module MapS.E := X.

  Module Data := D.
  Module Import MapS := IntMake(I)(X).
  Module LO := FMapList.Make_ord(X)(D).
  Module R := Raw.
  Module P := Raw.Proofs.

  Definition t := MapS.t D.t.

  Definition cmp e e' :=
   match D.compare e e' with EQ _ => true | _ => false end.

  (** One step of comparison of elements *)

  Definition compare_more x1 d1 (cont:R.enumeration D.t -> comparison) e2 :=
   match e2 with
    | R.End _ => Gt
    | R.More x2 d2 r2 e2 =>
       match X.compare x1 x2 with
        | EQ _ => match D.compare d1 d2 with
                   | EQ _ => cont (R.cons r2 e2)
                   | LT _ => Lt
                   | GT _ => Gt
                  end
        | LT _ => Lt
        | GT _ => Gt
       end
   end.

  (** Comparison of left tree, middle element, then right tree *)

  Fixpoint compare_cont s1 (cont:R.enumeration D.t -> comparison) e2 :=
   match s1 with
    | R.Leaf _ => cont e2
    | R.Node l1 x1 d1 r1 _ =>
       compare_cont l1 (compare_more x1 d1 (compare_cont r1 cont)) e2
   end.

  (** Initial continuation *)

  Definition compare_end (e2:R.enumeration D.t) :=
   match e2 with R.End _ => Eq | _ => Lt end.

  (** The complete comparison *)

  Definition compare_pure s1 s2 :=
   compare_cont s1 compare_end (R.cons s2 (Raw.End _)).

  (** Correctness of this comparison *)

  Definition Cmp c :=
   match c with
    | Eq => LO.eq_list
    | Lt => LO.lt_list
    | Gt => (fun l1 l2 => LO.lt_list l2 l1)
   end.

  Lemma cons_Cmp : forall c x1 x2 d1 d2 l1 l2,
   X.eq x1 x2 -> D.eq d1 d2 ->
   Cmp c l1 l2 -> Cmp c ((x1,d1)::l1) ((x2,d2)::l2).
  Proof.
   destruct c; simpl; intros; P.MX.elim_comp; auto.
  Qed.
  Hint Resolve cons_Cmp.

  Lemma compare_end_Cmp :
   forall e2, Cmp (compare_end e2) nil (P.flatten_e e2).
  Proof.
   destruct e2; simpl; auto.
  Qed.

  Lemma compare_more_Cmp : forall x1 d1 cont x2 d2 r2 e2 l,
    Cmp (cont (R.cons r2 e2)) l (R.elements r2 ++ P.flatten_e e2) ->
     Cmp (compare_more x1 d1 cont (R.More x2 d2 r2 e2)) ((x1,d1)::l)
       (P.flatten_e (R.More x2 d2 r2 e2)).
  Proof.
   simpl; intros; destruct X.compare; simpl;
    try destruct D.compare; simpl; auto; P.MX.elim_comp; auto.
  Qed.

  Lemma compare_cont_Cmp : forall s1 cont e2 l,
   (forall e, Cmp (cont e) l (P.flatten_e e)) ->
   Cmp (compare_cont s1 cont e2) (R.elements s1 ++ l) (P.flatten_e e2).
  Proof.
   induction s1 as [|l1 Hl1 x1 d1 r1 Hr1 h1]; intros; auto.
   rewrite <- P.elements_node; simpl.
   apply Hl1; auto. clear e2. intros [|x2 d2 r2 e2].
   simpl; auto.
   apply compare_more_Cmp.
   rewrite <- P.cons_1; auto.
  Qed.

  Lemma compare_Cmp : forall s1 s2,
   Cmp (compare_pure s1 s2) (R.elements s1) (R.elements s2).
  Proof.
   intros; unfold compare_pure.
   rewrite <- (app_nil_r (R.elements s1)).
   replace (R.elements s2) with (P.flatten_e (R.cons s2 (R.End _))) by
    (rewrite P.cons_1; simpl; rewrite app_nil_r; auto).
   auto using compare_cont_Cmp, compare_end_Cmp.
  Qed.

  (** The dependent-style [compare] *)

  Definition eq (m1 m2 : t) := LO.eq_list (elements m1) (elements m2).
  Definition lt (m1 m2 : t) := LO.lt_list (elements m1) (elements m2).

  Definition compare (s s':t) : Compare lt eq s s'.
  Proof.
   destruct s as (s,b), s' as (s',b').
   generalize (compare_Cmp s s').
   destruct compare_pure; intros; [apply EQ|apply LT|apply GT]; red; auto.
  Defined.

  (* Proofs about [eq] and [lt] *)

  Definition selements (m1 : t) :=
   LO.MapS.Build_slist (P.elements_sort m1.(is_bst)).

  Definition seq (m1 m2 : t) := LO.eq (selements m1) (selements m2).
  Definition slt (m1 m2 : t) := LO.lt (selements m1) (selements m2).

  Lemma eq_seq : forall m1 m2, eq m1 m2 <-> seq m1 m2.
  Proof.
   unfold eq, seq, selements, elements, LO.eq; intuition.
  Qed.

  Lemma lt_slt : forall m1 m2, lt m1 m2 <-> slt m1 m2.
  Proof.
   unfold lt, slt, selements, elements, LO.lt; intuition.
  Qed.

  Lemma eq_1 : forall (m m' : t), Equivb cmp m m' -> eq m m'.
  Proof.
  intros m m'.
  rewrite eq_seq; unfold seq.
  rewrite Equivb_Equivb.
  rewrite P.Equivb_elements.
  auto using LO.eq_1.
  Qed.

  Lemma eq_2 : forall m m', eq m m' -> Equivb cmp m m'.
  Proof.
  intros m m'.
  rewrite eq_seq; unfold seq.
  rewrite Equivb_Equivb.
  rewrite P.Equivb_elements.
  intros.
  generalize (LO.eq_2 H).
  auto.
  Qed.

  Lemma eq_refl : forall m : t, eq m m.
  Proof.
  intros; rewrite eq_seq; unfold seq; intros; apply LO.eq_refl.
  Qed.

  Lemma eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Proof.
  intros m1 m2; rewrite 2 eq_seq; unfold seq; intros; apply LO.eq_sym; auto.
  Qed.

  Lemma eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Proof.
  intros m1 m2 M3; rewrite 3 eq_seq; unfold seq.
   intros; eapply LO.eq_trans; eauto.
  Qed.

  Lemma lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Proof.
  intros m1 m2 m3; rewrite 3 lt_slt; unfold slt;
   intros; eapply LO.lt_trans; eauto.
  Qed.

  Lemma lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.
  Proof.
  intros m1 m2; rewrite lt_slt, eq_seq; unfold slt, seq;
   intros; apply LO.lt_not_eq; auto.
  Qed.

End IntMake_ord.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (X: OrderedType) <: S with Module E := X
 :=IntMake(Z_as_Int)(X).

Module Make_ord (X: OrderedType)(D: OrderedType)
 <: Sord with Module Data := D
            with Module MapS.E := X
 :=IntMake_ord(Z_as_Int)(X)(D).


 (***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** This module implements sets using red-black trees *)

Require FSetInterface.
Require FSetList.
Require FSetBridge.

Require Omega.
Require ZArith.

Import Z_scope.
Open Scope Z_scope.

Notation "[]" := (nil ?) (at level 1).
Notation "a :: l" := (cons a l) (at level 1, l at next level).

Module Make [X : OrderedType] <: Sdep with Module E := X.

  Module E := X.
  Module ME := MoreOrderedType X.

  Definition elt := X.t.

  (** * Red-black trees *)

  Inductive color : Set := red : color | black : color.

  Inductive tree : Set :=
  | Leaf : tree
  | Node : color -> tree -> X.t -> tree -> tree.

  (** * Occurrence in a tree *)

  Inductive In_tree [x:elt] : tree -> Prop :=
  | IsRoot : (l,r:tree)(c:color)(y:elt)
             (X.eq x y) -> (In_tree x (Node c l y r))
  | InLeft : (l,r:tree)(c:color)(y:elt)
             (In_tree x l) -> (In_tree x (Node c l y r))
  | InRight : (l,r:tree)(c:color)(y:elt)
              (In_tree x r) -> (In_tree x (Node c l y r)).

  Hint In_tree := Constructors In_tree.

  (** [In_tree] is  color-insensitive *)

  Lemma In_color : (c,c':color)(x,y:elt)(l,r:tree)
    (In_tree y (Node c l x r)) -> (In_tree y (Node c' l x r)).
  Proof.
    Inversion 1; Auto.
  Save.
  Hints Resolve In_color.

  (** * Binary search trees *)

  (** [lt_tree x s]: all elements in [s] are smaller than [x] 
      (resp. greater for [gt_tree]) *)

  Definition lt_tree [x:elt; s:tree] := (y:elt)(In_tree y s) -> (X.lt y x).
  Definition gt_tree [x:elt; s:tree] := (y:elt)(In_tree y s) -> (X.lt x y).

  Hints Unfold lt_tree gt_tree.

  (** Results about [lt_tree] and [gt_tree] *)

  Lemma lt_leaf : (x:elt)(lt_tree x Leaf).
  Proof.
    Unfold lt_tree; Intros; Inversion H.
  Save.

  Lemma gt_leaf : (x:elt)(gt_tree x Leaf).
  Proof.
    Unfold gt_tree; Intros; Inversion H.
  Save.

  Lemma lt_tree_node : (x,y:elt)(l,r:tree)(c:color)
    (lt_tree x l) -> (lt_tree x r) -> (X.lt y x) -> 
    (lt_tree x (Node c l y r)).
  Proof.
    Unfold lt_tree; Intuition.
    Inversion_clear H2; Intuition.
    Apply ME.eq_lt with y; Auto.
  Save.

  Lemma gt_tree_node : (x,y:elt)(l,r:tree)(c:color)
    (gt_tree x l) -> (gt_tree x r) -> (E.lt x y) -> 
    (gt_tree x (Node c l y r)).
  Proof.
    Unfold gt_tree; Intuition.
    Inversion_clear H2; Intuition.
    Apply ME.lt_eq with y; Auto.
  Save.

  Hints Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

  Lemma lt_node_lt : (x,y:elt)(l,r:tree)(c:color)
     (lt_tree x (Node c l y r)) -> (E.lt y x).
  Proof.
    Intros; Apply H; Auto.
  Save.

  Lemma gt_node_gt : (x,y:elt)(l,r:tree)(c:color)
     (gt_tree x (Node c l y r)) -> (E.lt x y).
  Proof.
    Intros; Apply H; Auto.
  Save.

  Lemma lt_left : (x,y:elt)(l,r:tree)(c:color)
     (lt_tree x (Node c l y r)) -> (lt_tree x l).
  Proof.
    Intros; Red; Intros; Apply H; Auto.
  Save.

  Lemma lt_right : (x,y:elt)(l,r:tree)(c:color)
     (lt_tree x (Node c l y r)) -> (lt_tree x r).
  Proof.
    Intros; Red; Intros; Apply H; Auto.
  Save.

  Lemma gt_left : (x,y:elt)(l,r:tree)(c:color)
     (gt_tree x (Node c l y r)) -> (gt_tree x l).
  Proof.
    Intros; Red; Intros; Apply H; Auto.
  Save.

  Lemma gt_right : (x,y:elt)(l,r:tree)(c:color)
     (gt_tree x (Node c l y r)) -> (gt_tree x r).
  Proof.
    Intros; Red; Intros; Apply H; Auto.
  Save.

  Hints Resolve lt_node_lt gt_node_gt
                lt_left lt_right gt_left gt_right.

  Lemma lt_tree_not_in : 
    (x:elt)(t:tree)(lt_tree x t) -> ~(In_tree x t).
  Proof.
    Unfold lt_tree; Intros; Red; Intros.
    Generalize (H x H0); Intro; Absurd (X.lt x x); Auto.
  Save.

  Lemma lt_tree_trans : 
    (x,y:elt)(X.lt x y) -> (t:tree)(lt_tree x t) -> (lt_tree y t).
  Proof.
    Unfold lt_tree; Ground EAuto.
  Save.

  Lemma gt_tree_not_in : 
    (x:elt)(t:tree)(gt_tree x t) -> ~(In_tree x t).
  Proof.
    Unfold gt_tree; Intros; Red; Intros.
    Generalize (H x H0); Intro; Absurd (X.lt x x); Auto.
  Save.

  Lemma gt_tree_trans : 
    (x,y:elt)(X.lt y x) -> (t:tree)(gt_tree x t) -> (gt_tree y t).
  Proof.
    Unfold gt_tree; Ground EAuto.
  Save.

  Hints Resolve lt_tree_not_in lt_tree_trans 
                gt_tree_not_in gt_tree_trans.

  (** [bst t] : [t] is a binary search tree *)

  Inductive bst : tree -> Prop :=
  | BSLeaf : 
      (bst Leaf)
  | BSNode : (x:elt)(l,r:tree)(c:color)
      (bst l) -> (bst r) ->
      (lt_tree x l) -> (gt_tree x r) ->
      (bst (Node c l x r)).

  Hint bst := Constructors bst.

  (** Results about [bst] *)
 
  Lemma bst_left : (x:elt)(l,r:tree)(c:color)
    (bst (Node c l x r)) -> (bst l).
  Proof.
    Intros x l r c H; Inversion H; Auto.
  Save.

  Lemma bst_right : (x:elt)(l,r:tree)(c:color)
    (bst (Node c l x r)) -> (bst r).
  Proof.
    Intros x l r c H; Inversion H; Auto.
  Save.

  Implicits bst_left. Implicits bst_right.
  Hints Resolve bst_left bst_right.

  Lemma bst_color : (c,c':color)(x:elt)(l,r:tree)
    (bst (Node c l x r)) -> (bst (Node c' l x r)).
  Proof.
    Inversion 1; Auto.
  Save.
  Hints Resolve bst_color.

  (** Key fact about binary search trees: rotations preserve the 
      [bst] property *)

  Lemma rotate_left : (x,y:elt)(a,b,c:tree)(c1,c2,c3,c4:color)
    (bst (Node c1 a x (Node c2 b y c))) ->
    (bst (Node c3 (Node c4 a x b) y c)).
  Proof.
    Intros; Inversion H; Intuition.
    Constructor; Intuition.
    Constructor; EAuto.
    EAuto.
    Apply lt_tree_node; Intuition.
    Apply lt_tree_trans with x; Auto.
    Inversion H5; Auto.
    Inversion H5; Auto.
  Save.

  Lemma rotate_right : (x,y:elt)(a,b,c:tree)(c1,c2,c3,c4:color)
    (bst (Node c3 (Node c4 a x b) y c)) ->
    (bst (Node c1 a x (Node c2 b y c))).
  Proof.
    Intros; Inversion H; Intuition.
    Constructor; Intuition.
    EAuto.
    Constructor; Auto.
    Inversion H4; Auto.
    Inversion H4; Auto.
    Apply gt_tree_node; Intuition.
    Inversion H4; Auto.
    Apply gt_tree_trans with y; Auto.
    EAuto.
  Save.

  Hints Resolve rotate_left rotate_right.

  (** * Balanced red-black trees *)

  (** [rbtree n t]: [t] is a properly balanced red-black tree, i.e. it
      satisfies the following two invariants:
      - a red node has no red son
      - any path from the root to a leaf has exactly [n] black nodes *)
       
  Definition is_not_red [t:tree] := Cases t of
  | Leaf => True
  | (Node black x0 x1 x2) => True
  | (Node red x0 x1 x2) => False
  end.

  Hints Unfold is_not_red.  

  Inductive rbtree : nat -> tree -> Prop :=
  | RBLeaf : 
      (rbtree O Leaf)
  | RBRed : (x:elt)(l,r:tree)(n:nat)
      (rbtree n l) -> (rbtree n r) ->
      (is_not_red l) -> (is_not_red r) ->
      (rbtree n (Node red l x r))
  | RBBlack : (x:elt)(l,r:tree)(n:nat)
      (rbtree n l) -> (rbtree n r) ->
      (rbtree (S n) (Node black l x r)).

  Hint rbtree := Constructors rbtree.

  (** Results about [rbtree] *)

  Lemma rbtree_left : 
    (x:elt)(l,r:tree)(c:color)
    (EX n:nat | (rbtree n (Node c l x r))) ->
    (EX n:nat | (rbtree n l)).
  Proof.
    Intros x l r c (n,Hn); Inversion_clear Hn; Intuition EAuto.
  Save.

  Lemma rbtree_right : 
    (x:elt)(l,r:tree)(c:color)
    (EX n:nat | (rbtree n (Node c l x r))) ->
    (EX n:nat | (rbtree n r)).
  Proof.
    Intros x l r c (n,Hn); Inversion_clear Hn; Intuition EAuto.
  Save.

  Implicits rbtree_left. Implicits rbtree_right.
  Hints Resolve rbtree_left rbtree_right.

  (** * Sets as red-black trees *)

  (** A set is implement as a record [t], containing a tree, 
      a proof that it is a binary search tree and a proof that it is 
      a properly balanced red-black tree *)

  Record t_ : Set := t_intro {
    the_tree :> tree; 
    is_bst : (bst the_tree);
    is_rbtree : (EX n:nat | (rbtree n the_tree)) }.
  Definition t := t_.

  (** * Rotations *)

  Lemma t_is_bst : (s:t)(bst s).
  Proof.
    Destruct s; Auto.
  Save.
  Hints Resolve t_is_bst.

  (** * Logical appartness *)

  Definition In : elt -> t -> Prop := [x:elt][s:t](In_tree x s).

  Definition Equal := [s,s'](a:elt)(In a s)<->(In a s').
  Definition Subset := [s,s'](a:elt)(In a s)->(In a s').
  Definition Add := [x:elt;s,s':t](y:elt)(In y s') <-> ((E.eq y x)\/(In y s)).
  Definition Empty := [s](a:elt)~(In a s).
  Definition For_all := [P:elt->Prop; s:t](x:elt)(In x s)->(P x).
  Definition Exists := [P:elt->Prop; s:t](EX x:elt | (In x s)/\(P x)).

  Lemma eq_In: (s:t)(x,y:elt)(E.eq x y) -> (In x s) -> (In y s).
  Proof.
    Unfold In; Destruct s; Simpl; Intuition Clear is_bst0 is_rbtree0.
    Induction the_tree0; Inversion_clear H0; Intuition.
    Apply IsRoot; EAuto.
  Save.

  Hints Resolve eq_In.

  (** * Empty set *)

  Definition t_empty : t.
  Proof.
    Exists Leaf; Auto; Exists O; Auto.
  Defined.

  Definition empty : { s:t | (x:elt)~(In x s) }. 
  Proof.
    Exists t_empty.
    Unfold In; Red; Intros.
    Inversion H.
  Defined.

  (** * Emptyness test *)

  Definition is_empty : (s:t){ Empty s }+{ ~(Empty s) }.
  Proof.
    Unfold Empty In; Destruct s; Destruct the_tree0; Simpl; Intros.
    Left; Auto.
    Right; Intuition.
    Apply (H t1); Auto.
  Defined.

  (** * Appartness *)

  (** The [mem] function is deciding appartness. It exploits the [bst] property
      to achieve logarithmic complexity. *)

  Definition mem : (x:elt) (s:t) { (In x s) } + { ~(In x s) }.
  Proof.
    Intros x (s,Hs,Hrb).
    Unfold In; Simpl; Clear Hrb.
    Generalize Hs; Elim s; Simpl; Intros.
  (* Leaf *)
    Right. 
    Unfold In; Red; Intros; Inversion H.
  (* Node *)
    Elim (X.compare x t1); Intro.
    (* lt x t1 *)
    Case H; Intros.
    EAuto.
    Left; Auto.
    Right; Intro.
    Inversion H1; Intuition.
    Absurd (X.eq x t1); Auto.
    Inversion Hs0.
    Absurd (In_tree x t2); EAuto.
    (* eq x t1 *)
    Left; Auto.
    (* lt t1 x *)
    Case H0; Intros.
    EAuto.
    Left; Auto.
    Right; Intro.
    Inversion H1; Intuition.
    Absurd (X.eq t1 x); Auto.
    Inversion Hs0.
    Absurd (In_tree x t0); EAuto.
  Defined.

  (** * Singleton set *)

  Definition singleton_tree [x:elt] := (Node red Leaf x Leaf).

  Lemma singleton_bst : (x:elt)(bst (singleton_tree x)).
  Proof.
    Unfold singleton_tree; Auto.
  Save.

  Lemma singleton_rbtree : (x:elt)(EX n:nat | (rbtree n (singleton_tree x))).
  Proof.
    Unfold singleton_tree; EAuto.
  Save.

  Definition singleton : (x:elt){ s:t | (y:elt)(In y s) <-> (E.eq x y)}.
  Proof.
    Intro x; Exists (t_intro (singleton_tree x) (singleton_bst x)
             (singleton_rbtree x)).
    Unfold In singleton_tree; Simpl; Intuition.
    Inversion_clear H; Auto; Inversion H0.
  Defined.

  (** * Insertion *)

  (** [almost_rbtree n t]: [t] may have one red-red conflict at its root;
      it satisfies [rbtree n] everywhere else *)

  Inductive almost_rbtree : nat -> tree -> Prop := 
  | ARBLeaf : 
      (almost_rbtree O Leaf)
  | ARBRed : (x:elt)(l,r:tree)(n:nat)
      (rbtree n l) -> (rbtree n r) ->
      (almost_rbtree n (Node red l x r))
  | ARBBlack : (x:elt)(l,r:tree)(n:nat)
      (rbtree n l) -> (rbtree n r) ->
      (almost_rbtree (S n) (Node black l x r)).

  Hint almost_rbtree := Constructors almost_rbtree.

  (** Results about [almost_rbtree] *)

  Lemma rbtree_almost_rbtree : 
    (n:nat)(t:tree)(rbtree n t) -> (almost_rbtree n t).
  Proof.
    Destruct 1; Intuition.
  Save.

  Hints Resolve rbtree_almost_rbtree.

  Lemma rbtree_almost_rbtree_ex : (s:tree)
    (EX n:nat | (rbtree n s)) -> (EX n:nat | (almost_rbtree n s)).
  Proof.
    Intros s (n,Hn); Exists n; Auto.
  Save.

  Hints Resolve rbtree_almost_rbtree_ex.

  Lemma almost_rbtree_rbtree_black : (x:elt)(l,r:tree)(n:nat)
    (almost_rbtree n (Node black l x r)) -> 
    (rbtree n (Node black l x r)).
  Proof.
    Inversion 1; Auto.
  Save.
  Hints Resolve almost_rbtree_rbtree_black.

  (** Balancing functions [lbalance] and [rbalance] (see below) require
      a rather complex pattern-matching; it is realized by the following
      function [conflict] which returns in the sum type [Conflict] *)

  Inductive Conflict [s:tree] : Set :=
  | NoConflict : 
      ((n:nat) (almost_rbtree n s) -> (rbtree n s)) -> 
      (Conflict s)
  | RedRedConflict : 
      (a,b,c:tree)(x,y:elt)
      (bst a) -> (bst b) -> (bst c) ->
      (lt_tree x a) -> (gt_tree x b) -> 
      (lt_tree y b) -> (gt_tree y c) -> (X.lt x y) ->
      ((z:elt)(In_tree z s) <-> 
        ((X.eq z x) \/ (X.eq z y) \/ 
         (In_tree z a) \/ (In_tree z b) \/ (In_tree z c))) ->
      ((n:nat)(almost_rbtree n s) ->
              ((rbtree n a) /\ (rbtree n b) /\ (rbtree n c))) ->
      (Conflict s).

  Definition conflict : (s:tree)(bst s) -> (Conflict s).
  Proof.
    Destruct s; Intros.
    (* s = Leaf *)
    Constructor 1; Inversion 1; Auto.
    (* s = Node c t0 t1 t2 *)
    Induction c.
    (* s = Node red t0 t1 t2 *)
    Generalize H; Clear H; Case t0; Intros.
    (* s = Node red Leaf t1 t2 *)
    Generalize H; Clear H; Case t2; Intros.
    (* s = Node red Leaf t1 Leaf *)
    Constructor 1; Inversion_clear 1; Intros.
    Constructor; Intuition.
    (* s = Node red Leaf t1 (Node c t3 t4 t5) *)
    Induction c.
    (* s = Node red Leaf t1 (Node red t3 t4 t5) *)
    Constructor 2 with a:=Leaf b:=t3 c:=t5 x:=t1 y:=t4; Intuition;
      Solve [ Inversion_clear H; Auto; Inversion_clear H1; Auto |
              Inversion_clear H0; Auto; Inversion_clear H2; Auto |
              Inversion_clear H0; Auto; Inversion_clear H1; Auto |
              Inversion_clear H1; Auto ].
    (* s = Node red Leaf t1 (Node black t3 t4 t5) *)
    Constructor 1; Inversion_clear 1; Intros.
    Constructor; Intuition.
    (* s = Node red (Node c t3 t4 t5) t1 t2 *)
    Induction c.
    (* s = Node red (Node red t3 t4 t5) t1 t2 *)
    Constructor 2 with a:=t3 b:=t5 c:=t2 x:=t4 y:=t1; Intuition;
       Solve [ Inversion_clear H; Auto; Inversion_clear H0; Auto |
              Inversion_clear H0; Auto; Inversion_clear H1; Auto |
              Inversion_clear H1; Auto ].
    (* s = Node red (Node black t3 t4 t5) t1 t2 *)
    Generalize H; Clear H; Case t2; Intros.
    (* s = Node red (Node black t3 t4 t5) t1 Leaf *)
    Constructor 1; Inversion_clear 1; Intros.
    Constructor; Intuition.
    (* s = Node red (Node black t3 t4 t5) t1 (Node c t6 t7 t8) *)
    Induction c.
    (* s = Node red (Node black t3 t4 t5) t1 (Node red t6 t7 t8) *)
    Constructor 2 with a:=(Node black t3 t4 t5)
      b:=t6 c:=t8 x:=t1 y:=t7; Intuition;
      Solve [ Inversion_clear H; Auto; Inversion_clear H1; Auto |
              Inversion_clear H0; Auto; Inversion_clear H2; Auto |
              Inversion_clear H0; Auto; Inversion_clear H1; Auto |
              Inversion_clear H1; Auto ].
    (* s = Node red (Node black t3 t4 t5) t1 (Node black t6 t7 t8) *)
    Constructor 1; Inversion_clear 1; Intros.
    Constructor; Intuition.
    (* s = Node black t0 t1 t2 *)
    Constructor 1; Inversion_clear 1; Intros.
    Constructor; Intuition.
  Defined.

  (** [lbalance c x l r] acts as a black node constructor,
      solving a possible red-red conflict on [l], using the following
      schema: 
<<   
     B (R (R a x b) y c) z d
     B (R a x (R b y c)) z d -> R (B a x b) y (R c z d) 
     B a x b -> B a x b 
>> 
      The result is not necessarily a black node. *)

  Definition lbalance : 
    (l:tree)(x:elt)(r:tree)
    (lt_tree x l) -> (gt_tree x r) ->
    (bst l) -> (bst r) ->
    { s:tree | 
        (bst s) /\
        ((n:nat)((almost_rbtree n l) /\ (rbtree n r)) -> 
                (rbtree (S n) s)) /\
	(y:elt)(In_tree y s) <-> ((E.eq y x)\/(In_tree y l)\/(In_tree y r)) }.
  Proof.
    Intros; Case (conflict l).
    Assumption.
    (* no conflict *)
    Exists (Node black l x r); Intuition. 
    Inversion H3; Auto. 
    (* red red conflict *)
    Intros; Exists (Node red (Node black a x0 b) y
                             (Node black c x  r)); Intuition.
    Constructor; Intuition.
    Constructor; Intuition.
    Intro z; Generalize (i z); Intuition.
    Apply lt_tree_node; Intuition.
    Apply lt_tree_trans with x0; Auto.
    Assert (In_tree y l). Ground. 
    Apply gt_tree_node; Intuition.
    Intro z; Generalize (i z); Intuition.
    Apply X.lt_trans with x; Auto.
    Apply H; Assumption.
    Generalize (a0 n H4); Constructor; Intuition.
    Generalize (i y0); Inversion_clear H3; Intuition; 
      Inversion_clear H4; Intuition.
    (* bug Ground *) Generalize (i y0); Intuition.
  Defined.

  (** [rbalance l x r] is similar to [lbalance], solving a possible red-red
      conflict on [r]. The balancing schema is similar:
<<
     B a x (R (R b y c) z d)
     B a x (R b y (R c z d)) -> R (B a x b) y (R c z d) 
     B a x b -> B a x b 
>> *)

  Definition rbalance : 
     (l:tree)(x:elt)(r:tree)
     (lt_tree x l) -> (gt_tree x r) ->
     (bst l) -> (bst r) ->
     { s:tree | 
        (bst s) /\
        ((n:nat)((almost_rbtree n r) /\ (rbtree n l)) -> 
                (rbtree (S n) s)) /\
	(y:elt)(In_tree y s) <-> ((E.eq y x)\/(In_tree y l)\/(In_tree y r)) }.
  Proof.
    Intros; Case (conflict r).
    Assumption.
    (* no conflict *)
    Exists (Node black l x r); Intuition. 
    Inversion H3; Auto. 
    (* red red conflict *)
    Intros; Exists (Node red (Node black l x a) x0
                             (Node black b y c)); Intuition.
    Constructor; Intuition.
    Constructor; Intuition.
    Intro z; Generalize (i z); Intuition.
    Assert (X.lt x x0).
    Assert (In_tree x0 r). Ground. 
    Apply H0; Assumption.
    Apply lt_tree_node; Intuition.
    Apply lt_tree_trans with x; Auto.
    Apply gt_tree_node; Intuition.
    Apply gt_tree_trans with y; Auto.
    Generalize (a0 n H4); Constructor; Intuition.
    Generalize (i y0); Inversion_clear H3; Intuition; 
      Inversion_clear H4; Intuition.
    (* bug Ground *) Generalize (i y0); Intuition.
  Defined.

  (** [insert x s] inserts [x] in tree [s], resulting in a possible top red-red
      conflict when [s] is red. Its code is:
<<  
     insert x Empty = 
       Node red Empty x Empty
     insert x (Node red a y b) = 
       if lt x y then Node red (insert x a) y b
       else if lt y x then Node red a y (insert x b)
       else (Node c a y b) 
     insert x (Node black a y b) = 
       if lt x y then lbalance (insert x a) y b
       else if lt y x then rbalance a y (insert x b)
       else (Node c a y b) 
>> *)

  Definition insert : 
    (x:elt) (s:t)
    { s':tree | (bst s') /\
                ((n:nat)(rbtree n s) -> 
                   ((almost_rbtree n s') /\
                    ((is_not_red s) -> (rbtree n s')))) /\
	        (y:elt)(In_tree y s') <-> ((E.eq y x) \/ (In_tree y s)) }.
  Proof.
    Intros x (s,Hs,Hrb).
    Generalize Hs Hrb; Clear Hs Hrb; Induction s; Simpl; Intros.
    (* Empty *)
    Exists (singleton_tree x); Unfold singleton_tree; Simpl; Intuition.
    Inversion H; EAuto.
    (* Node c t0 t1 t2 *)
    Simpl in Hrecs0 Hrecs1.
    Induction c.
    (* c = red => usual insertion in BST *)
    Elim (X.compare x t0); Intro.
    (* lt x t1 *)
    Clear Hrecs0; Case Hrecs1; Clear Hrecs1; Intros. EAuto. EAuto.
    Intuition.
    Exists (Node red x0 t0 s0); Intuition.
    Constructor; Intuition.
    Inversion Hs; Auto.
    Red; Intros.
    Generalize (H2 y); Intuition.
    Apply ME.eq_lt with x; Auto.
    Inversion Hs; Auto.
    Inversion Hs; Auto.
    Inversion_clear H0; Generalize (H1 n); Intuition.  (* BUG Ground *)
    Generalize (H2 y); Inversion H0; Intuition.
    Generalize (H2 y); Intuition.
    Generalize (H2 y); Inversion H3; Intuition.
    (* eq x t1 *)
    Clear Hrecs1 Hrecs0.
    Exists (Node red s1 t0 s0); Intuition.
    Apply IsRoot; EAuto.
    (* lt t1 x *)
    Clear Hrecs1; Case Hrecs0; Clear Hrecs0; Intros. EAuto. EAuto.
    Intuition.
    Exists (Node red s1 t0 x0); Intuition.
    Constructor; Intuition.
    Inversion Hs; Auto.
    Inversion Hs; Auto.
    Red; Intros.
    Generalize (H2 y); Intuition.
    Apply ME.lt_eq with x; Auto.
    Inversion Hs; Auto.
    Inversion_clear H0; (* bug Ground *) Generalize (H1 n); Intuition.
    Generalize (H2 y); Inversion H0; Intuition.
    Generalize (H2 y); Intuition.
    Generalize (H2 y); Inversion H3; Intuition.

    (* c = black => same code using smart constructors *)
    Elim (X.compare x t0); Intro.
    (* lt x t1 *)
    Clear Hrecs0; Case Hrecs1; Clear Hrecs1; Intros. EAuto. EAuto.
    Intuition.
    Case (lbalance x0 t0 s0); Intuition.
    Red; Intros.
    Generalize (H2 y); Intuition.
    Apply ME.eq_lt with x; Auto.
    Inversion Hs; Auto.
    Inversion Hs; Auto.
    Inversion Hs; Auto.
    Exists x1; Intuition.
    Inversion_clear H3; Ground.
    Inversion_clear H3; Ground.
    Generalize (H2 y); Generalize (H5 y); Intuition.
    Generalize (H2 y); Generalize (H5 y); Intuition.
    Inversion H6; Generalize (H2 y); Generalize (H5 y); Intuition.
    (* eq x t1 *)
    Clear Hrecs1 Hrecs0.
    Exists (Node black s1 t0 s0); Intuition.
    Apply IsRoot; EAuto.
    (* lt t1 x *)
    Clear Hrecs1; Case Hrecs0; Clear Hrecs0; Intros. EAuto. EAuto.
    Intuition.
    Case (rbalance s1 t0 x0); Intuition.
    Inversion Hs; Auto.
    Red; Intros.
    Generalize (H2 y); Intuition.
    Apply ME.lt_eq with x; Auto.
    Inversion Hs; Auto.
    Inversion Hs; Auto.
    Exists x1; Intuition.
    Inversion_clear H3; Ground.
    Inversion_clear H3; Ground.
    Generalize (H2 y); Generalize (H5 y); Intuition.
    Generalize (H2 y); Generalize (H5 y); Intuition.
    Inversion H6; Generalize (H2 y); Generalize (H5 y); Intuition.
  Defined.


  (** Finally [add x s] calls [insert] and recolors the root as black:
<<
      add x s = match insert x s with 
        | Node _ a y b -> Node black a y b
        | Empty -> assert false (* absurd *)
>> *)

  Definition add : (x:elt) (s:t) { s':t | (Add x s s') }.
  Proof.
    Intros x s; Case (insert x s). 
    Elim s; Clear s; Intros s Hbs Hrb;
      Simpl; Destruct x0; Intuition.
    (* Leaf => absurd *)
    Absurd (In_tree x Leaf).
    Intro; Inversion H0.
    Ground.
    (* Node c t0 t1 t2 *)
    Induction c.
    (* c = red => changed to black *)
    LetTac s' := (Node black t0 t1 t2).
    Assert s'bst: (bst s').
    Unfold s'; EAuto.
    Assert s'rbtree: (EX n:nat | (rbtree n s')).
    Elim Hrb; Clear Hrb; Intros n Hrb.
    Generalize (H1 n Hrb); Intuition.
    Exists (S n); Unfold s'.
    Inversion H3; Auto.
    Exists (t_intro s' s'bst s'rbtree); 
     Unfold s' Add In; Simpl.
    Intro y; Generalize (H2 y); Clear H2; Intuition;
      Try (Apply In_color with red; Assumption).
    Assert (In_tree y (Node red t0 t1 t2)); Auto.
    Apply In_color with black; Assumption.
    (* c = black => unchanged *)
    Assert s'rbtree: (EX n:nat | (rbtree n (Node black t0 t1 t2))).
    Elim Hrb; Clear Hrb; Intros n Hrb.
    Exists n; Ground. 
    Exists (t_intro (Node black t0 t1 t2) H s'rbtree); Intuition.
  Defined.

  (** * Deletion *)

  (* [UnbalancedLeft n t]: [t] is a tree of black height [S n]
     on its left side and [n] on its right side (the root color
     is taken into account, whathever it is) *)
     
  Inductive UnbalancedLeft : nat -> tree -> Prop :=
  | ULRed : (x:elt)(l,r:tree)(n:nat)
      (rbtree (S n) l) -> (rbtree n r) ->
      (is_not_red l) ->
      (UnbalancedLeft n (Node red l x r))
  | ULBlack : (x:elt)(l,r:tree)(n:nat)
      (rbtree (S n) l) -> (rbtree n r) ->
      (UnbalancedLeft (S n) (Node black l x r)).

  (* when a tree is unbalanced on its left, it can be repared *)

  Definition unbalanced_left : 
    (s:tree)(bst s) ->
    { r : tree * bool | 
        let (s',b) = r in 
        (bst s') /\
	((is_not_red s) /\ b=false -> (is_not_red s')) /\
	((n:nat)(UnbalancedLeft n s) ->
                (if b then (rbtree n s') else (rbtree (S n) s'))) /\
        ((y:elt)(In_tree y s') <-> (In_tree y s)) }.
  Proof.
    Destruct s.
    (* s = Leaf => Absurd *)
    Intro; Exists (Leaf,false); Intuition; Inversion H0.
    (* s = Node c t0 t1 t2 *)
    Induction c.
    (* s = Node red t0 t1 t2 *)
    Destruct t0.
    (* s = Node red Leaf t1 t2 => Absurd *)
    Intros; Exists ((Node black Leaf t1 t2), false); Intuition.
    Apply bst_color with red; Auto.
    Inversion H0.
    Inversion H5.
    Apply In_color with black; Auto.
    Apply In_color with red; Auto.
    (* s = Node red (Node c0 t1 t2 t3) t4 t5 *)
    Induction c0.
    (* s = Node red (Node red t1 t2 t3) t4 t5 => Absurd *)
    Intros; Exists ((Node black (Node red t1 t2 t3) t4 t5), false);
      Intuition.
    Apply bst_color with red; Auto.
    Inversion H0; Elim H7.
    Apply In_color with black; Auto.
    Apply In_color with red; Auto.
    (* s = Node red (Node black t1 t2 t3) t4 t5 *)
    Intros.
    Case (lbalance (Node red t1 t2 t3) t4 t5).
    Inversion H; Auto.
    Inversion H; Unfold gt_tree; Ground with In_color.
    Inversion H; Apply bst_color with black; Auto.
    Inversion H; Auto.
    Intros t' Ht'; Exists (t',false); Intuition.
    Elim H4.
    Apply H2; Intuition.
    Constructor; Inversion H1; Auto.
    Inversion_clear H8; Auto.
    Inversion_clear H8; Auto.
    Inversion_clear H1; Auto.
    Generalize (H3 y); Clear H3; Intuition.
    Constructor 2; Ground with In_color.
    Inversion_clear H1; Ground with In_color.
    (* s = Node black t0 t1 t2 *)
    Destruct t0.
    (* s = Node black Leaf t1 t2 => Absurd *)
    Intros; Exists ((Node black Leaf t1 t2), false); Intuition.
    Inversion H0.
    Inversion H4.
    (* s = Node black (Node c0 t1 t2 t3) t4 t5 *)
    Induction c0.
    (* s = Node black (Node red t1 t2 t3) t4 t5 *)
    Destruct t3.
    (* s = Node black (Node red t1 t2 Leaf) t4 t5 => Absurd *)
    Intros; Exists ((Node black (Node red t1 t2 Leaf) t4 t5), false); Intuition.
    Inversion H0; Inversion H4; Inversion H12.
    (* s = Node black (Node red t1 t2 (Node c1 t4 t5 t6)) t7 t8) *)
    Induction c1.
    (* s = Node black (Node red t1 t2 (Node red t4 t5 t6)) t7 t8) => absurd *)
    Intros; Exists ((Node black (Node red t1 t2 (Node red t4 t5 t6)) t7 t8),false); Intuition.
    Inversion H0; Inversion H4; Elim H14. 
    (* s = Node black (Node red t1 t2 (Node black t4 t5 t6)) t7 t8) *)
    Intros.
    Case (lbalance (Node red t4 t5 t6) t7 t8).
    Inversion H; Unfold lt_tree; Ground with In_color.
    Inversion H; Auto.
    Inversion H; Inversion H4; Apply bst_color with black; Auto.
    Inversion H; Auto.
    Intros t' Ht'; Exists ((Node black t1 t2 t'),false); Intuition.
    Constructor; Intuition.
    Inversion_clear H; Inversion_clear H1; Trivial.
    Inversion_clear H; Inversion_clear H1; Trivial.
    Intro; Generalize (H3 y); Clear H3; Intuition.
    Apply ME.lt_eq with t7; Auto.
    Inversion_clear H; Apply H9; Auto.
    Inversion_clear H; Inversion_clear H5; Apply H13; Ground with In_color.
    Inversion_clear H; Apply X.lt_trans with t7; Auto.
    Constructor; Intuition.
    Inversion_clear H1; Inversion_clear H4; Trivial.
    Inversion H1.
    Apply H2; Intuition.
    Inversion_clear H7; Constructor; Intuition.
    Inversion_clear H11; Trivial.
    Inversion_clear H11; Trivial.
    Generalize (H3 y); Clear H3; Inversion_clear H1; Intuition.
    Ground with In_color.
    Generalize (H3 y); Clear H3; Inversion_clear H1; Intuition.
    Inversion_clear H3; Intuition.
    Apply InRight; Apply H5; Apply In_color with black; Trivial.
    (* s = Node black (Node black t1 t2 t3) t4 t5 *)
    Intros.
    Case (lbalance (Node red t1 t2 t3) t4 t5).
    Inversion H; Auto.
    Inversion H; Auto.
    Inversion H; Apply bst_color with black; Auto.
    Inversion H; Auto.
    Intros t' Ht'; Exists (t',true); Intuition.
    Discriminate H5.
    Inversion H1.
    Apply H2; Intuition.
    Constructor.
    Inversion_clear H7; Auto.
    Inversion_clear H7; Auto.
    Generalize (H3 y); Clear H3; Intuition.
    Constructor 2; Ground with In_color.
    Inversion_clear H1; Ground with In_color.
  Defined.


  (* [UnbalancedRight n t]: [t] is a tree of black height [S n]
     on its right side and [n] on its left side (the root color
     is taken into account, whathever it is) *)
     
  Inductive UnbalancedRight : nat -> tree -> Prop :=
  | URRed : (x:elt)(l,r:tree)(n:nat)
      (rbtree n l) -> (rbtree (S n) r) ->
      (is_not_red r) ->
      (UnbalancedRight n (Node red l x r))
  | URBlack : (x:elt)(l,r:tree)(n:nat)
      (rbtree n l) -> (rbtree (S n) r) ->
      (UnbalancedRight (S n) (Node black l x r)).

  (* when a tree is unbalanced on its right, it can be repared *)

  Definition unbalanced_right : 
    (s:tree)(bst s) ->
    { r : tree * bool | 
        let (s',b) = r in 
        (bst s') /\
        ((is_not_red s) /\ b=false -> (is_not_red s')) /\
	((n:nat)(UnbalancedRight n s) ->
                (if b then (rbtree n s') else (rbtree (S n) s'))) /\
        ((y:elt)(In_tree y s') <-> (In_tree y s)) }.
  Proof.
    Destruct s.
    (* s = Leaf => Absurd *)
    Intro; Exists (Leaf,false); Intuition; Inversion H0.
    (* s = Node c t0 t1 t2 *)
    Induction c.
    (* s = Node red t0 t1 t2 *)
    Destruct t2.
    (* s = Node red t0 t1 Leaf => Absurd *)
    Intro; Exists ((Node black t0 t1 Leaf), false); Intuition.
    Apply bst_color with red; Auto.
    Inversion H0.
    Inversion H6.
    Apply In_color with black; Auto.
    Apply In_color with red; Auto.
    (* s = Node red t0 t1 (Node c0 t3 t4 t5) *)
    Induction c0.
    (* s = Node red t0 t1 (Node red t3 t4 t5) => Absurd *)
    Intros; Exists ((Node black t0 t1 (Node red t3 t4 t5)), false);
      Intuition.
    Apply bst_color with red; Auto.
    Inversion H0; Elim H7.
    Apply In_color with black; Auto.
    Apply In_color with red; Auto.
    (* s = Node red t0 t1 (Node black t3 t4 t5) *)
    Intros.
    Case (rbalance t0 t1 (Node red t3 t4 t5)).
    Inversion H; Auto.
    Inversion H; Unfold gt_tree; Ground with In_color.
    Inversion H; Auto.
    Inversion H; Apply bst_color with black; Auto.
    Intros t' Ht'; Exists (t',false); Intuition.
    Elim H4.
    Apply H2; Intuition.
    Constructor; Inversion H1; Auto.
    Inversion_clear H9; Auto.
    Inversion_clear H9; Auto.
    Inversion_clear H1; Auto.
    Generalize (H3 y); Clear H3; Intuition.
    Constructor 3; Ground with In_color.
    Inversion_clear H1; Ground with In_color.
    (* s = Node black t0 t1 t2 *)
    Destruct t2.
    (* s = Node black t0 t1 Leaf => Absurd *)
    Intro; Exists ((Node black t0 t1 Leaf), false); Intuition.
    Inversion H0.
    Inversion H6.
    (* s = Node black t0 t1 (Node c0 t3 t4 t5) *)
    Induction c0.
    (* s = Node black t0 t1 (Node red t3 t4 t5) *)
    Destruct t3.
    (* s = Node black t0 t1 (Node red Leaf t4 t5) => Absurd *)
    Intros; Exists ((Node black t0 t1 (Node red Leaf t4 t5)), false); Intuition.
    Inversion H0; Inversion H6; Inversion H10.
    (* s = Node black t0 t1 (Node red (Node c1 t4 t5 t6) t7 t8) *)
    Induction c1.
    (* s = Node black t0 t1 (Node red (Node red t4 t5 t6) t7 t8) => Absurd *)
    Intros; Exists ((Node black t0 t1 (Node red (Node red t4 t5 t6) t7 t8)),false); Intuition.
    Inversion H0; Inversion H6; Elim H13. 
    (* s = Node black t0 t1 (Node red (Node black t4 t5 t6) t7 t8) *)
    Intros.
    Case (rbalance t0 t1 (Node red t4 t5 t6)).
    Inversion H; Auto.
    Inversion H; Unfold gt_tree; Ground with In_color.
    Inversion H; Auto.
    Inversion H; Inversion H5; Apply bst_color with black; Auto.
    Intros t' Ht'; Exists ((Node black t' t7 t8),false); Intuition.
    Constructor; Intuition.
    Inversion_clear H; Inversion_clear H4; Trivial.
    Intro; Generalize (H3 y); Clear H3; Intuition.
    Apply ME.eq_lt with t1; Auto.
    Inversion_clear H; Apply H10; Auto.
    Inversion_clear H; Apply X.lt_trans with t1; Auto.
    Inversion_clear H; Inversion_clear H8; Apply H12; Ground with In_color.
    Inversion_clear H; Inversion_clear H4; Trivial.
    Constructor; Intuition.
    Inversion H1.
    Apply H2; Intuition.
    Inversion_clear H9; Constructor; Intuition.
    Inversion_clear H10; Trivial.
    Inversion_clear H10; Trivial.
    Inversion_clear H1; Inversion_clear H5; Trivial.
    Generalize (H3 y); Clear H3; Inversion_clear H1; Intuition.
    Ground with In_color.
    Generalize (H3 y); Clear H3; Inversion_clear H1; Intuition.
    Inversion_clear H3; Intuition.
    Apply InLeft; Apply H7; Apply In_color with black; Trivial.
    (* s = Node black t0 t1 (Node black t3 t4 t5) *)
    Intros.
    Case (rbalance t0 t1 (Node red t3 t4 t5)).
    Inversion H; Auto.
    Inversion H; Unfold gt_tree; Ground with In_color.
    Inversion H; Auto.
    Inversion H; Apply bst_color with black; Auto.
    Intros t' Ht'; Exists (t',true); Intuition.
    Discriminate H5.
    Inversion H1.
    Apply H2; Intuition.
    Constructor.
    Inversion_clear H9; Auto.
    Inversion_clear H9; Auto.
    Generalize (H3 y); Clear H3; Intuition.
    Constructor 3; Ground with In_color.
    Inversion_clear H1; Ground with In_color.
  Defined.

  Definition remove_min :
    (s:tree)(bst s) -> ~s=Leaf ->
    { r : tree * elt * bool |
        let (s',r') = r in
	let (m,b) = r' in
        (bst s') /\
	((is_not_red s) /\ b=false -> (is_not_red s')) /\
        ((n:nat) (rbtree n s) -> 
                 (if b then (lt O n) /\ (rbtree (pred n) s') else (rbtree n s'))) /\
        ((y:elt)(In_tree y s') -> (E.lt m y)) /\
        ((y:elt)(In_tree y s) <-> (E.eq y m) \/ (In_tree y s')) }.
  Proof.
    Induction s.
    (* s = Leaf => absurd *)
    Intuition.
    (* s = Node c t0 t1 t2 *)
    Destruct t0.
    Induction c.
    (* s = Node red Leaf t1 t2 *)
    Intros; Clear H H0. 
    Exists (t2,(t1,false)); Simpl; Intuition.
    Inversion_clear H1; Auto.
    Inversion_clear H; Auto.
    Inversion_clear H1; Apply H5; Auto.
    Inversion_clear H; Auto; Inversion H0.
    (* s = Node black Leaf t1 t2 *)
    Destruct t2; Intros; Clear H H0.
    (* s = Node black Leaf t1 Leaf *)
    Exists (Leaf,(t1,true)); Simpl; Intuition.
    Inversion_clear H; Auto with arith.
    Inversion_clear H; Auto.
    Inversion H.
    Inversion_clear H; Auto.
    (* s = Node black Leaf t1 (Node c t3 t4 t5) *)
    Exists ((Node black t3 t4 t5), (t1,false)); Intuition.
    Inversion_clear H1; Apply bst_color with c; Auto.
    Induction c.
    Inversion_clear H; Inversion_clear H3; Auto.
    Inversion_clear H; Inversion H3; Inversion H0.
    Rewrite <- H9 in H5; Discriminate H5.
    Inversion_clear H1; Apply H5; Apply In_color with black; Auto.
    Inversion_clear H; Auto.
    Inversion H0.
    Right; Apply In_color with c; Auto.
    Apply InRight; Apply In_color with black; Auto.
    (* s = Node c (Node c0 t1 t2 t3) t4 t5 *)
    Intros; Clear H0.
    LetTac l := (Node c0 t1 t2 t3).
    Case H; Clear H. (* remove_min l = l',m,d *)
    Inversion H1; Auto.
    Discriminate.
    Destruct x; Clear x; Intro l'; Destruct p; Clear p; Intros m d.
    Intuition. 
    Induction d.
    (* d = true *)
    Case (unbalanced_right (Node c l' t4 t5)).
    Inversion H1; Constructor; Auto.
    Intro; Ground.
    Destruct x; Clear x; Intros t' d'; Intuition.
    Exists (t',(m,d')); Repeat Split.
    Intuition.
    Intuition.
    Induction c; Intuition.
    (* c = red *)
    Assert (lt O n).
    Unfold l in H8.
    Induction c0; Inversion H8; Try Apply Lt.lt_O_Sn.
    Inversion H13; Inversion H17.
    Inversion H14; Apply Lt.lt_O_Sn.
    Induction d'; Intuition.
    (* d' = true *)
    Apply H7; Clear H7.
    Constructor; Inversion_clear H8; Auto.
    Generalize (H0 n); Intuition.
    Rewrite <- (Lt.S_pred n O H11); Auto.
    (* d' = false *)
    Rewrite (Lt.S_pred n O H11); Auto.
    Apply H7; Clear H7.
    Constructor; Inversion_clear H8; Auto.
    Generalize (H0 n); Intuition.
    Rewrite <- (Lt.S_pred n O H11); Auto.
    (* c = black *)
    Assert (le n (1)) \/ (lt (O) (pred n)); [ Omega | Intuition ].
    (* n = 1 => absurd *)
    Inversion H8.
    Absurd (le n (1)); Auto.
    Generalize (H0 n0 H15); Omega.
    (* n > 1 *)
    Induction d'; Intuition.
    (* d' = true *)
    Omega.
    Apply H7; Clear H7.
    Rewrite (Lt.S_pred (pred n) (O) H12); Auto.
    Constructor; Inversion H8; Simpl; Auto.
    Ground. 
    Rewrite <- (Lt.S_pred n0 (O)); Auto. Omega.
    (* d' = false *)
    Rewrite (Lt.S_pred n (O)); Auto. 
    Apply H7; Clear H7.
    Rewrite (Lt.S_pred (pred n) (O) H12); Auto.
    Constructor; Inversion H8; Simpl; Auto.
    Ground. 
    Rewrite <- (Lt.S_pred n0 (O)); Auto. Omega.
    Omega.
    (* ∀ y:elt,(In_tree y t') → E.lt m y *)
    Intros y Hy; Generalize (H10 y); Clear H10; Intuition.
    Inversion_clear H8.
      (* y=t4 *)
      Inversion H1.
      Apply ME.lt_eq with t4; Auto.
      Apply H17; Ground.
      (* y in l' *)
      Ground. 
      (* y in t5 *)
      Inversion H1.
      Apply E.lt_trans with t4; [ Apply H17 | Apply H18]; Ground.
    (* (In_tree y (Node c l t4 t5)) → (E.eq y m) ∨ In_tree y t' *)
    Generalize (H10 y); Clear H10; Intuition.
    Inversion_clear H10.
    Ground. 
    Generalize (H6 y); Clear H6; Intuition. 
    Ground.
    (* ((E.eq y m) ∨ In_tree y t') → In_tree y (Node c l t4 t5) *)
    Intuition.
    Ground.
    Generalize (H10 y); Clear H10; Intuition.
    Inversion_clear H8; Ground.
    (* d = false *)
    Exists ((Node c l' t4 t5),(m,false)); Simpl; Intuition.
    Inversion_clear H1; Constructor; Auto.
    Intro; Generalize (H6 y); Clear H6; Intuition.
    Inversion_clear H3; Constructor; Auto.
    Inversion_clear H3; Auto.
    Inversion H1.
    Apply ME.lt_eq with t4; Auto.
    Apply H13; Ground.
    Inversion H1.
    Apply E.lt_trans with t4; [ Apply H13 | Apply H14 ]; Ground.
    Generalize (H6 y); Clear H6; Intuition.
    Inversion_clear H3; Intuition.
    Ground.
    Generalize (H6 y); Clear H6; Intuition.
    Inversion_clear H7; Ground.
  Defined.

  Definition blackify :
    (s:tree)(bst s) ->
    { r : tree * bool | 
        let (s',b) = r in 
        (is_not_red s') /\ (bst s') /\
        ((n:nat)(rbtree n s) ->
	        if b then (rbtree n s') else (rbtree (S n) s')) /\
        ((y:elt)(In_tree y s) <-> (In_tree y s')) }.
  Proof.
    Destruct s; Intros.
    (* s = Leaf *)
    Exists (Leaf,true); Intuition.
    (* s = Node c t0 t1 t2 *)
    Induction c; [ Exists ((Node black t0 t1 t2), false) 
                 | Exists ((Node black t0 t1 t2), true) ];
    Intuition (Try Inversion H0; Auto).
    Apply bst_color with red; Trivial.
  Defined.

  Definition remove_aux : 
    (x:elt)(s:tree)(bst s) ->
    { r : tree * bool |
        let (s',b) = r in
        (bst s') /\
	((is_not_red s) /\ b=false -> (is_not_red s')) /\
        ((n:nat) (rbtree n s) -> 
                 (if b then (lt O n) /\ (rbtree (pred n) s') else (rbtree n s'))) /\
        ((y:elt)(In_tree y s') <-> (~(E.eq y x) /\ (In_tree y s))) }.
  Proof.
    Induction s.
    (* s = Leaf *)
    Intros; Exists (Leaf, false); Intuition.
    Inversion H0.
    (* s = Node c t0 t1 t2 *)
    Intros.
    Case (X.compare x t1); Intro.
    (* lt x t1 *)
    Clear H0; Case H; Clear H.
    Inversion H1; Trivial.
    Intros (l',d); Induction d; Intuition.
      (* d = true => unbalanced_right *)
      Case (unbalanced_right (Node c l' t1 t2)).
      Constructor; Inversion_clear H1; Auto.
      Intro; Generalize (H4 y); Intuition.
      Intros (s',d'); Intros; Exists (s',d').
      Intuition.
      Clear H4 H8; Induction c.
      Assert (UnbalancedRight (pred n) (Node red l' t1 t2)).
      Inversion_clear H6; Generalize (H0 n); Constructor; Intuition.
      Rewrite <- (S_pred n O); Trivial.
      Induction d'; Intuition.
      Inversion_clear H6; Ground.
      Rewrite (S_pred n O); Trivial. Apply H5; Trivial.
      Inversion_clear H6; Ground.
      Assert (UnbalancedRight (pred n) (Node black l' t1 t2)).
      Inversion H6; Simpl; Generalize (H0 n0); Intuition.
      Rewrite (S_pred n0 O); Trivial.
      Constructor; Intuition.
      Rewrite <- (S_pred n0 O); Trivial.
      Induction d'; Intuition.
      Inversion_clear H6; Ground.
      Rewrite (S_pred n O); Trivial. Apply H5; Trivial.
      Inversion_clear H6; Ground.
      (* In_tree y s' -> y <> x *)
      Clear H0 H5.
      Generalize (H8 y); Clear H8; Generalize (H4 y); Clear H4; Intuition.
      Inversion_clear H4.
      Apply (!E.lt_not_eq x t1); Auto.
      Apply E.eq_trans with y; Auto.
      Intuition.
      Apply (!ME.lt_not_gt y t1); Auto.
      Apply ME.eq_lt with x; Trivial.
      Inversion_clear H1; Auto.
      (* In_tree y s' -> In_tree y (Node c t0 t1 t2)) *)
      Clear H0 H5.
      Generalize (H8 y); Clear H8; Generalize (H4 y); Clear H4; Intuition.
      Inversion_clear H4; Intuition.
      (* In_tree y (Node c t0 t1 t2)) -> In_tree y s' *)
      Clear H0 H5.
      Generalize (H8 y); Clear H8; Generalize (H4 y); Clear H4; Intuition.
      Inversion_clear H10; Auto.
      (* d = false => Node c l' t1 t2, false *)
      Exists ((Node c l' t1 t2), false); Intuition.
      Inversion_clear H1; Constructor; Intuition.
      Intro; Intro; Generalize (H4 y); Clear H4; Intuition.
      Inversion_clear H2; Constructor; Ground.
      Generalize (H4 y); Clear H4; Intuition.
      Inversion_clear H2; Inversion_clear H1; Intuition.
      Apply (!E.lt_not_eq x t1); Auto.
      Apply E.eq_trans with y; Auto.
      Apply (!ME.lt_not_gt y t1); Auto.
      Apply ME.eq_lt with x; Trivial.
      Generalize (H4 y); Clear H4; Inversion_clear H2; Intuition.
      Generalize (H4 y); Clear H4; Inversion_clear H6; Intuition.
    (* eq x t1 *)
    Clear H H0.
    Generalize Dependent t2; Destruct t2; Intros.
      (* t2 = Leaf *)
      Induction c.
      (* c = red => t0, false *)
      Exists (t0, false); Intuition.
      Inversion_clear H1; Trivial.
      Inversion H0.
      Inversion_clear H; Trivial.
      Apply (!E.lt_not_eq y t1); Auto.
      Inversion_clear H1; Apply H4; Trivial.
      Apply E.eq_trans with x; Auto.
      Inversion_clear H2; Intuition.
      Absurd (X.eq y x); Auto.
      Apply E.eq_trans with t1; Auto.
      Inversion H.
      (* c = black => blackify t0 *)
      Case (blackify t0).
      Inversion_clear H1; Trivial.
      Intros (s',d); Intros; Exists (s',d); Intuition.
      Inversion H3; Induction d; Intuition.
      Generalize (H4 y); Clear H4; Inversion_clear H1; Intuition.
      Apply (!E.lt_not_eq y t1); Auto.
      Apply H7; Auto.
      Apply E.eq_trans with x; Auto.
      Ground. 
      Generalize (H4 y); Clear H4; Inversion_clear H6; Intuition.
      Absurd (X.eq y x); Auto.
      Apply E.eq_trans with t1; Auto.
      Inversion H3.
      (* t2 = Node c0 t3 t4 t5 *)
      Case (remove_min (Node c0 t3 t4 t5)).
      Inversion_clear H1; Trivial.
      Discriminate.
      Intros (r',(m,d)); Induction d; Intuition.
      (* d = true => unbalanced_left *)
      Case (unbalanced_left (Node c t0 m r')).
      Inversion_clear H1; Constructor; Trivial.
      Intro; Intro; Apply E.lt_trans with t1.
      Apply H7; Trivial.
      Apply H8; Ground.
      Intros (s',d); Intros; Exists (s',d); Intuition.
      Clear H3 H5 H9; Induction c.
      Assert (UnbalancedLeft (pred n) (Node red t0 m r')).
      Inversion_clear H7; Generalize (H0 n); Constructor; Intuition.
      Rewrite <- (S_pred n O); Trivial.
      Induction d; Intuition.
      Inversion_clear H7; Ground.
      Rewrite (S_pred n O); Trivial. Apply H6; Trivial.
      Inversion_clear H7; Ground.
      Assert (UnbalancedLeft (pred n) (Node black t0 m r')).
      Inversion H7; Simpl; Generalize (H0 n0); Intuition.
      Rewrite (S_pred n0 O); Trivial.
      Constructor; Intuition.
      Rewrite <- (S_pred n0 O); Trivial.
      Induction d; Intuition.
      Inversion_clear H7; Ground.
      Rewrite (S_pred n O); Trivial. Apply H6; Trivial.
      Inversion_clear H7; Ground.
      (* In_tree y s' -> y <> x *)
      Clear H0 H6.
      Generalize (H9 y); Clear H9; Generalize (H5 y);
      Generalize (H3 y); Clear H3; Intuition.
      Inversion_clear H6.
      Apply (!E.lt_not_eq x m); Auto.
      Inversion_clear H1.
      Apply ME.eq_lt with t1; Trivial.
      Apply H16; Ground.
      Apply E.eq_trans with y; Auto.
      Apply (!E.lt_not_eq y t1); Auto.
      Inversion_clear H1; Apply H15; Trivial.
      Apply E.eq_trans with x; Auto.
      Intuition.
      Apply (!E.lt_not_eq m y); Auto.
      Apply (!ME.lt_not_gt t1 m); Auto.
      Inversion_clear H1.
      Apply H16; Ground.
      Apply ME.lt_eq with y; Trivial.
      Apply E.eq_trans with x; Auto.
      (* In_tree y s' -> In_tree y (Node c t0 t1 t2)) *)
      Clear H0 H4 H6.
      Generalize (H9 y); Clear H9; Generalize (H5 y); Clear H5; Intuition.
      Inversion_clear H4; Intuition.
      (* In_tree y (Node c t0 t1 t2)) -> In_tree y s' *)
      Clear H0 H4 H6.
      Generalize (H9 y); Clear H9; Generalize (H5 y); Clear H5; Intuition.
      Inversion_clear H11; Intuition.
      Absurd (X.eq y x); Auto.
      Apply E.eq_trans with t1; Auto.
      (* d = false => Node c t0 m r', false *)
      Exists ((Node c t0 m r'), false); Intuition.
      Inversion_clear H1; Constructor; Intuition.
      Intro; Intro; Apply E.lt_trans with t1.
      Apply H7; Trivial.
      Generalize (H5 m); Clear H5; Intuition.
      Apply H8; Intuition.
      Inversion_clear H2; Constructor; Ground.
      Generalize (H5 y); Intuition.
      Inversion_clear H2; Inversion_clear H1.
      Generalize (H7 H9); Intro.
      Apply (!E.lt_not_eq t1 y); Auto.
      Apply H13; Trivial.
      Apply E.eq_trans with x; Auto.
      Apply (!E.lt_not_eq y t1); Auto.
      Apply H12; Trivial.
      Apply E.eq_trans with x; Auto.
      Generalize (H10 H9); Intro.
      Apply (!E.lt_not_eq t1 y); Auto.
      Apply H13; Trivial.
      Apply E.eq_trans with x; Auto.
      Generalize (H5 y); Clear H5; Inversion_clear H2; Intuition.
      Generalize (H5 y); Clear H5; Inversion_clear H7; Intuition.
      Absurd (X.eq y x); Auto.
      Apply E.eq_trans with t1; Auto.
     (* lt t1 x *)
    Clear H; Case H0; Clear H0.
    Inversion H1; Trivial.
    Intros (r',d); Induction d; Intuition.
      (* d = true => unbalanced_left *)
      Case (unbalanced_left (Node c t0 t1 r')).
      Constructor; Inversion_clear H1; Auto.
      Intro; Generalize (H4 y); Intuition.
      Intros (s',d'); Intros; Exists (s',d').
      Intuition.
      Clear H4 H8; Induction c.
      Assert (UnbalancedLeft (pred n) (Node red t0 t1 r')).
      Inversion_clear H6; Generalize (H0 n); Constructor; Intuition.
      Rewrite <- (S_pred n O); Trivial.
      Induction d'; Intuition.
      Inversion_clear H6; Ground.
      Rewrite (S_pred n O); Trivial. Apply H5; Trivial.
      Inversion_clear H6; Ground.
      Assert (UnbalancedLeft (pred n) (Node black t0 t1 r')).
      Inversion H6; Simpl; Generalize (H0 n0); Intuition.
      Rewrite (S_pred n0 O); Trivial.
      Constructor; Intuition.
      Rewrite <- (S_pred n0 O); Trivial.
      Induction d'; Intuition.
      Inversion_clear H6; Ground.
      Rewrite (S_pred n O); Trivial. Apply H5; Trivial.
      Inversion_clear H6; Ground.
      (* In_tree y s' -> y <> x *)
      Clear H0 H5.
      Generalize (H8 y); Clear H8; Generalize (H4 y); Clear H4; Intuition.
      Inversion_clear H4.
      Apply (!E.lt_not_eq t1 x); Auto.
      Apply E.eq_trans with y; Auto.
      Apply (!ME.lt_not_gt t1 y); Auto.
      Apply ME.lt_eq with x; Auto.
      Inversion_clear H1; Auto.
      Intuition.
      (* In_tree y s' -> In_tree y (Node c t0 t1 t2)) *)
      Clear H0 H5.
      Generalize (H8 y); Clear H8; Generalize (H4 y); Clear H4; Intuition.
      Inversion_clear H4; Intuition.
      (* In_tree y (Node c t0 t1 t2)) -> In_tree y s' *)
      Clear H0 H5.
      Generalize (H8 y); Clear H8; Generalize (H4 y); Clear H4; Intuition.
      Inversion_clear H10; Auto.
      (* d = false => Node c t0 t1 r', false *)
      Exists ((Node c t0 t1 r'), false); Intuition.
      Inversion_clear H1; Constructor; Intuition.
      Intro; Intro; Generalize (H4 y); Clear H4; Intuition.
      Inversion_clear H2; Constructor; Ground.
      Generalize (H4 y); Clear H4; Intuition.
      Inversion_clear H2; Inversion_clear H1; Intuition.
      Apply (!E.lt_not_eq t1 x); Auto.
      Apply E.eq_trans with y; Auto.
      Apply (!ME.lt_not_gt t1 y); Auto.
      Apply ME.lt_eq with x; Auto.
      Generalize (H4 y); Clear H4; Inversion_clear H2; Intuition.
      Generalize (H4 y); Clear H4; Inversion_clear H6; Intuition.
  Defined.

  Definition remove : (x:elt)(s:t)
                      { s':t | (y:elt)(In y s') <-> (~(E.eq y x) /\ (In y s))}.
  Proof.
    Intros x (s,Hs,Hrb); Case (remove_aux x s).
    Trivial.
    Intros (s',b); Intuition; Clear H2.
    Assert s'rbtree : (EX n:nat | (rbtree n s')).
    Elim Hrb; Clear Hrb; Intros n Hn; Induction b; Ground.
    Exists (t_intro s' H s'rbtree); Unfold In; Simpl; Intuition.
  Defined.

  (** * of_list *)
  
  (** Building a red-black tree from a sorted list *)

  Set Implicit Arguments.
  Record of_list_aux_Invariant [k,n:Z; l,l':(list elt); r:tree] : Prop := 
  make_olai  
  { olai_bst : (bst r); 
    olai_rb : (EX kn:nat | (inject_nat kn)=k /\ (rbtree kn r)); 
    olai_sort : (sort E.lt l'); 
    olai_length : (Zlength l')=(Zlength l)-n; 
    olai_same : 
      ((x:elt)(InList E.eq x l) <-> (In_tree x r) \/ (InList E.eq x l')); 
    olai_order : 
      ((x,y:elt)(In_tree x r) -> (InList E.eq y l') -> (E.lt x y)) }.
  Unset Implicit Arguments.

  Lemma power_invariant :  
    (n,k:Z)0<k ->
    (two_p k) <= n +1 <= (two_p (Zs k)) -> 
    let (nn,_) = (Zsplit2 (n-1)) in let (n1,n2) = nn in 
    (two_p (Zpred k)) <= n1+1 <= (two_p k)  /\
    (two_p (Zpred k)) <= n2+1 <= (two_p k).
  Proof.
    Intros.
    Case (Zsplit2 (n-1)).
    Intros (n1,n2) X.
    Generalize H0; Pattern 1 k; Rewrite (Zs_pred k).
    Rewrite two_p_S; Auto with zarith.
    Rewrite two_p_S; Auto with zarith.
    Apply Zlt_ZERO_pred_le_ZERO; Auto.
  Qed.

  Definition of_list_aux : 
    (k:Z) 0<=k -> 
    (n:Z) (two_p k) <= n+1 <= (two_p (Zs k)) -> 
    (l:(list elt)) (sort E.lt l) -> n <= (Zlength l) -> 
    { rl' : tree * (list elt) 
    | let (r,l')=rl' in (of_list_aux_Invariant k n l l' r) }.
  Proof.
  Intros k Hk; Pattern k; Apply natlike_rec2; Try Assumption.
  Intro n; Case (Z_eq_dec 0 n).
  (* k=0 n=0 *)
  Intros Hn1 Hn2 l Hl1 Hl2; Exists (Leaf, l); Intuition. 
  Apply make_olai; Intuition.
  Exists O; Auto.
  Inversion H2.
  Inversion H1.
  (* k=0 n>0 (in fact 1) *)
  Intros Hn1 Hn2.
  Assert n=1. Rewrite two_p_S in Hn2; Simpl in Hn2; Auto with zarith.
  Rewrite H.
  Intro l; Case l.
   (* l = [], absurd case. *)
   Intros Hl1 Hl2; Unfold Zlength Zlt in Hl2; Elim Hl2; Trivial.
   (* l = x::l' *)
   Intros x l' Hl1 Hl2; Exists ((Node red Leaf x Leaf), l'); Intuition.
   Apply make_olai; Intuition.
   Exists O; Auto.
   Inversion Hl1; Auto.   
   Rewrite Zlength_cons; Auto with zarith.
   Inversion_clear H2; Auto.
   Inversion_clear H3; Auto; Inversion_clear H2.
   Inversion_clear H2; Try Solve [ Inversion H4 ].
   Inversion_clear Hl1.
   Apply ME.In_sort with l'; Auto.
   EApply ME.Inf_eq; EAuto.   
  (* k>0 *)
  Clear k Hk; Intros k Hk Hrec n Hn l Hl1 Hl2.
  Rewrite <- Zs_pred in Hrec.
  Generalize (power_invariant n k Hk).
  Elim (Zsplit2 (n-1)); Intros (n1,n2) (A,B) C.  
  Elim (C Hn); Clear C; Intros Hn1 Hn2.
  (* First recursive call : (of_list_aux (Zpred k) n1 l) gives (lft,l') *)
  Elim (Hrec n1 Hn1 l Hl1). 
  Intro p; Case p; Clear p; Intros lft l'; Case l'.
   (* l' = [], absurd case. *)
   Intros o; ElimType False.  
   Generalize (olai_length o).
   Unfold 1 Zlength; Simpl; Intros X. 
   Assert n1 = (Zlength l). Omega. Clear X.
   Rewrite <- H in Hl2.
   Assert n <= n2.
     Apply Zle_trans with n1; Auto; Inversion H; Omega.
   Assert 0<n+1.
    Apply Zlt_le_trans with (two_p k).
    Generalize (two_p_gt_ZERO k); Omega.
    Inversion_clear Hn; Trivial.
   Omega. 
   (* l' = x :: l'' *)
   Intros x l'' o1.
   (* Second recursive call : (of_list_aux (Zpred k) n2 l'') gives (rht,l''') *)
   Elim (Hrec n2 Hn2 l''); Clear Hrec.
   Intro p; Case p; Clear p; Intros rht l''' o2.
   Exists ((Node black lft x rht),l''').   
   Apply make_olai.
   (* inv1 : bst *)
   Constructor; Try Solve [ EApply olai_bst; EAuto ].
   Unfold lt_tree; Intros.
   Apply (olai_order o1 7!y 8!x H); Auto.
   Assert sorted := (olai_sort o1). 
   Inversion_clear sorted.   
   Unfold gt_tree; Intros.
   Apply ME.In_sort with l''; Auto.
   Elim (olai_same o2 y); Auto.
   (* inv2 : rb *)  
   Elim (inject_nat_complete k); [Intros kn; Case kn |Omega].
   Simpl; Intros X; Rewrite X in Hk; Absurd 0<0; Auto with zarith.
   Clear kn; Intro kn.
   Exists (S kn); Split; Auto. 
   Constructor.
   Elim (olai_rb o1); Intros kn' (Hkn',Hrb); Rewrite inj_S in H.
   Rewrite H in Hkn'; Rewrite <- Zpred_Sn in Hkn'.
   Elim (eq_nat_dec kn kn'); Intro X; [Subst | Elim (inj_neq ?? X)]; Auto.
   Elim (olai_rb o2); Intros kn' (Hkn',Hrb); Rewrite inj_S in H.
   Rewrite H in Hkn'; Rewrite <- Zpred_Sn in Hkn'.
   Elim (eq_nat_dec kn kn'); Intro X; [Subst | Elim (inj_neq ?? X)]; Auto.
   (* inv3 : sort *)
   Exact (olai_sort o2).
   (* inv4 : length *)
   Rewrite (olai_length o2).
   Rewrite (Zpred_Sn (Zlength l'')).
   Rewrite <- (Zlength_cons x l'').
   Rewrite (olai_length o1); Unfold Zpred; Omega.
   (* inv5 : same *)
   Intro y; Generalize (olai_same o1 y); Generalize (olai_same o2 y).
   Assert (InList E.eq y x::l'') <-> (E.eq y x) \/ (InList E.eq y l'').
    Split; Intro H; Inversion H; Auto.
   Generalize H; Clear H A B Hn Hn1 Hn2 o1 o2.
   Intuition; Inversion_clear H9; Intuition.
   (* inv6 : order *)  
   Intros a b In_r In_l'''.
   Inversion_clear In_r.
   Assert sorted := (olai_sort o1).
   Inversion_clear sorted.
   Apply ME.eq_lt with x; Auto.
   Apply ME.In_sort with l''; Auto.  
   Generalize (olai_same o2 b); Intros (_,X); Auto.
   Apply (olai_order o1 7!a 8!b); Auto.
   Constructor 2.
   Generalize (olai_same o2 b); Intros (_,X); Auto.
   Apply (olai_order o2 7!a 8!b); Auto.
  (* misc preconditions to ensure *)
  Assert sorted := (olai_sort o1); Inversion_clear sorted; Trivial.
  Rewrite (Zpred_Sn (Zlength l'')).
  Rewrite <- (Zlength_cons x l'').
  Rewrite (olai_length o1); Unfold Zpred; Omega.
  Omega. 
  Defined.

  Definition of_list : (l:(list elt))(sort E.lt l) -> 
    { s : t  | (x:elt)(In x s) <-> (InList E.eq x l) }. 
  Proof.
  Intros.
  LetTac n := (Zlength l).
  LetTac k := (N_digits n).
  Assert 0<=n. 
   Unfold n; Rewrite Zlength_correct; Auto with zarith.
  Assert (two_p k) <= n+1 <= (two_p (Zs k)).
    Unfold k; Generalize H0; Case n; Intros.
    Rewrite two_p_S; Simpl; Omega.
    Unfold N_digits; Generalize (log_inf_correct p); Omega.
    Unfold Zle in H1; Elim H1; Auto.
  Elim (of_list_aux k (ZERO_le_N_digits n) n H1 l); Auto.
  Intros (r,l') o.
  Assert (EX n : nat | (rbtree n r)).
   Elim (olai_rb o); Intros kn Hkn; Exists kn; Intuition.
  Exists (t_intro r (olai_bst o) H2).
  Unfold In; Simpl.
  Intro x; Generalize (olai_same o x).
  Rewrite (Zlength_nil_inv l').
  Intuition; Inversion_clear H1.
  Rewrite (olai_length o); Unfold n; Omega.
  Unfold n; Omega. 
  Qed. 
  
  (** * Elements *)

  (** [elements_tree_aux acc t] catenates the elements of [t] in infix
      order to the list [acc] *)

  Fixpoint elements_tree_aux [acc:(list X.t); t:tree] : (list X.t) :=
    Cases t of
    | Leaf => 
        acc
    | (Node _ l x r) => 
        (elements_tree_aux (x :: (elements_tree_aux acc r)) l)
    end.

  (** then [elements_tree] is an instanciation with an empty [acc] *)

  Definition elements_tree := (elements_tree_aux []).

  Lemma elements_tree_aux_acc_1 : 
    (s:tree)(acc:(list elt))
    (x:elt)(InList E.eq x acc)->(InList E.eq x (elements_tree_aux acc s)).
  Proof.
    Induction s; Simpl; Intuition.
  Save.
  Hints Resolve elements_tree_aux_acc_1.

  Lemma elements_tree_aux_1 : 
    (s:tree)(acc:(list elt))
    (x:elt)(In_tree x s)->(InList E.eq x (elements_tree_aux acc s)).
  Proof.
    Induction s; Simpl; Intuition.
    Inversion H.
    Inversion_clear H1; Ground.
  Save.

  Lemma elements_tree_1 : 
    (s:tree)
    (x:elt)(In_tree x s)->(InList E.eq x (elements_tree s)).
  Proof.
    Unfold elements_tree; Intros; Apply elements_tree_aux_1; Auto.
  Save.
  Hints Resolve elements_tree_1.

  Lemma elements_tree_aux_acc_2 : 
    (s:tree)(acc:(list elt))
    (x:elt)(InList E.eq x (elements_tree_aux acc s)) ->
      (InList E.eq x acc) \/ (In_tree x s).
  Proof.
    Induction s; Simpl; Intuition.
    Elim (H ?? H1); Intuition.
    Inversion_clear H2; Intuition.
    Elim (H0 ?? H3); Intuition.
  Save.
  Hints Resolve elements_tree_aux_acc_2.

  Lemma elements_tree_2 : 
   (s:tree)
    (x:elt)(InList E.eq x (elements_tree s)) -> (In_tree x s).
  Proof.
    Unfold elements_tree; Intros.
    Elim (elements_tree_aux_acc_2 ??? H); Auto.
    Intros; Inversion H0.
  Save.
  Hints Resolve elements_tree_2.

  Lemma elements_tree_aux_sort : 
    (s:tree)(bst s) -> (acc:(list elt))
    (sort E.lt acc) -> 
    ((x:elt)(InList E.eq x acc) -> (y:elt)(In_tree y s) -> (E.lt y x)) ->
    (sort E.lt (elements_tree_aux acc s)).
  Proof.
    Induction s; Simpl; Intuition.
    Apply H.
    Inversion H1; Auto.
    Constructor. 
    Apply H0; Auto.
    Inversion H1; Auto.
    Apply ME.Inf_In_2.
    Replace X.eq with E.eq; Replace X.lt with E.lt; Auto.
    Intros.
    Elim (elements_tree_aux_acc_2 t2 acc y); Intuition.
    Inversion_clear H1.
    Apply H9; Auto.
    Intuition.
    Inversion_clear H4.
    Apply ME.lt_eq with t1; Auto.
    Inversion_clear H1.
    Apply H8; Auto.
    Elim (elements_tree_aux_acc_2 ??? H6); Intuition.
    Apply E.lt_trans with t1.
    Inversion_clear H1; Apply H9; Auto.
    Inversion_clear H1; Apply H10; Auto.
  Save.

  Lemma elements_tree_sort : 
    (s:tree)(bst s) -> (sort E.lt (elements_tree s)).
  Proof.
    Intros; Unfold elements_tree; Apply elements_tree_aux_sort; Auto.
    Intros; Inversion H0.
  Save.
  Hints Resolve elements_tree_sort.

  Definition elements : 
    (s:t){ l:(list elt) | (sort E.lt l) /\ (x:elt)(In x s)<->(InList E.eq x l)}.
  Proof.
    Intros (s,Hs,Hrb); Unfold In; Simpl.
    Exists (elements_tree s); Repeat Split.
    Apply elements_tree_sort; Auto.
    Apply elements_tree_1; Auto.
    Apply elements_tree_2; Auto.
  Defined.

  (** * Isomorphism with FSetList. *)

  Module Lists := FSetList.Make(X).

  Definition of_slist : (l:Lists.t) { s : t | (x:elt)(Lists.In x l)<->(In x s) }. 
  Proof.
  Intros (l,Hl).
  Elim (of_list l Hl); Intros s Hls. 
  Exists s; Unfold Lists.In Lists.Raw.In; Simpl; Ground.
  Defined.

  Definition to_slist : (s:t) { l : Lists.t | (x:elt)(In x s)<->(Lists.In x l) }. 
  Proof.
  Intro s; Elim (elements s); Intros l (Hl1, Hl2).
  Exists (Lists.Build_slist Hl1).
  Unfold Lists.In Lists.Raw.In; Simpl; Ground.
  Defined.

  (** * Union *)

  Definition union : (s,s':t){ s'':t | (x:elt)(In x s'') <-> ((In x s)\/(In x s'))}.
  Proof.
  Intros s s'.
  Elim (to_slist s); Intros l Hl.
  Elim (to_slist s'); Intros l' Hl'.
  Elim (of_slist (Lists.union l l')); Intros r Hr.
  Exists r; Intuition.
  Elim (!Lists.union_1 l l' x); Ground.
  Elim (Hr x); Intros A _; Apply A; Apply (!Lists.union_2 l l' x); Ground.
  Elim (Hr x); Intros A _; Apply A; Apply (!Lists.union_3 l l' x); Ground.
  Defined.

  (** * Intersection *)

  Lemma inter : (s,s':t){ s'':t | (x:elt)(In x s'') <-> ((In x s)/\(In x s'))}.
  Proof.
  Intros s s'.
  Elim (to_slist s); Intros l Hl.
  Elim (to_slist s'); Intros l' Hl'.
  Elim (of_slist (Lists.inter l l')); Intros r Hr.
  Exists r; Intuition.
  Elim (Hl x); Intros _ A; Apply A; Apply (!Lists.inter_1 l l' x); Ground.
  Elim (Hl' x); Intros _ A; Apply A; Apply (!Lists.inter_2 l l' x); Ground.
  Elim (Hr x); Intros A _; Apply A; Apply (!Lists.inter_3 l l' x); Ground.
  Defined.

  (** * Difference *)

  Lemma diff : (s,s':t){ s'':t | (x:elt)(In x s'') <-> ((In x s)/\~(In x s'))}.
  Proof.
  Intros s s'.
  Elim (to_slist s); Intros l Hl.
  Elim (to_slist s'); Intros l' Hl'.
  Elim (of_slist (Lists.diff l l')); Intros r Hr.
  Exists r; Intuition.
  Elim (Hl x); Intros _ A; Apply A; Apply (!Lists.diff_1 l l' x); Ground.
  Elim (!Lists.diff_2 l l' x); Ground.  
  Elim (Hr x); Intros A _; Apply A; Apply (!Lists.diff_3 l l' x); Ground.
  Defined.

  (** * Equality test *)

  Lemma equal : (s,s':t){ Equal s s' } + { ~(Equal s s') }.
  Proof. 
  Intros s s'.
  Elim (to_slist s); Intros l Hl.
  Elim (to_slist s'); Intros l' Hl'.
  Assert (Lists.Equal l l')->(Lists.equal l l')=true. Exact (!Lists.equal_1 l l').
  Assert (Lists.equal l l')=true->(Lists.Equal l l'). Exact (!Lists.equal_2 l l').
  Generalize H H0; Case (Lists.equal l l'); Unfold Lists.Equal Equal. 
  Left; Intros; Generalize (H2 (refl_equal ? true)); Ground.  
  Right; Intros; Intro. 
  Absurd false=true; [ Auto with bool | Ground ].
  Defined.

  (** * Inclusion test *)

  Lemma subset : (s,s':t){ Subset s s' } + { ~(Subset s s') }.
  Proof. 
  Intros s s'.
  Elim (to_slist s); Intros l Hl.
  Elim (to_slist s'); Intros l' Hl'.
  Assert (Lists.Subset l l')->(Lists.subset l l')=true. Exact (!Lists.subset_1 l l').
  Assert (Lists.subset l l')=true->(Lists.Subset l l'). Exact (!Lists.subset_2 l l').
  Generalize H H0; Case (Lists.subset l l'); Unfold Lists.Subset Subset. 
  Left; Intros; Generalize (H2 (refl_equal ? true)); Ground.  
  Right; Intros; Intro. 
  Absurd false=true; [ Auto with bool | Ground ].
  Defined.

  (** * Fold *)

  Fixpoint fold_tree [A:Set; f:elt->A->A; s:tree] : A -> A :=
    Cases s of
    | Leaf => [a]a
    | (Node _ l x r) => [a](fold_tree A f l (f x (fold_tree A f r a)))
    end.
  Implicits fold_tree [1].

  Definition fold_tree' := 
   [A:Set; f:elt->A->A; s:tree] (Lists.Raw.fold f (elements_tree s)).
  Implicits fold_tree' [1].

  Lemma fold_tree_equiv_aux : 
     (A:Set)(s:tree)(f:elt->A->A)(a:A; acc : (list elt))
     (Lists.Raw.fold f (elements_tree_aux acc s) a)
     = (fold_tree f s (Lists.Raw.fold f acc a)).
  Proof.
  Induction s.
  Simpl; Intuition.
  Simpl; Intros.
  Rewrite H.
  Rewrite <- H0.
  Simpl; Auto.
  Qed.

  Lemma fold_tree_equiv : 
     (A:Set)(s:tree)(f:elt->A->A; a:A)
     (fold_tree f s a)=(fold_tree' f s a).
  Proof.
  Unfold fold_tree' elements_tree. 
  Induction s; Simpl; Auto; Intros.
  Rewrite fold_tree_equiv_aux.
  Rewrite H0.
  Simpl; Auto.
  Qed.

  Definition fold : 
   (A:Set)(f:elt->A->A)(s:t)(i:A) 
   { r : A | (EX l:(list elt) | 
                  (Unique E.eq l) /\
                  ((x:elt)(In x s)<->(InList E.eq x l)) /\ 
                  r = (fold_right f i l)) }.
  Proof.
    Intros A f s i; Exists (fold_tree f s i).
    Rewrite fold_tree_equiv.
    Unfold fold_tree'.
    Elim (Lists.Raw.fold_1 (elements_tree_sort ? (is_bst s)) i f); Intro l.
    Exists l; Elim H; Clear H; Intros H1 (H2,H3); Split; Auto.
    Split; Auto.
    Intros x; Generalize (elements_tree_1 s x) (elements_tree_2 s x).
    Generalize (H2 x); Unfold In; Ground.
  Defined.

  (** * Cardinal *)

  Definition cardinal : 
     (s:t) { r : nat | (EX l:(list elt) | 
                              (Unique E.eq l) /\ 
                              ((x:elt)(In x s)<->(InList E.eq x l)) /\ 
                              r = (length l)) }.
  Proof.
    Intros; Elim (fold nat [_]S s O); Intro n; Exists n.
    Assert (l:(list elt))(length l)=(fold_right [_]S O l). 
     Induction l; Simpl; Auto.
    Elim p; Intro l; Exists l; Rewrite H; Auto.
  Qed.

  (** * Filter *)

  Module DLists := DepOfNodep(Lists).

  Definition filter : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { s':t | (compat_P E.eq P) -> (x:elt)(In x s') <-> ((In x s)/\(P x)) }.
  Proof.
  Intros.
  Elim (to_slist s); Intros l Hl.
  Elim (DLists.filter Pdec l); Intros l' Hl'.
  Elim (of_slist l'); Intros r Hr.
  Exists r.
  Intros C; Generalize (Hl' C); Ground.
  Qed.

  Lemma for_all : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { (compat_P E.eq P) -> (For_all P s) } + 
     { (compat_P E.eq P) -> ~(For_all P s) }.
  Proof.
  Intros; Unfold For_all.
  Elim (to_slist s); Intros l Hl.
  Elim (DLists.for_all Pdec l); Unfold Lists.For_all; Intro H; [Left|Right]; 
    Intro C; Generalize (H C); Ground.
  Qed.

  Lemma exists : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { (compat_P E.eq P) -> (Exists P s) } + 
     { (compat_P E.eq P) -> ~(Exists P s) }.
  Proof.
  Intros; Unfold Exists.
  Elim (to_slist s); Intros l Hl.
  Elim (DLists.exists Pdec l); Unfold Lists.Exists; Intro H; [Left|Right]; 
    Intro C; Generalize (H C); Ground.
  Qed.

  Lemma partition : (P:elt->Prop)(Pdec:(x:elt){P x}+{~(P x)})(s:t)
     { partition : t*t | 
        let (s1,s2) = partition in 
	(compat_P E.eq P) -> 
	((For_all P s1) /\ 
	 (For_all ([x]~(P x)) s2) /\
	 (x:elt)(In x s)<->((In x s1)\/(In x s2))) }.
  Proof.
  Intros; Unfold For_all.
  Elim (to_slist s); Intros l Hl.
  Elim (DLists.partition Pdec l); Unfold Lists.For_all; Intros (l1,l2) H.
  Elim (of_slist l1); Intros s1 Hs1.
  Elim (of_slist l2); Intros s2 Hs2.
  Exists (s1,s2).
  Intro Comp; Elim (H Comp); Intros A (B,C); Clear H Comp.
  Intuition.
  Apply A; Ground.
  Apply (B x); Ground.
  Elim (C x); Intros D _; Elim D; [Left|Right|Idtac]; Ground.
  Ground.
  Ground.
  Qed.

  (** * Minimum element *)

  Definition min_elt : 
     (s:t){ x:elt | (In x s) /\ (For_all [y]~(E.lt y x) s) } + { Empty s }.
  Proof.
    Intros (s,Hs,Hrb).
    Unfold For_all Empty In; Simpl.
    Generalize Hs; Clear Hs Hrb; Induction s; Simpl; Intros.
    (* s = Leaf *)
    Right; Intros; Intro; Inversion H.
    (* s = Node c s1 t0 s0 *)
    Clear Hrecs0; Generalize Hs Hrecs1; Clear Hs Hrecs1; Case s1; Intros.
    (* s1 = Leaf *)
    Left; Exists t0; Intuition.
    Inversion_clear H.
    Absurd (X.eq x t0); Auto.
    Inversion H1.
    Inversion_clear Hs; Absurd (E.lt x t0); Auto.
    (* s1 = Node c0 t1 t2 t3 *)
    Case Hrecs1; Clear Hrecs1.
    Inversion Hs; Auto.
    (* a minimum for [s1] *)
    Intros (m,Hm); Left; Exists m; Intuition.
    Apply (H0 x); Auto.
    Assert (X.lt m t0).
    Inversion_clear Hs; Auto.
    Inversion_clear H1; Auto.
    Elim (!X.lt_not_eq x t0); [ EAuto | Auto ].
    Inversion_clear Hs.
    Elim (!ME.lt_not_gt x t0); [ EAuto | Auto ].
    (* non minimum for [s1] => absurd *)
    Intro; Right; Intuition.
    Apply (n t2); Auto.
  Defined.

  (** * Maximum element *)

  Definition max_elt : 
     (s:t){ x:elt | (In x s) /\ (For_all [y]~(E.lt x y) s) } + { Empty s }.
   Proof.
    Intros (s,Hs,Hrb).
    Unfold For_all Empty In; Simpl.
    Generalize Hs; Clear Hs Hrb; Induction s; Simpl; Intros.
    (* s = Leaf *)
    Right; Intros; Intro; Inversion H.
    (* s = Node c s1 t0 s0 *)
    Clear Hrecs1; Generalize Hs Hrecs0; Clear Hs Hrecs0; Case s0; Intros.
    (* s0 = Leaf *)
    Left; Exists t0; Intuition.
    Inversion_clear H.
    Absurd (X.eq x t0); Auto.
    Inversion_clear Hs; Absurd (E.lt t0 x); Auto.
    Inversion H1.
    (* s0 = Node c0 t1 t2 t3 *)
    Case Hrecs0; Clear Hrecs0.
    Inversion Hs; Auto.
    (* a maximum for [s0] *)
    Intros (m,Hm); Left; Exists m; Intuition.
    Apply (H0 x); Auto.
    Assert (X.lt t0 m).
    Inversion_clear Hs; Auto.
    Inversion_clear H1; Auto.
    Elim (!X.lt_not_eq x t0); [ EAuto | Auto ].
    Inversion_clear Hs.
    Elim (!ME.lt_not_gt t0 x); [ EAuto | Auto ].
    (* non maximum for [s0] => absurd *)
    Intro; Right; Intuition.
    Apply (n t2); Auto.
  Defined.

  (** * Any element *)

  Definition choose : (s:t) { x:elt | (In x s)} + { Empty s }.
  Proof.
    Intros (s,Hs,Hrb); Unfold Empty In; Simpl; Case s; Intuition.
    Right; Intros; Inversion H.
    Left; Exists t1; Auto.
  Defined.

  (** * Comparison *)
  
  Definition eq : t -> t -> Prop := Equal.

  Definition lt : t -> t -> Prop :=
    [s,s':t]let (l,_) = (to_slist s) in
            let (l',_) = (to_slist s') in
	    (Lists.lt l l').

  Lemma eq_refl: (s:t)(eq s s). 
  Proof.
    Unfold eq Equal; Intuition.
  Save.

  Lemma eq_sym: (s,s':t)(eq s s') -> (eq s' s).
  Proof.
    Unfold eq Equal; Ground.
  Save.

  Lemma eq_trans: (s,s',s'':t)(eq s s') -> (eq s' s'') -> (eq s s'').
  Proof.
    Unfold eq Equal; Ground.
  Save.

  Lemma lt_trans : (s,s',s'':t)(lt s s') -> (lt s' s'') -> (lt s s'').
  Proof.
    Intros s s' s''; Unfold lt.
    Elim (to_slist s); Intros l Hl.
    Elim (to_slist s'); Intros l' Hl'.
    Elim (to_slist s''); Intros l'' Hl''.
    Exact (!Lists.lt_trans l l' l'').
  Save.

  Definition eql : t -> t -> Prop :=
    [s,s':t]let (l,_) = (to_slist s) in
            let (l',_) = (to_slist s') in
	    (Lists.eq l l').

  Lemma eq_eql : (s,s':t)(eq s s') -> (eql s s').
  Proof.
    Unfold eq Equal eql Lists.eq Lists.Raw.eq Lists.Raw.Equal.
    Intros s s'.
    Elim (to_slist s); Unfold Lists.In Lists.Raw.In; 
      Simpl; Intros l Hl.
    Elim (to_slist s'); Unfold Lists.In Lists.Raw.In; 
      Simpl; Intros l' Hl'.
    Ground.
   Save.

  Lemma eql_eq : (s,s':t)(eql s s') -> (eq s s').
  Proof.
    Unfold eq Equal eql Lists.eq Lists.Raw.eq Lists.Raw.Equal.
    Intros s s'.
    Elim (to_slist s); Unfold Lists.In Lists.Raw.In; 
      Simpl; Intros l Hl.
    Elim (to_slist s'); Unfold Lists.In Lists.Raw.In; 
      Simpl; Intros l' Hl'.
    Ground.
  Save.

  Lemma lt_not_eq : (s,s':t)(lt s s') -> ~(eq s s').
  Proof.
    Intros s s' H; Intro.
    Generalize (eq_eql s s' H0).
    Generalize H; Unfold lt eql.
    Elim (to_slist s); Intros l Hl.
    Elim (to_slist s'); Intros l' Hl'.
    Exact (!Lists.lt_not_eq l l').
  Save.
  
  Definition compare: (s,s':t)(Compare lt eq s s').
  Proof.
    Intros s s'.
    Cut (lt s s') -> (Compare lt eq s s').    
    Cut (eq s s') -> (Compare lt eq s s'). 
    Cut (lt s' s) -> (Compare lt eq s s'). 
    Unfold 1 4 lt.
    Generalize (eql_eq s s'); Unfold eql.
    Elim (to_slist s); Intros l Hl.
    Elim (to_slist s'); Intros l' Hl'.
    Elim (Lists.compare l l'); Intuition.
    Constructor 3; Trivial.
    Constructor 2; Trivial.
    Constructor 1; Trivial.
  Defined.

End Make.




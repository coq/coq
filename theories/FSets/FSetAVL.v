(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** This module implements sets using AVL trees.
    It follows the implementation from Ocaml's standard library. *)

Require FSetInterface.

Require ZArith.
Import Z_scope.
Open Scope Z_scope.

Set Ground Depth 3.

Module Make [X : OrderedType] <: Sdep with Module E := X.

  Module E := X.
  Module ME := MoreOrderedType X.

  Definition elt := X.t.

  (** * Trees *)

  Inductive tree : Set :=
  | Leaf : tree
  | Node : tree -> X.t -> tree -> Z -> tree.

  (** * Occurrence in a tree *)

  Inductive In_tree [x:elt] : tree -> Prop :=
  | IsRoot : (l,r:tree)(h:Z)(y:elt)
             (X.eq x y) -> (In_tree x (Node l y r h))
  | InLeft : (l,r:tree)(h:Z)(y:elt)
             (In_tree x l) -> (In_tree x (Node l y r h))
  | InRight : (l,r:tree)(h:Z)(y:elt)
              (In_tree x r) -> (In_tree x (Node l y r h)).

  Hint In_tree := Constructors In_tree.

  (** [In_tree] is height-insensitive *)

  Lemma In_height : (h,h':Z)(x,y:elt)(l,r:tree)
    (In_tree y (Node l x r h)) -> (In_tree y (Node l x r h')).
  Proof.
    Inversion 1; Auto.
  Save.
  Hints Resolve In_height.

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

  Lemma lt_tree_node : (x,y:elt)(l,r:tree)(h:Z)
    (lt_tree x l) -> (lt_tree x r) -> (X.lt y x) -> 
    (lt_tree x (Node l y r h)).
  Proof.
    Unfold lt_tree; Intuition.
    Inversion_clear H2; Intuition.
    Apply ME.eq_lt with y; Auto.
  Save.

  Lemma gt_tree_node : (x,y:elt)(l,r:tree)(h:Z)
    (gt_tree x l) -> (gt_tree x r) -> (E.lt x y) -> 
    (gt_tree x (Node l y r h)).
  Proof.
    Unfold gt_tree; Intuition.
    Inversion_clear H2; Intuition.
    Apply ME.lt_eq with y; Auto.
  Save.

  Hints Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

  Lemma lt_node_lt : (x,y:elt)(l,r:tree)(h:Z)
     (lt_tree x (Node l y r h)) -> (E.lt y x).
  Proof.
    Intros; Apply H; Auto.
  Save.

  Lemma gt_node_gt : (x,y:elt)(l,r:tree)(h:Z)
     (gt_tree x (Node l y r h)) -> (E.lt x y).
  Proof.
    Intros; Apply H; Auto.
  Save.

  Lemma lt_left : (x,y:elt)(l,r:tree)(h:Z)
     (lt_tree x (Node l y r h)) -> (lt_tree x l).
  Proof.
    Intros; Red; Intros; Apply H; Auto.
  Save.

  Lemma lt_right : (x,y:elt)(l,r:tree)(h:Z)
     (lt_tree x (Node l y r h)) -> (lt_tree x r).
  Proof.
    Intros; Red; Intros; Apply H; Auto.
  Save.

  Lemma gt_left : (x,y:elt)(l,r:tree)(h:Z)
     (gt_tree x (Node l y r h)) -> (gt_tree x l).
  Proof.
    Intros; Red; Intros; Apply H; Auto.
  Save.

  Lemma gt_right : (x,y:elt)(l,r:tree)(h:Z)
     (gt_tree x (Node l y r h)) -> (gt_tree x r).
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
  | BSNode : (x:elt)(l,r:tree)(h:Z)
      (bst l) -> (bst r) ->
      (lt_tree x l) -> (gt_tree x r) ->
      (bst (Node l x r h)).

  Hint bst := Constructors bst.

  (** Results about [bst] *)
 
  Lemma bst_left : (x:elt)(l,r:tree)(h:Z)
    (bst (Node l x r h)) -> (bst l).
  Proof.
    Intros x l r h H; Inversion H; Auto.
  Save.

  Lemma bst_right : (x:elt)(l,r:tree)(h:Z)
    (bst (Node l x r h)) -> (bst r).
  Proof.
    Intros x l r h H; Inversion H; Auto.
  Save.

  Implicits bst_left. Implicits bst_right.
  Hints Resolve bst_left bst_right.

  Lemma bst_height : (h,h':Z)(x:elt)(l,r:tree)
    (bst (Node l x r h)) -> (bst (Node l x r h')).
  Proof.
    Inversion 1; Auto.
  Save.
  Hints Resolve bst_height.

  (** Key fact about binary search trees: rotations preserve the 
      [bst] property *)

  Lemma rotate_left : (x,y:elt)(a,b,c:tree)(h1,h2,h3,h4:Z)
    (bst (Node a x (Node b y c h2) h1)) ->
    (bst (Node (Node a x b h4) y c h3)).
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

  Lemma rotate_right : (x,y:elt)(a,b,c:tree)(h1,h2,h3,h4:Z)
    (bst (Node (Node a x b h4) y c h3)) ->
    (bst (Node a x (Node b y c h2) h1)).
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

  (** * AVL trees *)

  (** [avl s] : [s] is a properly balanced AVL tree,
      i.e. for any node the heights of the two children
      differ by at most 2 *)

  Definition height : tree -> Z :=
    [s:tree]Cases s of
            | Leaf => 0
            | (Node _ _ _ h) => h end.

  Definition max [x,y:Z] : Z := 
    if (Z_lt_ge_dec x y) then [_]y else [_]x.

  Inductive avl : tree -> Prop :=
  | RBLeaf : 
      (avl Leaf)
  | RBNode : (x:elt)(l,r:tree)
      (avl l) -> (avl r) ->
      `-2 <= (height l) - (height r) <= 2` ->
      (avl (Node l x r ((max (height l) (height r)) + 1))).

  Hint avl := Constructors avl.

 (** Results about [avl] *)

  Lemma avl_left : 
    (x:elt)(l,r:tree)(h:Z)
    (avl (Node l x r h)) -> (avl l).
  Proof.
    Intros x l r h H; Inversion_clear H; Intuition.
  Save.

  Lemma avl_right : 
    (x:elt)(l,r:tree)(h:Z)
    (avl (Node l x r h)) -> (avl l).
  Proof.
    Intros x l r c H; Inversion_clear H; Intuition.
  Save.

  Implicits avl_left. Implicits avl_right.
  Hints Resolve avl_left avl_right.

  Tactic Definition MaxCase x y := 
    Unfold max; Case (Z_lt_ge_dec x y); Simpl.

  Lemma height_non_negative :
    (s:tree)(avl s) -> (height s) >= 0.
  Proof.
    Induction s; Simpl; Intros.
    Omega.
    Inversion_clear H1; Intuition.
    MaxCase '(height t) '(height t1); Intros; Omega.
  Save.
  
  Lemma height_equation :
    (l,r:tree)(x:elt)(h:Z)
    (avl (Node l x r h)) -> 
    h = (max (height l) (height r)) + 1.
  Proof.
    Inversion 1; Trivial.
  Save.

  (* variant without [max] to ease the use of Omega *)
  Lemma height_equation_2 : 
    (l,r:tree)(x:elt)(h:Z)
    (avl (Node l x r h)) -> 
    ((height l) >= (height r) /\ h = (height l) + 1) \/
    ((height r) >= (height l) /\ h = (height r) + 1).
  Proof.
    Inversion 1.
    Generalize H4; Clear H4.
    MaxCase '(height l) '(height r); Intuition.
  Save.

  Implicits height_non_negative. 
  Implicits height_equation.
  Implicits height_equation_2.

  (** * Sets as AVL trees *)

  (** A set is implement as a record [t], containing a tree, 
      a proof that it is a binary search tree and a proof that it is 
      a properly balanced AVL tree *)

  Record t_ : Set := t_intro {
    the_tree :> tree; 
    is_bst : (bst the_tree);
    is_avl : (avl the_tree) }.
  Definition t := t_.

   (** * Projections *)

  Lemma t_is_bst : (s:t)(bst s).
  Proof.
    Destruct s; Auto.
  Save.
  Hints Resolve t_is_bst.

  Lemma t_is_avl : (s:t)(avl s).
  Proof.
    Destruct s; Auto.
  Save.
  Hints Resolve t_is_avl.

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
    Unfold In; Destruct s; Simpl; Intuition Clear is_bst0 is_avl0.
    Induction the_tree0; Inversion_clear H0; Intuition.
    Apply IsRoot; EAuto.
  Save.

  Hints Resolve eq_In.

  (** * Empty set *)

  Definition t_empty : t.
  Proof.
    Exists Leaf; Auto.
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
    Intros x (s,Hs,Ha).
    Unfold In; Simpl; Clear Ha.
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

  Definition singleton_tree [x:elt] := (Node Leaf x Leaf 1).

  Lemma singleton_bst : (x:elt)(bst (singleton_tree x)).
  Proof.
    Unfold singleton_tree; Auto.
  Save.

  Lemma singleton_avl : (x:elt)(avl (singleton_tree x)).
  Proof.
    Unfold singleton_tree; Intro.
    Replace 1 with (max (height Leaf) (height Leaf)) + 1; Trivial.
    Constructor; Auto.
    Unfold height; Simpl; Omega.
  Save.

  Definition singleton : (x:elt){ s:t | (y:elt)(In y s) <-> (E.eq x y)}.
  Proof.
    Intro x; Exists (t_intro (singleton_tree x) (singleton_bst x)
             (singleton_avl x)).
    Unfold In singleton_tree; Simpl; Intuition.
    Inversion_clear H; Auto; Inversion H0.
  Defined.

  (** * Helper functions *)

  (** [create l x r] creates a node, assuming [l] and [r]
      to be balanced and [|height l - height r| <= 2]. *)

  Definition create :
    (l:tree)(x:elt)(r:tree)
    (bst l) -> (avl l) -> (bst r) -> (avl r) ->
    (lt_tree x l) -> (gt_tree x r) ->
    `-2 <= (height l) - (height r) <= 2` ->
    { s:tree | 
        (bst s) /\
        (avl s) /\
        (((height l) >= (height r) /\ (height s) = (height l) + 1) \/
         ((height r) >= (height l) /\ (height s) = (height r) + 1)) /\
        (y:elt)(In_tree y s) <-> 
            ((X.eq y x) \/ (In_tree y l) \/ (In_tree y r)) }.
  Proof.
    Intros.
    Exists (Node l x r ((max (height l) (height r)) + 1)).
    Intuition.
    MaxCase '(height l) '(height r); Intuition.
    Inversion_clear H5; Intuition.
  Defined.

  (* [h] is a proof of [avl (Node l x r h)] *)
  Tactic Definition AVL h :=
    (Generalize (height_non_negative h); Try Simpl);
    (Try Generalize (height_equation_2 h)); Intros.

  (** [bal l x r] acts as [create], but performs one step of
      rebalancing if necessary. *)

  Definition bal :
    (l:t)(x:elt)(r:t)
    (lt_tree x l) -> (gt_tree x r) ->
    `-3 <= (height l) - (height r) <= 3` ->
    { s:t | (y:elt)(In y s) <-> 
            ((X.eq y x) \/ (In y l) \/ (In y r)) }.
  Proof.
    Intros (l,bst_l,avl_l) x (r,bst_r,avl_r); Unfold In; Simpl.
    Intros Hl Hr Hh.
    LetTac hl := (height l).
    LetTac hr := (height r).
    Case (Z_gt_le_dec hl (hr + 2)); Intro.
    (* hl > hr + 2 *)
    NewDestruct l.
    (* l = Leaf => absurd *)
    Simpl in hl; Unfold hl.
    Absurd hl>hr+2; Trivial.
    Generalize (height_non_negative avl_r).
    Unfold hl hr; Omega.
    (* l = Node t0 t1 t2 z0 *)
    Case (Z_ge_lt_dec (height t0) (height t2)); Intro.
    (* height t0 >= height t2 *)
    Case (create t2 x r); Auto.
    Inversion_clear bst_l; Trivial. 
    Inversion_clear avl_l; Trivial.
    Generalize Hh z; Clear Hh z; Simpl in hl; Unfold hl hr.
    AVL avl_l; AVL avl_r; Intuition Try Omega.
    Inversion_clear avl_l; AVL H4; Omega.
    Intro t2xr; Intros.
    Case (create t0 t1 t2xr).
    Inversion_clear bst_l; Trivial. 
    Inversion_clear avl_l; Trivial.
    Intuition.
    Intuition.
    Inversion_clear bst_l; Trivial.     
    Inversion_clear bst_l; Trivial. 
    Intro; Intro; Intuition; Generalize (H10 y); Intuition.
    Apply ME.lt_eq with x; Auto. 
    Apply E.lt_trans with x; Auto.
    Apply Hl; Auto.
    Apply Hr; Auto.
    Apply ME.lt_eq with x; Auto. 
    Apply E.lt_trans with x; Auto.
    Apply Hl; Auto.
    Apply Hr; Auto.


  Defined.


End Make.








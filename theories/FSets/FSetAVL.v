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

  Definition height_of_node [l,r:tree; h:Z] :=  
    ((height l) >= (height r) /\ h = (height l) + 1) \/
    ((height r) >= (height l) /\ h = (height r) + 1).

  Inductive avl : tree -> Prop :=
  | RBLeaf : 
      (avl Leaf)
  | RBNode : (x:elt)(l,r:tree)(h:Z)
      (avl l) -> (avl r) ->
      `-2 <= (height l) - (height r) <= 2` ->
      (height_of_node l r h) -> 
      (avl (Node l x r h)).

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

  Lemma avl_node: (x:elt)(l,r:tree)
     (avl l) -> (avl r) ->
     `-2 <= (height l) - (height r) <= 2` ->
     (avl (Node l x r ((max (height l) (height r)) + 1))).
  Proof.
    Intros; Constructor; Unfold height_of_node; 
    MaxCase '(height l) '(height r); Intuition.
  Save.
  Hints Resolve avl_node.

  Lemma height_non_negative :
    (s:tree)(avl s) -> (height s) >= 0.
  Proof.
    Induction s; Simpl; Intros.
    Omega.
    Inversion_clear H1; Unfold height_of_node in H5; Intuition.
  Save.
  
  Lemma height_equation : 
    (l,r:tree)(x:elt)(h:Z)
    (avl (Node l x r h)) -> 
    `-2 <= (height l) - (height r) <= 2` /\
    (((height l) >= (height r) /\ h = (height l) + 1) \/
     ((height r) >= (height l) /\ h = (height r) + 1)).
  Proof.
    Inversion 1; Intuition.
  Save.

  Implicits height_non_negative. 
  Implicits height_equation.

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
    Constructor; Auto; Unfold height_of_node height; Simpl; Omega.
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
        (height_of_node l r (height s)) /\
        (y:elt)(In_tree y s) <-> 
            ((X.eq y x) \/ (In_tree y l) \/ (In_tree y r)) }.
  Proof.
    Unfold height_of_node; Intros.
    Exists (Node l x r ((max (height l) (height r)) + 1)).
    Intuition.
    MaxCase '(height l) '(height r); Intuition.
    Inversion_clear H5; Intuition.
  Defined.

  (* [h] is a proof of [avl (Node l x r h)] *)
  Tactic Definition AVL h :=
    (Generalize (height_non_negative h); Try Simpl);
    (Try Generalize (height_equation h)); Intros.

  (** [bal l x r] acts as [create], but performs one step of
      rebalancing if necessary. *)

(*
  Axiom bal :
    (l:tree)(x:elt)(r:tree)
    (bst l) -> (avl l) -> (bst r) -> (avl r) ->
    (lt_tree x l) -> (gt_tree x r) ->
    `-3 <= (height l) - (height r) <= 3` ->
    { s:tree | 
       (bst s) /\ (avl s) /\
       (* height may be decreased by 1 *)
       (((height_of_node l r (height s)) \/
         (height_of_node l r ((height s) + 1))) /\
       (* ...but is unchanged when no rebalancing *)
        (`-2 <= (height l) - (height r) <= 2` -> 
         (height_of_node l r (height s)))) /\
       (* elements are those of (l,x,r) *)
       (y:elt)(In_tree y s) <-> 
              ((X.eq y x) \/ (In_tree y l) \/ (In_tree y r)) }.
*)

  Definition bal :
    (l:tree)(x:elt)(r:tree)
    (bst l) -> (avl l) -> (bst r) -> (avl r) ->
    (lt_tree x l) -> (gt_tree x r) ->
    `-3 <= (height l) - (height r) <= 3` ->
    { s:tree | 
       (bst s) /\ (avl s) /\
       (* height may be decreased by 1 *)
       (((height_of_node l r (height s)) \/
         (height_of_node l r ((height s) + 1))) /\
       (* ...but is unchanged when no rebalancing *)
        (`-2 <= (height l) - (height r) <= 2` -> 
         (height_of_node l r (height s)))) /\
       (* elements are those of (l,x,r) *)
       (y:elt)(In_tree y s) <-> 
              ((X.eq y x) \/ (In_tree y l) \/ (In_tree y r)) }.
  Proof.
    Intros l x r bst_l avl_l bst_r avl_r; Simpl.
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
    Intro t2xr; Intuition.
    Case (create t0 t1 t2xr).
    Inversion_clear bst_l; Trivial. 
    Inversion_clear avl_l; Trivial.
    Intuition.
    Intuition.
    Inversion_clear bst_l; Trivial.     
    Inversion_clear bst_l; Trivial. 
    Clear H2; Intro; Intro; Intuition; Generalize (H5 y); Intuition.
    Apply ME.lt_eq with x; Auto. 
    Apply E.lt_trans with x; Auto.
    Apply Hl; Auto.
    Apply Hr; Auto.
    Clear H5.
    Generalize z H H0; Clear z H H0; Simpl in hl; Unfold hl hr.
    Unfold height_of_node in H2; AVL avl_l; AVL H3; Omega.
    Intros s (s_bst,(s_avl,(Hs1,Hs2))).
    Exists s; Simpl.
    Do 3 (Split; Trivial).
    Unfold height_of_node; Simpl.
    Clear H5 Hs2.
    Generalize z H H0; Clear z H H0; Simpl in hl; Unfold hl hr.
    Unfold height_of_node in H2 Hs1; AVL avl_l; AVL H3; AVL s_avl; Omega.
    Intuition; Generalize (Hs2 y); Generalize (H5 y); Clear Hs2 H5; Intuition.
    Inversion_clear H4; Intuition.
    (* height t0 < height t2 *)
    NewDestruct t2.
    (* t2 = Leaf => absurd *)
    Simpl in z1.
    Absurd (height t0)<0; Trivial.
    Inversion_clear avl_l; AVL H; Omega.
    (* t2 = Node t2 t3 t4 z2 *)
    Case (create t4 x r); Auto.
    Inversion_clear bst_l; Inversion_clear H0; Auto.
    Inversion_clear avl_l; Inversion_clear H0; Auto.
    Generalize z Hh; Clear z Hh; Simpl in hl; Unfold hl hr.
    Simpl in z1; AVL avl_l; Simpl in H.
    Inversion_clear avl_l; Unfold height_of_node in H4; Simpl in H3 H4.
    AVL H2; Omega.
    Intros r' (r'_bst, (r'_avl, (r'_h1, r'_h2))).
    Case (create t0 t1 t2).
    Inversion_clear bst_l; Trivial.
    Inversion_clear avl_l; Trivial.
    Inversion_clear bst_l; Inversion_clear H0; Trivial.
    Inversion_clear avl_l; Inversion_clear H0; Trivial.
    Inversion_clear bst_l; Trivial.
    Inversion_clear bst_l; Intro; Intro; Apply H2; EAuto.
    Generalize z Hh; Clear z Hh; Simpl in hl; Unfold hl hr.
    Simpl in z1; AVL avl_l; Simpl in H.
    Inversion_clear avl_l; Unfold height_of_node in H4; Simpl in H3 H4.
    AVL H2; Omega.
    Intros l' (l'_bst, (l'_avl, (l'_h1, l'_h2))).
    Case (create l' t3 r'); Auto.
    Inversion_clear bst_l; Inversion_clear H0.
    Intro; Intro; Generalize (l'_h2 y); Clear l'_h2; Intuition.
    Apply ME.eq_lt with t1; Auto.
    Apply E.lt_trans with t1; [ Apply H1 | Apply H2 ]; Auto.
    Inversion_clear bst_l; Inversion_clear H0.
    Intro; Intro; Generalize (r'_h2 y); Clear r'_h2; Intuition.
    Apply ME.lt_eq with x; Auto.
    Apply E.lt_trans with x; [Apply Hl|Apply Hr]; Auto.
    Generalize z Hh; Clear z Hh; Simpl in hl; Unfold hl hr.
    Simpl in z1; AVL avl_l; Simpl in H.
    Inversion_clear avl_l; Unfold height_of_node in H4; Simpl in H3 H4.
    AVL H2; Unfold height_of_node in r'_h1 l'_h1; Omega.
    Intros s (s_bst,(s_avl,(s_h1,s_h2))).
    Exists s; Simpl; Do 3 (Split; Trivial).
    Clear r'_h2 l'_h2 s_h2.
    Generalize z Hh; Clear z Hh; Simpl in hl; Unfold hl hr.
    AVL avl_l; Inversion_clear avl_l.
    AVL H2; Unfold height_of_node in H4; Simpl in H4.
    Unfold height_of_node; Simpl.
    Unfold height_of_node in s_h1 r'_h1 l'_h1; Simpl.
    Simpl in z1; AVL r'_avl; AVL l'_avl; Simpl in H.
    Clear bst_l bst_r avl_r Hl Hr hl hr r'_bst r'_avl
      l'_bst l'_avl s_bst s_avl H1 H2; Intuition Omega. (* 9 seconds *)
    Intro y; Generalize (r'_h2 y); 
      Generalize (l'_h2 y); Generalize (s_h2 y); 
      Clear r'_h2 l'_h2 s_h2; Intuition.
    Inversion_clear H10; Intuition.
    Inversion_clear H14; Intuition.
    (* hl <= hr + 2 *)
    Case (Z_gt_le_dec hr (hl + 2)); Intro.
    (* hr > hl + 2 *)
    NewDestruct r.
    (* r = Leaf => absurd *)
    Simpl in hr; Unfold hr.
    Absurd hr>hl+2; Trivial.
    AVL avl_l; Unfold hl hr; Omega.
    (* r = Node t0 t1 t2 z0 *)
    Case (Z_ge_lt_dec (height t2) (height t0)); Intro.
    (* height t2 >= height t0 *)
    Case (create l x t0); Auto.
    Inversion_clear bst_r; Trivial. 
    Inversion_clear avl_r; Trivial.
    Generalize Hh z z0; Clear Hh z z0; Simpl in hr; Unfold hl hr.
    AVL avl_l; AVL avl_r; Intuition Try Omega.
    Intro lxt0; Intuition.
    Case (create lxt0 t1 t2); Auto.
    Inversion_clear bst_r; Trivial. 
    Inversion_clear avl_r; Trivial.
    Clear H2; Intro; Intro; Intuition; Generalize (H5 y); Intuition.
    Apply ME.eq_lt with x; Auto. 
    Apply E.lt_trans with x; [Apply Hl|Apply Hr]; Auto.
    Inversion_clear bst_r; Auto. 
    Inversion_clear bst_r; Auto. 
    Clear H5.
    Generalize z z0 H H0; Clear z z0 H H0; Simpl in hr; Unfold hl hr.
    Unfold height_of_node in H2; AVL avl_r; AVL H3; Omega.
    Intros s (s_bst,(s_avl,(Hs1,Hs2))).
    Exists s; Simpl; Do 3 (Split; Trivial).
    Unfold height_of_node; Simpl.
    Clear H5 Hs2.
    Generalize z z0 H H0; Clear z z0 H H0; Simpl in hr; Unfold hl hr.
    Unfold height_of_node in H2 Hs1; AVL avl_r; AVL H3; AVL s_avl; Omega.
    Intuition; Generalize (Hs2 y); Generalize (H5 y); Clear Hs2 H5; Intuition.
    Inversion_clear H4; Intuition.
    (* height t2 < height t0 *)
    NewDestruct t0.
    (* t0 = Leaf => absurd *)
    Simpl in z2.
    Absurd (height t2)<0; Trivial.
    Inversion_clear avl_r; AVL H0; Omega.
    (* t0 = Node t0 t3 t4 z2 *)
    Case (create l x t0); Auto.
    Inversion_clear bst_r; Inversion_clear H; Auto.
    Inversion_clear avl_r; Inversion_clear H; Auto.
    Generalize z z0 Hh; Clear z z0 Hh; Simpl in hr; Unfold hl hr.
    Simpl in z2; AVL avl_r; Simpl in H.
    Inversion_clear avl_r; Unfold height_of_node in H4; Simpl in H3 H4.
    AVL H1; Omega.
    Intros l' (l'_bst, (l'_avl, (l'_h1, l'_h2))).
    Case (create t4 t1 t2).
    Inversion_clear bst_r; Inversion_clear H; Trivial.
    Inversion_clear avl_r; Inversion_clear H; Trivial.
    Inversion_clear bst_r; Trivial.
    Inversion_clear avl_r; Trivial.
    Inversion_clear bst_r; Intro; Intro; Apply H1; EAuto.
    Inversion_clear bst_r; Trivial.
    Generalize z z0 Hh; Clear z z0 Hh; Simpl in hr; Unfold hl hr.
    Simpl in z2; AVL avl_r; Simpl in H.
    Inversion_clear avl_r; Unfold height_of_node in H4; Simpl in H3 H4.
    AVL H1; Omega.
    Intros r' (r'_bst, (r'_avl, (r'_h1, r'_h2))).
    Case (create l' t3 r'); Auto.
    Inversion_clear bst_r; Inversion_clear H.
    Intro; Intro; Generalize (l'_h2 y); Clear l'_h2; Intuition.
    Apply ME.eq_lt with x; Auto.
    Apply E.lt_trans with x; [ Apply Hl | Apply Hr ]; Auto.
    Inversion_clear bst_r; Inversion_clear H.
    Intro; Intro; Generalize (r'_h2 y); Clear r'_h2; Intuition.
    Apply ME.lt_eq with t1; Auto.
    Apply E.lt_trans with t1; [Apply H1|Apply H2]; Auto.
    Generalize z z0 Hh; Clear z z0 Hh; Simpl in hr; Unfold hl hr.
    Simpl in z2; AVL avl_r; Simpl in H.
    Inversion_clear avl_r; Unfold height_of_node in H4; Simpl in H3 H4.
    AVL H1; Unfold height_of_node in r'_h1 l'_h1; Omega.
    Intros s (s_bst,(s_avl,(s_h1,s_h2))).
    Exists s; Simpl; Do 3 (Split; Trivial).
    Clear r'_h2 l'_h2 s_h2.
    Generalize z z0 Hh; Clear z z0 Hh; Simpl in hr; Unfold hl hr.
    AVL avl_r; Inversion_clear avl_r.
    AVL H1; Unfold height_of_node in H4; Simpl in H4.
    Unfold height_of_node; Simpl.
    Unfold height_of_node in s_h1 r'_h1 l'_h1; Simpl.
    Simpl in z2; AVL r'_avl; AVL l'_avl; Simpl in H.
    Clear bst_l bst_r avl_l Hl Hr hl hr r'_bst r'_avl
      l'_bst l'_avl s_bst s_avl H1 H2; Intuition Omega. (* 9 seconds *)
    Intro y; Generalize (r'_h2 y); 
      Generalize (l'_h2 y); Generalize (s_h2 y); 
      Clear r'_h2 l'_h2 s_h2; Intuition.
    Inversion_clear H10; Intuition.
    Inversion_clear H14; Intuition.
    (* hr <= hl + 2 *)
    LetTac s := (Node l x r ((max (height l) (height r)) + 1)).
    Assert (bst s). 
    Unfold s; Auto.
    Assert (avl s). 
    Unfold s; Constructor; Auto.
    Generalize z z0; Unfold hl hr; Intros; Omega.
    Unfold height_of_node; MaxCase '(height l) '(height r); Intros; Omega.
    Exists s; Unfold s height_of_node; Simpl; Do 3 (Split; Trivial).
    Generalize z z0; Unfold hl hr; MaxCase '(height l) '(height r); Intros; Omega.
    Intuition; Inversion_clear H3; Intuition.
  Defined.

  (** * Insertion *)

  Definition add_tree : 
    (x:elt)(s:tree)(bst s) -> (avl s) ->
    { s':tree | (bst s') /\ (avl s') /\ 
                0 <= (height s')-(height s) <= 1 /\
                ((y:elt)(In_tree y s') <-> ((E.eq y x)\/(In_tree y s))) }.
  Proof.
    Induction s; Simpl; Intros.
    (* s = Leaf *)
    Exists (Node Leaf x Leaf 1); Simpl; Intuition.
    Constructor; Unfold height_of_node; Simpl; 
      Intuition Try Omega.
    Inversion_clear H1; Intuition.
    (* s = Node t0 t1 t2 *)
    Case (X.compare x t1); Intro.
    (* x < t1 *)
    Clear H0; Case H; Clear H.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Intro l'; Simpl; Intuition.
    Case (bal l' t1 t2); Auto.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Intro; Intro; Generalize (H5 y); Clear H5; Intuition.
    Apply ME.eq_lt with x; Auto.
    Inversion_clear H1; Auto.
    Inversion_clear H1; Auto.
    Clear H5; AVL H2; AVL H3; Intuition.
    Intros s' (s'_bst,(s'_avl,(s'_h1, s'_h2))).
    Exists s'; Simpl; Do 3 (Split ; Trivial).
    Clear s'_h2 H; Unfold height_of_node in s'_h1.
    AVL H2; AVL H3; AVL s'_avl. Omega.
    Clear s'_h1; Intro.
    Generalize (s'_h2 y) (H5 y); Clear s'_h2 H5; Intuition.
    Inversion_clear H13; Intuition.
    (* x = t1 *)
    Clear H H0.
    Exists (Node t0 t1 t2 z); Simpl; Intuition.
    Apply IsRoot; Apply E.eq_trans with x; Auto.
    (* x > t1 *)
    Clear H; Case H0; Clear H0.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Intros r' (r'_bst,(r'_avl,H3)); Simpl; Intuition.
    Case (bal t0 t1 r'); Auto.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Intro; Intro; Generalize (H0 y); Clear H0; Intuition.
    Inversion_clear H1; Auto.
    Intro; Intro; Generalize (H0 y); Clear H0; Intuition.
    Apply ME.lt_eq with x; Auto.
    Inversion_clear H1; Auto.
    Clear H0; AVL H2; AVL r'_avl; Intuition.
    Intros s' (s'_bst,(s'_avl,(s'_h1, s'_h2))).
    Exists s'; Simpl; Do 3 (Split; Trivial).
    Clear s'_h2 H0; Unfold height_of_node in s'_h1.
    AVL H2; AVL r'_avl; AVL s'_avl; Omega.
    Clear s'_h1; Intro.
    Generalize (s'_h2 y) (H0 y); Clear s'_h2 H0; Intuition.
    Inversion_clear H11; Intuition.
  Defined.

  Definition add : (x:elt) (s:t) { s':t | (Add x s s') }.
  Proof.
    Intros x (s,s_bst,s_avl); Unfold Add In.
    Case (add_tree x s); Trivial.
    Intros s' (s'_bst,(s'_avl,Hs')).
    Exists (t_intro s' s'_bst s'_avl); Intuition.
  Defined.

  (** * Join

      Same as [bal] but does not assumme anything regarding heights
      of [l] and [r].
<<
    let rec join l v r =
      match (l, r) with
        (Empty, _) -> add v r
      | (_, Empty) -> add v l
      | (Node(ll, lv, lr, lh), Node(rl, rv, rr, rh)) ->
          if lh > rh + 2 then bal ll lv (join lr v r) else
          if rh > lh + 2 then bal (join l v rl) rv rr else
          create l v r
>>
  *)

  Definition join : 
    (l:tree)(x:elt)(r:tree)
    (bst l) -> (avl l) -> (bst r) -> (avl r) ->
    (lt_tree x l) -> (gt_tree x r) ->
    { s:tree | (bst s) /\ (avl s) /\
               ((height_of_node l r (height s)) \/
                (height_of_node l r ((height s)+1))) /\
               ((y:elt)(In_tree y s) <-> 
                       ((X.eq y x) \/ (In_tree y l) \/ (In_tree y r))) }.
  Proof.
    Induction l; Simpl.
    (* l = Leaf *)
    Intros; Case (add_tree x r); Trivial.
    Intros s' (s'_bst,(s'_avl,Hs')); Simpl; Exists s'; Intuition.
    Unfold height_of_node; Simpl. AVL H2; AVL s'_avl; Intuition Omega.
    Ground. Ground. Inversion_clear H5. Ground.
    Intros; Clear H.
    Induction r; Simpl.
    (* r = Leaf *)
    Clear H0.
    Intros; Case (add_tree x (Node t0 t1 t2 z)); Simpl; Trivial.
    Intros s' (s'_bst,(s'_avl,Hs')); Simpl; Exists s'; Intuition.
    Unfold height_of_node; Simpl. AVL s'_avl; Intuition Omega.
    Ground. Ground. Ground. Inversion_clear H.
    (* l = Node t0 t1 t2 z and r = Node r1 t3 r0 z0 *)
    Intros.
    Case (Z_gt_le_dec z (z0+2)); Intro.
    (* z > z0+2 *)
    Clear Hrecr1 Hrecr0.
    Case (H0 x (Node r1 t3 r0 z0)); Clear H0; Auto.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Intro s'; Unfold height_of_node; Simpl; Intuition.
    Case (bal t0 t1 s'); Auto.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Inversion_clear H1; Trivial.
    Clear H0; Intro; Intro; Generalize (H9 y); Clear H9; Intuition.
    Apply ME.lt_eq with x; Auto.
    Inversion_clear H1; Auto.
    Apply X.lt_trans with x; Auto.
    Clear H9; AVL H2; Intuition Omega.
    Intro s''; Unfold height_of_node; Simpl; Intuition.
    Exists s''; Do 3 (Split; Trivial).
    Clear H5 H6 H7 H8 H9 H13; AVL H2; Clear H2; Intuition Omega.
    Clear H0 H12 H10; Ground.
    Inversion_clear H0; Ground.
    (* z <= z0 + 2 *)
    Case (Z_gt_le_dec z0 (z+2)); Intro.
    (* z0 > z+2 *)
    Clear H0 Hrecr0.
    Case Hrecr1; Clear Hrecr1; Auto.
    Inversion_clear H3; Trivial.
    Inversion_clear H4; Trivial.
    Intro s'; Unfold height_of_node; Simpl; Intuition.
    Case (bal s' t3 r0); Auto.
    Inversion_clear H3; Trivial.
    Inversion_clear H4; Trivial.
    Inversion_clear H3; Trivial.
    Clear H0; Intro; Intro; Generalize (H9 y); Clear H9; Intuition.
    Apply ME.eq_lt with x; Auto.
    Apply X.lt_trans with x; Auto.
    Inversion_clear H3; Auto.
    Clear H9; AVL H4; Intuition Omega.
    Intro s''; Unfold height_of_node; Simpl; Intuition.
    Exists s''; Do 3 (Split; Trivial).
    Clear H5 H6 H7 H8 H9 H13; AVL H4; Clear H4; Intuition Omega.
    Clear H0 H12 H10; Ground.
    Inversion_clear H0; Ground.
    (* -2 <= z-z0 <= 2 *)
    Clear H0 Hrecr0 Hrecr1.
    Case (create (Node t0 t1 t2 z) x (Node r1 t3 r0 z0)); Simpl; Intuition.
    Exists x0; Intuition.
  Defined.

  (** * Extraction of minimum and maximum element *)

  Definition remove_min :
    (s:tree)(bst s) -> (avl s) -> ~s=Leaf ->
    { r : tree * elt |
        let (s',m) = r in
        (bst s') /\ (avl s') /\
        ((height s') = (height s) \/ (height s')=(height s)-1) /\
        ((y:elt)(In_tree y s') -> (E.lt m y)) /\
        ((y:elt)(In_tree y s) <-> (E.eq y m) \/ (In_tree y s')) }.
  Proof.
    Induction s; Simpl; Intros.
    Elim H1; Trivial.
    (* s = Node t0 t1 t2 *)
    NewDestruct t0.
    (* t0 = Leaf *)
    Clear H H0.
    Exists (t2, t1); Intuition.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    AVL H2; Simpl in H; Inversion_clear H2; AVL H5; Intuition; Omega.
    Inversion_clear H1; Apply H6; Auto.
    Inversion_clear H; Auto; Inversion_clear H0.
    (* t0 = Node t0 t3 t4 *)
    Clear H0; Case H; Clear H.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Discriminate.
    Intros (l',m); Intuition.
    Case (bal l' t1 t2); Auto.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Intro; Intros; Generalize (H7 y) (H5 y); Clear H7 H5 H0; Intuition.
    Elim (!ME.eq_not_gt y m); Auto.
    Inversion_clear H1; Auto.
    Inversion_clear H1; Trivial.
    Clear H5 H7.
    AVL H2; Omega. 
    Intro s'; Unfold height_of_node; Intuition.
    Exists (s',m).
    Do 3 (Split; Trivial).
    Clear H5 H7 H11; AVL H2; AVL H4; AVL H9; Omega.
    Clear H0 H10 H8; Intuition.
    Generalize (H5 y) (H7 y) (H11 y); Clear H5 H11; Intuition.
    Apply ME.lt_eq with t1; Auto.
    Generalize (H7 m); Inversion_clear H1; Intuition.
    Apply X.lt_trans with t1; Auto.
    Inversion_clear H1; Apply H18; Ground.
    Inversion_clear H1; Auto.
    Inversion_clear H0; Ground.
    Apply InLeft; Ground.
    Ground.
  Defined.

   Definition remove_max :
    (s:tree)(bst s) -> (avl s) -> ~s=Leaf ->
    { r : tree * elt |
        let (s',m) = r in
        (bst s') /\ (avl s') /\
        ((height s') = (height s) \/ (height s')=(height s)-1) /\
        ((y:elt)(In_tree y s') -> (E.lt y m)) /\
        ((y:elt)(In_tree y s) <-> (E.eq y m) \/ (In_tree y s')) }.
  Proof.
    Induction s; Simpl; Intros.
    Elim H1; Trivial.
    (* s = Node t0 t1 t2 *)
    NewDestruct t2.
    (* t2 = Leaf *)
    Clear H H0.
    Exists (t0, t1); Intuition.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    AVL H2; Simpl in H; Inversion_clear H2; AVL H4; Intuition; Omega.
    Inversion_clear H1; Apply H5; Auto.
    Inversion_clear H; Auto; Inversion_clear H0.
    (* t2 = Node t2 t3 t4 *)
    Clear H; Case H0; Clear H0.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Discriminate.
    Intros (r',m); Intuition.
    Case (bal t0 t1 r'); Auto.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Inversion_clear H1; Auto.
    Intro; Intros; Generalize (H7 y) (H5 y); Clear H7 H5 H0; Intuition.
    Elim (!ME.eq_not_lt y m); Auto.
    Inversion_clear H1; Auto.
    Clear H5 H7.
    AVL H2; Omega. 
    Intro s'; Unfold height_of_node; Intuition.
    Exists (s',m).
    Do 3 (Split; Trivial).
    Clear H5 H7 H11; AVL H2; AVL H4; AVL H9; Omega.
    Clear H0 H10 H8; Intuition.
    Generalize (H5 y) (H7 y) (H11 y); Clear H5 H11; Intuition.
    Apply ME.eq_lt with t1; Auto.
    Generalize (H7 m); Inversion_clear H1; Intuition.
    Apply X.lt_trans with t1; Auto.
    Inversion_clear H1; Apply H18; Ground.
    Inversion_clear H1; Ground.
    Inversion_clear H0; Ground.
    Apply InRight; Ground.
    Ground.
  Defined.

  (** * Merging two trees
<<
    let merge t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) -> let (m,t'2) = remove_min t2 in bal t1 m t'2
>> 
  *)

  Definition merge :
    (s1,s2:tree)(bst s1) -> (avl s1) -> (bst s2) -> (avl s2) ->
    ((y1,y2:elt)(In_tree y1 s1) -> (In_tree y2 s2) -> (X.lt y1 y2)) ->
    `-2 <= (height s1) - (height s2) <= 2` ->
    { s:tree | (bst s) /\ (avl s) /\
               ((height_of_node s1 s2 (height s)) \/
                (height_of_node s1 s2 ((height s)+1))) /\
               ((y:elt)(In_tree y s) <-> 
                       ((In_tree y s1) \/ (In_tree y s2))) }.
  Proof.
    Destruct s1; Simpl.
    (* s1 = Leaf *)
    Intros; Exists s2; Unfold height_of_node; Simpl; Intuition.
    AVL H2; Omega.
    Inversion_clear H7.
    (* s1 = Node t0 t1 t2 *)
    Destruct s2; Simpl.
    (* s2 = Leaf *)
    Intros; Exists (Node t0 t1 t2 z); Unfold height_of_node; Simpl; Intuition.
    AVL H0; Omega.
    Inversion_clear H7.
    (* s2 = Node t3 t4 t5 *)
    Intros.
    Case (remove_min (Node t3 t4 t5 z0)); Auto.
    Discriminate.
    Intros (s'2,m); Intuition.
    Case (bal (Node t0 t1 t2 z) m s'2); Auto.
    Ground.
    Clear H3 H11; AVL H0; AVL H2; AVL H8; Simpl in H7; Omega.
    Intro s'; Unfold height_of_node; Intuition. 
    Exists s'.
    Do 3 (Split; Trivial).
    Clear H3 H9 H11 H15; AVL H0; AVL H2; AVL H8; AVL H13.
    Simpl in H7 H14 H12; Simpl; Intuition Omega.
    Clear H7 H12 H14; Ground.
  Defined.

  (** Variant where we remove from the biggest subtree *)

  Definition merge_bis :
    (s1,s2:tree)(bst s1) -> (avl s1) -> (bst s2) -> (avl s2) ->
    ((y1,y2:elt)(In_tree y1 s1) -> (In_tree y2 s2) -> (X.lt y1 y2)) ->
    `-2 <= (height s1) - (height s2) <= 2` ->
    { s:tree | (bst s) /\ (avl s) /\
               ((height_of_node s1 s2 (height s)) \/
                (height_of_node s1 s2 ((height s)+1))) /\
               ((y:elt)(In_tree y s) <-> 
                       ((In_tree y s1) \/ (In_tree y s2))) }.
  Proof.
    Destruct s1; Simpl.
    (* s1 = Leaf *)
    Intros; Exists s2; Unfold height_of_node; Simpl; Intuition.
    AVL H2; Omega.
    Inversion_clear H7.
    (* s1 = Node t0 t1 t2 *)
    Destruct s2; Simpl.
    (* s2 = Leaf *)
    Intros; Exists (Node t0 t1 t2 z); Unfold height_of_node; Simpl; Intuition.
    AVL H0; Omega.
    Inversion_clear H7.
    (* s2 = Node t3 t4 t5 *)
    Intros; Case (Z_ge_lt_dec z z0); Intro.
    (* z >= z0 *)
    Case (remove_max (Node t0 t1 t2 z)); Auto.
    Discriminate.
    Intros (s'1,m); Intuition.
    Case (create s'1 m (Node t3 t4 t5 z0)); Auto.
    Ground.
    Clear H3 H11; AVL H0; AVL H2; AVL H8; Simpl in H7; Omega.
    Intro s'; Unfold height_of_node; Intuition. 
    Exists s'.
    Do 3 (Split; Trivial).
    Clear H3 H9 H11 H15; AVL H0; AVL H2; AVL H8; AVL H13.
    Simpl in H7 H14 H12; Simpl.
    Intuition Omega.
    Clear H7 H12; Ground.
    (* z < z0 *)
    Case (remove_min (Node t3 t4 t5 z0)); Auto.
    Discriminate.
    Intros (s'2,m); Intuition.
    Case (create (Node t0 t1 t2 z) m s'2); Auto.
    Ground.
    Clear H3 H11; AVL H0; AVL H2; AVL H8; Simpl in H7; Omega.
    Intro s'; Unfold height_of_node; Intuition. 
    Exists s'.
    Do 3 (Split; Trivial).
    Clear H3 H9 H11 H15; AVL H0; AVL H2; AVL H8; AVL H13.
    Simpl in H7 H14 H12; Simpl.
    Intuition Omega.
    Clear H7 H12; Ground.
  Defined.

  (** * Deletion *)

  Definition remove_tree :
    (x:elt)(s:tree)(bst s) -> (avl s) ->
    { s':tree | (bst s') /\ (avl s') /\
                ((height s') = (height s) \/ (height s') = (height s) - 1) /\
                ((y:elt)(In_tree y s') <-> (~(E.eq y x) /\ (In_tree y s))) }.
  Proof.
    Induction s; Simpl; Intuition.
    (* s = Leaf *)
    Exists Leaf; Simpl; Intuition; 
      (Inversion_clear H1 Orelse Inversion_clear H3).
    (* s = Node t0 t1 t2 *)
    Case (X.compare x t1); Intro.
    (* x < t1 *)
    Clear H0; Case H; Clear H.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Intros t'0; Intuition.
    Case (bal t'0 t1 t2); Auto.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Clear H0; Intro; Intro; Generalize (H5 y); Clear H5; Intuition.
    Inversion_clear H1; Auto.
    Inversion_clear H1; Auto.
    Clear H5; AVL H2; AVL H3; Omega.
    Intros s'; Unfold height_of_node; Intuition.
    Exists s'; Do 3 (Split; Trivial).
    Clear H5 H9; AVL H2; AVL H3; AVL H7; Omega.
    Clear H0 H8 H6; Intuition.
    Generalize (H9 y) (H5 y); Clear H5 H9; Intuition.
    Apply (!ME.eq_not_lt y t1); Auto.
    Apply ME.eq_lt with x; Auto.
    Apply (!ME.lt_not_gt t1 y); Auto.
    Inversion_clear H1; Apply H16; Auto.
    Apply ME.eq_lt with x; Auto.
    Generalize (H9 y) (H5 y); Clear H5 H9; Intuition.
    Inversion_clear H8; 
    Generalize (H9 y) (H5 y); Clear H5 H9; Intuition.
    (* x = t1 *)
    Clear H H0; Case (merge t0 t2).
    Inversion_clear H1; Auto.
    Inversion_clear H2; Auto.
    Inversion_clear H1; Auto.
    Inversion_clear H2; Auto.
    Intros; Apply X.lt_trans with t1; Inversion_clear H1; Auto.
    AVL H2; Omega.
    Intro s'; Unfold height_of_node; Intuition.
    Exists s'; Do 3 (Split; Trivial).
    Clear H5; AVL H2; AVL H3; Omega.
    Clear H0; Intro; Generalize (H5 y); Clear H5; Intuition.
    Apply (!E.lt_not_eq y t1); Auto.
    Inversion_clear H1; Apply H10; Auto.
    Apply X.eq_trans with x; Auto.
    Apply (!E.lt_not_eq t1 y); Auto.
    Inversion_clear H1; Apply H11; Auto.
    Apply X.eq_trans with x; Auto.
    Inversion_clear H8; Intuition.
    Absurd (X.eq y x); Auto.
    Apply X.eq_trans with t1; Auto.
    (* t1 < x *)
    Clear H; Case H0; Clear H0.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Intros t'2; Intuition.
    Case (bal t0 t1 t'2); Auto.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Inversion_clear H1; Auto.
    Inversion_clear H1; Auto.
    Clear H0; Intro; Intro; Generalize (H5 y); Clear H5; Intuition.
    Clear H5; AVL H2; AVL H3; Omega.
    Intros s'; Unfold height_of_node; Intuition.
    Exists s'; Do 3 (Split; Trivial).
    Clear H5 H9; AVL H2; AVL H3; AVL H7; Omega.
    Clear H0 H8 H6; Intuition.
    Generalize (H9 y) (H5 y); Clear H5 H9; Intuition.
    Apply (!ME.eq_not_lt t1 y); Auto.
    Apply ME.lt_eq with x; Auto.
    Apply (!ME.lt_not_gt y t1); Auto.
    Inversion_clear H1; Apply H15; Auto.
    Apply ME.lt_eq with x; Auto.
    Generalize (H9 y) (H5 y); Clear H5 H9; Intuition.
    Inversion_clear H8; 
    Generalize (H9 y) (H5 y); Clear H5 H9; Intuition.
  Defined.

  Definition remove : (x:elt)(s:t)
                      { s':t | (y:elt)(In y s') <-> (~(E.eq y x) /\ (In y s))}.
  Proof.
    Intros x (s,Hs,Hrb); Case (remove_tree x s); Trivial.
    Intros s'; Intuition; Clear H0.
    Exists (t_intro s' H H1); Intuition.
  Defined.

 (** * Minimum element *)

  Definition min_elt : 
     (s:t){ x:elt | (In x s) /\ (For_all [y]~(E.lt y x) s) } + { Empty s }.
  Proof.
    Intros (s,Hs,Ha).
    Unfold For_all Empty In; Simpl.
    Generalize Hs; Clear Hs Ha; Induction s; Simpl; Intros.
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
    Intros (s,Hs,Ha).
    Unfold For_all Empty In; Simpl.
    Generalize Hs; Clear Hs Ha; Induction s; Simpl; Intros.
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
    Intros (s,Hs,Ha); Unfold Empty In; Simpl; Case s; Intuition.
    Right; Intros; Inversion H.
    Left; Exists t1; Auto.
  Defined.


  (** * Concatenation

        Same as [merge] but does not assume anything about heights 
<<
    let concat t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) -> join t1 (min_elt t2) (remove_min_elt t2)
>> 
  *)

  Definition concat :
    (s1,s2:tree)(bst s1) -> (avl s1) -> (bst s2) -> (avl s2) ->
    ((y1,y2:elt)(In_tree y1 s1) -> (In_tree y2 s2) -> (X.lt y1 y2)) ->
    { s:tree | (bst s) /\ (avl s) /\
               ((y:elt)(In_tree y s) <-> 
                       ((In_tree y s1) \/ (In_tree y s2))) }.
  Proof.
    Destruct s1; Simpl.
    (* s1 = Leaf *)
    Intros; Exists s2; Simpl; Intuition.
    Inversion_clear H5.
    (* s1 = Node t0 t1 t2 *)
    Destruct s2; Simpl.
    (* s2 = Leaf *)
    Intros; Exists (Node t0 t1 t2 z); Simpl; Intuition.
    Inversion_clear H5.
    (* s2 = Node t3 t4 t5 *)
    Intros.
    Case (remove_min (Node t3 t4 t5 z0)); Auto.
    Discriminate.
    Intros (s'2,m); Intuition.
    Case (join (Node t0 t1 t2 z) m s'2); Auto.
    Ground.
    Intro s'; Intuition. 
    Exists s'.
    Do 2 (Split; Trivial).
    Clear H5 H10; Ground.
  Defined.

  (** * Splitting 

      [split x s] returns a triple [(l, present, r)] where
      - [l] is the set of elements of [s] that are [< x]
      - [r] is the set of elements of [s] that are [> x]
      - [present] is [false] if [s] contains no element equal to [x],
          or [true] if [s] contains an element equal to [x]. 
<<
    let rec split x = function
        Empty ->
          (Empty, false, Empty)
      | Node(l, v, r, _) ->
          let c = Ord.compare x v in
          if c = 0 then (l, true, r)
          else if c < 0 then
            let (ll, pres, rl) = split x l in (ll, pres, join rl v r)
          else
            let (lr, pres, rr) = split x r in (join l v lr, pres, rr)
>> 
  *)

  Definition split :
    (x:elt)(s:tree)(bst s) -> (avl s) ->
    { res:tree*bool*tree |
      let (l,res') = res in
      let (b,r) = res' in
      (bst l) /\ (avl l) /\ (bst r) /\ (avl r) /\
      ((y:elt)(In_tree y l) <-> ((In_tree y s) /\ (X.lt y x))) /\
      ((y:elt)(In_tree y r) <-> ((In_tree y s) /\ (X.lt x y))) /\
      (b=true <-> (In_tree x s)) }.
  Proof.
    Induction s; Simpl; Intuition.
    (* s = Leaf *)
    Exists (Leaf,(false,Leaf)); Simpl; Intuition; Inversion_clear H1.
    (* s = Node t0 t1 t2 z *)
    Case (X.compare x t1); Intro.
    (* x < t1 *)
    Clear H0; Case H; Clear H.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Intros (ll,(pres,rl)); Intuition.
    Case (join rl t1 t2); Auto.
    Inversion_clear H1; Trivial.
    Inversion_clear H2; Trivial.
    Inversion_clear H1; Ground.
    Inversion_clear H1; Ground.
    Intros s' (s'_bst,(s'_avl,(s'_h,s'_y))); Clear s'_h.
    Exists (ll,(pres,s')); Intuition.
    Ground.


  Defined.



End Make.








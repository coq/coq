
(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite map library.  *)

(* $Id$ *)

(** This module implements map using AVL trees.
    It follows the implementation from Ocaml's standard library. *)

Require Import Recdef FMapInterface FMapList ZArith Int.

Set Implicit Arguments.
Unset Strict Implicit.

Module Raw (Import I:Int)(X: OrderedType).
Module Import II:=MoreInt(I).
Open Local Scope Int_scope.
Module MX := OrderedTypeFacts X.
Module PX := KeyOrderedType X.
Module L := FMapList.Raw X.

Definition key := X.t.

(** Notations and helper lemma about pairs *)

Notation "s #1" := (fst s) (at level 9, format "s '#1'").
Notation "s #2" := (snd s) (at level 9, format "s '#2'").

Lemma distr_pair : forall (A B:Set)(s:A*B)(a:A)(b:B), s = (a,b) -> 
 s#1 = a /\ s#2 = b.
Proof.
 destruct s; simpl; injection 1; auto.
Qed.


(** * Trees *)

Section Elt.

Variable elt : Set.

(** * Trees

   The fifth field of [Node] is the height of the tree *)

Inductive tree  : Set :=
  | Leaf : tree
  | Node : tree -> key -> elt -> tree -> int -> tree.

Notation t := tree.

(** * Basic functions on trees: height and cardinal *)

Definition height (s : tree) : int :=
  match s with
  | Leaf => 0
  | Node _ _ _ _ h => h
  end.

Fixpoint cardinal (s : tree) : nat :=
  match s with
   | Leaf => 0%nat
   | Node l _ _ r _ => S (cardinal l + cardinal r)
  end.

(** * Occurrence in a tree *)

Inductive MapsTo (x : key)(e : elt) : tree -> Prop :=
  | MapsRoot : forall l r h y,
      X.eq x y -> MapsTo x e (Node l y e r h)
  | MapsLeft : forall l r h y e', 
      MapsTo x e l -> MapsTo x e (Node l y e' r h)
  | MapsRight : forall l r h y e', 
      MapsTo x e r -> MapsTo x e (Node l y e' r h).

Inductive In (x : key) : tree -> Prop :=
  | InRoot : forall l r h y e,
      X.eq x y -> In x (Node l y e r h)
  | InLeft : forall l r h y e', 
      In x l -> In x (Node l y e' r h)
  | InRight : forall l r h y e', 
      In x r -> In x (Node l y e' r h).

Definition In0 (k:key)(m:t) : Prop := exists e:elt, MapsTo k e m.

(** * Binary search trees *)

(** [lt_tree x s]: all elements in [s] are smaller than [x] 
   (resp. greater for [gt_tree]) *)

Definition lt_tree x s := forall y:key, In y s -> X.lt y x.
Definition gt_tree x s := forall y:key, In y s -> X.lt x y.

(** [bst t] : [t] is a binary search tree *)

Inductive bst : tree -> Prop :=
  | BSLeaf : bst Leaf
  | BSNode : forall x e l r h, bst l -> bst r -> 
     lt_tree x l -> gt_tree x r -> bst (Node l x e r h).

(** * AVL trees *)

(** [avl s] : [s] is a properly balanced AVL tree,
    i.e. for any node the heights of the two children
    differ by at most 2 *)

Inductive avl : tree -> Prop :=
  | RBLeaf : avl Leaf
  | RBNode : forall x e l r h, 
      avl l ->
      avl r ->
      -(2) <= height l - height r <= 2 ->
      h = max (height l) (height r) + 1 -> 
      avl (Node l x e r h).

(* We should end this section before the big proofs that follows, 
    otherwise the discharge takes a lot of time. *)
End Elt. 

Notation t := tree.



(** * Automation and dedicated tactics. *)

Hint Constructors tree MapsTo In bst avl.
Hint Unfold lt_tree gt_tree.

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

(** Same, but with a backup of the original hypothesis. *)

Ltac safe_inv f := match goal with 
  | H:f (Node _ _ _ _ _) |- _ => 
        generalize H; inversion_clear H; safe_inv f
  | H:f _ (Node _ _ _ _ _) |- _ => 
        generalize H; inversion_clear H; safe_inv f
  | _ => intros 
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

Ltac intuition_in := repeat progress (intuition; inv In; inv MapsTo).

(** Tactics about [avl] *)

Lemma height_non_negative : forall elt (s : t elt), avl s -> 
 height s >= 0.
Proof.
 induction s; simpl; intros; auto with zarith.
 inv avl; intuition; omega_max.
Qed.

Ltac avl_nn_hyp H := 
     let nz := fresh "nz" in assert (nz := height_non_negative H).

Ltac avl_nn h := 
  let t := type of h in 
  match type of t with 
   | Prop => avl_nn_hyp h
   | _ => match goal with H : avl h |- _ => avl_nn_hyp H end
  end.

(* Repeat the previous tactic. 
   Drawback: need to clear the [avl _] hyps ... Thank you Ltac *)

Ltac avl_nns :=
  match goal with 
     | H:avl _ |- _ => avl_nn_hyp H; clear H; avl_nns
     | _ => idtac
  end.




(** * Basic results about [MapsTo], [In], [lt_tree], [gt_tree], [avl], 
    [height] *)

(** Facts about [MapsTo] and [In]. *)

Lemma MapsTo_In : forall elt k e (m:t elt), MapsTo k e m -> In k m.
Proof.
 induction 1; auto.
Qed.
Hint Resolve MapsTo_In.

Lemma In_MapsTo : forall elt k (m:t elt), In k m -> exists e, MapsTo k e m.
Proof.
 induction 1; try destruct IHIn as (e,He); exists e; auto.
Qed.

Lemma In_alt : forall elt k (m:t elt), In0 k m <-> In k m.
Proof. 
 split.
 intros (e,H); eauto.
 unfold In0; apply In_MapsTo; auto.
Qed.

Lemma MapsTo_1 :
 forall elt (m:t elt) x y e, X.eq x y -> MapsTo x e m -> MapsTo y e m.
Proof.
 induction m; simpl; intuition_in; eauto.
Qed.
Hint Immediate MapsTo_1.

Lemma In_1 : 
 forall elt (m:t elt) x y, X.eq x y -> In x m -> In y m.
Proof.
 intros elt m x y; induction m; simpl; intuition_in; eauto.
Qed.

(** Results about [lt_tree] and [gt_tree] *)

Lemma lt_leaf : forall elt x, lt_tree x (Leaf elt).
Proof.
 unfold lt_tree in |- *; intros; intuition_in.
Qed.

Lemma gt_leaf : forall elt x, gt_tree x (Leaf elt).
Proof.
  unfold gt_tree in |- *; intros; intuition_in.
Qed.

Lemma lt_tree_node : forall elt x y (l:t elt) r e h, 
 lt_tree x l -> lt_tree x r -> X.lt y x -> lt_tree x (Node l y e r h).
Proof.
 unfold lt_tree in *; intuition_in; order.
Qed.

Lemma gt_tree_node : forall elt x y (l:t elt) r e h,
 gt_tree x l -> gt_tree x r -> X.lt x y -> gt_tree x (Node l y e r h).
Proof.
 unfold gt_tree in *; intuition_in; order.
Qed.

Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

Lemma lt_left : forall elt x y (l: t elt) r e h, 
 lt_tree x (Node l y e r h) -> lt_tree x l.
Proof.
 intuition_in.
Qed.

Lemma lt_right : forall elt x y (l:t elt) r e h, 
 lt_tree x (Node l y e r h) -> lt_tree x r.
Proof.
 intuition_in.
Qed.

Lemma gt_left : forall elt x y (l:t elt) r e h, 
 gt_tree x (Node l y e r h) -> gt_tree x l.
Proof.
 intuition_in.
Qed.

Lemma gt_right : forall elt x y (l:t elt) r e h, 
 gt_tree x (Node l y e r h) -> gt_tree x r.
Proof.
 intuition_in.
Qed.

Hint Resolve lt_left lt_right gt_left gt_right.

Lemma lt_tree_not_in :
 forall elt x (t : t elt), lt_tree x t -> ~ In x t.
Proof.
 intros; intro; generalize (H _ H0); order.
Qed.

Lemma lt_tree_trans :
 forall elt x y, X.lt x y -> forall (t:t elt), lt_tree x t -> lt_tree y t.
Proof.
 eauto.
Qed.

Lemma gt_tree_not_in :
 forall elt x (t : t elt), gt_tree x t -> ~ In x t.
Proof.
 intros; intro; generalize (H _ H0); order.
Qed.

Lemma gt_tree_trans :
 forall elt x y, X.lt y x -> forall (t:t elt), gt_tree x t -> gt_tree y t.
Proof.
 eauto.
Qed.

Hint Resolve lt_tree_not_in lt_tree_trans gt_tree_not_in gt_tree_trans.

(** Results about [avl] *)

Lemma avl_node : forall elt x e (l:t elt) r, avl l -> avl r ->
 -(2) <= height l - height r <= 2 ->
 avl (Node l x e r (max (height l) (height r) + 1)).
Proof.
  intros; auto.
Qed.
Hint Resolve avl_node.

(** Results about [height] *)

Lemma height_0 : forall elt (l:t elt), avl l -> height l = 0 -> 
 l = @Leaf _.
Proof.
 destruct 1; intuition; simpl in *.
 avl_nns; simpl in *; elimtype False; omega_max.
Qed.



(** trick for emulating [assert false] in Coq *)

Definition assert_false := Leaf.
Lemma assert_false_cardinal : forall elt, 
 cardinal (assert_false elt) = 0%nat.
Proof. simpl; auto. Qed.
Opaque assert_false.



(** * Helper functions *)

(** [create l x r] creates a node, assuming [l] and [r]
    to be balanced and [|height l - height r| <= 2]. *)

Definition create elt (l:t elt) x e r := 
   Node l x e r (max (height l) (height r) + 1).

Lemma create_bst : 
 forall elt (l:t elt) x e r, bst l -> bst r -> lt_tree x l -> gt_tree x r -> 
 bst (create l x e r).
Proof.
 unfold create; auto.
Qed.
Hint Resolve create_bst.

Lemma create_avl : 
 forall elt (l:t elt) x e r, avl l -> avl r ->  -(2) <= height l - height r <= 2 -> 
 avl (create l x e r).
Proof.
 unfold create; auto.
Qed.

Lemma create_height : 
 forall elt (l:t elt) x e r, avl l -> avl r ->  -(2) <= height l - height r <= 2 -> 
 height (create l x e r) = max (height l) (height r) + 1.
Proof.
 unfold create; intros; auto.
Qed.

Lemma create_in : 
 forall elt (l:t elt) x e r y,  In y (create l x e r) <-> X.eq y x \/ In y l \/ In y r.
Proof.
 unfold create; split; [ inversion_clear 1 | ]; intuition.
Qed.


(** [bal l x e r] acts as [create], but performs one step of
    rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

Function bal (elt:Set)(l: t elt)(x:key)(e:elt)(r:t elt) : t elt := 
  let hl := height l in 
  let hr := height r in
  if gt_le_dec hl (hr+2) then 
    match l with 
     | Leaf => assert_false _
     | Node ll lx le lr _ => 
       if ge_lt_dec (height ll) (height lr) then 
         create ll lx le (create lr x e r)
       else 
         match lr with 
          | Leaf => assert_false _
          | Node lrl lrx lre lrr _ => 
              create (create ll lx le lrl) lrx lre (create lrr x e r)
         end
    end
  else 
    if gt_le_dec hr (hl+2) then 
      match r with
       | Leaf => assert_false _
       | Node rl rx re rr _ =>
         if ge_lt_dec (height rr) (height rl) then 
            create (create l x e rl) rx re rr
         else 
           match rl with
            | Leaf => assert_false _
            | Node rll rlx rle rlr _ => 
                create (create l x e rll) rlx rle (create rlr rx re rr) 
           end
      end
    else 
      create l x e r. 

Lemma bal_bst : forall elt (l:t elt) x e r, bst l -> bst r -> 
 lt_tree x l -> gt_tree x r -> bst (bal l x e r).
Proof.
 intros elt l x e r; functional induction (bal l x e r); intros; clearf;
 inv bst; repeat apply create_bst; auto; unfold create; try constructor;
 (apply lt_tree_node || apply gt_tree_node); auto; 
 (eapply lt_tree_trans || eapply gt_tree_trans); eauto.
Qed.

Lemma bal_avl : forall elt (l:t elt) x e r, avl l -> avl r -> 
 -(3) <= height l - height r <= 3 -> avl (bal l x e r).
Proof.
 intros elt l x e r; functional induction (bal l x e r); intros; clearf;
 try constructor; inv avl; repeat apply create_avl; simpl in *; auto; 
 omega_max.
Qed.

Lemma bal_height_1 : forall elt (l:t elt) x e r, avl l -> avl r -> 
 -(3) <= height l - height r <= 3 ->
 0 <= height (bal l x e r) - max (height l) (height r) <= 1.
Proof.
 intros elt l x e r; functional induction (bal l x e r); intros; clearf;
 inv avl; avl_nns; simpl in *; omega_max.
Qed.

Lemma bal_height_2 : 
 forall elt (l:t elt) x e r, avl l -> avl r -> -(2) <= height l - height r <= 2 -> 
 height (bal l x e r) == max (height l) (height r) +1.
Proof.
 intros elt l x e r; functional induction (bal l x e r); intros; clearf;
 inv avl; avl_nns; simpl in *; omega_max.
Qed.

Lemma bal_in : forall elt (l:t elt) x e r y, avl l -> avl r -> 
 (In y (bal l x e r) <-> X.eq y x \/ In y l \/ In y r).
Proof.
 intros elt l x e r; functional induction (bal l x e r); intros; clearf;
 inv avl; solve [repeat rewrite create_in; intuition_in
                |inv avl; avl_nns; simpl in *; omega_max ].
Qed.

Lemma bal_mapsto : forall elt (l:t elt) x e r y e', avl l -> avl r -> 
 (MapsTo y e' (bal l x e r) <-> MapsTo y e' (create l x e r)).
Proof.
 intros elt l x e r; functional induction (bal l x e r); intros; clearf;
 inv avl; solve [unfold create; intuition_in
                |inv avl; avl_nns; simpl in *; omega_max ].
Qed.

Ltac omega_bal := match goal with 
  | H:avl ?l, H':avl ?r |- context [ bal ?l ?x ?e ?r ] => 
     generalize (bal_height_1 x e H H') (bal_height_2 x e H H'); 
     omega_max
  end.



(** * Insertion *)

Function add (elt:Set)(x:key)(e:elt)(s:t elt) { struct s } : t elt := 
  match s with 
   | Leaf => Node (Leaf _) x e (Leaf _) 1
   | Node l y e' r h => 
      match X.compare x y with
         | LT _ => bal (add x e l) y e' r
         | EQ _ => Node l y e r h
         | GT _ => bal l y e' (add x e r)
      end
  end.

Lemma add_avl_1 :  forall elt (m:t elt) x e, avl m -> 
 avl (add x e m) /\ 0 <= height (add x e m) - height m <= 1.
Proof. 
 intros elt m x e; functional induction (add x e m); intros; inv avl; simpl in *.
 intuition; try constructor; simpl; auto; try omega_max.
 (* LT *)
 destruct IHt; auto.
 split.
 apply bal_avl; auto; omega_max.
 omega_bal.
 (* EQ *)
 intuition; omega_max.
 (* GT *)
 destruct IHt; auto.
 split.
 apply bal_avl; auto; omega_max.
 omega_bal.
Qed.

Lemma add_avl : forall elt (m:t elt) x e, avl m -> avl (add x e m).
Proof.
 intros; generalize (add_avl_1 x e H); intuition.
Qed.
Hint Resolve add_avl.

Lemma add_in : forall elt (m:t elt) x y e, avl m -> 
 (In y (add x e m) <-> X.eq y x \/ In y m).
Proof.
 intros elt m x y e; functional induction (add x e m); auto; intros.
 intuition_in.
 (* LT *)
 inv avl.
 rewrite bal_in; auto.
 rewrite (IHt H0); intuition_in.
 (* EQ *)  
 inv avl.
 intuition_in.
 apply InRoot; apply X.eq_sym; eauto.
 (* GT *)
 inv avl.
 rewrite bal_in; auto.
 rewrite (IHt H1); intuition_in.
Qed.

Lemma add_bst : forall elt (m:t elt) x e, bst m -> avl m -> bst (add x e m).
Proof. 
 intros elt m x e; functional induction (add x e m); 
   intros; inv bst; inv avl; auto; apply bal_bst; auto.
 (* lt_tree -> lt_tree (add ...) *)
 red; red in H4.
 intros.
 rewrite (add_in x y0 e H) in H0.
 intuition.
 eauto.
 (* gt_tree -> gt_tree (add ...) *)
 red; red in H4.
 intros.
 rewrite (add_in x y0 e H5) in H0.
 intuition.
 apply MX.lt_eq with x; auto.
Qed.

Lemma add_1 : forall elt (m:t elt) x y e, avl m -> X.eq x y -> MapsTo y e (add x e m).
Proof. 
 intros elt m x y e; functional induction (add x e m); 
   intros; inv bst; inv avl; try rewrite bal_mapsto; unfold create; eauto.
Qed.

Lemma add_2 : forall elt (m:t elt) x y e e', avl m -> ~X.eq x y -> 
 MapsTo y e m -> MapsTo y e (add x e' m).
Proof.
 intros elt m x y e e'; induction m; simpl; auto.
 destruct (X.compare x k);
 intros; inv bst; inv avl; try rewrite bal_mapsto; unfold create; auto; 
   inv MapsTo; auto; order.
Qed.

Lemma add_3 : forall elt (m:t elt) x y e e', avl m -> ~X.eq x y -> 
 MapsTo y e (add x e' m) -> MapsTo y e m.
Proof.
 intros elt m x y e e'; induction m; simpl; auto. 
 intros; inv avl; inv MapsTo; auto; order.
 destruct (X.compare x k); intro; inv avl; 
  try rewrite bal_mapsto; auto; unfold create; intros; inv MapsTo; auto; 
  order.
Qed.



(** * Extraction of minimum binding

  morally, [remove_min] is to be applied to a non-empty tree 
  [t = Node l x e r h]. Since we can't deal here with [assert false] 
  for [t=Leaf], we pre-unpack [t] (and forget about [h]). 
*)
 
Function remove_min (elt:Set)(l:t elt)(x:key)(e:elt)(r:t elt) { struct l } : t elt*(key*elt) := 
  match l with 
    | Leaf => (r,(x,e))
    | Node ll lx le lr lh => let (l',m) := (remove_min ll lx le lr : t elt*(key*elt)) in (bal l' x e r, m)
  end.

Lemma remove_min_avl_1 : forall elt (l:t elt) x e r h, avl (Node l x e r h) -> 
 avl (remove_min l x e r)#1 /\ 
 0 <= height (Node l x e r h) - height (remove_min l x e r)#1 <= 1.
Proof.
 intros elt l x e r; functional induction (remove_min l x e r); simpl in *; intros.
 inv avl; simpl in *; split; auto.
 avl_nns; omega_max.
 (* l = Node *)
 inversion_clear H.
 destruct (IHp lh); auto.
 split; simpl in *.
 rewrite e1 in *. simpl in *.
 apply bal_avl; subst;auto; omega_max.
 rewrite_all e1;simpl in *;omega_bal.
Qed.

Lemma remove_min_avl : forall elt (l:t elt) x e r h, avl (Node l x e r h) -> 
    avl (remove_min l x e r)#1. 
Proof.
 intros; generalize (remove_min_avl_1 H); intuition.
Qed.

Lemma remove_min_in : forall elt (l:t elt) x e r h y, avl (Node l x e r h) -> 
 (In y (Node l x e r h) <-> 
  X.eq y (remove_min l x e r)#2#1 \/ In y (remove_min l x e r)#1).
Proof.
 intros elt l x e r; functional induction (remove_min l x e r); simpl in *; intros.
 intuition_in.
 (* l = Node *)
 inversion_clear H.
 generalize (remove_min_avl H0).
 
 rewrite e1 in *; simpl; intros.
 rewrite bal_in; auto.
 generalize (IHp lh y H0).
 intuition.
 inversion_clear H7; intuition.
Qed.

Lemma remove_min_mapsto : forall elt (l:t elt) x e r h y e', avl (Node l x e r h) -> 
 (MapsTo y e' (Node l x e r h) <-> 
   ((X.eq y (remove_min l x e r)#2#1) /\ e' = (remove_min l x e r)#2#2)
    \/ MapsTo y e' (remove_min l x e r)#1).
Proof.
 intros elt l x e r; functional induction (remove_min l x e r); simpl in *; intros.
 intuition_in; subst; auto.
 (* l = Node *)
 inversion_clear H.
 generalize (remove_min_avl H0).
 rewrite e1 in *; simpl; intros.
 rewrite bal_mapsto; auto; unfold create.
 simpl in *;destruct (IHp lh y e').
 auto.
 intuition.
 inversion_clear H2; intuition.
 inversion_clear H9; intuition.
Qed.

Lemma remove_min_bst : forall elt (l:t elt) x e r h, 
 bst (Node l x e r h) -> avl (Node l x e r h) -> bst (remove_min l x e r)#1.
Proof.
 intros elt l x e r; functional induction (remove_min l x e r); simpl in *; intros.
 inv bst; auto.
 inversion_clear H; inversion_clear H0.
 apply bal_bst; auto.
 rewrite e1 in *; simpl in *; apply (IHp lh); auto.
 intro; intros.
 generalize (remove_min_in y H).
 rewrite e1; simpl in *.
 destruct 1.
 apply H3; intuition.
Qed.

Lemma remove_min_gt_tree : forall elt (l:t elt) x e r h, 
 bst (Node l x e r h) -> avl (Node l x e r h) -> 
 gt_tree (remove_min l x e r)#2#1 (remove_min l x e r)#1.
Proof.
 intros elt l x e r; functional induction (remove_min l x e r); simpl in *; intros.
 inv bst; auto.
 inversion_clear H; inversion_clear H0.
 intro; intro.
 rewrite e1 in *;simpl in *.
 generalize (IHp lh H1 H); clear H7 H6 IHp.
 generalize (remove_min_avl H).
 generalize (remove_min_in m#1 H).
 rewrite e1; simpl; intros.
 rewrite (bal_in x e y H7 H5) in H0.
 assert (In m#1 (Node ll lx le lr lh)) by (rewrite H6; auto); clear H6.
 assert (X.lt m#1 x) by order.
 decompose [or] H0; order.
Qed.



(** * Merging two trees

  [merge t1 t2] builds the union of [t1] and [t2] assuming all elements
  of [t1] to be smaller than all elements of [t2], and
  [|height t1 - height t2| <= 2].
*)

Function merge (elt:Set) (s1 s2 : t elt) : tree elt :=  match s1,s2 with 
  | Leaf, _ => s2 
  | _, Leaf => s1
  | _, Node l2 x2 e2 r2 h2 => 
    match remove_min l2 x2 e2 r2 with 
      (s2',(x,e)) => bal s1 x e s2'
    end
end.

Lemma merge_avl_1 : forall elt (s1 s2:t elt), avl s1 -> avl s2 -> 
 -(2) <= height s1 - height s2 <= 2 -> 
 avl (merge s1 s2) /\ 
 0<= height (merge s1 s2) - max (height s1) (height s2) <=1.
Proof.
 intros elt s1 s2; functional induction (merge s1 s2); simpl in *; intros.
 split; auto; avl_nns; omega_max.
 destruct s1;try contradiction;clear y.
 split; auto; avl_nns; simpl in *; omega_max.
 destruct s1;try contradiction;clear y.
 generalize (remove_min_avl_1 H0).
 rewrite e3; simpl;destruct 1.
 split.
 apply bal_avl; auto.
 omega_max.
 omega_bal.
Qed.

Lemma merge_avl : forall elt (s1 s2:t elt), avl s1 -> avl s2 -> 
  -(2) <= height s1 - height s2 <= 2 -> avl (merge s1 s2).
Proof. 
 intros; generalize (merge_avl_1 H H0 H1); intuition.
Qed.

Lemma merge_in : forall elt (s1 s2:t elt) y, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 (In y (merge s1 s2) <-> In y s1 \/ In y s2).
Proof. 
 intros elt s1 s2; functional induction (merge s1 s2);intros.
 intuition_in.
 intuition_in.
 destruct s1;try contradiction;clear y.
(*  rewrite H_eq_2; rewrite H_eq_2 in H_eq_1; clear H_eq_2. *)
 replace s2' with ((remove_min l2 x2 e2 r2)#1); [|rewrite e3; auto].
 rewrite bal_in; auto.
 generalize (remove_min_avl H2); rewrite e3; simpl; auto.
 generalize (remove_min_in y0 H2); rewrite e3; simpl; intro.
 rewrite H3; intuition.
Qed.

Lemma merge_mapsto : forall elt (s1 s2:t elt) y e, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
  (MapsTo y e (merge s1 s2) <-> MapsTo y e s1 \/ MapsTo y e s2).
Proof.
 intros elt s1 s2; functional induction (@merge elt s1 s2); intros.
 intuition_in.
 intuition_in.
 destruct s1;try contradiction;clear y.
 replace s2' with ((remove_min l2 x2 e2 r2)#1); [|rewrite e3; auto].
 rewrite bal_mapsto; auto; unfold create.
 generalize (remove_min_avl H2); rewrite e3; simpl; auto.
 generalize (remove_min_mapsto y0 e H2); rewrite e3; simpl; intro.
 rewrite H3; intuition (try subst; auto).
 inversion_clear H3; intuition.
Qed.

Lemma merge_bst : forall elt (s1 s2:t elt), bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 (forall y1 y2 : key, In y1 s1 -> In y2 s2 -> X.lt y1 y2) -> 
 bst (merge s1 s2). 
Proof.
 intros elt s1 s2; functional induction (@merge elt s1 s2); intros; auto.

 apply bal_bst; auto.
 destruct s1;try contradiction.
 generalize (remove_min_bst H1); rewrite e3; simpl in *; auto.
 destruct s1;try contradiction.
 intro; intro.
 apply H3; auto.
 generalize (remove_min_in x H2); rewrite e3; simpl; intuition.
 destruct s1;try contradiction.
 generalize (remove_min_gt_tree H1); rewrite e3; simpl; auto.
Qed. 



(** * Deletion *)

Function remove (elt:Set)(x:key)(s:t elt) { struct s } : t elt := match s with 
  | Leaf => Leaf _
  | Node l y e r h =>
      match X.compare x y with
         | LT _ => bal (remove x l) y e r
         | EQ _ => merge l r
         | GT _ => bal l y e (remove x r)
      end
   end.

Lemma remove_avl_1 : forall elt (s:t elt) x, avl s -> 
 avl (remove x s) /\ 0 <= height s - height (remove x s) <= 1.
Proof.
 intros elt s x; functional induction (@remove elt x s); intros.
 split; auto; omega_max.
 (* LT *)
 inv avl.
 destruct (IHt H0).
 split. 
 apply bal_avl; auto.
 omega_max.
 omega_bal.
 (* EQ *)
 inv avl. 
 generalize (merge_avl_1 H0 H1 H2).
 intuition omega_max.
 (* GT *)
 inv avl.
 destruct (IHt H1).
 split. 
 apply bal_avl; auto.
 omega_max.
 omega_bal.
Qed.

Lemma remove_avl : forall elt (s:t elt) x, avl s -> avl (remove x s).
Proof. 
 intros; generalize (remove_avl_1 x H); intuition.
Qed.
Hint Resolve remove_avl.

Lemma remove_in : forall elt (s:t elt) x y, bst s -> avl s -> 
 (In y (remove x s) <-> ~ X.eq y x /\ In y s).
Proof.
 intros elt s x; functional induction (@remove elt x s); simpl; intros.
 intuition_in.
 (* LT *)
 inv avl; inv bst; clear e1.
 rewrite bal_in; auto.
 generalize (IHt y0 H0); intuition; [ order | order | intuition_in ].
 (* EQ *)
 inv avl; inv bst; clear e1.
 rewrite merge_in; intuition; [ order | order | intuition_in ].
 elim H9; eauto.
 (* GT *)
 inv avl; inv bst; clear e1.
 rewrite bal_in; auto.
 generalize (IHt y0 H5); intuition; [ order | order | intuition_in ].
Qed.

Lemma remove_bst : forall elt (s:t elt) x, bst s -> avl s -> bst (remove x s).
Proof. 
 intros elt s x; functional induction (@remove elt x s); simpl; intros.
 auto.
 (* LT *)
 inv avl; inv bst.
 apply bal_bst; auto.
 intro; intro.
 rewrite (remove_in x y0 H0) in H; auto.
 destruct H; eauto.
 (* EQ *)
 inv avl; inv bst.
 apply merge_bst; eauto.
 (* GT *) 
 inv avl; inv bst.
 apply bal_bst; auto.
 intro; intro.
 rewrite (remove_in x y0 H5) in H; auto.
 destruct H; eauto.
Qed.

Lemma remove_1 : forall elt (m:t elt) x y, bst m -> avl m -> X.eq x y -> ~ In y (remove x m).
Proof. 
 intros; rewrite remove_in; intuition.
Qed. 

Lemma remove_2 : forall elt (m:t elt) x y e, bst m -> avl m -> ~X.eq x y -> 
 MapsTo y e m -> MapsTo y e (remove x m).
Proof.
 intros elt m x y e; induction m; simpl; auto.
 destruct (X.compare x k); 
   intros; inv bst; inv avl; try rewrite bal_mapsto; unfold create; auto; 
   try solve [inv MapsTo; auto].
 rewrite merge_mapsto; auto.
 inv MapsTo; auto; order.
Qed.

Lemma remove_3 : forall elt (m:t elt) x y e, bst m -> avl m ->
 MapsTo y e (remove x m) -> MapsTo y e m.
Proof.
 intros elt m x y e; induction m; simpl; auto.
 destruct (X.compare x k); intros Bs Av; inv avl; inv bst; 
  try rewrite bal_mapsto; auto; unfold create.
  intros; inv MapsTo; auto. 
  rewrite merge_mapsto; intuition.
  intros; inv MapsTo; auto.
Qed.

Section Elt2.

Variable elt:Set.

Notation eqk := (PX.eqk (elt:= elt)).
Notation eqke := (PX.eqke (elt:= elt)).
Notation ltk := (PX.ltk (elt:= elt)).

(** * Empty map *)

Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

Definition empty := (Leaf elt).

Lemma empty_bst : bst empty.
Proof.
 unfold empty; auto.
Qed.

Lemma empty_avl : avl empty.
Proof. 
 unfold empty; auto.
Qed.

Lemma empty_1 : Empty empty.
Proof.
 unfold empty, Empty; intuition_in.
Qed.

(** * Emptyness test *)

Definition is_empty (s:t elt) := match s with Leaf => true | _ => false end.

Lemma is_empty_1 : forall s, Empty s -> is_empty s = true. 
Proof.
 destruct s as [|r x e l h]; simpl; auto.
 intro H; elim (H x e); auto.
Qed.

Lemma is_empty_2 : forall s, is_empty s = true -> Empty s.
Proof. 
 destruct s; simpl; intros; try discriminate; red; intuition_in.
Qed.



(** * Appartness *)

(** The [mem] function is deciding appartness. It exploits the [bst] property
    to achieve logarithmic complexity. *)

Function mem (x:key)(m:t elt) { struct m } : bool := 
   match m with 
     |  Leaf => false 
     |  Node l y e r _ => match X.compare x y with 
             | LT _ => mem x l 
             | EQ _ => true
             | GT _ => mem x r
         end
   end.
Implicit Arguments mem. 

Lemma mem_1 : forall s x, bst s -> In x s -> mem x s = true.
Proof. 
 intros s x; functional induction mem x s; auto; intros; clearf;
  inv bst; intuition_in; order.
Qed.

Lemma mem_2 : forall s x, mem x s = true -> In x s. 
Proof. 
 intros s x; functional induction mem x s; auto; intros; discriminate.
Qed.

Function find (x:key)(m:t elt) { struct m } : option elt := 
   match m with 
     |  Leaf => None 
     |  Node l y e r _ => match X.compare x y with 
             | LT _ => find x l 
             | EQ _ => Some e
             | GT _ => find x r
         end
   end.

Lemma find_1 : forall m x e, bst m -> MapsTo x e m -> find x m = Some e.
Proof. 
 intros s x; functional induction find x s; auto; intros; clearf;
  inv bst; intuition_in; simpl; auto; 
 try solve [order | absurd (X.lt x y); eauto | absurd (X.lt y x); eauto].
Qed.

Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
Proof. 
 intros m x; functional induction find x m; subst; intros; clearf;
  try discriminate.
 constructor 2; auto.
 inversion H; auto.
 constructor 3; auto.
Qed.

(** An all-in-one spec for [add] used later in the naive [map2] *)

Lemma add_spec : forall m x y e , bst m -> avl m -> 
  find x (add y e m) = if MX.eq_dec x y then Some e else find x m.
Proof.
intros.
destruct (MX.eq_dec x y).
apply find_1.
apply add_bst; auto.
eapply MapsTo_1 with y; eauto.
apply add_1; auto.
case_eq (find x m); intros.
apply find_1.
apply add_bst; auto.
apply add_2; auto.
apply find_2; auto.
case_eq (find x (add y e m)); auto; intros.
rewrite <- H1; symmetry.
apply find_1; auto.
eapply add_3; eauto.
apply find_2; eauto.
Qed.



(** * Elements *)

(** [elements_tree_aux acc t] catenates the elements of [t] in infix
    order to the list [acc] *)

Fixpoint elements_aux (acc : list (key*elt)) (t : t elt) {struct t} : list (key*elt) :=
  match t with
   | Leaf => acc
   | Node l x e r _ => elements_aux ((x,e) :: elements_aux acc r) l
  end.

(** then [elements] is an instanciation with an empty [acc] *)

Definition elements := elements_aux nil.

Lemma elements_aux_mapsto : forall s acc x e, 
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

Lemma elements_mapsto : forall s x e, InA eqke (x,e) (elements s) <-> MapsTo x e s. 
Proof. 
 intros; generalize (elements_aux_mapsto s nil x e); intuition.
 inversion_clear H0.
Qed.

Lemma elements_in : forall s x, L.PX.In x (elements s) <-> In x s.
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

Lemma elements_aux_sort : forall s acc, bst s -> sort ltk acc ->
 (forall x e y, InA eqke (x,e) acc -> In y s -> X.lt y x) ->
 sort ltk (elements_aux acc s).
Proof.
 induction s as [ | l Hl y e r Hr h]; simpl; intuition.
 inv bst.
 apply Hl; auto.
 constructor. 
 apply Hr; eauto.
 apply (InA_InfA (PX.eqke_refl (elt:=elt))); intros (y',e') H6.
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



(** * Fold *)

Fixpoint fold (A : Type) (f : key -> elt -> A -> A)(s : t elt) {struct s} : A -> A := 
 fun a => match s with
  | Leaf => a
  | Node l x e r _ => fold f r (f x e (fold f l a))
 end.

Definition fold' (A : Type) (f : key -> elt -> A -> A)(s : t elt) := 
  L.fold f (elements s).

Lemma fold_equiv_aux :
 forall (A : Type) (s : t elt) (f : key -> elt -> A -> A) (a : A) acc,
 L.fold f (elements_aux acc s) a = L.fold f acc (fold f s a).
Proof.
 simple induction s.
 simpl in |- *; intuition.
 simpl in |- *; intros.
 rewrite H.
 simpl.
 apply H0.
Qed.

Lemma fold_equiv :
 forall (A : Type) (s : t elt) (f : key -> elt -> A -> A) (a : A),
 fold f s a = fold' f s a.
Proof.
 unfold fold', elements in |- *. 
 simple induction s; simpl in |- *; auto; intros.
 rewrite fold_equiv_aux.
 rewrite H0.
 simpl in |- *; auto.
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

Definition Equal (cmp:elt->elt->bool) m m' := 
  (forall k, In k m <-> In k m') /\ 
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).  

(** ** Enumeration of the elements of a tree *)

Inductive enumeration : Set :=
 | End : enumeration
 | More : key -> elt -> t elt -> enumeration -> enumeration.

(** [flatten_e e] returns the list of elements of [e] i.e. the list
    of elements actually compared *)
 
Fixpoint flatten_e (e : enumeration) : list (key*elt) := match e with
  | End => nil
  | More x e t r => (x,e) :: elements t ++ flatten_e r
 end.

(** [sorted_e e] expresses that elements in the enumeration [e] are
    sorted, and that all trees in [e] are binary search trees. *)

Inductive In_e (p:key*elt) : enumeration -> Prop :=
  | InEHd1 : forall y d s e, eqke p (y,d) -> In_e p (More y d s e)
  | InEHd2 : forall y d s e, MapsTo p#1 p#2 s -> In_e p (More y d s e)
  | InETl : forall y d s e, In_e p e -> In_e p (More y d s e).

Hint Constructors In_e.

Inductive sorted_e : enumeration -> Prop :=
  | SortedEEnd : sorted_e End
  | SortedEMore :
      forall x d s e, bst s -> gt_tree x s -> sorted_e e ->
      (forall p, In_e p e -> ltk (x,d) p) ->
      (forall p, MapsTo p#1 p#2 s -> forall q, In_e q e -> ltk p q) ->
      sorted_e (More x d s e).

Hint Constructors sorted_e.

Lemma in_flatten_e :
 forall p e, InA eqke p (flatten_e e) -> In_e p e.
Proof.
 simple induction e; simpl in |- *; intuition.
 inversion_clear H.
 inversion_clear H0; auto.
 elim (InA_app H1); auto.
 destruct (elements_mapsto t a b); auto.
Qed.

Lemma sorted_flatten_e :
 forall e : enumeration, sorted_e e -> sort ltk (flatten_e e).
Proof.
 simple induction e; simpl in |- *; intuition.
 apply cons_sort.
 apply (SortA_app (PX.eqke_refl (elt:=elt))); inversion_clear H0; auto.
 intros; apply H5; auto.
 rewrite <- elements_mapsto; auto; destruct x; auto.
 apply in_flatten_e; auto.
 inversion_clear H0.
 apply In_InfA; intros.
 intros; elim (in_app_or _ _ _ H0); intuition.
 generalize (In_InA (PX.eqke_refl (elt:=elt)) H6).
 destruct y; rewrite elements_mapsto; eauto.
 apply H4; apply in_flatten_e; auto.
 apply In_InA; auto.
Qed.

Lemma elements_app :
 forall s acc, elements_aux acc s = elements s ++ acc.
Proof.
 simple induction s; simpl in |- *; intuition.
 rewrite H0.
 rewrite H.
 unfold elements; simpl.
 do 2 rewrite H.
 rewrite H0.
 repeat rewrite <- app_nil_end.
 repeat rewrite app_ass; auto.
Qed.

Lemma compare_flatten_1 :
 forall t1 t2 x e z l,
 elements t1 ++ (x,e) :: elements t2 ++ l =
 elements (Node t1 x e t2 z) ++ l.
Proof.
 simpl in |- *; unfold elements in |- *; simpl in |- *; intuition.
 repeat rewrite elements_app.
 repeat rewrite <- app_nil_end.
 repeat rewrite app_ass; auto.
Qed.

(** key lemma for correctness *)

Lemma flatten_e_elements :
 forall l r x d z e,
 elements l ++ flatten_e (More x d r e) = 
 elements (Node l x d r z) ++ flatten_e e.
Proof.
 intros; simpl.
 apply compare_flatten_1.
Qed.

(** termination of [compare_aux] *)

Open Scope nat_scope.

Fixpoint measure_e_t (s : t elt) : nat := match s with
  | Leaf => 0
  | Node l _ _ r _ => 1 + measure_e_t l + measure_e_t r
 end.

Fixpoint measure_e (e : enumeration) : nat := match e with
  | End => 0
  | More _ _ s r => 1 + measure_e_t s + measure_e r
 end.

(** [cons t e] adds the elements of tree [t] on the head of 
    enumeration [e]. *)

Fixpoint cons s e {struct s} : enumeration := 
 match s with 
  | Leaf => e
  | Node l x d r h => cons l (More x d r e)
 end.

Lemma cons_measure_e : forall s e, 
 measure_e (cons s e) = measure_e_t s + measure_e e.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1; simpl; rewrite <- plus_n_Sm; auto with arith.
Qed.

Lemma cons_1 : forall s e, 
  bst s -> sorted_e e ->
  (forall x y, MapsTo x#1 x#2 s -> In_e y e -> ltk x y) ->
  sorted_e (cons s e) /\ 
  flatten_e (cons s e) = elements s ++ flatten_e e.
Proof.
 induction s; simpl; auto.
 clear IHs2; intros.
 inv bst.
 destruct (IHs1 (More k e s2 e0)); clear IHs1; intuition.
 inversion_clear H6; subst; auto; clear H1.
 destruct y; red in H7; simpl in *; destruct H7; subst.
 red; simpl; auto.
 assert (In a s1) by eauto.
 order.
 destruct y; simpl in *; auto.
 red; simpl; auto.
 assert (In a s1) by eauto.
 assert (In k0 s2) by eauto.
 order.
 rewrite H6.
 apply flatten_e_elements.
Qed.

Definition measure2 e := (measure_e e#1 + measure_e e#2)%nat.

Function equal_aux 
 (cmp: elt -> elt -> bool)(e:enumeration*enumeration)
 { measure measure2 e } : bool := 
 match e with 
 | (End,End) => true
 | (End,More _ _ _ _) => false
 | (More _ _ _ _, End) => false
 | (More x1 d1 r1 e1, More x2 d2 r2 e2) => 
       match X.compare x1 x2 with 
        | EQ _ => cmp d1 d2 && equal_aux cmp (cons r1 e1, cons r2 e2)
        | LT _ => false
        | GT _ => false
       end
 end.
Proof.
intros; unfold measure2; simpl; 
abstract (do 2 rewrite cons_measure_e; romega with *).
Defined.

Definition equal (cmp: elt -> elt -> bool) s s' := 
 equal_aux cmp (cons s End, cons s' End).

Lemma equal_aux_Equal : forall cmp e, sorted_e e#1 -> sorted_e e#2 ->
 (equal_aux cmp e = L.equal cmp (flatten_e e#1) (flatten_e e#2)).
Proof.
 intros cmp e; functional induction equal_aux cmp e; intros; clearf;
  simpl in *; auto; MX.elim_comp; auto.
 f_equal; auto.
 inversion_clear H.
 inversion_clear H0.
 destruct (@cons_1 r1 e1); auto.
 destruct (@cons_1 r2 e2); auto.
 rewrite <- H11, <- H13; auto.
Qed.

Lemma Equal_elements : forall cmp s s', 
 Equal cmp s s' <-> L.Equal cmp (elements s) (elements s').
Proof.
unfold Equal, L.Equal; split; split; intros.
do 2 rewrite elements_in; firstorder.
destruct H.
apply (H2 k); rewrite <- elements_mapsto; auto.
do 2 rewrite <- elements_in; firstorder.
destruct H.
apply (H2 k); unfold L.PX.MapsTo; rewrite elements_mapsto; auto.
Qed.

Lemma equal_Equal : forall cmp s s', bst s -> bst s' -> 
 (equal cmp s s' = true <-> Equal cmp s s').
Proof.
 intros; unfold equal.
 destruct (@cons_1 s End); auto.
 inversion 2.
 destruct (@cons_1 s' End); auto.
 inversion 2.
 rewrite equal_aux_Equal; simpl; auto.
 rewrite Equal_elements.
 rewrite H2, H4.
 simpl; do 2 rewrite <- app_nil_end.
 split; [apply L.equal_2|apply L.equal_1]; auto.
Qed.

Close Scope nat_scope.

End Elt2.

Section Elts. 

Variable elt elt' elt'' : Set.

Section Map. 
Variable f : elt -> elt'. 

Fixpoint map (m:t elt) {struct m} : t elt' := 
  match m with 
   | Leaf   => Leaf _
   | Node l v d r h => Node (map l) v  (f d) (map r) h
  end.

Lemma map_height : forall m, height (map m) = height m.
Proof. 
destruct m; simpl; auto.
Qed.

Lemma map_avl : forall m, avl m -> avl (map m).
Proof.
induction m; simpl; auto.
inversion_clear 1; constructor; auto; do 2 rewrite map_height; auto.
Qed.

Lemma map_1 : forall (m: tree elt)(x:key)(e:elt), 
    MapsTo x e m -> MapsTo x (f e) (map m).
Proof.
induction m; simpl; inversion_clear 1; auto.
Qed.

Lemma map_2 : forall (m: t elt)(x:key), 
    In x (map m) -> In x m.
Proof.
induction m; simpl; inversion_clear 1; auto.
Qed.

Lemma map_bst : forall m, bst m -> bst (map m).
Proof.
induction m; simpl; auto.
inversion_clear 1; constructor; auto.
red; intros; apply H2; apply map_2; auto.
red; intros; apply H3; apply map_2; auto.
Qed.

End Map.
Section Mapi. 
Variable f : key -> elt -> elt'. 

Fixpoint mapi (m:t elt) {struct m} : t elt' := 
  match m with 
   | Leaf   => Leaf _
   | Node l v d r h => Node (mapi l) v  (f v d) (mapi r) h
  end.

Lemma mapi_height : forall m, height (mapi m) = height m.
Proof. 
destruct m; simpl; auto.
Qed.

Lemma mapi_avl : forall m, avl m -> avl (mapi m).
Proof.
induction m; simpl; auto.
inversion_clear 1; constructor; auto; do 2 rewrite mapi_height; auto.
Qed.

Lemma mapi_1 : forall (m: tree elt)(x:key)(e:elt), 
    MapsTo x e m -> exists y, X.eq y x /\ MapsTo x (f y e) (mapi m).
Proof.
induction m; simpl; inversion_clear 1; auto.
exists k; auto.
destruct (IHm1 _ _ H0).
exists x0; intuition.
destruct (IHm2 _ _ H0).
exists x0; intuition.
Qed.

Lemma mapi_2 : forall (m: t elt)(x:key), 
    In x (mapi m) -> In x m.
Proof.
induction m; simpl; inversion_clear 1; auto.
Qed.

Lemma mapi_bst : forall m, bst m -> bst (mapi m).
Proof.
induction m; simpl; auto.
inversion_clear 1; constructor; auto.
red; intros; apply H2; apply mapi_2; auto.
red; intros; apply H3; apply mapi_2; auto.
Qed.

End Mapi.

Section Map2.
Variable f : option elt -> option elt' -> option elt''.

(* Not exactly pretty nor perfect, but should suffice as a first naive implem. 
    Anyway, map2 isn't in Ocaml...
*)

Definition anti_elements (l:list (key*elt'')) := L.fold (@add _) l (empty _).

Definition map2 (m:t elt)(m':t elt') : t elt'' := 
  anti_elements (L.map2 f (elements m) (elements m')).

Lemma anti_elements_avl_aux : forall (l:list (key*elt''))(m:t elt''), 
  avl m -> avl (L.fold (@add _) l m).
Proof.
unfold anti_elements; induction l.
simpl; auto.
simpl; destruct a; intros.
apply IHl.
apply add_avl; auto.
Qed.

Lemma anti_elements_avl : forall l, avl (anti_elements l).
Proof.
unfold anti_elements, empty; intros; apply anti_elements_avl_aux; auto.
Qed.

Lemma anti_elements_bst_aux : forall (l:list (key*elt''))(m:t elt''), 
  bst m -> avl m -> bst (L.fold (@add _) l m).
Proof.
induction l.
simpl; auto.
simpl; destruct a; intros.
apply IHl.
apply add_bst; auto.
apply add_avl; auto.
Qed.

Lemma anti_elements_bst : forall l, bst (anti_elements l).
Proof.
unfold anti_elements, empty; intros; apply anti_elements_bst_aux; auto.
Qed.

Lemma anti_elements_mapsto_aux : forall (l:list (key*elt'')) m k e,
  bst m -> avl m -> NoDupA (PX.eqk (elt:=elt'')) l -> 
  (forall x, L.PX.In x l -> In x m -> False) -> 
  (MapsTo k e (L.fold (@add _) l m) <-> L.PX.MapsTo k e l \/ MapsTo k e m).
Proof.
induction l. 
simpl; auto.
intuition.
inversion H4.
simpl; destruct a; intros.
rewrite IHl; clear IHl.
apply add_bst; auto.
apply add_avl; auto.
inversion H1; auto.
intros.
inversion_clear H1.
assert (~X.eq x k).
 contradict H5.
 destruct H3.
 apply InA_eqA with (x,x0); eauto.
apply (H2 x).
destruct H3; exists x0; auto.
revert H4; do 2 rewrite <- In_alt; destruct 1; exists x0; auto.
eapply add_3; eauto.
intuition.
assert (find k0 (add k e m) = Some e0).
 apply find_1; auto.
 apply add_bst; auto.
clear H4. 
rewrite add_spec in H3; auto.
destruct (MX.eq_dec k0 k).
inversion_clear H3; subst; auto.
right; apply find_2; auto.
inversion_clear H4; auto.
compute in H3; destruct H3.
subst; right; apply add_1; auto.
inversion_clear H1.
destruct (MX.eq_dec k0 k).
destruct (H2 k); eauto.
right; apply add_2; auto.
Qed.

Lemma anti_elements_mapsto : forall l k e, NoDupA (PX.eqk (elt:=elt'')) l ->
  (MapsTo k e (anti_elements l) <-> L.PX.MapsTo k e l).
Proof. 
intros. 
unfold anti_elements.
rewrite anti_elements_mapsto_aux; auto; unfold empty; auto.
inversion 2.
intuition.
inversion H1.
Qed.

Lemma map2_avl : forall (m: t elt)(m': t elt'), avl (map2 m m').
Proof.
unfold map2; intros; apply anti_elements_avl; auto.
Qed.

Lemma map2_bst : forall (m: t elt)(m': t elt'), bst (map2 m m').
Proof.
unfold map2; intros; apply anti_elements_bst; auto.
Qed.

Lemma find_elements : forall (elt:Set)(m: t elt) x, bst m -> 
  L.find x (elements m) = find x m.
Proof. 
intros.
case_eq (find x m); intros.
apply L.find_1.
apply elements_sort; auto.
red; rewrite elements_mapsto.
apply find_2; auto.
case_eq (L.find x (elements m)); auto; intros.
rewrite <- H0; symmetry.
apply find_1; auto.
rewrite <- elements_mapsto.
apply L.find_2; auto.
Qed.

Lemma find_anti_elements : forall (l: list (key*elt'')) x, 
 sort (@PX.ltk _) l -> 
 find x (anti_elements l) = L.find x l.
Proof.
intros.
case_eq (L.find x l); intros.
apply find_1.
apply anti_elements_bst; auto.
rewrite anti_elements_mapsto.
apply L.PX.Sort_NoDupA; auto.
apply L.find_2; auto.
case_eq (find x (anti_elements l)); auto; intros.
rewrite <- H0; symmetry.
apply L.find_1; auto.
rewrite <- anti_elements_mapsto.
apply L.PX.Sort_NoDupA; auto.
apply find_2; auto.
Qed.

Lemma map2_1 : forall (m: t elt)(m': t elt')(x:key), bst m -> bst m' -> 
  In x m \/ In x m' -> find x (map2 m m') = f (find x m) (find x m').       
Proof. 
unfold map2; intros.
rewrite find_anti_elements; auto.
rewrite <- find_elements; auto.
rewrite <- find_elements; auto.
apply L.map2_1; auto.
apply elements_sort; auto.
apply elements_sort; auto.
do 2 rewrite elements_in; auto.
apply L.map2_sorted; auto.
apply elements_sort; auto.
apply elements_sort; auto.
Qed.

Lemma map2_2 : forall (m: t elt)(m': t elt')(x:key), bst m -> bst m' -> 
  In x (map2 m m') -> In x m \/ In x m'.
Proof.
unfold map2; intros.
do 2 rewrite <- elements_in.
apply L.map2_2 with (f:=f); auto.
apply elements_sort; auto.
apply elements_sort; auto.
revert H1.
rewrite <- In_alt.
destruct 1.
exists x0.
rewrite <- anti_elements_mapsto; auto.
apply L.PX.Sort_NoDupA; auto.
apply L.map2_sorted; auto.
apply elements_sort; auto.
apply elements_sort; auto.
Qed.

End Map2.
End Elts.
End Raw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we 
   need to encapsulate everything into a type of balanced binary search trees. *)

Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.

 Module E := X.
 Module Raw := Raw I X. 

 Record bbst (elt:Set) : Set := 
  Bbst {this :> Raw.tree elt; is_bst : Raw.bst this; is_avl: Raw.avl this}.
 
 Definition t := bbst. 
 Definition key := E.t.
 
 Section Elt. 
 Variable elt elt' elt'': Set.

 Implicit Types m : t elt.
 Implicit Types x y : key. 
 Implicit Types e : elt. 

 Definition empty : t elt := Bbst (Raw.empty_bst elt) (Raw.empty_avl elt).
 Definition is_empty m : bool := Raw.is_empty m.(this).
 Definition add x e m : t elt := 
  Bbst (Raw.add_bst x e m.(is_bst) m.(is_avl)) (Raw.add_avl x e m.(is_avl)).
 Definition remove x m : t elt := 
  Bbst (Raw.remove_bst x m.(is_bst) m.(is_avl)) (Raw.remove_avl x m.(is_avl)). 
 Definition mem x m : bool := Raw.mem x m.(this).
 Definition find x m : option elt := Raw.find x m.(this).
 Definition map f m : t elt' := 
  Bbst (Raw.map_bst f m.(is_bst)) (Raw.map_avl f m.(is_avl)).
 Definition mapi (f:key->elt->elt') m : t elt' := 
  Bbst (Raw.mapi_bst f m.(is_bst)) (Raw.mapi_avl f m.(is_avl)).
 Definition map2 f m (m':t elt') : t elt'' := 
  Bbst (Raw.map2_bst f m m') (Raw.map2_avl f m m').
 Definition elements m : list (key*elt) := Raw.elements m.(this).
 Definition fold (A:Type) (f:key->elt->A->A) m i := Raw.fold (A:=A) f m.(this) i.
 Definition equal cmp m m' : bool := Raw.equal cmp m.(this) m'.(this).

 Definition MapsTo x e m : Prop := Raw.MapsTo x e m.(this).
 Definition In x m : Prop := Raw.In0 x m.(this).
 Definition Empty m : Prop := Raw.Empty m.(this).

 Definition eq_key : (key*elt) -> (key*elt) -> Prop := @Raw.PX.eqk elt.
 Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop := @Raw.PX.eqke elt.
 Definition lt_key : (key*elt) -> (key*elt) -> Prop := @Raw.PX.ltk elt.

 Lemma MapsTo_1 : forall m x y e, E.eq x y -> MapsTo x e m -> MapsTo y e m.
 Proof. intros m; exact (@Raw.MapsTo_1 _ m.(this)). Qed.
 
 Lemma mem_1 : forall m x, In x m -> mem x m = true.
 Proof.
 unfold In, mem; intros m x; rewrite Raw.In_alt; simpl; apply Raw.mem_1; auto.
 apply m.(is_bst).
 Qed.
 
 Lemma mem_2 : forall m x, mem x m = true -> In x m. 
 Proof.
 unfold In, mem; intros m x; rewrite Raw.In_alt; simpl; apply Raw.mem_2; auto.
 Qed.

 Lemma empty_1 : Empty empty.
 Proof. exact (@Raw.empty_1 elt). Qed.

 Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
 Proof. intros m; exact (@Raw.is_empty_1 _ m.(this)). Qed.
 Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
 Proof. intros m; exact (@Raw.is_empty_2 _ m.(this)). Qed.

 Lemma add_1 : forall m x y e, E.eq x y -> MapsTo y e (add x e m).
 Proof. intros m x y e; exact (@Raw.add_1 elt _ x y e m.(is_avl)). Qed.
 Lemma add_2 : forall m x y e e', ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
 Proof. intros m x y e e'; exact (@Raw.add_2 elt _ x y e e' m.(is_avl)). Qed.
 Lemma add_3 : forall m x y e e', ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
 Proof. intros m x y e e'; exact (@Raw.add_3 elt _ x y e e' m.(is_avl)). Qed.

 Lemma remove_1 : forall m x y, E.eq x y -> ~ In y (remove x m).
 Proof.
 unfold In, remove; intros m x y; rewrite Raw.In_alt; simpl; apply Raw.remove_1; auto.
 apply m.(is_bst).
 apply m.(is_avl).
 Qed.
 Lemma remove_2 : forall m x y e, ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
 Proof. intros m x y e; exact (@Raw.remove_2 elt _ x y e m.(is_bst) m.(is_avl)). Qed.
 Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.
 Proof. intros m x y e; exact (@Raw.remove_3 elt _ x y e m.(is_bst) m.(is_avl)). Qed.


 Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e. 
 Proof. intros m x e; exact (@Raw.find_1 elt _ x e m.(is_bst)). Qed.
 Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
 Proof. intros m; exact (@Raw.find_2 elt m.(this)). Qed.

 Lemma fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
 Proof. intros m; exact (@Raw.fold_1 elt m.(this) m.(is_bst)). Qed.

 Lemma elements_1 : forall m x e,       
   MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
 Proof.
 intros; unfold elements, MapsTo, eq_key_elt; rewrite Raw.elements_mapsto; auto.
 Qed.

 Lemma elements_2 : forall m x e,   
   InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
 Proof.
 intros; unfold elements, MapsTo, eq_key_elt; rewrite <- Raw.elements_mapsto; auto.
 Qed.

 Lemma elements_3 : forall m, sort lt_key (elements m).  
 Proof. intros m; exact (@Raw.elements_sort elt m.(this) m.(is_bst)). Qed.

 Lemma elements_3w : forall m, NoDupA eq_key (elements m).  
 Proof. intros m; exact (@Raw.elements_nodup elt m.(this) m.(is_bst)). Qed.

 Definition Equal cmp m m' := 
   (forall k, In k m <-> In k m') /\ 
   (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).  

 Lemma Equal_Equal : forall cmp m m', Equal cmp m m' <-> Raw.Equal cmp m m'.
 Proof. 
 intros; unfold Equal, Raw.Equal, In; intuition.
 generalize (H0 k); do 2 rewrite Raw.In_alt; intuition.
 generalize (H0 k); do 2 rewrite Raw.In_alt; intuition.
 generalize (H0 k); do 2 rewrite <- Raw.In_alt; intuition.
 generalize (H0 k); do 2 rewrite <- Raw.In_alt; intuition.
 Qed. 

 Lemma equal_1 : forall m m' cmp, 
   Equal cmp m m' -> equal cmp m m' = true. 
 Proof. 
 unfold equal; intros (m,b,a) (m',b',a') cmp; rewrite Equal_Equal; 
  intros; simpl in *; rewrite Raw.equal_Equal; auto.
 Qed. 

 Lemma equal_2 : forall m m' cmp, 
   equal cmp m m' = true -> Equal cmp m m'.
 Proof. 
 unfold equal; intros (m,b,a) (m',b',a') cmp; rewrite Equal_Equal; 
  intros; simpl in *; rewrite <-Raw.equal_Equal; auto.
 Qed.  

 End Elt.

 Lemma map_1 : forall (elt elt':Set)(m: t elt)(x:key)(e:elt)(f:elt->elt'), 
        MapsTo x e m -> MapsTo x (f e) (map f m).
 Proof. intros elt elt' m x e f; exact (@Raw.map_1 elt elt' f m.(this) x e). Qed.

 Lemma map_2 : forall (elt elt':Set)(m:t elt)(x:key)(f:elt->elt'), In x (map f m) -> In x m.
 Proof.
 intros elt elt' m x f; do 2 unfold In in *; do 2 rewrite Raw.In_alt; simpl.
 apply Raw.map_2; auto.
 Qed. 

 Lemma mapi_1 : forall (elt elt':Set)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m -> 
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
 Proof. intros elt elt' m x e f; exact (@Raw.mapi_1 elt elt' f m.(this) x e). Qed.
 Lemma mapi_2 : forall (elt elt':Set)(m: t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.
 Proof.
 intros elt elt' m x f; unfold In in *; do 2 rewrite Raw.In_alt; simpl; apply Raw.mapi_2; auto.
 Qed. 

 Lemma map2_1 : forall (elt elt' elt'':Set)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''), 
    In x m \/ In x m' -> 
    find x (map2 f m m') = f (find x m) (find x m'). 
 Proof. 
 unfold find, map2, In; intros elt elt' elt'' m m' x f.
 do 2 rewrite Raw.In_alt; intros; simpl; apply Raw.map2_1; auto.
 apply m.(is_bst).
 apply m'.(is_bst).
 Qed.

 Lemma map2_2 : forall (elt elt' elt'':Set)(m: t elt)(m': t elt')
     (x:key)(f:option elt->option elt'->option elt''), 
     In x (map2 f m m') -> In x m \/ In x m'.
 Proof. 
 unfold In, map2; intros elt elt' elt'' m m' x f.
 do 3 rewrite Raw.In_alt; intros; simpl in *; eapply Raw.map2_2; eauto.
 apply m.(is_bst).
 apply m'.(is_bst).
 Qed.

End IntMake.


Module IntMake_ord (I:Int)(X: OrderedType)(D : OrderedType) <: 
    Sord with Module Data := D 
            with Module MapS.E := X.

  Module Data := D.
  Module Import MapS := IntMake(I)(X). 
  Module Import MD := OrderedTypeFacts(D).
  Module LO := FMapList.Make_ord(X)(D).

  Definition t := MapS.t D.t. 

  Definition cmp e e' := 
   match D.compare e e' with EQ _ => true | _ => false end.

  Definition elements (m:t) := 
    LO.MapS.Build_slist (Raw.elements_sort m.(is_bst)).

  Open Scope nat_scope.

  Function compare_aux (e:Raw.enumeration D.t * Raw.enumeration D.t) 
   { measure Raw.measure2 e } : comparison := 
  match e with 
  | (Raw.End, Raw.End) => Eq
  | (Raw.End, Raw.More _ _ _ _) => Lt
  | (Raw.More _ _ _ _, Raw.End) => Gt
  | (Raw.More x1 d1 r1 e1, Raw.More x2 d2 r2 e2) =>
      match X.compare x1 x2 with
      | EQ _ => match D.compare d1 d2 with 
                | EQ _ => compare_aux (Raw.cons r1 e1, Raw.cons r2 e2)
                | LT _ => Lt
                | GT _ => Gt
                end
      | LT _ => Lt
      | GT _ => Gt
      end
  end.
  Proof.
  intros; unfold Raw.measure2; simpl; 
  abstract (do 2 rewrite Raw.cons_measure_e; romega with *).
  Defined.

  Lemma compare_aux_Eq : 
   forall e, Raw.sorted_e (fst e) -> Raw.sorted_e (snd e) -> 
   compare_aux e = Eq -> 
   LO.eq_list (Raw.flatten_e (fst e)) (Raw.flatten_e (snd e)).
  Proof.
  intros e; functional induction compare_aux e; simpl in *; intros; 
   try discriminate; simpl; auto; try clear e3 e4; 
   Raw.MX.elim_comp; split; auto.
  inversion_clear H.
  inversion_clear H0.
  destruct (@Raw.cons_1 _ r1 e1); auto.
  destruct (@Raw.cons_1 _ r2 e2); auto.
  rewrite <- H12, <- H14; auto.
  Qed.

  Lemma compare_aux_Lt : 
   forall e,  Raw.sorted_e (fst e) -> Raw.sorted_e (snd e) -> 
   compare_aux e = Lt -> 
   LO.lt_list (Raw.flatten_e (fst e)) (Raw.flatten_e (snd e)).
  Proof.
  intros e; functional induction compare_aux e; simpl in *; intros; 
   try discriminate; simpl; auto; clear e3; try clear e4; 
   Raw.MX.elim_comp; auto.
  right; split; auto.
  inversion_clear H.
  inversion_clear H0.
  destruct (@Raw.cons_1 _ r1 e1); auto.
  destruct (@Raw.cons_1 _ r2 e2); auto.
  rewrite <- H12, <- H14; auto.
  Qed.

  Lemma compare_aux_Gt : 
   forall e,  Raw.sorted_e (fst e) -> Raw.sorted_e (snd e) -> 
   compare_aux e = Gt -> 
   LO.lt_list (Raw.flatten_e (snd e)) (Raw.flatten_e (fst e)).
  Proof.
  intros e; functional induction compare_aux e; simpl in *; intros; 
   try discriminate; simpl; auto; clear e3; try clear e4; 
   Raw.MX.elim_comp; auto.
  right; split; auto.
  inversion_clear H.
  inversion_clear H0.
  destruct (@Raw.cons_1 _ r1 e1); auto.
  destruct (@Raw.cons_1 _ r2 e2); auto.
  rewrite <- H12, <- H14; auto.
  Qed.

  Definition eq (m1 m2 : t) := LO.eq (elements m1) (elements m2).

  Definition lt (m1 m2 : t) := LO.lt (elements m1) (elements m2).

  Definition compare (m1 m2 : t) : Compare lt eq m1 m2.
  Proof.
   intros.
   destruct (@Raw.cons_1 _ _ (Raw.End _) m1.(is_bst)).
    constructor.
    inversion 2.
   destruct (@Raw.cons_1 _ _ (Raw.End _) m2.(is_bst)).
    constructor.
    inversion 2.
   set (e:= (Raw.cons m1 (Raw.End _), Raw.cons m2 (Raw.End _))).
   generalize (@compare_aux_Eq e H H1)(@compare_aux_Lt e H H1)
     (@compare_aux_Gt e H H1).
   destruct (compare_aux e); intros; [ apply EQ | apply LT | apply GT ]; 
    unfold eq, LO.eq, lt, LO.lt in *; simpl in *; 
    rewrite H0, H2, <-app_nil_end, <-app_nil_end in *; auto.
  Defined.

  Lemma eq_1 : forall m m', Equal cmp m m' -> eq m m'.
  Proof.
  intros m m'.
  unfold eq.
  rewrite Equal_Equal.
  rewrite Raw.Equal_elements.
  intros.
  apply LO.eq_1.
  auto.
  Qed.

  Lemma eq_2 : forall m m', eq m m' -> Equal cmp m m'.
  Proof.
  intros m m'.
  unfold eq.
  rewrite Equal_Equal.
  rewrite Raw.Equal_elements.
  intros.
  generalize (LO.eq_2 H).
  auto.
  Qed.

  Lemma eq_refl : forall m : t, eq m m.
  Proof. 
  unfold eq; intros; apply LO.eq_refl.
  Qed.

  Lemma eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Proof.
  unfold eq; intros; apply LO.eq_sym; auto.
  Qed.

  Lemma eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Proof.
  unfold eq; intros; eapply LO.eq_trans; eauto.
  Qed.

  Lemma lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Proof.
  unfold lt; intros; eapply LO.lt_trans; eauto.
  Qed.

  Lemma lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.
  Proof.
  unfold lt, eq; intros; apply LO.lt_not_eq; auto.
  Qed.

End IntMake_ord.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (X: OrderedType) <: S with Module E := X
 :=IntMake(Z_as_Int)(X).

Module Make_ord (X: OrderedType)(D: OrderedType) 
 <: Sord with Module Data := D 
            with Module MapS.E := X
 :=IntMake_ord(Z_as_Int)(X)(D).

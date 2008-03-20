(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite sets library.  
 * Authors: Pierre Letouzey and Jean-Christophe Filliâtre 
 * Institution: LRI, CNRS UMR 8623 - Université Paris Sud
 *              91405 Orsay, France *)

(* $Id$ *)

(** * FSetAVL *)

(** This module implements sets using AVL trees.
    It follows the implementation from Ocaml's standard library,
    
    All operations given here expect and produce well-balanced trees
    (in the ocaml sense: heigths of subtrees shouldn't differ by more
    than 2), and hence has low complexities (e.g. add is logarithmic
    in the size of the set). But proving these balancing preservations
    is in fact not necessary for ensuring correct operational behavior
    and hence fulfilling the FSet interface. As a consequence,
    balancing results are not part of this file anymore, they can 
    now be found in [FSetFullAVL].

    Four operations ([union], [subset], [compare] and [equal]) have
    been slightly adapted in order to have only structural recursive
    calls. The precise ocaml versions of these operations have also
    been formalized (thanks to Function+measure), see [ocaml_union],
    [ocaml_subset], [ocaml_compare] and [ocaml_equal] in
    [FSetFullAVL]. The structural variants compute faster in Coq,
    whereas the other variants produce nicer and/or (slightly) faster
    code after extraction.
*)

Require Import FSetInterface FSetList ZArith Int.

Set Implicit Arguments.
Unset Strict Implicit.

Module Raw (Import I:Int)(X:OrderedType).
Open Local Scope Int_scope.
Module MX := OrderedTypeFacts X.

Definition elt := X.t.

(** Notations and helper lemma about pairs *)

Notation "s #1" := (fst s) (at level 9, format "s '#1'").
Notation "s #2" := (snd s) (at level 9, format "s '#2'").

Lemma distr_pair : forall (A B:Type)(s:A*B)(a:A)(b:B), s = (a,b) -> 
 s#1 = a /\ s#2 = b.
Proof.
 destruct s; simpl; injection 1; auto.
Qed.


(** * Trees

   The fourth field of [Node] is the height of the tree *)

Inductive tree :=
  | Leaf : tree
  | Node : tree -> X.t -> tree -> int -> tree.

Notation t := tree.

(** * Basic functions on trees: height and cardinal *)

Definition height (s : tree) : int :=
  match s with
  | Leaf => 0
  | Node _ _ _ h => h
  end.

Fixpoint cardinal (s : tree) : nat :=
  match s with
   | Leaf => 0%nat
   | Node l _ r _ => S (cardinal l + cardinal r)
  end.

(** * Occurrence in a tree *)

Inductive In (x : elt) : tree -> Prop :=
  | IsRoot : forall l r h y, X.eq x y -> In x (Node l y r h)
  | InLeft : forall l r h y, In x l -> In x (Node l y r h)
  | InRight : forall l r h y, In x r -> In x (Node l y r h).

(** * Binary search trees *)

(** [lt_tree x s]: all elements in [s] are smaller than [x] 
   (resp. greater for [gt_tree]) *)

Definition lt_tree x s := forall y, In y s -> X.lt y x.
Definition gt_tree x s := forall y, In y s -> X.lt x y.

(** [bst t] : [t] is a binary search tree *)

Inductive bst : tree -> Prop :=
  | BSLeaf : bst Leaf
  | BSNode : forall x l r h, bst l -> bst r -> 
     lt_tree x l -> gt_tree x r -> bst (Node l x r h).

(** * Automation and dedicated tactics *)

Hint Constructors In bst.
Hint Unfold lt_tree gt_tree.

(** A tactic to repeat [inversion_clear] on all hyps of the 
    form [(f (Node _ _ _ _))] *)

Ltac inv f :=
  match goal with 
     | H:f Leaf |- _ => inversion_clear H; inv f
     | H:f _ Leaf |- _ => inversion_clear H; inv f
     | H:f (Node _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ (Node _ _ _ _) |- _ => inversion_clear H; inv f
     | _ => idtac
  end.

Ltac intuition_in := repeat progress (intuition; inv In).

(** Helper tactic concerning order of elements. *)

Ltac order := match goal with 
 | U: lt_tree _ ?s, V: In _ ?s |- _ => generalize (U _ V); clear U; order
 | U: gt_tree _ ?s, V: In _ ?s |- _ => generalize (U _ V); clear U; order
 | _ => MX.order
end.


(** * Basic results about [In], [lt_tree], [gt_tree], [height] *)

(** [In] is compatible with [X.eq] *)

Lemma In_1 :
 forall s x y, X.eq x y -> In x s -> In y s.
Proof.
 induction s; simpl; intuition_in; eauto.
Qed.
Hint Immediate In_1.

Lemma In_node_iff : 
 forall l x r h y, 
  In y (Node l x r h) <-> In y l \/ X.eq y x \/ In y r.
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
 forall (x : elt) (t : tree), lt_tree x t -> ~ In x t.
Proof.
 intros; intro; order.
Qed.

Lemma lt_tree_trans :
 forall x y, X.lt x y -> forall t, lt_tree x t -> lt_tree y t.
Proof.
 eauto.
Qed.

Lemma gt_tree_not_in :
 forall (x : elt) (t : tree), gt_tree x t -> ~ In x t.
Proof.
 intros; intro; order.
Qed.

Lemma gt_tree_trans :
 forall x y, X.lt y x -> forall t, gt_tree x t -> gt_tree y t.
Proof.
 eauto.
Qed.

Hint Resolve lt_tree_not_in lt_tree_trans gt_tree_not_in gt_tree_trans.


(** * Some shortcuts. *)

Definition Equal s s' := forall a : elt, In a s <-> In a s'.
Definition Subset s s' := forall a : elt, In a s -> In a s'.
Definition Empty s := forall a : elt, ~ In a s.
Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.


(** * Empty set *)

Definition empty := Leaf.

Lemma empty_1 : Empty empty.
Proof.
 intro; intro.
 inversion H.
Qed.

Lemma empty_bst : bst empty.
Proof.
 auto.
Qed.


(** * Emptyness test *)

Definition is_empty (s:t) := match s with Leaf => true | _ => false end.

Lemma is_empty_1 : forall s, Empty s -> is_empty s = true. 
Proof.
 destruct s as [|r x l h]; simpl; auto.
 intro H; elim (H x); auto.
Qed.

Lemma is_empty_2 : forall s, is_empty s = true -> Empty s.
Proof. 
 destruct s; simpl; intros; try discriminate; red; auto.
Qed.



(** * Appartness *)

(** The [mem] function is deciding appartness. It exploits the [bst] property
    to achieve logarithmic complexity. *)

Function mem (x:elt)(s:t) { struct s } : bool := 
   match s with 
     |  Leaf => false 
     |  Node l y r _ => match X.compare x y with 
             | LT _ => mem x l 
             | EQ _ => true
             | GT _ => mem x r
         end
   end.

Lemma mem_1 : forall s x, bst s -> In x s -> mem x s = true.
Proof.
 intros s x; functional induction mem x s; auto; intros; try clear e0; 
  inv bst; intuition_in; order.
Qed.

Lemma mem_2 : forall s x, mem x s = true -> In x s. 
Proof. 
 intros s x; functional induction mem x s; auto; intros; discriminate.
Qed.



(** * Singleton set *)

Definition singleton (x : elt) := Node Leaf x Leaf 1.

Lemma singleton_1 : forall x y, In y (singleton x) -> X.eq x y. 
Proof. 
 unfold singleton; intros; inv In; order.
Qed.

Lemma singleton_2 : forall x y, X.eq x y -> In y (singleton x). 
Proof. 
 unfold singleton; auto.
Qed.

Lemma singleton_bst : forall x : elt, bst (singleton x).
Proof.
 unfold singleton; auto.
Qed.



(** * Helper functions *)

(** [create l x r] creates a node, assuming [l] and [r]
    to be balanced and [|height l - height r| <= 2]. *)

Definition create l x r := 
   Node l x r (max (height l) (height r) + 1).

Lemma create_in : 
 forall l x r y,  In y (create l x r) <-> X.eq y x \/ In y l \/ In y r.
Proof.
 unfold create; split; [ inversion_clear 1 | ]; intuition.
Qed.

Lemma create_bst : 
 forall l x r, bst l -> bst r -> lt_tree x l -> gt_tree x r -> 
 bst (create l x r).
Proof.
 unfold create; auto.
Qed.
Hint Resolve create_bst.


(** [bal l x r] acts as [create], but performs one step of
    rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

Definition assert_false := create.

Function bal (l:t)(x:elt)(r:t) : t := 
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

Lemma bal_in : forall l x r y, 
 In y (bal l x r) <-> X.eq y x \/ In y l \/ In y r.
Proof.
 intros l x r; functional induction bal l x r; intros; try clear e0; 
 rewrite !create_in; intuition_in.
Qed.

Lemma bal_bst : forall l x r, bst l -> bst r -> 
 lt_tree x l -> gt_tree x r -> bst (bal l x r).
Proof.
 intros l x r; functional induction bal l x r; intros;
 inv bst; repeat apply create_bst; auto; unfold create;
 (apply lt_tree_node || apply gt_tree_node); auto; 
 (eapply lt_tree_trans || eapply gt_tree_trans); eauto.
Qed.
Hint Resolve bal_bst.


(** * Insertion *)

Function add (x:elt)(s:t) { struct s } : t := match s with 
   | Leaf => Node Leaf x Leaf 1
   | Node l y r h => 
      match X.compare x y with
         | LT _ => bal (add x l) y r
         | EQ _ => Node l y r h
         | GT _ => bal l y (add x r)
      end
  end.

Lemma add_in : forall s x y,
 In y (add x s) <-> X.eq y x \/ In y s.
Proof.
 intros s x; functional induction (add x s); auto; intros; 
 try rewrite bal_in, IHt; intuition_in.
 eapply In_1; eauto.
Qed.

Lemma add_bst : forall s x, bst s -> bst (add x s).
Proof. 
 intros s x; functional induction (add x s); auto; intros; 
 inv bst; apply bal_bst; auto.
 (* lt_tree -> lt_tree (add ...) *)
 red; red in H3.
 intros.
 rewrite add_in in H.
 intuition.
 eauto.
 inv bst; auto using bal_bst.
 (* gt_tree -> gt_tree (add ...) *)
 red; red in H3.
 intros.
 rewrite add_in in H.
 intuition.
 apply MX.lt_eq with x; auto.
Qed.
Hint Resolve add_bst.



(** * Join

    Same as [bal] but does not assume anything regarding heights
    of [l] and [r].
*)

Fixpoint join (l:t) : elt -> t -> t :=
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

(* Function can't deal with internal fix. Let's do its job by hand: *)

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

Lemma join_in : forall l x r y, 
 In y (join l x r) <-> X.eq y x \/ In y l \/ In y r.
Proof.
 join_tac.
 simpl.
 rewrite add_in; intuition_in.
 rewrite add_in; intuition_in.
 rewrite bal_in, Hlr; clear Hlr Hrl; intuition_in.
 rewrite bal_in, Hrl; clear Hlr Hrl; intuition_in.
 apply create_in.
Qed.

Lemma join_bst : forall l x r, bst l -> bst r -> 
 lt_tree x l -> gt_tree x r -> bst (join l x r).
Proof.
 join_tac; auto; inv bst; apply bal_bst; auto; 
 clear Hrl Hlr z; intro; intros; rewrite join_in in *.
 intuition; [ apply MX.lt_eq with x | ]; eauto.
 intuition; [ apply MX.eq_lt with x | ]; eauto.
Qed.
Hint Resolve join_bst.



(** * Extraction of minimum element

  Morally, [remove_min] is to be applied to a non-empty tree 
  [t = Node l x r h]. Since we can't deal here with [assert false] 
  for [t=Leaf], we pre-unpack [t] (and forget about [h]). 
*)
 
Function remove_min (l:t)(x:elt)(r:t) { struct l } : t*elt := 
  match l with 
    | Leaf => (r,x)
    | Node ll lx lr lh => 
       let (l',m) := remove_min ll lx lr in (bal l' x r, m)
  end.

Lemma remove_min_in : forall l x r h y, 
 In y (Node l x r h) <-> 
  X.eq y (remove_min l x r)#2 \/ In y (remove_min l x r)#1.
Proof.
 intros l x r; functional induction (remove_min l x r); simpl in *; intros.
 intuition_in.
 rewrite bal_in, In_node_iff, IHp, e0; simpl; intuition.
Qed.

Lemma remove_min_bst : forall l x r h, 
 bst (Node l x r h) -> bst (remove_min l x r)#1.
Proof.
 intros l x r; functional induction (remove_min l x r); subst;simpl in *; intros.
 inv bst; auto.
 inversion_clear H.
 specialize IHp with (1:=H0); rewrite e0 in IHp; auto.
 apply bal_bst; auto.
 intro y; specialize (H2 y).
 rewrite remove_min_in, e0 in H2; simpl in H2; intuition.
Qed.

Lemma remove_min_gt_tree : forall l x r h, 
 bst (Node l x r h) ->
 gt_tree (remove_min l x r)#2 (remove_min l x r)#1.
Proof.
 intros l x r; functional induction (remove_min l x r); subst;simpl in *; intros.
 inv bst; auto.
 inversion_clear H.
 specialize IHp with (1:=H0); rewrite e0 in IHp; simpl in IHp.
 intro y; rewrite bal_in; intuition; 
  specialize (H2 m); rewrite remove_min_in, e0 in H2; simpl in H2; 
  [ apply MX.lt_eq with x | ]; eauto.
Qed.
Hint Resolve remove_min_bst remove_min_gt_tree.



(** * Merging two trees

  [merge t1 t2] builds the union of [t1] and [t2] assuming all elements
  of [t1] to be smaller than all elements of [t2], and
  [|height t1 - height t2| <= 2].
*)

Function merge (s1 s2 :t) : t:=  match s1,s2 with 
  | Leaf, _ => s2 
  | _, Leaf => s1
  | _, Node l2 x2 r2 h2 => 
        let (s2',m) := remove_min l2 x2 r2 in bal s1 m s2'
end.

Lemma merge_in : forall s1 s2 y,
 In y (merge s1 s2) <-> In y s1 \/ In y s2.
Proof.
 intros s1 s2; functional induction (merge s1 s2); subst; simpl in *; intros.
 intuition_in.
 intuition_in.
 rewrite bal_in, remove_min_in, e1; simpl; intuition.
Qed.

Lemma merge_bst : forall s1 s2, bst s1 -> bst s2 -> 
 (forall y1 y2 : elt, In y1 s1 -> In y2 s2 -> X.lt y1 y2) -> 
 bst (merge s1 s2).
Proof.
 intros s1 s2; functional induction (merge s1 s2); subst; simpl in *; intros; auto; clear y.
 apply bal_bst; auto.
 change s2' with ((s2',m)#1); rewrite <-e1; eauto.
 intros y Hy.
 apply H1; auto.
 rewrite remove_min_in, e1; simpl; auto.
 change (gt_tree (s2',m)#2 (s2',m)#1); rewrite <-e1; eauto.
Qed.
Hint Resolve merge_bst.



(** * Deletion *)

Function remove (x:elt)(s:t) { struct s } : t := match s with 
  | Leaf => Leaf
  | Node l y r h =>
      match X.compare x y with
         | LT _ => bal (remove x l) y r
         | EQ _ => merge l r
         | GT _ => bal l  y (remove x r)
      end
   end.

Lemma remove_in : forall s x y, bst s ->
 (In y (remove x s) <-> ~ X.eq y x /\ In y s).
Proof.
 intros s x; functional induction (remove x s); subst; simpl; 
  intros; inv bst.
 intuition_in.
 rewrite bal_in, IHt; clear e0 IHt; intuition; [order|order|intuition_in].
 rewrite merge_in; clear e0; intuition; [order|order|intuition_in].
 elim H4; eauto.
 rewrite bal_in, IHt; clear e0 IHt; intuition; [order|order|intuition_in].
Qed.

Lemma remove_bst : forall s x, bst s -> bst (remove x s).
Proof. 
 intros s x; functional induction (remove x s); simpl; 
  intros; inv bst.
 auto.
 (* LT *)
 apply bal_bst; auto.
 intro z; rewrite remove_in; auto; destruct 1; eauto.
 (* EQ *)
 eauto.
 (* GT *) 
 apply bal_bst; auto.
 intro z; rewrite remove_in; auto; destruct 1; eauto.
Qed.
Hint Resolve remove_bst.



(** * Minimum element *)

Function min_elt (s:t) : option elt := match s with 
   | Leaf => None
   | Node Leaf y _  _ => Some y
   | Node l _ _ _ => min_elt l
end.

Lemma min_elt_1 : forall s x, min_elt s = Some x -> In x s. 
Proof. 
 intro s; functional induction (min_elt s); subst; simpl.
 inversion 1.
 inversion 1; auto.
 intros.
 destruct l; auto.
Qed.

Lemma min_elt_2 : forall s x y, bst s ->
 min_elt s = Some x -> In y s -> ~ X.lt y x. 
Proof.
 intro s; functional induction (min_elt s); subst;simpl.
 inversion_clear 2.
 inversion_clear 1.
 inversion 1; subst.
 inversion_clear 1; auto.
 inversion_clear H5.
 destruct l;try contradiction.
 inversion_clear 1.
 simpl.
 destruct l1.
 inversion 1; subst.
 assert (X.lt x _x) by (apply H2; auto).
 inversion_clear 1; auto; order.
 assert (X.lt t _x) by auto.
 inversion_clear 2; auto; 
   (assert (~ X.lt t x) by auto); order.
Qed.

Lemma min_elt_3 : forall s, min_elt s = None -> Empty s.
Proof.
 intro s; functional induction (min_elt s); subst;simpl.
 red; auto.
 inversion 1.
 destruct l;try contradiction. 
 clear y;intro H0.
 destruct (IHo H0 t);  auto.
Qed.



(** * Maximum element *)

Function max_elt (s:t) : option elt := match s with 
   | Leaf => None
   | Node _ y Leaf  _ => Some y
   | Node _ _ r _ => max_elt r
end.

Lemma max_elt_1 : forall s x, max_elt s = Some x -> In x s. 
Proof. 
 intro s; functional induction (max_elt s); subst;simpl.
 inversion 1.
 inversion 1; auto.
 destruct r;try contradiction; auto.
Qed.

Lemma max_elt_2 : forall s x y, bst s -> 
 max_elt s = Some x -> In y s -> ~ X.lt x y. 
Proof.
 intro s; functional induction (max_elt s); subst;simpl.
 inversion_clear 2.
 inversion_clear 1.
 inversion 1; subst.
 inversion_clear 1; auto.
 inversion_clear H5.
 destruct r;try contradiction.
 inversion_clear 1.
 assert (X.lt _x0 t) by auto.
 inversion_clear 2; auto; 
  (assert (~ X.lt x t) by auto); order.
Qed.

Lemma max_elt_3 : forall s, max_elt s = None -> Empty s.
Proof.
 intro s; functional induction (max_elt s); subst;simpl.
 red; auto.
 inversion 1.
 destruct r;try contradiction.
 intros H0; destruct (IHo H0 t); auto.
Qed.



(** * Any element *)

Definition choose := min_elt.

Lemma choose_1 : forall s x, choose s = Some x -> In x s.
Proof. 
 exact min_elt_1.
Qed.

Lemma choose_2 : forall s, choose s = None -> Empty s.
Proof. 
 exact min_elt_3.
Qed.

Lemma choose_3 : forall s s', bst s -> bst s' -> 
 forall x x', choose s = Some x -> choose s' = Some x' -> 
  Equal s s' -> X.eq x x'.
Proof.
 unfold choose, Equal; intros s s' Hb Hb' x x' Hx Hx' H.
 assert (~X.lt x x').
  apply min_elt_2 with s'; auto.
  rewrite <-H; auto using min_elt_1.
 assert (~X.lt x' x).
  apply min_elt_2 with s; auto.
  rewrite H; auto using min_elt_1.
 destruct (X.compare x x'); intuition.
Qed.



(** * Concatenation

    Same as [merge] but does not assume anything about heights.
*)

Function concat (s1 s2 : t) : t  := 
   match s1, s2 with 
      | Leaf, _ => s2 
      | _, Leaf => s1
      | _, Node l2 x2 r2 h2 => 
            let (s2',m) := remove_min l2 x2 r2 in 
            join s1 m s2'
   end.

Lemma concat_in : forall s1 s2 y, 
 In y (concat s1 s2) <-> In y s1 \/ In y s2.
Proof.
 intros s1 s2; functional induction (concat s1 s2);subst;simpl;intros.
 intuition_in.
 intuition_in.
 rewrite join_in, remove_min_in, e1; simpl; intuition.
Qed.
 
Lemma concat_bst :   forall s1 s2, bst s1 -> bst s2 -> 
 (forall y1 y2 : elt, In y1 s1 -> In y2 s2 -> X.lt y1 y2) -> 
 bst (concat s1 s2).
Proof. 
 intros s1 s2; functional induction (concat s1 s2); subst; auto; clear y.
 intros; apply join_bst; auto.
 change (bst (s2',m)#1); rewrite <-e1; eauto.
 intros y Hy.
 apply H1; auto.
 rewrite remove_min_in, e1; simpl; auto.
 change (gt_tree (s2',m)#2 (s2',m)#1); rewrite <-e1; eauto.
Qed.
Hint Resolve concat_bst.



(** * Splitting 

    [split x s] returns a triple [(l, present, r)] where
    - [l] is the set of elements of [s] that are [< x]
    - [r] is the set of elements of [s] that are [> x]
    - [present] is [true] if and only if [s] contains  [x].
*)

Function split (x:elt)(s:t) { struct s } : t * (bool * t) := match s with 
  | Leaf => (Leaf, (false, Leaf))
  | Node l y r h => 
     match X.compare x y with 
      | LT _ => match split x l with 
                 | (ll,(pres,rl)) => (ll, (pres, join rl y r))
                end
      | EQ _ => (l, (true, r))
      | GT _ => match split x r with 
                 | (rl,(pres,rr)) => (join l y rl, (pres, rr))
                end
     end
 end.

Lemma split_in_1 : forall s x y, bst s -> 
 (In y (split x s)#1 <-> In y s /\ X.lt y x).
Proof.
 intros s x; functional induction (split x s); subst; simpl; intros; 
  inv bst; try clear e0.
 intuition_in.
 rewrite e1 in IHp; simpl in IHp; rewrite IHp; intuition_in; order.
 intuition_in; order.
 rewrite join_in.
 rewrite e1 in IHp; simpl in IHp; rewrite IHp; intuition_in; order.
Qed.

Lemma split_in_2 : forall s x y, bst s -> 
 (In y (split x s)#2#2 <-> In y s /\ X.lt x y).
Proof. 
 intros s x; functional induction (split x s); subst; simpl; intros; 
  inv bst; try clear e0.
 intuition_in.
 rewrite join_in.
 rewrite e1 in IHp; simpl in IHp; rewrite IHp; intuition_in; order.
 intuition_in; order.
 rewrite e1 in IHp; simpl in IHp; rewrite IHp; intuition_in; order.
Qed.

Lemma split_in_3 : forall s x, bst s -> 
 ((split x s)#2#1 = true <-> In x s).
Proof. 
 intros s x; functional induction (split x s); subst; simpl; intros; 
  inv bst; try clear e0.
 intuition_in; try discriminate.
 rewrite e1 in IHp; simpl in IHp; rewrite IHp; intuition_in; order.
 intuition.
 rewrite e1 in IHp; simpl in IHp; rewrite IHp; intuition_in; order.
Qed.

Lemma split_bst : forall s x, bst s -> 
 bst (split x s)#1 /\ bst (split x s)#2#2.
Proof. 
 intros s x; functional induction (split x s); subst; simpl; intros; 
  inv bst; try clear e0; try rewrite e1 in *; simpl in *; intuition;
  apply join_bst; auto.
 intros y0.
 generalize (split_in_2 x y0 H0); rewrite e1; simpl; intuition.
 intros y0.
 generalize (split_in_1 x y0 H1); rewrite e1; simpl; intuition.
Qed.



(** * Intersection *)

Function inter (s1 s2 : t) { struct s1 } : t := match s1, s2 with 
    | Leaf, _ => Leaf
    | _, Leaf => Leaf
    | Node l1 x1 r1 h1, Node l2 x2 r2 h2 => 
            match split x1 s2 with
               | (l2',(true,r2')) => join (inter l1 l2') x1 (inter r1 r2')
               | (l2',(false,r2')) => concat (inter l1 l2') (inter r1 r2')
            end
    end.

Lemma inter_bst_in : forall s1 s2, bst s1 -> bst s2 -> 
 bst (inter s1 s2) /\ (forall y, In y (inter s1 s2) <-> In y s1 /\ In y s2).
Proof.
 intros s1 s2; functional induction inter s1 s2; intros B1 B2; 
 [intuition_in|intuition_in | | ]; 
 set (r:=Node l2 x2 r2 h2) in *; 
 generalize (split_bst x1 B2); 
  rewrite e1; simpl; destruct 1; inv bst; 
 destruct IHt as (IHb1,IHi1); auto; 
 destruct IHt0 as (IHb2,IHi2); auto; 
 destruct (distr_pair e1); clear e1;
 destruct (distr_pair H6); clear H6; split.
 (* bst join *)
 apply join_bst; auto; intro y; [rewrite IHi1|rewrite IHi2]; intuition.
 (* In join *)
 intros.
 rewrite join_in, IHi1, IHi2, <- H5, <- H8, split_in_1, split_in_2; auto.
 rewrite split_in_3 in H7; intuition_in.
 apply In_1 with x1; auto.
 (* bst concat *)
 apply concat_bst; auto; intros y1 y2; rewrite IHi1, IHi2; intuition; order.
 (* In concat *)
 intros.
 rewrite concat_in, IHi1, IHi2, <- H5, <- H8, split_in_1, split_in_2; auto.
 assert (~In x1 r) by (rewrite <- split_in_3, H7; auto).
 intuition_in.
 elim H6.
 apply In_1 with y; auto.
Qed.

Lemma inter_in : forall s1 s2 y, bst s1 -> bst s2 -> 
 (In y (inter s1 s2) <-> In y s1 /\ In y s2).
Proof. 
 intros s1 s2 y B1 B2; destruct (inter_bst_in B1 B2); auto.
Qed.

Lemma inter_bst : forall s1 s2, bst s1 -> bst s2 -> bst (inter s1 s2).
Proof. 
 intros s1 s2 B1 B2; destruct (inter_bst_in B1 B2); auto.
Qed.



(** * Difference *)

Function diff (s1 s2 : t) { struct s1 } : t := match s1, s2 with 
 | Leaf, _ => Leaf
 | _, Leaf => s1
 | Node l1 x1 r1 h1, Node l2 x2 r2 h2 => 
    match split x1 s2 with 
      | (l2',(true,r2')) => concat (diff l1 l2') (diff r1 r2')
      | (l2',(false,r2')) => join (diff l1 l2') x1 (diff r1 r2')
    end
end.

Lemma diff_bst_in : forall s1 s2, bst s1 -> bst s2 -> 
 bst (diff s1 s2) /\ (forall y, In y (diff s1 s2) <-> In y s1 /\ ~In y s2).
Proof.
 intros s1 s2; functional induction diff s1 s2; intros B1 B2; 
 [intuition_in|intuition_in | | ]; 
 set (r:=Node l2 x2 r2 h2) in *; 
 generalize (split_bst x1 B2); 
  rewrite e1; simpl; destruct 1; 
 inv avl; inv bst; 
 destruct IHt as (IHb1,IHi1); auto; 
 destruct IHt0 as (IHb2,IHi2); auto; 
 destruct (distr_pair e1); clear e1; 
 destruct (distr_pair H6); clear H6; split.
 (* bst concat *)
 apply concat_bst; auto; intros y1 y2; rewrite IHi1, IHi2; intuition; order.
 (* In concat *)
 intros.
 rewrite concat_in, IHi1, IHi2, <-H5, <- H8, split_in_1, split_in_2; auto.
 rewrite split_in_3 in H7; intuition_in.
 elim H10.
 apply In_1 with x1; auto.
 (* bst join *)
 apply join_bst; auto; intro y; [rewrite IHi1|rewrite IHi2]; intuition.
 (* In join *)
 intros.
 rewrite join_in, IHi1, IHi2, <-H5, <-H8, split_in_1, split_in_2; auto.
 assert (~In x1 r) by (rewrite <- split_in_3, H7; auto).
 intuition_in.
 elim H6.
 apply In_1 with y; auto.
Qed.

Lemma diff_in : forall s1 s2 y, bst s1 -> bst s2 -> 
 (In y (diff s1 s2) <-> In y s1 /\ ~In y s2).
Proof. 
 intros s1 s2 y B1 B2; destruct (diff_bst_in B1 B2); auto.
Qed.

Lemma diff_bst : forall s1 s2, bst s1 -> bst s2 -> bst (diff s1 s2). 
Proof. 
 intros s1 s2 B1 B2; destruct (diff_bst_in B1 B2); auto.
Qed.



(** * Union *)

(** In ocaml, heights of [s1] and [s2] are compared each time in order
   to recursively perform the split on the smaller set.
   Unfortunately, this leads to a non-structural algorithm. The
   following code is a simplification of the ocaml version: no
   comparison of heights. It might be slightly slower, but
   experimentally all the tests I've made in ocaml have shown this
   potential slowdown to be non-significant. Anyway, the exact code
   of ocaml has also been formalized thanks to Function+measure, see
   [ocaml_union] in [FSetFullAVL].  
*)

Function union (s1 s2 : t) { struct s1 } : t := 
 match s1, s2 with 
  | Leaf, _ => s2
  | Node _ _ _ _, Leaf => s1
  | Node l1 x1 r1 h1, Node l2 x2 r2 h2 => 
     let (l2',r2') := split x1 s2 in 
     join (union l1 l2') x1 (union r1 r2'#2)
 end.

Lemma union_in : forall s1 s2 y, bst s1 -> bst s2 -> 
 (In y (union s1 s2) <-> In y s1 \/ In y s2).
Proof.
 intros s1 s2; functional induction union s1 s2; intros y B1 B2.
 intuition_in.
 intuition_in.
 generalize (split_bst x1 B2) (split_in_1 x1 y B2) (split_in_2 x1 y B2).
 rewrite e1; simpl.
 destruct 1; inv bst.
 rewrite join_in, IHt, IHt0; auto.
 do 2 (intro Eq; rewrite Eq; clear Eq).
 case (X.compare y x1); intuition_in.
Qed.

Lemma union_bst : forall s1 s2, bst s1 -> bst s2 -> 
 bst (union s1 s2).
Proof.
 intros s1 s2; functional induction union s1 s2; intros B1 B2; auto.
 generalize (split_bst x1 B2) .
 inv bst.
 rewrite e1; simpl; destruct 1.
 destruct (distr_pair e1) as (L,R); clear e1.
 apply join_bst; auto.
 intro y; rewrite union_in; auto; simpl.
 rewrite <- L, split_in_1; auto; intuition_in.
 intro y; rewrite union_in; auto; simpl.
 rewrite <- R, split_in_2; auto; intuition_in.
Qed.



(** * Elements *)

(** [elements_tree_aux acc t] catenates the elements of [t] in infix
    order to the list [acc] *)

Fixpoint elements_aux (acc : list X.t) (t : tree) {struct t} : list X.t :=
  match t with
   | Leaf => acc
   | Node l x r _ => elements_aux (x :: elements_aux acc r) l
  end.

(** then [elements] is an instanciation with an empty [acc] *)

Definition elements := elements_aux nil.

Lemma elements_aux_in : forall s acc x, 
 InA X.eq x (elements_aux acc s) <-> In x s \/ InA X.eq x acc.
Proof.
 induction s as [ | l Hl x r Hr h ]; simpl; auto.
 intuition.
 inversion H0.
 intros.
 rewrite Hl.
 destruct (Hr acc x0); clear Hl Hr.
 intuition; inversion_clear H3; intuition.
Qed.

Lemma elements_in : forall s x, InA X.eq x (elements s) <-> In x s. 
Proof. 
 intros; generalize (elements_aux_in s nil x); intuition.
 inversion_clear H0.
Qed.

Lemma elements_aux_sort : forall s acc, bst s -> sort X.lt acc ->
 (forall x y : elt, InA X.eq x acc -> In y s -> X.lt y x) ->
 sort X.lt (elements_aux acc s).
Proof.
 induction s as [ | l Hl y r Hr h]; simpl; intuition.
 inv bst.
 apply Hl; auto.
 constructor. 
 apply Hr; auto.
 apply MX.In_Inf; intros.
 destruct (elements_aux_in r acc y0); intuition.
 intros.
 inversion_clear H.
 order.
 destruct (elements_aux_in r acc x); intuition eauto.
Qed.

Lemma elements_sort : forall s : tree, bst s -> sort X.lt (elements s).
Proof.
 intros; unfold elements; apply elements_aux_sort; auto.
 intros; inversion H0.
Qed.
Hint Resolve elements_sort.

Lemma elements_nodup : forall s : tree, bst s -> NoDupA X.eq (elements s).
Proof.
 auto.
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



(** * Filter *)

Section F.
Variable f : elt -> bool.

Fixpoint filter_acc (acc:t)(s:t) { struct s } : t := match s with 
  | Leaf => acc
  | Node l x r h => 
     filter_acc (filter_acc (if f x then add x acc else acc) l) r 
 end.

Definition filter := filter_acc Leaf. 

Lemma filter_acc_in : forall s acc, 
 compat_bool X.eq f -> forall x : elt, 
 In x (filter_acc acc s) <-> In x acc \/ In x s /\ f x = true.
Proof.  
 induction s; simpl; intros.
 intuition_in.
 rewrite IHs2, IHs1 by (destruct (f t); auto).
 case_eq (f t); intros.
 rewrite (add_in); auto.
 intuition_in.
 rewrite (H _ _ H2).
 intuition.
 intuition_in.
 rewrite (H _ _ H2) in H3.
 rewrite H0 in H3; discriminate.
Qed.

Lemma filter_acc_bst : forall s acc, bst s -> bst acc -> 
 bst (filter_acc acc s).
Proof.
 induction s; simpl; auto.
 intros.
 inv bst.
 destruct (f t); auto.
Qed.

Lemma filter_in : forall s,
 compat_bool X.eq f -> forall x : elt, 
 In x (filter s) <-> In x s /\ f x = true.
Proof.
 unfold filter; intros; rewrite filter_acc_in; intuition_in.
Qed.

Lemma filter_bst : forall s, bst s -> bst (filter s). 
Proof.
 unfold filter; intros; apply filter_acc_bst; auto.
Qed.



(** * Partition *)

Fixpoint partition_acc (acc : t*t)(s : t) { struct s } : t*t := 
  match s with 
   | Leaf => acc
   | Node l x r _ => 
      let (acct,accf) := acc in 
      partition_acc 
        (partition_acc 
           (if f x then (add x acct, accf) else (acct, add x accf)) l) r
  end. 

Definition partition := partition_acc (Leaf,Leaf).

Lemma partition_acc_in_1 : forall s acc, 
 compat_bool X.eq f -> forall x : elt, 
 In x (partition_acc acc s)#1 <-> 
 In x acc#1 \/ In x s /\ f x = true.
Proof.  
 induction s; simpl; intros.
 intuition_in.
 destruct acc as [acct accf]; simpl in *.
 rewrite IHs2 by 
  (destruct (f t); auto; apply partition_acc_avl_1; simpl; auto).
 rewrite IHs1 by (destruct (f t); simpl; auto).
 case_eq (f t); simpl; intros.
 rewrite (add_in); auto.
 intuition_in.
 rewrite (H _ _ H2).
 intuition.
 intuition_in.
 rewrite (H _ _ H2) in H3.
 rewrite H0 in H3; discriminate.
Qed.

Lemma partition_acc_in_2 : forall s acc, 
 compat_bool X.eq f -> forall x : elt, 
 In x (partition_acc acc s)#2 <-> 
 In x acc#2 \/ In x s /\ f x = false.
Proof.  
 induction s; simpl; intros.
 intuition_in.
 destruct acc as [acct accf]; simpl in *.
 rewrite IHs2 by 
  (destruct (f t); auto; apply partition_acc_avl_2; simpl; auto).
 rewrite IHs1 by (destruct (f t); simpl; auto).
 case_eq (f t); simpl; intros.
 intuition.
 intuition_in.
 rewrite (H _ _ H2) in H3.
 rewrite H0 in H3; discriminate.
 rewrite (add_in); auto.
 intuition_in.
 rewrite (H _ _ H2).
 intuition.
Qed.

Lemma partition_in_1 : forall s, 
 compat_bool X.eq f -> forall x : elt, 
 In x (partition s)#1 <-> In x s /\ f x = true.
Proof.
 unfold partition; intros; rewrite partition_acc_in_1; 
 simpl in *; intuition_in.
Qed. 

Lemma partition_in_2 : forall s,
 compat_bool X.eq f -> forall x : elt, 
 In x (partition s)#2 <-> In x s /\ f x = false.
Proof.
 unfold partition; intros; rewrite partition_acc_in_2; 
 simpl in *; intuition_in.
Qed. 

Lemma partition_acc_bst_1 : forall s acc, bst s -> bst acc#1 -> 
 bst (partition_acc acc s)#1.
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros.
 inv bst.
 destruct (f t); auto.
 apply IHs2; simpl; auto.
 apply IHs1; simpl; auto.
Qed.

Lemma partition_acc_bst_2 : forall s acc, bst s -> bst acc#2 -> 
 bst (partition_acc acc s)#2.
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros.
 inv bst.
 destruct (f t); auto.
 apply IHs2; simpl; auto.
 apply IHs1; simpl; auto.
Qed.

Lemma partition_bst_1 : forall s, bst s -> bst (partition s)#1. 
Proof.
 unfold partition; intros; apply partition_acc_bst_1; auto.
Qed.

Lemma partition_bst_2 : forall s, bst s -> bst (partition s)#2. 
Proof.
 unfold partition; intros; apply partition_acc_bst_2; auto.
Qed.



(** * [for_all] and [exists] *)

Fixpoint for_all (s:t) : bool := match s with 
  | Leaf => true
  | Node l x r _ => f x && for_all l && for_all r
end.

Lemma for_all_1 : forall s, compat_bool X.eq f ->
 For_all (fun x => f x = true) s -> for_all s = true.
Proof.
 induction s; simpl; auto.
 intros.
 rewrite IHs1; try red; auto.
 rewrite IHs2; try red; auto.
 generalize (H0 t).
 destruct (f t); simpl; auto.
Qed.

Lemma for_all_2 : forall s, compat_bool X.eq f ->
 for_all s = true -> For_all (fun x => f x = true) s.
Proof.
 induction s; simpl; auto; intros; red; intros; inv In.
 destruct (andb_prop _ _ H0); auto.
 destruct (andb_prop _ _ H1); eauto.
 apply IHs1; auto.
 destruct (andb_prop _ _ H0); auto.
 destruct (andb_prop _ _ H1); auto.
 apply IHs2; auto.
 destruct (andb_prop _ _ H0); auto.
Qed.

Fixpoint exists_ (s:t) : bool := match s with 
  | Leaf => false
  | Node l x r _ => f x || exists_ l || exists_ r
end.  

Lemma exists_1 : forall s, compat_bool X.eq f ->
 Exists (fun x => f x = true) s -> exists_ s = true.
Proof.
 induction s; simpl; destruct 2 as (x,(U,V)); inv In.
 rewrite (H _ _ (X.eq_sym H0)); rewrite V; auto.
 apply orb_true_intro; left.
 apply orb_true_intro; right; apply IHs1; auto; exists x; auto.
 apply orb_true_intro; right; apply IHs2; auto; exists x; auto.
Qed.

Lemma exists_2 : forall s, compat_bool X.eq f ->
 exists_ s = true -> Exists (fun x => f x = true) s.
Proof. 
 induction s; simpl; intros.
 discriminate.
 destruct (orb_true_elim _ _ H0) as [H1|H1]. 
 destruct (orb_true_elim _ _ H1) as [H2|H2].
 exists t; auto.
 destruct (IHs1 H H2); auto; exists x; intuition.
 destruct (IHs2 H H1); auto; exists x; intuition.
Qed.

End F.



(** * Fold *)

Module L := FSetList.Raw X.

Fixpoint fold (A : Type) (f : elt -> A -> A)(s : tree) {struct s} : A -> A := 
 fun a => match s with
  | Leaf => a
  | Node l x r _ => fold f r (f x (fold f l a))
 end.
Implicit Arguments fold [A].

Definition fold' (A : Type) (f : elt -> A -> A)(s : tree) := 
  L.fold f (elements s).
Implicit Arguments fold' [A].

Lemma fold_equiv_aux :
 forall (A : Type) (s : tree) (f : elt -> A -> A) (a : A) (acc : list elt),
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
 forall (A : Type) (s : tree) (f : elt -> A -> A) (a : A),
 fold f s a = fold' f s a.
Proof.
 unfold fold', elements in |- *. 
 simple induction s; simpl in |- *; auto; intros.
 rewrite fold_equiv_aux.
 rewrite H0.
 simpl in |- *; auto.
Qed.

Lemma fold_1 : 
 forall (s:t)(Hs:bst s)(A : Type)(f : elt -> A -> A)(i : A),
 fold f s i = fold_left (fun a e => f e a) (elements s) i.
Proof.
 intros.
 rewrite fold_equiv.
 unfold fold'.
 rewrite L.fold_1.
 unfold L.elements; auto.
 apply elements_sort; auto.
Qed.



(** * Subset *)

(** In ocaml, recursive calls are made on "half-trees" such as 
   (Node l1 x1 Leaf _) and (Node Leaf x1 r1 _). Instead of these
   non-structural calls, we propose here two specialized functions for
   these situations. This version should be almost as efficient as 
   the one of ocaml (closures as arguments may slow things a bit),  
   it is simply less compact. The exact ocaml version has also been
   formalized (thanks to Function+measure), see [ocaml_subset] in 
   [FSetFullAVL].
 *)

Fixpoint subsetl (subset_l1:t->bool) x1 s2 : bool := 
 match s2 with 
  | Leaf => false
  | Node l2 x2 r2 h2 => 
     match X.compare x1 x2 with 
      | EQ _ => subset_l1 l2 
      | LT _ => subsetl subset_l1 x1 l2
      | GT _ => mem x1 r2 && subset_l1 s2
     end
 end.

Fixpoint subsetr (subset_r1:t->bool) x1 s2 : bool := 
 match s2 with 
  | Leaf => false
  | Node l2 x2 r2 h2 => 
     match X.compare x1 x2 with 
      | EQ _ => subset_r1 r2 
      | LT _ => mem x1 l2 && subset_r1 s2
      | GT _ => subsetr subset_r1 x1 r2
     end
 end.

Fixpoint subset s1 s2 : bool := match s1, s2 with 
  | Leaf, _ => true
  | Node _ _ _ _, Leaf => false
  | Node l1 x1 r1 h1, Node l2 x2 r2 h2 => 
     match X.compare x1 x2 with 
      | EQ _ => subset l1 l2 && subset r1 r2
      | LT _ => subsetl (subset l1) x1 l2 && subset r1 s2
      | GT _ => subsetr (subset r1) x1 r2 && subset l1 s2
     end
 end.

Lemma subsetl_12 : forall subset_l1 l1 x1 h1 s2,
 bst (Node l1 x1 Leaf h1) -> bst s2 ->
 (forall s, bst s -> (subset_l1 s = true <-> Subset l1 s)) -> 
 (subsetl subset_l1 x1 s2 = true <-> Subset (Node l1 x1 Leaf h1) s2 ).
Proof.
 induction s2 as [|l2 IHl2 x2 r2 IHr2 h2]; simpl; intros.
 unfold Subset; intuition; try discriminate.
 assert (H': In x1 Leaf) by auto; inversion H'.
 inversion_clear H0.
 specialize (IHl2 H H2 H1).
 specialize (IHr2 H H3 H1).
 inv bst. clear H8.
 destruct X.compare.
 
 rewrite IHl2; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

 rewrite H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (X.eq a x2) by order; intuition_in.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

 rewrite andb_true_iff, H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (H':=mem_2 H6); apply In_1 with x1; auto.
 apply mem_1; auto.
 assert (In x1 (Node l2 x2 r2 h2)) by auto; intuition_in; order.
Qed.


Lemma subsetr_12 : forall subset_r1 r1 x1 h1 s2,
 bst (Node Leaf x1 r1 h1) -> bst s2 ->
 (forall s, bst s -> (subset_r1 s = true <-> Subset r1 s)) -> 
 (subsetr subset_r1 x1 s2 = true <-> Subset (Node Leaf x1 r1 h1) s2).
Proof.
 induction s2 as [|l2 IHl2 x2 r2 IHr2 h2]; simpl; intros.
 unfold Subset; intuition; try discriminate.
 assert (H': In x1 Leaf) by auto; inversion H'.
 inversion_clear H0.
 specialize (IHl2 H H2 H1).
 specialize (IHr2 H H3 H1).
 inv bst. clear H7.
 destruct X.compare.

 rewrite andb_true_iff, H1 by auto;  clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (H':=mem_2 H1); apply In_1 with x1; auto.
 apply mem_1; auto.
 assert (In x1 (Node l2 x2 r2 h2)) by auto; intuition_in; order.

 rewrite H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (X.eq a x2) by order; intuition_in.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 
 rewrite IHr2; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
Qed.


Lemma subset_12 : forall s1 s2, bst s1 -> bst s2 -> 
 (subset s1 s2 = true <-> Subset s1 s2).
Proof.
 induction s1 as [|l1 IHl1 x1 r1 IHr1 h1]; simpl; intros.
 unfold Subset; intuition_in.
 destruct s2 as [|l2 x2 r2 h2]; simpl; intros.
 unfold Subset; intuition_in; try discriminate.
 assert (H': In x1 Leaf) by auto; inversion H'.
 inv bst.
 destruct X.compare.

 rewrite andb_true_iff, IHr1 by auto.
 rewrite (@subsetl_12 (subset l1) l1 x1 h1) by auto.
 clear IHl1 IHr1.
 unfold Subset; intuition_in.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.

 rewrite andb_true_iff, IHl1, IHr1 by auto.
 clear IHl1 IHr1.
 unfold Subset; intuition_in.
 assert (X.eq a x2) by order; intuition_in.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 
 rewrite andb_true_iff, IHl1 by auto.
 rewrite (@subsetr_12 (subset r1) r1 x1 h1) by auto.
 clear IHl1 IHr1.
 unfold Subset; intuition_in.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
Qed.



(** * Comparison *)

(** ** Relations [eq] and [lt] over trees *)

Lemma eq_refl : forall s : t, Equal s s. 
Proof.
 unfold Equal; intuition.
Qed.

Lemma eq_sym : forall s s' : t, Equal s s' -> Equal s' s.
Proof.
 unfold Equal; intros s s' H x; destruct (H x); split; auto.
Qed.

Lemma eq_trans : forall s s' s'' : t, 
 Equal s s' -> Equal s' s'' -> Equal s s''.
Proof.
 unfold Equal; intros s s' s'' H1 H2 x; 
 destruct (H1 x); destruct (H2 x); split; auto.
Qed.

Lemma eq_L_eq :
 forall s s' : t, Equal s s' -> L.eq (elements s) (elements s').
Proof.
 unfold Equal, L.eq, L.Equal; intros; do 2 rewrite elements_in; auto.
Qed.

Lemma L_eq_eq :
 forall s s' : t, L.eq (elements s) (elements s') -> Equal s s'.
Proof.
 unfold Equal, L.eq, L.Equal; intros; do 2 rewrite <-elements_in; auto.
Qed.
Hint Resolve eq_L_eq L_eq_eq.

Definition lt (s1 s2 : t) : Prop := L.lt (elements s1) (elements s2).

Definition lt_trans (s s' s'' : t) (h : lt s s') 
  (h' : lt s' s'') : lt s s'' := L.lt_trans h h'.

Lemma lt_not_eq : forall s s' : t, 
 bst s -> bst s' -> lt s s' -> ~ Equal s s'.
Proof.
 unfold lt in |- *; intros; intro.
 apply L.lt_not_eq with (s := elements s) (s' := elements s'); auto.
Qed.

Lemma L_eq_cons :
 forall (l1 l2 : list elt) (x y : elt),
 X.eq x y -> L.eq l1 l2 -> L.eq (x :: l1) (y :: l2).
Proof.
 unfold L.eq, L.Equal in |- *; intuition.
 inversion_clear H1; generalize (H0 a); clear H0; intuition.
 apply InA_eqA with x; eauto.
 inversion_clear H1; generalize (H0 a); clear H0; intuition.
 apply InA_eqA with y; eauto.
Qed.
Hint Resolve L_eq_cons.


(** * A new comparison algorithm suggested by Xavier Leroy

    Transformation in C.P.S. suggested by Benjamin Grégoire.
    The original ocaml code (with non-structural recursive calls)
    has also been formalized (thanks to Function+measure), see
    [ocaml_compare] in [FSetFullAVL]. The following code with 
    continuations computes dramatically faster in Coq, and 
    should be almost as efficient after extraction.
*)

(** ** Enumeration of the elements of a tree *)

Inductive enumeration :=
 | End : enumeration
 | More : elt -> tree -> enumeration -> enumeration.

(** [flatten_e e] returns the list of elements of [e] i.e. the list
    of elements actually compared *)
 
Fixpoint flatten_e (e : enumeration) : list elt := match e with
  | End => nil
  | More x t r => x :: elements t ++ flatten_e r
 end.

(** [sorted_e e] expresses that elements in the enumeration [e] are
    sorted, and that all trees in [e] are binary search trees. *)

Inductive In_e (x:elt) : enumeration -> Prop :=
  | InEHd1 :
      forall (y : elt) (s : tree) (e : enumeration),
      X.eq x y -> In_e x (More y s e)
  | InEHd2 :
      forall (y : elt) (s : tree) (e : enumeration),
      In x s -> In_e x (More y s e)
  | InETl :
      forall (y : elt) (s : tree) (e : enumeration),
      In_e x e -> In_e x (More y s e).

Hint Constructors In_e.

Lemma elements_app :
 forall s acc, elements_aux acc s = elements s ++ acc.
Proof.
 induction s; simpl; intuition.
 rewrite IHs1, IHs2.
 unfold elements; simpl.
 rewrite 2 IHs1, IHs2, <- !app_nil_end, !app_ass; auto.
Qed.

Lemma compare_flatten_1 :
 forall l x r h acc,
 elements l ++ x :: elements r ++ acc =
 elements (Node l x r h) ++ acc.
Proof.
 unfold elements; simpl; intuition.
 rewrite !elements_app, <- !app_nil_end, !app_ass; auto.
Qed.

(** key lemma for correctness *)

Lemma flatten_e_elements :
 forall l x r h e,
 elements l ++ flatten_e (More x r e) = elements (Node l x r h) ++ flatten_e e.
Proof.
 intros; simpl; apply compare_flatten_1.
Qed.

(** [cons t e] adds the elements of tree [t] on the head of 
    enumeration [e]. *)

Fixpoint cons s e : enumeration := 
 match s with 
  | Leaf => e
  | Node l x r h => cons l (More x r e)
 end.

Lemma cons_1 : forall s e, 
  flatten_e (cons s e) = elements s ++ flatten_e e.
Proof.
 induction s; simpl; auto; intros.
 rewrite IHs1; apply flatten_e_elements.
Qed.

(** One step of comparison of elements *)

Definition compare_more x1 (cont:enumeration->comparison) e2 :=
 match e2 with
 | End => Gt
 | More x2 r2 e2 =>
     match X.compare x1 x2 with
      | EQ _ => cont (cons r2 e2)
      | LT _ => Lt
      | GT _ => Gt
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

(** Correctness of this comparison *)

Definition Cmp c := 
 match c with 
  | Eq => L.eq
  | Lt => L.lt
  | Gt => (fun l1 l2 => L.lt l2 l1)
 end.

Lemma cons_Cmp : forall c x1 x2 l1 l2, X.eq x1 x2 ->
 Cmp c l1 l2 -> Cmp c (x1::l1) (x2::l2). 
Proof.
 destruct c; simpl; auto.
Qed.
Hint Resolve cons_Cmp.

Lemma compare_end_Cmp : 
 forall e2, Cmp (compare_end e2) nil (flatten_e e2).
Proof.
 destruct e2; simpl; auto.
 apply L.eq_refl.
Qed.

Lemma compare_more_Cmp : forall x1 cont x2 r2 e2 l, 
  Cmp (cont (cons r2 e2)) l (elements r2 ++ flatten_e e2) -> 
   Cmp (compare_more x1 cont (More x2 r2 e2)) (x1::l) 
      (flatten_e (More x2 r2 e2)).
Proof.
 simpl; intros; destruct X.compare; simpl; auto.
Qed.

Lemma compare_cont_Cmp : forall s1 cont e2 l,
 (forall e, Cmp (cont e) l (flatten_e e)) -> 
 Cmp (compare_cont s1 cont e2) (elements s1 ++ l) (flatten_e e2).
Proof.
 induction s1 as [|l1 Hl1 x1 r1 Hr1 h1]; simpl; intros; auto.
 inv bst.
 rewrite <- compare_flatten_1; simpl.
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

(** * Equality test *)

Definition equal s1 s2 : bool := 
 match compare s1 s2 with 
  | Eq => true
  | _ => false 
 end.

Lemma equal_1 : forall s1 s2, bst s1 -> bst s2 ->  
 Equal s1 s2 -> equal s1 s2 = true.
Proof.
unfold equal; intros s1 s2 B1 B2 E.
generalize (compare_Cmp s1 s2). 
destruct (compare s1 s2); simpl in *; auto; intros.
elim (lt_not_eq B1 B2 H E); auto.
elim (lt_not_eq B2 B1 H (eq_sym E)); auto.
Qed.

Lemma equal_2 : forall s1 s2,  
 equal s1 s2 = true -> Equal s1 s2.
Proof.
unfold equal; intros s1 s2 E.
generalize (compare_Cmp s1 s2); 
 destruct compare; auto; discriminate.
Qed.

End Raw.



(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we 
   need to encapsulate everything into a type of binary search trees. 
   They also happen to be well-balanced, but this has no influence 
   on the correctness of operations, so we won't state this here, 
   see [FSetFullAVL] if you need more than just the FSet interface.
*)

Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.

 Module E := X.
 Module Raw := Raw I X.

 Record bst := Bst {this :> Raw.t; is_bst : Raw.bst this}.
 Definition t := bst.
 Definition elt := E.t.
 
 Definition In (x : elt) (s : t) := Raw.In x s.
 Definition Equal (s s':t) := forall a : elt, In a s <-> In a s'.
 Definition Subset (s s':t) := forall a : elt, In a s -> In a s'.
 Definition Empty (s:t) := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop) (s:t) := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop) (s:t) := exists x, In x s /\ P x.

 Lemma In_1 : forall (s:t)(x y:elt), E.eq x y -> In x s -> In y s. 
 Proof. intro s; exact (@Raw.In_1 s). Qed.
 
 Definition mem (x:elt)(s:t) : bool := Raw.mem x s.

 Definition empty : t := Bst Raw.empty_bst.
 Definition is_empty (s:t) : bool := Raw.is_empty s.
 Definition singleton (x:elt) : t := Bst (Raw.singleton_bst x).
 Definition add (x:elt)(s:t) : t := Bst (Raw.add_bst x (is_bst s)). 
 Definition remove (x:elt)(s:t) : t := Bst (Raw.remove_bst x (is_bst s)).
 Definition inter (s s':t) : t := Bst (Raw.inter_bst (is_bst s) (is_bst s')).
 Definition union (s s':t) : t := Bst (Raw.union_bst (is_bst s) (is_bst s')).
 Definition diff (s s':t) : t := Bst (Raw.diff_bst (is_bst s) (is_bst s')).
 Definition elements (s:t) : list elt := Raw.elements s.
 Definition min_elt (s:t) : option elt := Raw.min_elt s.
 Definition max_elt (s:t) : option elt := Raw.max_elt s.
 Definition choose (s:t) : option elt := Raw.choose s.
 Definition fold (B : Type) (f : elt -> B -> B) (s:t) : B -> B := Raw.fold f s.
 Definition cardinal (s:t) : nat := Raw.cardinal s.
 Definition filter (f : elt -> bool) (s:t) : t := 
   Bst (Raw.filter_bst f (is_bst s)).
 Definition for_all (f : elt -> bool) (s:t) : bool := Raw.for_all f s.
 Definition exists_ (f : elt -> bool) (s:t) : bool := Raw.exists_ f s.
 Definition partition (f : elt -> bool) (s:t) : t * t :=
   let p := Raw.partition f s in
   (@Bst (fst p) (Raw.partition_bst_1 f (is_bst s)), 
    @Bst (snd p) (Raw.partition_bst_2 f (is_bst s))).

 Definition equal (s s':t) : bool := Raw.equal s s'.
 Definition subset (s s':t) : bool := Raw.subset s s'.

 Definition eq (s s':t) : Prop := Raw.Equal s s'.
 Definition lt (s s':t) : Prop := Raw.lt s s'.

 Definition compare (s s':t) : Compare lt eq s s'.
 Proof.
  intros (s,b) (s',b').
  generalize (Raw.compare_Cmp s s').
  destruct Raw.compare; intros; [apply EQ|apply LT|apply GT]; red; auto.
 Defined.

 (* specs *)
 Section Specs. 
 Variable s s' s'': t. 
 Variable x y : elt.

 Hint Resolve is_bst.
 
 Lemma mem_1 : In x s -> mem x s = true. 
 Proof. exact (Raw.mem_1 (is_bst s)). Qed.
 Lemma mem_2 : mem x s = true -> In x s.
 Proof. exact (@Raw.mem_2 s x). Qed.

 Lemma equal_1 : Equal s s' -> equal s s' = true.
 Proof. exact (Raw.equal_1 (is_bst s) (is_bst s')). Qed.
 Lemma equal_2 : equal s s' = true -> Equal s s'.
 Proof. exact (@Raw.equal_2 s s'). Qed.

 Ltac wrap t H := unfold t, In; simpl; rewrite H; auto; intuition.

 Lemma subset_1 : Subset s s' -> subset s s' = true.
 Proof. wrap subset Raw.subset_12. Qed.
 Lemma subset_2 : subset s s' = true -> Subset s s'.
 Proof. wrap subset Raw.subset_12. Qed.

 Lemma empty_1 : Empty empty.
 Proof. exact Raw.empty_1. Qed.

 Lemma is_empty_1 : Empty s -> is_empty s = true.
 Proof. exact (@Raw.is_empty_1 s). Qed.
 Lemma is_empty_2 : is_empty s = true -> Empty s. 
 Proof. exact (@Raw.is_empty_2 s). Qed.
 
 Lemma add_1 : E.eq x y -> In y (add x s).
 Proof. wrap add Raw.add_in. Qed.
 Lemma add_2 : In y s -> In y (add x s).
 Proof. wrap add Raw.add_in. Qed.
 Lemma add_3 : ~ E.eq x y -> In y (add x s) -> In y s. 
 Proof. wrap add Raw.add_in. elim H; auto. Qed.

 Lemma remove_1 : E.eq x y -> ~ In y (remove x s).
 Proof. wrap remove Raw.remove_in. Qed.
 Lemma remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
 Proof. wrap remove Raw.remove_in. Qed.
 Lemma remove_3 : In y (remove x s) -> In y s.
 Proof. wrap remove Raw.remove_in. Qed.

 Lemma singleton_1 : In y (singleton x) -> E.eq x y. 
 Proof. exact (@Raw.singleton_1 x y). Qed.
 Lemma singleton_2 : E.eq x y -> In y (singleton x). 
 Proof. exact (@Raw.singleton_2 x y). Qed.

 Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
 Proof. wrap union Raw.union_in. Qed.
 Lemma union_2 : In x s -> In x (union s s'). 
 Proof. wrap union Raw.union_in. Qed.
 Lemma union_3 : In x s' -> In x (union s s').
 Proof. wrap union Raw.union_in. Qed.

 Lemma inter_1 : In x (inter s s') -> In x s.
 Proof. wrap inter Raw.inter_in. Qed.
 Lemma inter_2 : In x (inter s s') -> In x s'.
 Proof. wrap inter Raw.inter_in. Qed.
 Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
 Proof. wrap inter Raw.inter_in. Qed.
 
 Lemma diff_1 : In x (diff s s') -> In x s. 
 Proof. wrap diff Raw.diff_in. Qed.
 Lemma diff_2 : In x (diff s s') -> ~ In x s'.
 Proof. wrap diff Raw.diff_in. Qed.
 Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
 Proof. wrap diff Raw.diff_in. Qed.
 
 Lemma fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.
 Proof. 
 unfold fold, elements; intros; apply Raw.fold_1; auto.
 Qed.

 Lemma cardinal_1 : cardinal s = length (elements s).
 Proof. 
 unfold cardinal, elements; intros; apply Raw.elements_cardinal; auto.
 Qed.

 Section Filter.
 Variable f : elt -> bool.

 Lemma filter_1 : compat_bool E.eq f -> In x (filter f s) -> In x s. 
 Proof. intro. wrap filter Raw.filter_in. Qed.
 Lemma filter_2 : compat_bool E.eq f -> In x (filter f s) -> f x = true. 
 Proof. intro. wrap filter Raw.filter_in. Qed. 
 Lemma filter_3 : compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).
 Proof. intro. wrap filter Raw.filter_in. Qed.

 Lemma for_all_1 : compat_bool E.eq f -> For_all (fun x => f x = true) s -> for_all f s = true.
 Proof. exact (@Raw.for_all_1 f s). Qed.
 Lemma for_all_2 : compat_bool E.eq f -> for_all f s = true -> For_all (fun x => f x = true) s.
 Proof. exact (@Raw.for_all_2 f s). Qed.

 Lemma exists_1 : compat_bool E.eq f -> Exists (fun x => f x = true) s -> exists_ f s = true.
 Proof. exact (@Raw.exists_1 f s). Qed.
 Lemma exists_2 : compat_bool E.eq f -> exists_ f s = true -> Exists (fun x => f x = true) s.
 Proof. exact (@Raw.exists_2 f s). Qed.

 Lemma partition_1 : compat_bool E.eq f -> 
  Equal (fst (partition f s)) (filter f s).
 Proof.
 unfold partition, filter, Equal, In; simpl ;intros H a.
 rewrite Raw.partition_in_1, Raw.filter_in; intuition.
 Qed.

 Lemma partition_2 : compat_bool E.eq f -> 
  Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
 Proof.
 unfold partition, filter, Equal, In; simpl ;intros H a.
 rewrite Raw.partition_in_2, Raw.filter_in; intuition.
 rewrite H2; auto.
 destruct (f a); auto.
 red; intros; f_equal.
 rewrite (H _ _ H0); auto.
 Qed.

 End Filter.

 Lemma elements_1 : In x s -> InA E.eq x (elements s).
 Proof. wrap elements Raw.elements_in. Qed.
 Lemma elements_2 : InA E.eq x (elements s) -> In x s.
 Proof. wrap elements Raw.elements_in. Qed.
 Lemma elements_3 : sort E.lt (elements s).
 Proof. exact (Raw.elements_sort (is_bst s)). Qed.
 Lemma elements_3w : NoDupA E.eq (elements s).
 Proof. exact (Raw.elements_nodup (is_bst s)). Qed.

 Lemma min_elt_1 : min_elt s = Some x -> In x s. 
 Proof. exact (@Raw.min_elt_1 s x). Qed.
 Lemma min_elt_2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
 Proof. exact (@Raw.min_elt_2 s x y (is_bst s)). Qed.
 Lemma min_elt_3 : min_elt s = None -> Empty s.
 Proof. exact (@Raw.min_elt_3 s). Qed.

 Lemma max_elt_1 : max_elt s = Some x -> In x s. 
 Proof. exact (@Raw.max_elt_1 s x). Qed.
 Lemma max_elt_2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
 Proof. exact (@Raw.max_elt_2 s x y (is_bst s)). Qed.
 Lemma max_elt_3 : max_elt s = None -> Empty s.
 Proof. exact (@Raw.max_elt_3 s). Qed.

 Lemma choose_1 : choose s = Some x -> In x s.
 Proof. exact (@Raw.choose_1 s x). Qed.
 Lemma choose_2 : choose s = None -> Empty s.
 Proof. exact (@Raw.choose_2 s). Qed.
 Lemma choose_3 : choose s = Some x -> choose s' = Some y -> 
  Equal s s' -> E.eq x y.
 Proof. exact (@Raw.choose_3 _ _ (is_bst s) (is_bst s') x y). Qed.

 Lemma eq_refl : eq s s. 
 Proof. exact (Raw.eq_refl s). Qed.
 Lemma eq_sym : eq s s' -> eq s' s.
 Proof. exact (@Raw.eq_sym s s'). Qed.
 Lemma eq_trans : eq s s' -> eq s' s'' -> eq s s''.
 Proof. exact (@Raw.eq_trans s s' s''). Qed.
  
 Lemma lt_trans : lt s s' -> lt s' s'' -> lt s s''.
 Proof. exact (@Raw.lt_trans s s' s''). Qed.
 Lemma lt_not_eq : lt s s' -> ~eq s s'.
 Proof. exact (@Raw.lt_not_eq _ _ (is_bst s) (is_bst s')). Qed.

 End Specs.
End IntMake.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (X: OrderedType) <: S with Module E := X
 :=IntMake(Z_as_Int)(X).


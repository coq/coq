(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * MSetGenTree : sets via generic trees

    This module factorizes common parts in implementations
    of finite sets as AVL trees and as Red-Black trees. The nodes
    of the trees defined here include an generic information
    parameter, that will be the height in AVL trees and the color
    in Red-Black trees. Without more details here about these
    information parameters, trees here are not known to be
    well-balanced, but simply binary-search-trees.

    The operations we could define and prove correct here are the
    one that do not build non-empty trees, but only analyze them :

     - empty is_empty
     - mem
     - compare equal subset
     - fold cardinal elements
     - for_all exists_
     - min_elt max_elt choose
*)

Require Import FunInd Orders OrdersFacts MSetInterface PeanoNat.
Local Open Scope list_scope.
Local Open Scope lazy_bool_scope.

(* For nicer extraction, we create induction principles
   only when needed *)
Local Unset Elimination Schemes.

Module Type InfoTyp.
 Parameter t : Set.
End InfoTyp.

(** * Ops : the pure functions *)

Module Type Ops (X:OrderedType)(Info:InfoTyp).

Definition elt := X.t.
Hint Transparent elt.

Inductive tree  : Type :=
| Leaf : tree
| Node : Info.t -> tree -> X.t -> tree -> tree.

(** ** The empty set and emptyness test *)

Definition empty := Leaf.

Definition is_empty t :=
 match t with
 | Leaf => true
 | _ => false
 end.

(** ** Membership test *)

(** The [mem] function is deciding membership. It exploits the
    binary search tree invariant to achieve logarithmic complexity. *)

Fixpoint mem x t :=
 match t with
 | Leaf => false
 | Node _ l k r =>
   match X.compare x k with
     | Lt => mem x l
     | Eq => true
     | Gt => mem x r
   end
 end.

(** ** Minimal, maximal, arbitrary elements *)

Fixpoint min_elt (t : tree) : option elt :=
 match t with
 | Leaf => None
 | Node _ Leaf x r => Some x
 | Node _ l x r => min_elt l
 end.

Fixpoint max_elt (t : tree) : option elt :=
  match t with
  | Leaf => None
  | Node _ l x Leaf => Some x
  | Node _ l x r => max_elt r
  end.

Definition choose := min_elt.

(** ** Iteration on elements *)

Fixpoint fold {A: Type} (f: elt -> A -> A) (t: tree) (base: A) : A :=
  match t with
  | Leaf => base
  | Node _ l x r => fold f r (f x (fold f l base))
 end.

Fixpoint elements_aux acc s :=
  match s with
   | Leaf => acc
   | Node _ l x r => elements_aux (x :: elements_aux acc r) l
  end.

Definition elements := elements_aux nil.

Fixpoint rev_elements_aux acc s :=
  match s with
   | Leaf => acc
   | Node _ l x r => rev_elements_aux (x :: rev_elements_aux acc l) r
  end.

Definition rev_elements := rev_elements_aux nil.

Fixpoint cardinal (s : tree) : nat :=
  match s with
   | Leaf => 0
   | Node _ l _ r => S (cardinal l + cardinal r)
  end.

Fixpoint maxdepth s :=
 match s with
 | Leaf => 0
 | Node _ l _ r => S (max (maxdepth l) (maxdepth r))
 end.

Fixpoint mindepth s :=
 match s with
 | Leaf => 0
 | Node _ l _ r => S (min (mindepth l) (mindepth r))
 end.

(** ** Testing universal or existential properties. *)

(** We do not use the standard boolean operators of Coq,
    but lazy ones. *)

Fixpoint for_all (f:elt->bool) s := match s with
  | Leaf => true
  | Node _ l x r => f x &&& for_all f l &&& for_all f r
end.

Fixpoint exists_ (f:elt->bool) s := match s with
  | Leaf => false
  | Node _ l x r => f x ||| exists_ f l ||| exists_ f r
end.

(** ** Comparison of trees *)

(** The algorithm here has been suggested by Xavier Leroy,
    and transformed into c.p.s. by Benjamin Grégoire.
    The original ocaml code (with non-structural recursive calls)
    has also been formalized (thanks to Function+measure), see
    [ocaml_compare] in [MSetFullAVL]. The following code with
    continuations computes dramatically faster in Coq, and
    should be almost as efficient after extraction.
*)

(** Enumeration of the elements of a tree. This corresponds
    to the "samefringe" notion in the litterature. *)

Inductive enumeration :=
 | End : enumeration
 | More : elt -> tree -> enumeration -> enumeration.


(** [cons t e] adds the elements of tree [t] on the head of
    enumeration [e]. *)

Fixpoint cons s e : enumeration :=
 match s with
  | Leaf => e
  | Node _ l x r => cons l (More x r e)
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
  | Node _ l1 x1 r1 =>
     compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2
  end.

(** Initial continuation *)

Definition compare_end e2 :=
 match e2 with End => Eq | _ => Lt end.

(** The complete comparison *)

Definition compare s1 s2 := compare_cont s1 compare_end (cons s2 End).

Definition equal s1 s2 :=
 match compare s1 s2 with Eq => true | _ => false end.

(** ** Subset test *)

(** In ocaml, recursive calls are made on "half-trees" such as
   (Node _ l1 x1 Leaf) and (Node _ Leaf x1 r1). Instead of these
   non-structural calls, we propose here two specialized functions
   for these situations. This version should be almost as efficient
   as the one of ocaml (closures as arguments may slow things a bit),
   it is simply less compact. The exact ocaml version has also been
   formalized (thanks to Function+measure), see [ocaml_subset] in
   [MSetFullAVL].
*)

Fixpoint subsetl (subset_l1 : tree -> bool) x1 s2 : bool :=
 match s2 with
  | Leaf => false
  | Node _ l2 x2 r2 =>
     match X.compare x1 x2 with
      | Eq => subset_l1 l2
      | Lt => subsetl subset_l1 x1 l2
      | Gt => mem x1 r2 &&& subset_l1 s2
     end
 end.

Fixpoint subsetr (subset_r1 : tree -> bool) x1 s2 : bool :=
 match s2 with
  | Leaf => false
  | Node _ l2 x2 r2 =>
     match X.compare x1 x2 with
      | Eq => subset_r1 r2
      | Lt => mem x1 l2 &&& subset_r1 s2
      | Gt => subsetr subset_r1 x1 r2
     end
 end.

Fixpoint subset s1 s2 : bool := match s1, s2 with
  | Leaf, _ => true
  | Node _ _ _ _, Leaf => false
  | Node _ l1 x1 r1, Node _ l2 x2 r2 =>
     match X.compare x1 x2 with
      | Eq => subset l1 l2 &&& subset r1 r2
      | Lt => subsetl (subset l1) x1 l2 &&& subset r1 s2
      | Gt => subsetr (subset r1) x1 r2 &&& subset l1 s2
     end
 end.

End Ops.

(** * Props : correctness proofs of these generic operations *)

Module Type Props (X:OrderedType)(Info:InfoTyp)(Import M:Ops X Info).

(** ** Occurrence in a tree *)

Inductive InT (x : elt) : tree -> Prop :=
  | IsRoot : forall c l r y, X.eq x y -> InT x (Node c l y r)
  | InLeft : forall c l r y, InT x l -> InT x (Node c l y r)
  | InRight : forall c l r y, InT x r -> InT x (Node c l y r).

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
  | BSNode : forall c x l r, bst l -> bst r ->
     lt_tree x l -> gt_tree x r -> bst (Node c l x r).

(** [bst] is the (decidable) invariant our trees will have to satisfy. *)

Definition IsOk := bst.

Class Ok (s:tree) : Prop := ok : bst s.

Instance bst_Ok s (Hs : bst s) : Ok s := { ok := Hs }.

Fixpoint ltb_tree x s :=
 match s with
  | Leaf => true
  | Node _ l y r =>
     match X.compare x y with
      | Gt => ltb_tree x l && ltb_tree x r
      | _ => false
     end
 end.

Fixpoint gtb_tree x s :=
 match s with
  | Leaf => true
  | Node _ l y r =>
     match X.compare x y with
      | Lt => gtb_tree x l && gtb_tree x r
      | _ => false
     end
 end.

Fixpoint isok s :=
 match s with
  | Leaf => true
  | Node _  l x r => isok l && isok r && ltb_tree x l && gtb_tree x r
 end.


(** ** Known facts about ordered types *)

Module Import MX := OrderedTypeFacts X.

(** ** Automation and dedicated tactics *)

Scheme tree_ind := Induction for tree Sort Prop.
Scheme bst_ind := Induction for bst Sort Prop.

Local Hint Resolve MX.eq_refl MX.eq_trans MX.lt_trans ok.
Local Hint Immediate MX.eq_sym.
Local Hint Unfold In lt_tree gt_tree.
Local Hint Constructors InT bst.
Local Hint Unfold Ok.

(** Automatic treatment of [Ok] hypothesis *)

Ltac clear_inversion H := inversion H; clear H; subst.

Ltac inv_ok := match goal with
 | H:Ok (Node _ _ _ _) |- _ => clear_inversion H; inv_ok
 | H:Ok Leaf |- _ => clear H; inv_ok
 | H:bst ?x |- _ => change (Ok x) in H; inv_ok
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
     | H:f ?s |- _ => is_tree_constr s; clear_inversion H; invtree f
     | H:f _ ?s |- _ => is_tree_constr s; clear_inversion H; invtree f
     | H:f _ _ ?s |- _ => is_tree_constr s; clear_inversion H; invtree f
     | _ => idtac
  end.

Ltac inv := inv_ok; invtree InT.

Ltac intuition_in := repeat (intuition; inv).

(** Helper tactic concerning order of elements. *)

Ltac order := match goal with
 | U: lt_tree _ ?s, V: InT _ ?s |- _ => generalize (U _ V); clear U; order
 | U: gt_tree _ ?s, V: InT _ ?s |- _ => generalize (U _ V); clear U; order
 | _ => MX.order
end.


(** [isok] is indeed a decision procedure for [Ok] *)

Lemma ltb_tree_iff : forall x s, lt_tree x s <-> ltb_tree x s = true.
Proof.
 induction s as [|c l IHl y r IHr]; simpl.
 unfold lt_tree; intuition_in.
 elim_compare x y.
 split; intros; try discriminate. assert (X.lt y x) by auto. order.
 split; intros; try discriminate. assert (X.lt y x) by auto. order.
 rewrite !andb_true_iff, <-IHl, <-IHr.
  unfold lt_tree; intuition_in; order.
Qed.

Lemma gtb_tree_iff : forall x s, gt_tree x s <-> gtb_tree x s = true.
Proof.
 induction s as [|c l IHl y r IHr]; simpl.
 unfold gt_tree; intuition_in.
 elim_compare x y.
 split; intros; try discriminate. assert (X.lt x y) by auto. order.
 rewrite !andb_true_iff, <-IHl, <-IHr.
  unfold gt_tree; intuition_in; order.
 split; intros; try discriminate. assert (X.lt x y) by auto. order.
Qed.

Lemma isok_iff : forall s, Ok s <-> isok s = true.
Proof.
 induction s as [|c l IHl y r IHr]; simpl.
 intuition_in.
 rewrite !andb_true_iff, <- IHl, <-IHr, <- ltb_tree_iff, <- gtb_tree_iff.
 intuition_in.
Qed.

Instance isok_Ok s : isok s = true -> Ok s | 10.
Proof. intros; apply <- isok_iff; auto. Qed.

(** ** Basic results about [In] *)

Lemma In_1 :
 forall s x y, X.eq x y -> InT x s -> InT y s.
Proof.
 induction s; simpl; intuition_in; eauto.
Qed.
Local Hint Immediate In_1.

Instance In_compat : Proper (X.eq==>eq==>iff) InT.
Proof.
apply proper_sym_impl_iff_2; auto with *.
repeat red; intros; subst. apply In_1 with x; auto.
Qed.

Lemma In_node_iff :
 forall c l x r y,
  InT y (Node c l x r) <-> InT y l \/ X.eq y x \/ InT y r.
Proof.
 intuition_in.
Qed.

Lemma In_leaf_iff : forall x, InT x Leaf <-> False.
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
 forall (x y : elt) (l r : tree) (i : Info.t),
 lt_tree x l -> lt_tree x r -> X.lt y x -> lt_tree x (Node i l y r).
Proof.
 unfold lt_tree; intuition_in; order.
Qed.

Lemma gt_tree_node :
 forall (x y : elt) (l r : tree) (i : Info.t),
 gt_tree x l -> gt_tree x r -> X.lt x y -> gt_tree x (Node i l y r).
Proof.
 unfold gt_tree; intuition_in; order.
Qed.

Local Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

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

Instance lt_tree_compat : Proper (X.eq ==> Logic.eq ==> iff) lt_tree.
Proof.
 apply proper_sym_impl_iff_2; auto.
 intros x x' Hx s s' Hs H y Hy. subst. setoid_rewrite <- Hx; auto.
Qed.

Instance gt_tree_compat : Proper (X.eq ==> Logic.eq ==> iff) gt_tree.
Proof.
 apply proper_sym_impl_iff_2; auto.
 intros x x' Hx s s' Hs H y Hy. subst. setoid_rewrite <- Hx; auto.
Qed.

Local Hint Resolve lt_tree_not_in lt_tree_trans gt_tree_not_in gt_tree_trans.

Ltac induct s x :=
 induction s as [|i l IHl x' r IHr]; simpl; intros;
 [|elim_compare x x'; intros; inv].

Ltac auto_tc := auto with typeclass_instances.

Ltac ok :=
 inv; change bst with Ok in *;
 match goal with
   | |- Ok (Node _ _ _ _) => constructor; auto_tc; ok
   | |- lt_tree _ (Node _ _ _ _) => apply lt_tree_node; ok
   | |- gt_tree _ (Node _ _ _ _) => apply gt_tree_node; ok
   | _ => eauto with typeclass_instances
 end.

(** ** Empty set *)

Lemma empty_spec : Empty empty.
Proof.
 intros x H. inversion H.
Qed.

Instance empty_ok : Ok empty.
Proof.
 auto.
Qed.

(** ** Emptyness test *)

Lemma is_empty_spec : forall s, is_empty s = true <-> Empty s.
Proof.
 destruct s as [|c r x l]; simpl; auto.
 - split; auto. intros _ x H. inv.
 - split; auto. try discriminate. intro H; elim (H x); auto.
Qed.

(** ** Membership *)

Lemma mem_spec : forall s x `{Ok s}, mem x s = true <-> InT x s.
Proof.
 split.
 - induct s x; now auto.
 - induct s x; intuition_in; order.
Qed.

(** ** Minimal and maximal elements *)

Functional Scheme min_elt_ind := Induction for min_elt Sort Prop.
Functional Scheme max_elt_ind := Induction for max_elt Sort Prop.

Lemma min_elt_spec1 s x : min_elt s = Some x -> InT x s.
Proof.
 functional induction (min_elt s); auto; inversion 1; auto.
Qed.

Lemma min_elt_spec2 s x y `{Ok s} :
 min_elt s = Some x -> InT y s -> ~ X.lt y x.
Proof.
 revert y.
 functional induction (min_elt s);
 try rename _x0 into r; try rename _x2 into l1, _x3 into x1, _x4 into r1.
 - discriminate.
 - intros y V W.
   inversion V; clear V; subst.
   inv; order.
 - intros; inv; auto.
   * assert (X.lt x x0) by (apply H8; apply min_elt_spec1; auto).
     order.
   * assert (X.lt x1 x0) by auto.
     assert (~X.lt x1 x) by auto.
     order.
Qed.

Lemma min_elt_spec3 s : min_elt s = None -> Empty s.
Proof.
 functional induction (min_elt s).
 red; red; inversion 2.
 inversion 1.
 intro H0.
 destruct (IHo H0 _x3); auto.
Qed.

Lemma max_elt_spec1 s x : max_elt s = Some x -> InT x s.
Proof.
 functional induction (max_elt s); auto; inversion 1; auto.
Qed.

Lemma max_elt_spec2 s x y `{Ok s} :
 max_elt s = Some x -> InT y s -> ~ X.lt x y.
Proof.
 revert y.
 functional induction (max_elt s);
 try rename _x0 into r; try rename _x2 into l1, _x3 into x1, _x4 into r1.
 - discriminate.
 - intros y V W.
   inversion V; clear V; subst.
   inv; order.
 - intros; inv; auto.
   * assert (X.lt x0 x) by (apply H9; apply max_elt_spec1; auto).
     order.
   * assert (X.lt x0 x1) by auto.
     assert (~X.lt x x1) by auto.
     order.
Qed.

Lemma max_elt_spec3 s : max_elt s = None -> Empty s.
Proof.
 functional induction (max_elt s).
 red; red; inversion 2.
 inversion 1.
 intro H0.
 destruct (IHo H0 _x3); auto.
Qed.

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

(** ** Elements *)

Lemma elements_spec1' : forall s acc x,
 InA X.eq x (elements_aux acc s) <-> InT x s \/ InA X.eq x acc.
Proof.
 induction s as [ | c l Hl x r Hr ]; simpl; auto.
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
 induction s as [ | c l Hl y r Hr]; simpl; intuition.
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
Local Hint Resolve elements_spec2.

Lemma elements_spec2w : forall s `(Ok s), NoDupA X.eq (elements s).
Proof.
 intros. eapply SortA_NoDupA; eauto with *.
Qed.

Lemma elements_aux_cardinal :
 forall s acc, (length acc + cardinal s)%nat = length (elements_aux acc s).
Proof.
 simple induction s; simpl; intuition.
 rewrite <- H.
 simpl.
 rewrite <- H0. rewrite (Nat.add_comm (cardinal t0)).
 now rewrite <- Nat.add_succ_r, Nat.add_assoc.
Qed.

Lemma elements_cardinal : forall s : tree, cardinal s = length (elements s).
Proof.
 exact (fun s => elements_aux_cardinal s nil).
Qed.

Definition cardinal_spec (s:tree)(Hs:Ok s) := elements_cardinal s.

Lemma elements_app :
 forall s acc, elements_aux acc s = elements s ++ acc.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1, IHs2.
 unfold elements; simpl.
 rewrite 2 IHs1, IHs2, !app_nil_r, !app_ass; auto.
Qed.

Lemma elements_node c l x r :
 elements (Node c l x r) = elements l ++ x :: elements r.
Proof.
 unfold elements; simpl.
 now rewrite !elements_app, !app_nil_r.
Qed.

Lemma rev_elements_app :
 forall s acc, rev_elements_aux acc s = rev_elements s ++ acc.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1, IHs2.
 unfold rev_elements; simpl.
 rewrite IHs1, 2 IHs2, !app_nil_r, !app_ass; auto.
Qed.

Lemma rev_elements_node c l x r :
 rev_elements (Node c l x r) = rev_elements r ++ x :: rev_elements l.
Proof.
 unfold rev_elements; simpl.
 now rewrite !rev_elements_app, !app_nil_r.
Qed.

Lemma rev_elements_rev s : rev_elements s = rev (elements s).
Proof.
 induction s as [|c l IHl x r IHr]; trivial.
 rewrite elements_node, rev_elements_node, IHl, IHr, rev_app_distr.
 simpl. now rewrite !app_ass.
Qed.

(** The converse of [elements_spec2], used in MSetRBT *)

(* TODO: TO MIGRATE ELSEWHERE... *)

Lemma sorted_app_inv l1 l2 :
 sort X.lt (l1++l2) ->
 sort X.lt l1 /\ sort X.lt l2 /\
 forall x1 x2, InA X.eq x1 l1 -> InA X.eq x2 l2 -> X.lt x1 x2.
Proof.
 induction l1 as [|a1 l1 IHl1].
 - simpl; repeat split; auto.
   intros. now rewrite InA_nil in *.
 - simpl. inversion_clear 1 as [ | ? ? Hs Hhd ].
   destruct (IHl1 Hs) as (H1 & H2 & H3).
   repeat split.
   * constructor; auto.
     destruct l1; simpl in *; auto; inversion_clear Hhd; auto.
   * trivial.
   * intros x1 x2 Hx1 Hx2. rewrite InA_cons in Hx1. destruct Hx1.
     + rewrite H.
       apply SortA_InfA_InA with (eqA:=X.eq)(l:=l1++l2); auto_tc.
       rewrite InA_app_iff; auto_tc.
     + auto.
Qed.

Lemma elements_sort_ok s : sort X.lt (elements s) -> Ok s.
Proof.
 induction s as [|c l IHl x r IHr].
 - auto.
 - rewrite elements_node.
   intros H. destruct (sorted_app_inv _ _ H) as (H1 & H2 & H3).
   inversion_clear H2.
   constructor; ok.
   * intros y Hy. apply H3.
     + now rewrite elements_spec1.
     + rewrite InA_cons. now left.
   * intros y Hy.
     apply SortA_InfA_InA with (eqA:=X.eq)(l:=elements r); auto_tc.
     now rewrite elements_spec1.
Qed.

(** ** [for_all] and [exists] *)

Lemma for_all_spec s f : Proper (X.eq==>eq) f ->
 (for_all f s = true <-> For_all (fun x => f x = true) s).
Proof.
 intros Hf; unfold For_all.
 induction s as [|i l IHl x r IHr]; simpl; auto.
 - split; intros; inv; auto.
 - rewrite <- !andb_lazy_alt, !andb_true_iff, IHl, IHr. clear IHl IHr.
   intuition_in. eauto.
Qed.

Lemma exists_spec s f : Proper (X.eq==>eq) f ->
 (exists_ f s = true <-> Exists (fun x => f x = true) s).
Proof.
 intros Hf; unfold Exists.
 induction s as [|i l IHl x r IHr]; simpl; auto.
 - split.
   * discriminate.
   * intros (y,(H,_)); inv.
 - rewrite <- !orb_lazy_alt, !orb_true_iff, IHl, IHr. clear IHl IHr.
   split; [intros [[H|(y,(H,H'))]|(y,(H,H'))]|intros (y,(H,H'))].
   * exists x; auto.
   * exists y; auto.
   * exists y; auto.
   * inv; [left;left|left;right|right]; try (exists y); eauto.
Qed.

(** ** Fold *)

Lemma fold_spec' {A} (f : elt -> A -> A) (s : tree) (i : A) (acc : list elt) :
 fold_left (flip f) (elements_aux acc s) i = fold_left (flip f) acc (fold f s i).
Proof.
 revert i acc.
 induction s as [|c l IHl x r IHr]; simpl; intros; auto.
 rewrite IHl.
 simpl. unfold flip at 2.
 apply IHr.
Qed.

Lemma fold_spec (s:tree) {A} (i : A) (f : elt -> A -> A) :
 fold f s i = fold_left (flip f) (elements s) i.
Proof.
 revert i. unfold elements.
 induction s as [|c l IHl x r IHr]; simpl; intros; auto.
 rewrite fold_spec'.
 rewrite IHr.
 simpl; auto.
Qed.


(** ** Subset *)

Lemma subsetl_spec : forall subset_l1 l1 x1 c1 s2
 `{Ok (Node c1 l1 x1 Leaf), Ok s2},
 (forall s `{Ok s}, (subset_l1 s = true <-> Subset l1 s)) ->
 (subsetl subset_l1 x1 s2 = true <-> Subset (Node c1 l1 x1 Leaf) s2 ).
Proof.
 induction s2 as [|c2 l2 IHl2 x2 r2 IHr2]; simpl; intros.
 unfold Subset; intuition; try discriminate.
 assert (H': InT x1 Leaf) by auto; inversion H'.
 specialize (IHl2 H).
 specialize (IHr2 H).
 inv.
 elim_compare x1 x2.

 rewrite H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (X.eq a x2) by order; intuition_in.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.

 rewrite IHl2 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.

 rewrite <-andb_lazy_alt, andb_true_iff, H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 constructor 3. setoid_replace a with x1; auto. rewrite <- mem_spec; auto.
 rewrite mem_spec; auto.
 assert (InT x1 (Node c2 l2 x2 r2)) by auto; intuition_in; order.
Qed.


Lemma subsetr_spec : forall subset_r1 r1 x1 c1 s2,
 bst (Node c1 Leaf x1 r1) -> bst s2 ->
 (forall s, bst s -> (subset_r1 s = true <-> Subset r1 s)) ->
 (subsetr subset_r1 x1 s2 = true <-> Subset (Node c1 Leaf x1 r1) s2).
Proof.
 induction s2 as [|c2 l2 IHl2 x2 r2 IHr2]; simpl; intros.
 unfold Subset; intuition; try discriminate.
 assert (H': InT x1 Leaf) by auto; inversion H'.
 specialize (IHl2 H).
 specialize (IHr2 H).
 inv.
 elim_compare x1 x2.

 rewrite H1 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (X.eq a x2) by order; intuition_in.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.

 rewrite <-andb_lazy_alt, andb_true_iff, H1 by auto;  clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 constructor 2. setoid_replace a with x1; auto. rewrite <- mem_spec; auto.
 rewrite mem_spec; auto.
 assert (InT x1 (Node c2 l2 x2 r2)) by auto; intuition_in; order.

 rewrite IHr2 by auto; clear H1 IHl2 IHr2.
 unfold Subset. intuition_in.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.
Qed.

Lemma subset_spec : forall s1 s2 `{Ok s1, Ok s2},
 (subset s1 s2 = true <-> Subset s1 s2).
Proof.
 induction s1 as [|c1 l1 IHl1 x1 r1 IHr1]; simpl; intros.
 unfold Subset; intuition_in.
 destruct s2 as [|c2 l2 x2 r2]; simpl; intros.
 unfold Subset; intuition_in; try discriminate.
 assert (H': InT x1 Leaf) by auto; inversion H'.
 inv.
 elim_compare x1 x2.

 rewrite <-andb_lazy_alt, andb_true_iff, IHl1, IHr1 by auto.
 clear IHl1 IHr1.
 unfold Subset; intuition_in.
 assert (X.eq a x2) by order; intuition_in.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.

 rewrite <-andb_lazy_alt, andb_true_iff, IHr1 by auto.
 rewrite (@subsetl_spec (subset l1) l1 x1 c1) by auto.
 clear IHl1 IHr1.
 unfold Subset; intuition_in.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.

 rewrite <-andb_lazy_alt, andb_true_iff, IHl1 by auto.
 rewrite (@subsetr_spec (subset r1) r1 x1 c1) by auto.
 clear IHl1 IHr1.
 unfold Subset; intuition_in.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.
 assert (InT a (Node c2 l2 x2 r2)) by auto; intuition_in; order.
Qed.


(** ** Comparison *)

(** Relations [eq] and [lt] over trees *)

Module L := MSetInterface.MakeListOrdering X.

Definition eq := Equal.
Instance eq_equiv : Equivalence eq.
Proof. firstorder. Qed.

Lemma eq_Leq : forall s s', eq s s' <-> L.eq (elements s) (elements s').
Proof.
 unfold eq, Equal, L.eq; intros.
 setoid_rewrite elements_spec1.
 firstorder. 
Qed.

Definition lt (s1 s2 : tree) : Prop :=
 exists s1' s2', Ok s1' /\ Ok s2' /\ eq s1 s1' /\ eq s2 s2'
   /\ L.lt (elements s1') (elements s2').

Declare Equivalent Keys L.eq equivlistA.

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


(** Proof of the comparison algorithm *)

(** [flatten_e e] returns the list of elements of [e] i.e. the list
    of elements actually compared *)

Fixpoint flatten_e (e : enumeration) : list elt := match e with
  | End => nil
  | More x t r => x :: elements t ++ flatten_e r
 end.

Lemma flatten_e_elements :
 forall l x r c e,
 elements l ++ flatten_e (More x r e) = elements (Node c l x r) ++ flatten_e e.
Proof.
 intros. now rewrite elements_node, app_ass.
Qed.

Lemma cons_1 : forall s e,
  flatten_e (cons s e) = elements s ++ flatten_e e.
Proof.
 induction s; simpl; auto; intros.
 rewrite IHs1; apply flatten_e_elements.
Qed.

(** Correctness of this comparison *)

Definition Cmp c x y := CompSpec L.eq L.lt x y c.

Local Hint Unfold Cmp flip.

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
 simpl; intros; elim_compare x1 x2; simpl; red; auto.
Qed.

Lemma compare_cont_Cmp : forall s1 cont e2 l,
 (forall e, Cmp (cont e) l (flatten_e e)) ->
 Cmp (compare_cont s1 cont e2) (elements s1 ++ l) (flatten_e e2).
Proof.
 induction s1 as [|c1 l1 Hl1 x1 r1 Hr1]; intros; auto.
 rewrite elements_node, app_ass; simpl.
 apply Hl1; auto. clear e2. intros [|x2 r2 e2].
 simpl; auto.
 apply compare_more_Cmp.
 rewrite <- cons_1; auto.
Qed.

Lemma compare_Cmp : forall s1 s2,
 Cmp (compare s1 s2) (elements s1) (elements s2).
Proof.
 intros; unfold compare.
 rewrite <- (app_nil_r (elements s1)).
 replace (elements s2) with (flatten_e (cons s2 End)) by
  (rewrite cons_1; simpl; rewrite app_nil_r; auto).
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


(** ** Equality test *)

Lemma equal_spec : forall s1 s2 `{Ok s1, Ok s2},
 equal s1 s2 = true <-> eq s1 s2.
Proof.
unfold equal; intros s1 s2 B1 B2.
destruct (@compare_spec s1 s2 B1 B2) as [H|H|H];
 split; intros H'; auto; try discriminate.
rewrite H' in H. elim (StrictOrder_Irreflexive s2); auto.
rewrite H' in H. elim (StrictOrder_Irreflexive s2); auto.
Qed.

(** ** A few results about [mindepth] and [maxdepth] *)

Lemma mindepth_maxdepth s : mindepth s <= maxdepth s.
Proof.
 induction s; simpl; auto.
 rewrite <- Nat.succ_le_mono.
 transitivity (mindepth s1). apply Nat.le_min_l.
 transitivity (maxdepth s1). trivial. apply Nat.le_max_l.
Qed.

Lemma maxdepth_cardinal s : cardinal s < 2^(maxdepth s).
Proof.
 unfold Peano.lt.
 induction s as [|c l IHl x r IHr].
 - auto.
 - simpl. rewrite <- Nat.add_succ_r, <- Nat.add_succ_l, Nat.add_0_r.
   apply Nat.add_le_mono; etransitivity;
   try apply IHl; try apply IHr; apply Nat.pow_le_mono; auto.
   * apply Nat.le_max_l.
   * apply Nat.le_max_r.
Qed.

Lemma mindepth_cardinal s : 2^(mindepth s) <= S (cardinal s).
Proof.
 unfold Peano.lt.
 induction s as [|c l IHl x r IHr].
 - auto.
 - simpl. rewrite <- Nat.add_succ_r, <- Nat.add_succ_l, Nat.add_0_r.
   apply Nat.add_le_mono; etransitivity;
   try apply IHl; try apply IHr; apply Nat.pow_le_mono; auto.
   * apply Nat.le_min_l.
   * apply Nat.le_min_r.
Qed.

Lemma maxdepth_log_cardinal s : s <> Leaf ->
 Nat.log2 (cardinal s) < maxdepth s.
Proof.
 intros H.
 apply Nat.log2_lt_pow2. destruct s; simpl; intuition.
 apply maxdepth_cardinal.
Qed.

Lemma mindepth_log_cardinal s : mindepth s <= Nat.log2 (S (cardinal s)).
Proof.
 apply Nat.log2_le_pow2. auto with arith.
 apply mindepth_cardinal.
Qed.

End Props.

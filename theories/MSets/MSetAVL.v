(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * MSetAVL : Implementation of MSetInterface via AVL trees *)

(** This module implements finite sets using AVL trees.
    It follows the implementation from Ocaml's standard library,

    All operations given here expect and produce well-balanced trees
    (in the ocaml sense: heights of subtrees shouldn't differ by more
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

Require Import FunInd MSetInterface MSetGenTree BinInt Int.

Set Implicit Arguments.
Unset Strict Implicit.
(* for nicer extraction, we create inductive principles
   only when needed *)
Local Unset Elimination Schemes.

(** * Ops : the pure functions *)

Module Ops (Import I:Int)(X:OrderedType) <: MSetInterface.Ops X.
Local Open Scope Int_scope.
Local Notation int := I.t.

(** ** Generic trees instantiated with integer height *)

(** We reuse a generic definition of trees where the information
    parameter is a [Int.t]. Functions like mem or fold are also
    provided by this generic functor. *)

Include MSetGenTree.Ops X I.

Definition t := tree.

(** ** Height of trees *)

Definition height (s : t) : int :=
  match s with
  | Leaf => 0
  | Node h _ _ _ => h
  end.

(** ** Singleton set *)

Definition singleton x := Node 1 Leaf x Leaf.

(** ** Helper functions *)

(** [create l x r] creates a node, assuming [l] and [r]
    to be balanced and [|height l - height r| <= 2]. *)

Definition create l x r :=
   Node (max (height l) (height r) + 1) l x r.

(** [bal l x r] acts as [create], but performs one step of
    rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

Definition assert_false := create.

Definition bal l x r :=
  let hl := height l in
  let hr := height r in
  if (hr+2) <? hl then
    match l with
     | Leaf => assert_false l x r
     | Node _ ll lx lr =>
       if (height lr) <=? (height ll) then
         create ll lx (create lr x r)
       else
         match lr with
          | Leaf => assert_false l x r
          | Node _ lrl lrx lrr =>
              create (create ll lx lrl) lrx (create lrr x r)
         end
    end
  else
    if (hl+2) <? hr then
      match r with
       | Leaf => assert_false l x r
       | Node _ rl rx rr =>
         if (height rl) <=? (height rr) then
            create (create l x rl) rx rr
         else
           match rl with
            | Leaf => assert_false l x r
            | Node _ rll rlx rlr =>
                create (create l x rll) rlx (create rlr rx rr)
           end
      end
    else
      create l x r.

(** ** Insertion *)

Fixpoint add x s := match s with
   | Leaf => Node 1 Leaf x Leaf
   | Node h l y r =>
      match X.compare x y with
         | Lt => bal (add x l) y r
         | Eq => Node h l y r
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
    | Node lh ll lx lr => fun x =>
       fix join_aux (r:t) : t := match r with
          | Leaf => add x l
          | Node rh rl rx rr =>
               if (rh+2) <? lh then bal ll lx (join lr x r)
               else if (lh+2) <? rh then bal (join_aux rl) rx rr
               else create l x r
          end
  end.

(** ** Extraction of minimum element

  Morally, [remove_min] is to be applied to a non-empty tree
  [t = Node h l x r]. Since we can't deal here with [assert false]
  for [t=Leaf], we pre-unpack [t] (and forget about [h]).
*)

Fixpoint remove_min l x r : t*elt :=
  match l with
    | Leaf => (r,x)
    | Node lh ll lx lr =>
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
  | _, Node _ l2 x2 r2 =>
        let (s2',m) := remove_min l2 x2 r2 in bal s1 m s2'
end.

(** ** Deletion *)

Fixpoint remove x s := match s with
  | Leaf => Leaf
  | Node _ l y r =>
      match X.compare x y with
         | Lt => bal (remove x l) y r
         | Eq => merge l r
         | Gt => bal l y (remove x r)
      end
   end.

(** ** Concatenation

    Same as [merge] but does not assume anything about heights.
*)

Definition concat s1 s2 :=
   match s1, s2 with
      | Leaf, _ => s2
      | _, Leaf => s1
      | _, Node _ l2 x2 r2 =>
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
  | Node _ l y r =>
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
    | Node _ l1 x1 r1, _ =>
            let (l2',pres,r2') := split x1 s2 in
            if pres then join (inter l1 l2') x1 (inter r1 r2')
            else concat (inter l1 l2') (inter r1 r2')
    end.

(** ** Difference *)

Fixpoint diff s1 s2 := match s1, s2 with
 | Leaf, _ => Leaf
 | _, Leaf => s1
 | Node _ l1 x1 r1, _ =>
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
  | Node _ l1 x1 r1, _ =>
     let (l2',_,r2') := split x1 s2 in
     join (union l1 l2') x1 (union r1 r2')
 end.

(** ** Filter *)

Fixpoint filter (f:elt->bool) s := match s with
  | Leaf => Leaf
  | Node _ l x r =>
    let l' := filter f l in
    let r' := filter f r in
    if f x then join l' x r' else concat l' r'
 end.

(** ** Partition *)

Fixpoint partition (f:elt->bool)(s : t) : t*t :=
  match s with
   | Leaf => (Leaf, Leaf)
   | Node _ l x r =>
      let (l1,l2) := partition f l in
      let (r1,r2) := partition f r in
      if f x then (join l1 x r1, concat l2 r2)
      else (concat l1 r1, join l2 x r2)
  end.

End Ops.


(** * MakeRaw

   Functor of pure functions + a posteriori proofs of invariant
   preservation *)

Module MakeRaw (Import I:Int)(X:OrderedType) <: RawSets X.
Include Ops I X.

(** Generic definition of binary-search-trees and proofs of
    specifications for generic functions such as mem or fold. *)

Include MSetGenTree.Props X I.

(** Automation and dedicated tactics *)

Local Hint Immediate MX.eq_sym.
Local Hint Unfold In lt_tree gt_tree Ok.
Local Hint Constructors InT bst.
Local Hint Resolve MX.eq_refl MX.eq_trans MX.lt_trans ok.
Local Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.
Local Hint Resolve lt_tree_not_in lt_tree_trans gt_tree_not_in gt_tree_trans.
Local Hint Resolve elements_spec2.

(* Sometimes functional induction will expose too much of
   a tree structure. The following tactic allows factoring back
   a Node whose internal parts occurs nowhere else. *)

(* TODO: why Ltac instead of Tactic Notation don't work ? why clear ? *)

Tactic Notation "factornode" ident(s) :=
 try clear s;
 match goal with
   | |- context [Node ?l ?x ?r ?h] =>
       set (s:=Node l x r h) in *; clearbody s; clear l x r h
   | _ : context [Node ?l ?x ?r ?h] |- _ =>
       set (s:=Node l x r h) in *; clearbody s; clear l x r h
 end.

(** Inductions principles for some of the set operators *)

Functional Scheme bal_ind := Induction for bal Sort Prop.
Functional Scheme remove_min_ind := Induction for remove_min Sort Prop.
Functional Scheme merge_ind := Induction for merge Sort Prop.
Functional Scheme concat_ind := Induction for concat Sort Prop.
Functional Scheme inter_ind := Induction for inter Sort Prop.
Functional Scheme diff_ind := Induction for diff Sort Prop.
Functional Scheme union_ind := Induction for union Sort Prop.

(** Notations and helper lemma about pairs and triples *)

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.
Notation "t #l" := (t_left t) (at level 9, format "t '#l'") : pair_scope.
Notation "t #b" := (t_in t) (at level 9, format "t '#b'") : pair_scope.
Notation "t #r" := (t_right t) (at level 9, format "t '#r'") : pair_scope.

Local Open Scope pair_scope.

(** ** Singleton set *)

Lemma singleton_spec : forall x y, InT y (singleton x) <-> X.eq y x.
Proof.
 unfold singleton; intuition_in.
Qed.

Instance singleton_ok x : Ok (singleton x).
Proof.
 unfold singleton; auto.
Qed.

(** ** Helper functions *)

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
 functional induction bal l x r; intros;
 inv; repeat apply create_ok; auto; unfold create;
 (apply lt_tree_node || apply gt_tree_node); auto;
 (eapply lt_tree_trans || eapply gt_tree_trans); eauto.
Qed.


(** ** Insertion *)

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


Local Open Scope Int_scope.

(** ** Join *)

(** Function/Functional Scheme can't deal with internal fix.
    Let's do its job by hand: *)

Ltac join_tac :=
 let l := fresh "l" in
 intro l; induction l as [| lh ll _ lx lr Hlr];
   [ | intros x r; induction r as [| rh rl Hrl rx rr _]; unfold join;
     [ | destruct ((rh+2) <? lh) eqn:LT;
       [ match goal with |- context b [ bal ?a ?b ?c] =>
           replace (bal a b c)
           with (bal ll lx (join lr x (Node rh rl rx rr))); [ | auto]
         end
       | destruct ((lh+2) <? rh) eqn:LT';
         [ match goal with |- context b [ bal ?a ?b ?c] =>
             replace (bal a b c)
             with (bal (join (Node lh ll lx lr) x rl) rx rr); [ | auto]
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

Instance join_ok : forall l x r `(Ok l, Ok r, lt_tree x l, gt_tree x r),
 Ok (join l x r).
Proof.
 join_tac; auto with *; inv; apply bal_ok; auto;
 clear Hrl Hlr; intro; intros; rewrite join_spec in *.
 intuition; [ setoid_replace y with x | ]; eauto.
 intuition; [ setoid_replace y with x | ]; eauto.
Qed.


(** ** Extraction of minimum element *)

Lemma remove_min_spec : forall l x r y h,
 InT y (Node h l x r) <->
  X.eq y (remove_min l x r)#2 \/ InT y (remove_min l x r)#1.
Proof.
 intros l x r; functional induction (remove_min l x r); simpl in *; intros.
 intuition_in.
 rewrite bal_spec, In_node_iff, IHp, e0; simpl; intuition.
Qed.

Instance remove_min_ok l x r : forall h `(Ok (Node h l x r)),
 Ok (remove_min l x r)#1.
Proof.
 functional induction (remove_min l x r); simpl; intros.
 inv; auto.
 assert (O : Ok (Node _x ll lx lr)) by (inv; auto).
 assert (L : lt_tree x (Node _x ll lx lr)) by (inv; auto).
 specialize IHp with (1:=O); rewrite e0 in IHp; auto; simpl in *.
 apply bal_ok; auto.
 inv; auto.
 intro y; specialize (L y).
 rewrite remove_min_spec, e0 in L; simpl in L; intuition.
 inv; auto.
Qed.

Lemma remove_min_gt_tree : forall l x r h `{Ok (Node h l x r)},
 gt_tree (remove_min l x r)#2 (remove_min l x r)#1.
Proof.
 intros l x r; functional induction (remove_min l x r); simpl; intros.
 inv; auto.
 assert (O : Ok (Node _x ll lx lr)) by (inv; auto).
 assert (L : lt_tree x (Node _x ll lx lr)) by (inv; auto).
 specialize IHp with (1:=O); rewrite e0 in IHp; simpl in IHp.
 intro y; rewrite bal_spec; intuition;
  specialize (L m); rewrite remove_min_spec, e0 in L; simpl in L;
   [setoid_replace y with x|inv]; eauto.
Qed.
Local Hint Resolve remove_min_gt_tree.


(** ** Merging two trees *)

Lemma merge_spec : forall s1 s2 y,
 InT y (merge s1 s2) <-> InT y s1 \/ InT y s2.
Proof.
 intros s1 s2; functional induction (merge s1 s2); intros;
  try factornode s1.
 intuition_in.
 intuition_in.
 rewrite bal_spec, remove_min_spec, e1; simpl; intuition.
Qed.

Instance merge_ok s1 s2 : forall `(Ok s1, Ok s2)
 `(forall y1 y2 : elt, InT y1 s1 -> InT y2 s2 -> X.lt y1 y2),
 Ok (merge s1 s2).
Proof.
 functional induction (merge s1 s2); intros; auto;
  try factornode s1.
 apply bal_ok; auto.
 change s2' with ((s2',m)#1); rewrite <-e1; eauto with *.
 intros y Hy.
 apply H1; auto.
 rewrite remove_min_spec, e1; simpl; auto.
 change (gt_tree (s2',m)#2 (s2',m)#1); rewrite <-e1; eauto.
Qed.



(** ** Deletion *)

Lemma remove_spec : forall s x y `{Ok s},
 (InT y (remove x s) <-> InT y s /\ ~ X.eq y x).
Proof.
 induct s x.
 intuition_in.
 rewrite merge_spec; intuition; [order|order|intuition_in].
 elim H2; eauto.
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


(** ** Concatenation *)

Lemma concat_spec : forall s1 s2 y,
 InT y (concat s1 s2) <-> InT y s1 \/ InT y s2.
Proof.
 intros s1 s2; functional induction (concat s1 s2); intros;
  try factornode s1.
 intuition_in.
 intuition_in.
 rewrite join_spec, remove_min_spec, e1; simpl; intuition.
Qed.

Instance concat_ok s1 s2 : forall `(Ok s1, Ok s2)
 `(forall y1 y2 : elt, InT y1 s1 -> InT y2 s2 -> X.lt y1 y2),
 Ok (concat s1 s2).
Proof.
 functional induction (concat s1 s2); intros; auto;
  try factornode s1.
 apply join_ok; auto.
 change (Ok (s2',m)#1); rewrite <-e1; eauto with *.
 intros y Hy.
 apply H1; auto.
 rewrite remove_min_spec, e1; simpl; auto.
 change (gt_tree (s2',m)#2 (s2',m)#1); rewrite <-e1; eauto.
Qed.



(** ** Splitting *)

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

Lemma split_ok : forall s x `{Ok s}, Ok (split x s)#l /\ Ok (split x s)#r.
Proof.
 induct s x; simpl; auto.
 specialize (IHl x).
 generalize (fun y => @split_spec2 l x y _).
 destruct (split x l); simpl in *; intuition. apply join_ok; auto.
 intros y; rewrite H; intuition.
 specialize (IHr x).
 generalize (fun y => @split_spec1 r x y _).
 destruct (split x r); simpl in *; intuition. apply join_ok; auto.
 intros y; rewrite H; intuition.
Qed.

Instance split_ok1 s x `(Ok s) : Ok (split x s)#l.
Proof. intros; destruct (@split_ok s x); auto. Qed.

Instance split_ok2 s x `(Ok s) : Ok (split x s)#r.
Proof. intros; destruct (@split_ok s x); auto. Qed.


(** ** Intersection *)

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
 [intuition_in|intuition_in | | ]; factornode s2;
 destruct_split; inv;
 destruct IHt0 as (IHo1,IHi1), IHt1 as (IHo2,IHi2); auto with *;
 split; intros.
 - (* Ok join *)
   apply join_ok; auto with *; intro y; rewrite ?IHi1, ?IHi2; intuition.
 - (* InT join *)
   rewrite join_spec, IHi1, IHi2, split_spec1, split_spec2; intuition_in.
   setoid_replace y with x1; auto. rewrite <- split_spec3; auto.
 - (* Ok concat *)
   apply concat_ok; auto with *; intros y1 y2; rewrite IHi1, IHi2;
   intuition; order.
 - (* InT concat *)
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


(** ** Difference *)

Lemma diff_spec_ok : forall s1 s2 `{Ok s1, Ok s2},
 Ok (diff s1 s2) /\ (forall y, InT y (diff s1 s2) <-> InT y s1 /\ ~InT y s2).
Proof.
 intros s1 s2; functional induction diff s1 s2; intros B1 B2;
 [intuition_in|intuition_in | | ]; factornode s2;
 destruct_split; inv;
 destruct IHt0 as (IHb1,IHi1), IHt1 as (IHb2,IHi2); auto with *;
 split; intros.
 - (* Ok concat *)
   apply concat_ok; auto; intros y1 y2; rewrite IHi1, IHi2; intuition; order.
 - (* InT concat *)
   rewrite concat_spec, IHi1, IHi2, split_spec1, split_spec2; intuition_in.
   absurd (InT x1 s2).
   + setoid_replace x1 with y; auto.
   + rewrite <- split_spec3; auto; congruence.
 - (* Ok join *)
   apply join_ok; auto; intro y; rewrite ?IHi1, ?IHi2; intuition.
 - (* InT join *)
   rewrite join_spec, IHi1, IHi2, split_spec1, split_spec2; auto with *.
   intuition_in.
   absurd (InT x1 s2); auto.
   * rewrite <- split_spec3; auto; congruence.
   * setoid_replace x1 with y; auto.
Qed.

Lemma diff_spec : forall s1 s2 y `{Ok s1, Ok s2},
 (InT y (diff s1 s2) <-> InT y s1 /\ ~InT y s2).
Proof. intros; destruct (@diff_spec_ok s1 s2); auto. Qed.

Instance diff_ok s1 s2 `(Ok s1, Ok s2) : Ok (diff s1 s2).
Proof. intros; destruct (@diff_spec_ok s1 s2); auto. Qed.


(** ** Union *)

Lemma union_spec : forall s1 s2 y `{Ok s1, Ok s2},
 (InT y (union s1 s2) <-> InT y s1 \/ InT y s2).
Proof.
 intros s1 s2; functional induction union s1 s2; intros y B1 B2.
 intuition_in.
 intuition_in.
 factornode s2; destruct_split; inv.
 rewrite join_spec, IHt0, IHt1, split_spec1, split_spec2; auto with *.
 destruct (X.compare_spec y x1); intuition_in.
Qed.

Instance union_ok s1 s2 : forall `(Ok s1, Ok s2), Ok (union s1 s2).
Proof.
 functional induction union s1 s2; intros B1 B2; auto.
 factornode s2; destruct_split; inv.
 apply join_ok; auto with *.
 intro y; rewrite union_spec, split_spec1; intuition_in.
 intro y; rewrite union_spec, split_spec2; intuition_in.
Qed.

(** * Filter *)

Lemma filter_spec : forall s x f,
 Proper (X.eq==>Logic.eq) f ->
 (InT x (filter f s) <-> InT x s /\ f x = true).
Proof.
 induction s as [ |h l Hl x0 r Hr]; intros x f Hf; simpl.
 - intuition_in.
 - case_eq (f x0); intros Hx0.
   * rewrite join_spec, Hl, Hr; intuition_in.
     now setoid_replace x with x0.
   * rewrite concat_spec, Hl, Hr; intuition_in.
     assert (f x = f x0) by auto. congruence.
Qed.

Lemma filter_weak_spec : forall s x f,
 InT x (filter f s) -> InT x s.
Proof.
 induction s as [ |h l Hl x0 r Hr]; intros x f; simpl.
 - trivial.
 - destruct (f x0).
   * rewrite join_spec; intuition_in; eauto.
   * rewrite concat_spec; intuition_in; eauto.
Qed.

Instance filter_ok s f `(H : Ok s) : Ok (filter f s).
Proof.
 induction H as [ | h x l r Hl Hfl Hr Hfr Hlt Hgt ].
 - constructor.
 - simpl.
   assert (lt_tree x (filter f l)) by (eauto using filter_weak_spec).
   assert (gt_tree x (filter f r)) by (eauto using filter_weak_spec).
   destruct (f x); eauto using concat_ok, join_ok.
Qed.


(** * Partition *)

Lemma partition_spec1' s f : (partition f s)#1 = filter f s.
Proof.
 induction s as [ | h l Hl x r Hr ]; simpl.
 - trivial.
 - rewrite <- Hl, <- Hr.
   now destruct (partition f l), (partition f r), (f x).
Qed.

Lemma partition_spec2' s f :
 (partition f s)#2 = filter (fun x => negb (f x)) s.
Proof.
 induction s as [ | h l Hl x r Hr ]; simpl.
 - trivial.
 - rewrite <- Hl, <- Hr.
   now destruct (partition f l), (partition f r), (f x).
Qed.

Lemma partition_spec1 s f :
 Proper (X.eq==>Logic.eq) f ->
 Equal (partition f s)#1 (filter f s).
Proof. now rewrite partition_spec1'. Qed.

Lemma partition_spec2 s f :
 Proper (X.eq==>Logic.eq) f ->
 Equal (partition f s)#2 (filter (fun x => negb (f x)) s).
Proof. now rewrite partition_spec2'. Qed.

Instance partition_ok1 s f `(Ok s) : Ok (partition f s)#1.
Proof. rewrite partition_spec1'; now apply filter_ok. Qed.

Instance partition_ok2 s f `(Ok s) : Ok (partition f s)#2.
Proof. rewrite partition_spec2'; now apply filter_ok. Qed.

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

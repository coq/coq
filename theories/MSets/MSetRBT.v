(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * MSetRBT : Implementation of MSetInterface via Red-Black trees *)

(** Initial author: Andrew W. Appel, 2011.
    Extra modifications by: Pierre Letouzey

The design decisions behind this implementation are described here:

 - Efficient Verified Red-Black Trees, by Andrew W. Appel, September 2011.
   http://www.cs.princeton.edu/~appel/papers/redblack.pdf

Additional suggested reading:

 - Red-Black Trees in a Functional Setting by Chris Okasaki.
   Journal of Functional Programming, 9(4):471-477, July 1999.
   http://www.eecs.usma.edu/webs/people/okasaki/jfp99redblack.pdf

 - Red-black trees with types, by Stefan Kahrs.
   Journal of Functional Programming, 11(4), 425-432, 2001.

 - Functors for Proofs and Programs, by J.-C. Filliatre and P. Letouzey.
   ESOP'04: European Symposium on Programming, pp. 370-384, 2004.
   http://www.lri.fr/~filliatr/ftp/publis/fpp.ps.gz
*)

Require MSetGenTree.
Require Import Bool List BinPos Pnat Setoid SetoidList PeanoNat.
Local Open Scope list_scope.

(* For nicer extraction, we create induction principles
   only when needed *)
Local Unset Elimination Schemes.

(** An extra function not (yet?) in MSetInterface.S *)

Module Type MSetRemoveMin (Import M:MSetInterface.S).

 Parameter remove_min : t -> option (elt * t).

 Axiom remove_min_spec1 : forall s k s',
  remove_min s = Some (k,s') ->
   min_elt s = Some k /\ remove k s [=] s'.

 Axiom remove_min_spec2 : forall s, remove_min s = None -> Empty s.

End MSetRemoveMin.

(** The type of color annotation. *)

Inductive color := Red | Black.

Module Color.
 Definition t := color.
End Color.

(** * Ops : the pure functions *)

Module Ops (X:Orders.OrderedType) <: MSetInterface.Ops X.

(** ** Generic trees instantiated with color *)

(** We reuse a generic definition of trees where the information
    parameter is a color. Functions like mem or fold are also
    provided by this generic functor. *)

Include MSetGenTree.Ops X Color.

Definition t := tree.
Local Notation Rd := (Node Red).
Local Notation Bk := (Node Black).

(** ** Basic tree *)

Definition singleton (k: elt) : tree := Bk Leaf k Leaf.

(** ** Changing root color *)

Definition makeBlack t :=
 match t with
 | Leaf => Leaf
 | Node _ a x b => Bk a x b
 end.

Definition makeRed t :=
 match t with
 | Leaf => Leaf
 | Node _ a x b => Rd a x b
 end.

(** ** Balancing *)

(** We adapt when one side is not a true red-black tree.
    Both sides have the same black depth. *)

Definition lbal l k r :=
 match l with
 | Rd (Rd a x b) y c => Rd (Bk a x b) y (Bk c k r)
 | Rd a x (Rd b y c) => Rd (Bk a x b) y (Bk c k r)
 | _ => Bk l k r
 end.

Definition rbal l k r :=
 match r with
 | Rd (Rd b y c) z d => Rd (Bk l k b) y (Bk c z d)
 | Rd b y (Rd c z d) => Rd (Bk l k b) y (Bk c z d)
 | _ => Bk l k r
 end.

(** A variant of [rbal], with reverse pattern order.
    Is it really useful ? Should we always use it ? *)

Definition rbal' l k r :=
 match r with
 | Rd b y (Rd c z d) => Rd (Bk l k b) y (Bk c z d)
 | Rd (Rd b y c) z d => Rd (Bk l k b) y (Bk c z d)
 | _ => Bk l k r
 end.

(** Balancing with different black depth.
    One side is almost a red-black tree, while the other is
    a true red-black tree, but with black depth + 1.
    Used in deletion. *)

Definition lbalS l k r :=
 match l with
 | Rd a x b => Rd (Bk a x b) k r
 | _ =>
   match r with
   | Bk a y b => rbal' l k (Rd a y b)
   | Rd (Bk a y b) z c => Rd (Bk l k a) y (rbal' b z (makeRed c))
   | _ => Rd l k r (* impossible *)
   end
 end.

Definition rbalS l k r :=
 match r with
 | Rd b y c => Rd l k (Bk b y c)
 | _ =>
   match l with
   | Bk a x b => lbal (Rd a x b) k r
   | Rd a x (Bk b y c) => Rd (lbal (makeRed a) x b) y (Bk c k r)
   | _ => Rd l k r (* impossible *)
   end
 end.

(** ** Insertion *)

Fixpoint ins x s :=
 match s with
 | Leaf => Rd Leaf x Leaf
 | Node c l y r =>
   match X.compare x y with
   | Eq => s
   | Lt =>
     match c with
     | Red => Rd (ins x l) y r
     | Black => lbal (ins x l) y r
     end
   | Gt =>
     match c with
     | Red => Rd l y (ins x r)
     | Black => rbal l y (ins x r)
     end
   end
 end.

Definition add x s := makeBlack (ins x s).

(** ** Deletion *)

Fixpoint append (l:tree) : tree -> tree :=
 match l with
 | Leaf => fun r => r
 | Node lc ll lx lr =>
   fix append_l (r:tree) : tree :=
   match r with
   | Leaf => l
   | Node rc rl rx rr =>
     match lc, rc with
     | Red, Red =>
       let lrl := append lr rl in
       match lrl with
       | Rd lr' x rl' => Rd (Rd ll lx lr') x (Rd rl' rx rr)
       | _ => Rd ll lx (Rd lrl rx rr)
       end
     | Black, Black =>
       let lrl := append lr rl in
       match lrl with
       | Rd lr' x rl' => Rd (Bk ll lx lr') x (Bk rl' rx rr)
       | _ => lbalS ll lx (Bk lrl rx rr)
       end
     | Black, Red => Rd (append_l rl) rx rr
     | Red, Black => Rd ll lx (append lr r)
     end
   end
 end.

Fixpoint del x t :=
 match t with
 | Leaf => Leaf
 | Node _ a y b =>
   match X.compare x y with
   | Eq => append a b
   | Lt =>
     match a with
     | Bk _ _ _ => lbalS (del x a) y b
     | _ => Rd (del x a) y b
     end
   | Gt =>
     match b with
     | Bk _ _ _ => rbalS a y (del x b)
     | _ => Rd a y (del x b)
     end
   end
 end.

Definition remove x t := makeBlack (del x t).

(** ** Removing minimal element *)

Fixpoint delmin l x r : (elt * tree) :=
 match l with
 | Leaf => (x,r)
 | Node lc ll lx lr =>
   let (k,l') := delmin ll lx lr in
   match lc with
   | Black => (k, lbalS l' x r)
   | Red => (k, Rd l' x r)
   end
 end.

Definition remove_min t : option (elt * tree) :=
 match t with
 | Leaf => None
 | Node _ l x r =>
   let (k,t) := delmin l x r in
   Some (k, makeBlack t)
 end.

(** ** Tree-ification

    We rebuild a tree of size [if pred then n-1 else n] as soon
    as the list [l] has enough elements *)

Definition bogus : tree * list elt := (Leaf, nil).

Notation treeify_t := (list elt -> tree * list elt).

Definition treeify_zero : treeify_t :=
 fun acc => (Leaf,acc).

Definition treeify_one : treeify_t :=
 fun acc => match acc with
 | x::acc => (Rd Leaf x Leaf, acc)
 | _ => bogus
 end.

Definition treeify_cont (f g : treeify_t) : treeify_t :=
 fun acc =>
 match f acc with
 | (l, x::acc) =>
   match g acc with
   | (r, acc) => (Bk l x r, acc)
   end
 | _ => bogus
 end.

Fixpoint treeify_aux (pred:bool)(n: positive) : treeify_t :=
 match n with
 | xH => if pred then treeify_zero else treeify_one
 | xO n => treeify_cont (treeify_aux pred n) (treeify_aux true n)
 | xI n => treeify_cont (treeify_aux false n) (treeify_aux pred n)
 end.

Fixpoint plength_aux (l:list elt)(p:positive) := match l with
 | nil => p
 | _::l => plength_aux l (Pos.succ p)
end.

Definition plength l := plength_aux l 1.

Definition treeify (l:list elt) :=
 fst (treeify_aux true (plength l) l).

(** ** Filtering *)

Fixpoint filter_aux (f: elt -> bool) s acc :=
 match s with
 | Leaf => acc
 | Node _ l k r =>
   let acc := filter_aux f r acc in
   if f k then filter_aux f l (k::acc)
   else filter_aux f l acc
 end.

Definition filter (f: elt -> bool) (s: t) : t :=
 treeify (filter_aux f s nil).

Fixpoint partition_aux (f: elt -> bool) s acc1 acc2 :=
 match s with
 | Leaf => (acc1,acc2)
 | Node _ sl k sr =>
   let (acc1, acc2) := partition_aux f sr acc1 acc2 in
   if f k then partition_aux f sl (k::acc1) acc2
   else partition_aux f sl acc1 (k::acc2)
 end.

Definition partition (f: elt -> bool) (s:t) : t*t :=
  let (ok,ko) := partition_aux f s nil nil in
  (treeify ok, treeify ko).

(** ** Union, intersection, difference *)

(** union of the elements of [l1] and [l2] into a third [acc] list. *)

Fixpoint union_list l1 : list elt -> list elt -> list elt :=
 match l1 with
 | nil => @rev_append _
 | x::l1' =>
    fix union_l1 l2 acc :=
    match l2 with
    | nil => rev_append l1 acc
    | y::l2' =>
       match X.compare x y with
       | Eq => union_list l1' l2' (x::acc)
       | Lt => union_l1 l2' (y::acc)
       | Gt => union_list l1' l2 (x::acc)
       end
    end
 end.

Definition linear_union s1 s2 :=
  treeify (union_list (rev_elements s1) (rev_elements s2) nil).

Fixpoint inter_list l1 : list elt -> list elt -> list elt :=
 match l1 with
 | nil => fun _ acc => acc
 | x::l1' =>
    fix inter_l1 l2 acc :=
    match l2 with
    | nil => acc
    | y::l2' =>
       match X.compare x y with
       | Eq => inter_list l1' l2' (x::acc)
       | Lt => inter_l1 l2' acc
       | Gt => inter_list l1' l2 acc
       end
    end
 end.

Definition linear_inter s1 s2 :=
  treeify (inter_list (rev_elements s1) (rev_elements s2) nil).

Fixpoint diff_list l1 : list elt -> list elt -> list elt :=
 match l1 with
 | nil => fun _ acc => acc
 | x::l1' =>
    fix diff_l1 l2 acc :=
    match l2 with
    | nil => rev_append l1 acc
    | y::l2' =>
       match X.compare x y with
       | Eq => diff_list l1' l2' acc
       | Lt => diff_l1 l2' acc
       | Gt => diff_list l1' l2 (x::acc)
       end
    end
 end.

Definition linear_diff s1 s2 :=
  treeify (diff_list (rev_elements s1) (rev_elements s2) nil).

(** [compare_height] returns:
  - [Lt] if [height s2] is at least twice [height s1];
  - [Gt] if [height s1] is at least twice [height s2];
  - [Eq] if heights are approximately equal.
  Warning: this is not an equivalence relation! but who cares.... *)

Definition skip_red t :=
 match t with
 | Rd t' _ _ => t'
 | _ => t
 end.

Definition skip_black t :=
 match skip_red t with
 | Bk t' _ _ => t'
 | t' => t'
 end.

Fixpoint compare_height (s1x s1 s2 s2x: tree) : comparison :=
 match skip_red s1x, skip_red s1, skip_red s2, skip_red s2x with
 | Node _ s1x' _ _, Node _ s1' _ _, Node _ s2' _ _, Node _ s2x' _ _ =>
   compare_height (skip_black s1x') s1' s2' (skip_black s2x')
 | _, Leaf, _, Node _ _ _ _ => Lt
 | Node _ _ _ _, _, Leaf, _ => Gt
 | Node _ s1x' _ _, Node _ s1' _ _, Node _ s2' _ _, Leaf =>
   compare_height (skip_black s1x') s1' s2' Leaf
 | Leaf, Node _ s1' _ _, Node _ s2' _ _, Node _ s2x' _ _ =>
   compare_height Leaf s1'  s2'  (skip_black s2x')
 | _, _, _, _ => Eq
 end.

(** When one tree is quite smaller than the other, we simply
    adds repeatively all its elements in the big one.
    For trees of comparable height, we rather use [linear_union]. *)

Definition union (t1 t2: t) : t :=
 match compare_height t1 t1 t2 t2 with
 | Lt => fold add t1 t2
 | Gt => fold add t2 t1
 | Eq => linear_union t1 t2
 end.

Definition diff (t1 t2: t) : t :=
 match compare_height t1 t1 t2 t2 with
 | Lt => filter (fun k => negb (mem k t2)) t1
 | Gt => fold remove t2 t1
 | Eq => linear_diff t1 t2
 end.

Definition inter (t1 t2: t) : t :=
 match compare_height t1 t1 t2 t2 with
 | Lt => filter (fun k => mem k t2) t1
 | Gt => filter (fun k => mem k t1) t2
 | Eq => linear_inter t1 t2
 end.

End Ops.

(** * MakeRaw : the pure functions and their specifications *)

Module Type MakeRaw (X:Orders.OrderedType) <: MSetInterface.RawSets X.
Include Ops X.

(** Generic definition of binary-search-trees and proofs of
    specifications for generic functions such as mem or fold. *)

Include MSetGenTree.Props X Color.

Local Notation Rd := (Node Red).
Local Notation Bk := (Node Black).

Local Hint Immediate MX.eq_sym.
Local Hint Unfold In lt_tree gt_tree Ok.
Local Hint Constructors InT bst.
Local Hint Resolve MX.eq_refl MX.eq_trans MX.lt_trans ok.
Local Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.
Local Hint Resolve lt_tree_not_in lt_tree_trans gt_tree_not_in gt_tree_trans.
Local Hint Resolve elements_spec2.

(** ** Singleton set *)

Lemma singleton_spec x y : InT y (singleton x) <-> X.eq y x.
Proof.
 unfold singleton; intuition_in.
Qed.

Instance singleton_ok x : Ok (singleton x).
Proof.
 unfold singleton; auto.
Qed.

(** ** makeBlack, MakeRed *)

Lemma makeBlack_spec s x : InT x (makeBlack s) <-> InT x s.
Proof.
 destruct s; simpl; intuition_in.
Qed.

Lemma makeRed_spec s x : InT x (makeRed s) <-> InT x s.
Proof.
 destruct s; simpl; intuition_in.
Qed.

Instance makeBlack_ok s `{Ok s} : Ok (makeBlack s).
Proof.
 destruct s; simpl; ok.
Qed.

Instance makeRed_ok s `{Ok s} : Ok (makeRed s).
Proof.
 destruct s; simpl; ok.
Qed.

(** ** Generic handling for red-matching and red-red-matching *)

Definition isblack t :=
 match t with Bk _ _ _ => True | _ => False end.

Definition notblack t :=
 match t with Bk _ _ _ => False | _ => True end.

Definition notred t :=
 match t with Rd _ _ _ => False | _ => True end.

Definition rcase {A} f g t : A :=
 match t with
 | Rd a x b => f a x b
 | _ => g t
 end.

Inductive rspec {A} f g : tree -> A -> Prop :=
 | rred a x b : rspec f g (Rd a x b) (f a x b)
 | relse t : notred t -> rspec f g t (g t).

Fact rmatch {A} f g t : rspec (A:=A) f g t (rcase f g t).
Proof.
destruct t as [|[|] l x r]; simpl; now constructor.
Qed.

Definition rrcase {A} f g t : A :=
 match t with
 | Rd (Rd a x b) y c => f a x b y c
 | Rd a x (Rd b y c) => f a x b y c
 | _ => g t
 end.

Notation notredred := (rrcase (fun _ _ _ _ _ => False) (fun _ => True)).

Inductive rrspec {A} f g : tree -> A -> Prop :=
 | rrleft a x b y c : rrspec f g (Rd (Rd a x b) y c) (f a x b y c)
 | rrright a x b y c : rrspec f g (Rd a x (Rd b y c)) (f a x b y c)
 | rrelse t : notredred t -> rrspec f g t (g t).

Fact rrmatch {A} f g t : rrspec (A:=A) f g t (rrcase f g t).
Proof.
destruct t as [|[|] l x r]; simpl; try now constructor.
destruct l as [|[|] ll lx lr], r as [|[|] rl rx rr]; now constructor.
Qed.

Definition rrcase' {A} f g t : A :=
 match t with
 | Rd a x (Rd b y c) => f a x b y c
 | Rd (Rd a x b) y c => f a x b y c
 | _ => g t
 end.

Fact rrmatch' {A} f g t : rrspec (A:=A) f g t (rrcase' f g t).
Proof.
destruct t as [|[|] l x r]; simpl; try now constructor.
destruct l as [|[|] ll lx lr], r as [|[|] rl rx rr]; now constructor.
Qed.

(** Balancing operations are instances of generic match *)

Fact lbal_match l k r :
 rrspec
   (fun a x b y c => Rd (Bk a x b) y (Bk c k r))
   (fun l => Bk l k r)
   l
   (lbal l k r).
Proof.
 exact (rrmatch _ _ _).
Qed.

Fact rbal_match l k r :
 rrspec
   (fun a x b y c => Rd (Bk l k a) x (Bk b y c))
   (fun r => Bk l k r)
   r
   (rbal l k r).
Proof.
 exact (rrmatch _ _ _).
Qed.

Fact rbal'_match l k r :
 rrspec
   (fun a x b y c => Rd (Bk l k a) x (Bk b y c))
   (fun r => Bk l k r)
   r
   (rbal' l k r).
Proof.
 exact (rrmatch' _ _ _).
Qed.

Fact lbalS_match l x r :
 rspec
  (fun a y b => Rd (Bk a y b) x r)
  (fun l =>
    match r with
    | Bk a y b => rbal' l x (Rd a y b)
    | Rd (Bk a y b) z c => Rd (Bk l x a) y (rbal' b z (makeRed c))
    | _ => Rd l x r
    end)
  l
  (lbalS l x r).
Proof.
 exact (rmatch _ _ _).
Qed.

Fact rbalS_match l x r :
 rspec
  (fun a y b => Rd l x (Bk a y b))
  (fun r =>
    match l with
    | Bk a y b => lbal (Rd a y b) x r
    | Rd a y (Bk b z c) => Rd (lbal (makeRed a) y b) z (Bk c x r)
    | _ => Rd l x r
    end)
  r
  (rbalS l x r).
Proof.
 exact (rmatch _ _ _).
Qed.

(** ** Balancing for insertion *)

Lemma lbal_spec l x r y :
   InT y (lbal l x r) <-> X.eq y x \/ InT y l \/ InT y r.
Proof.
 case lbal_match; intuition_in.
Qed.

Instance lbal_ok l x r `(Ok l, Ok r, lt_tree x l, gt_tree x r) :
 Ok (lbal l x r).
Proof.
 destruct (lbal_match l x r); ok.
Qed.

Lemma rbal_spec l x r y :
   InT y (rbal l x r) <-> X.eq y x \/ InT y l \/ InT y r.
Proof.
 case rbal_match; intuition_in.
Qed.

Instance rbal_ok l x r `(Ok l, Ok r, lt_tree x l, gt_tree x r) :
 Ok (rbal l x r).
Proof.
 destruct (rbal_match l x r); ok.
Qed.

Lemma rbal'_spec l x r y :
   InT y (rbal' l x r) <-> X.eq y x \/ InT y l \/ InT y r.
Proof.
 case rbal'_match; intuition_in.
Qed.

Instance rbal'_ok l x r `(Ok l, Ok r, lt_tree x l, gt_tree x r) :
 Ok (rbal' l x r).
Proof.
 destruct (rbal'_match l x r); ok.
Qed.

Hint Rewrite In_node_iff In_leaf_iff
 makeRed_spec makeBlack_spec lbal_spec rbal_spec rbal'_spec : rb.

Ltac descolor := destruct_all Color.t.
Ltac destree t := destruct t as [|[|] ? ? ?].
Ltac autorew := autorewrite with rb.
Tactic Notation "autorew" "in" ident(H) := autorewrite with rb in H.

(** ** Insertion *)

Lemma ins_spec : forall s x y,
 InT y (ins x s) <-> X.eq y x \/ InT y s.
Proof.
 induct s x.
 - intuition_in.
 - intuition_in. setoid_replace y with x; eauto.
 - descolor; autorew; rewrite IHl; intuition_in.
 - descolor; autorew; rewrite IHr; intuition_in.
Qed.
Hint Rewrite ins_spec : rb.

Instance ins_ok s x `{Ok s} : Ok (ins x s).
Proof.
 induct s x; auto; descolor;
 (apply lbal_ok || apply rbal_ok || ok); auto;
 intros y; autorew; intuition; order.
Qed.

Lemma add_spec' s x y :
 InT y (add x s) <-> X.eq y x \/ InT y s.
Proof.
 unfold add. now autorew.
Qed.

Hint Rewrite add_spec' : rb.

Lemma add_spec s x y `{Ok s} :
 InT y (add x s) <-> X.eq y x \/ InT y s.
Proof.
 apply add_spec'.
Qed.

Instance add_ok s x `{Ok s} : Ok (add x s).
Proof.
 unfold add; auto_tc.
Qed.

(** ** Balancing for deletion *)

Lemma lbalS_spec l x r y :
  InT y (lbalS l x r) <-> X.eq y x \/ InT y l \/ InT y r.
Proof.
 case lbalS_match.
 - intros; autorew; intuition_in.
 - clear l. intros l _.
   destruct r as [|[|] rl rx rr].
   * autorew. intuition_in.
   * destree rl; autorew; intuition_in.
   * autorew. intuition_in.
Qed.

Instance lbalS_ok l x r :
 forall `(Ok l, Ok r, lt_tree x l, gt_tree x r), Ok (lbalS l x r).
Proof.
 case lbalS_match; intros.
 - ok.
 - destruct r as [|[|] rl rx rr].
   * ok.
   * destruct rl as [|[|] rll rlx rlr]; intros; ok.
     + apply rbal'_ok; ok.
       intros w; autorew; auto.
     + intros w; autorew.
       destruct 1 as [Hw|[Hw|Hw]]; try rewrite Hw; eauto.
   * ok. autorew. apply rbal'_ok; ok.
Qed.

Lemma rbalS_spec l x r y :
  InT y (rbalS l x r) <-> X.eq y x \/ InT y l \/ InT y r.
Proof.
 case rbalS_match.
 - intros; autorew; intuition_in.
 - intros t _.
   destruct l as [|[|] ll lx lr].
   * autorew. intuition_in.
   * destruct lr as [|[|] lrl lrx lrr]; autorew; intuition_in.
   * autorew. intuition_in.
Qed.

Instance rbalS_ok l x r :
 forall `(Ok l, Ok r, lt_tree x l, gt_tree x r), Ok (rbalS l x r).
Proof.
 case rbalS_match; intros.
 - ok.
 - destruct l as [|[|] ll lx lr].
   * ok.
   * destruct lr as [|[|] lrl lrx lrr]; intros; ok.
     + apply lbal_ok; ok.
       intros w; autorew; auto.
     + intros w; autorew.
       destruct 1 as [Hw|[Hw|Hw]]; try rewrite Hw; eauto.
   * ok. apply lbal_ok; ok.
Qed.

Hint Rewrite lbalS_spec rbalS_spec : rb.

(** ** Append for deletion *)

Ltac append_tac l r :=
 induction l as [| lc ll _ lx lr IHlr];
 [intro r; simpl
 |induction r as [| rc rl IHrl rx rr _];
   [simpl
   |destruct lc, rc;
     [specialize (IHlr rl); clear IHrl
     |simpl;
      assert (Hr:notred (Bk rl rx rr)) by (simpl; trivial);
      set (r:=Bk rl rx rr) in *; clearbody r; clear IHrl rl rx rr;
      specialize (IHlr r)
     |change (append _ _) with (Rd (append (Bk ll lx lr) rl) rx rr);
      assert (Hl:notred (Bk ll lx lr)) by (simpl; trivial);
      set (l:=Bk ll lx lr) in *; clearbody l; clear IHlr ll lx lr
     |specialize (IHlr rl); clear IHrl]]].

Fact append_rr_match ll lx lr rl rx rr :
 rspec
  (fun a x b => Rd (Rd ll lx a) x (Rd b rx rr))
  (fun t => Rd ll lx (Rd t rx rr))
  (append lr rl)
  (append (Rd ll lx lr) (Rd rl rx rr)).
Proof.
 exact (rmatch _ _ _).
Qed.

Fact append_bb_match ll lx lr rl rx rr :
 rspec
  (fun a x b => Rd (Bk ll lx a) x (Bk b rx rr))
  (fun t => lbalS ll lx (Bk t rx rr))
  (append lr rl)
  (append (Bk ll lx lr) (Bk rl rx rr)).
Proof.
 exact (rmatch _ _ _).
Qed.

Lemma append_spec l r x :
 InT x (append l r) <-> InT x l \/ InT x r.
Proof.
 revert r.
 append_tac l r; autorew; try tauto.
 - (* Red / Red *)
   revert IHlr; case append_rr_match;
    [intros a y b | intros t Ht]; autorew; tauto.
 - (* Black / Black *)
   revert IHlr; case append_bb_match;
    [intros a y b | intros t Ht]; autorew; tauto.
Qed.

Hint Rewrite append_spec : rb.

Lemma append_ok : forall x l r `{Ok l, Ok r},
 lt_tree x l -> gt_tree x r -> Ok (append l r).
Proof.
 append_tac l r.
 - (* Leaf / _ *)
   trivial.
 - (* _ / Leaf *)
   trivial.
 - (* Red / Red *)
   intros; inv.
   assert (IH : Ok (append lr rl)) by (apply IHlr; eauto). clear IHlr.
   assert (X.lt lx rx) by (transitivity x; eauto).
   assert (G : gt_tree lx (append lr rl)).
    { intros w. autorew. destruct 1; [|transitivity x]; eauto. }
   assert (L : lt_tree rx (append lr rl)).
    { intros w. autorew. destruct 1; [transitivity x|]; eauto. }
   revert IH G L; case append_rr_match; intros; ok.
 - (* Red / Black *)
   intros; ok.
   intros w; autorew; destruct 1; eauto.
 - (* Black / Red *)
   intros; ok.
   intros w; autorew; destruct 1; eauto.
 - (* Black / Black *)
   intros; inv.
   assert (IH : Ok (append lr rl)) by (apply IHlr; eauto). clear IHlr.
   assert (X.lt lx rx) by (transitivity x; eauto).
   assert (G : gt_tree lx (append lr rl)).
    { intros w. autorew. destruct 1; [|transitivity x]; eauto. }
   assert (L : lt_tree rx (append lr rl)).
    { intros w. autorew. destruct 1; [transitivity x|]; eauto. }
   revert IH G L; case append_bb_match; intros; ok.
    apply lbalS_ok; ok.
Qed.

(** ** Deletion *)

Lemma del_spec : forall s x y `{Ok s},
 InT y (del x s) <-> InT y s /\ ~X.eq y x.
Proof.
induct s x.
- intuition_in.
- autorew; intuition_in.
  assert (X.lt y x') by eauto. order.
  assert (X.lt x' y) by eauto. order.
  order.
- destruct l as [|[|] ll lx lr]; autorew;
  rewrite ?IHl by trivial; intuition_in; order.
- destruct r as [|[|] rl rx rr]; autorew;
  rewrite ?IHr by trivial; intuition_in; order.
Qed.

Hint Rewrite del_spec : rb.

Instance del_ok s x `{Ok s} : Ok (del x s).
Proof.
induct s x.
- trivial.
- eapply append_ok; eauto.
- assert (lt_tree x' (del x l)).
  { intro w. autorew; trivial. destruct 1. eauto. }
  destruct l as [|[|] ll lx lr]; auto_tc.
- assert (gt_tree x' (del x r)).
  { intro w. autorew; trivial. destruct 1. eauto. }
  destruct r as [|[|] rl rx rr]; auto_tc.
Qed.

Lemma remove_spec s x y `{Ok s} :
 InT y (remove x s) <-> InT y s /\ ~X.eq y x.
Proof.
unfold remove. now autorew.
Qed.

Hint Rewrite remove_spec : rb.

Instance remove_ok s x `{Ok s} : Ok (remove x s).
Proof.
unfold remove; auto_tc.
Qed.

(** ** Removing the minimal element *)

Lemma delmin_spec l y r c x s' `{O : Ok (Node c l y r)} :
 delmin l y r = (x,s') ->
  min_elt (Node c l y r) = Some x /\ del x (Node c l y r) = s'.
Proof.
 revert y r c x s' O.
 induction l as [|lc ll IH ly lr _].
 - simpl. intros y r _ x s' _. injection 1; intros; subst.
   now rewrite MX.compare_refl.
 - intros y r c x s' O.
   simpl delmin.
   specialize (IH ly lr). destruct delmin as (x0,s0).
   destruct (IH lc x0 s0); clear IH; [ok|trivial|].
   remember (Node lc ll ly lr) as l.
   simpl min_elt in *.
   intros E.
   replace x0 with x in * by (destruct lc; now injection E).
   split.
   * subst l; intuition.
   * assert (X.lt x y).
     { inversion_clear O.
       assert (InT x l) by now apply min_elt_spec1. auto. }
     simpl. case X.compare_spec; try order.
     destruct lc; injection E; subst l s0; auto.
Qed.

Lemma remove_min_spec1 s x s' `{Ok s}:
 remove_min s = Some (x,s') ->
  min_elt s = Some x /\ remove x s = s'.
Proof.
 unfold remove_min.
 destruct s as [|c l y r]; try easy.
 generalize (delmin_spec l y r c).
 destruct delmin as (x0,s0). intros D.
 destruct (D x0 s0) as (->,<-); auto.
 fold (remove x0 (Node c l y r)).
 inversion_clear 1; auto.
Qed.

Lemma remove_min_spec2 s : remove_min s = None -> Empty s.
Proof.
 unfold remove_min.
 destruct s as [|c l y r].
 - easy.
 - now destruct delmin.
Qed.

Lemma remove_min_ok (s:t) `{Ok s}:
 match remove_min s with
 | Some (_,s') => Ok s'
 | None => True
 end.
Proof.
 generalize (remove_min_spec1 s).
 destruct remove_min as [(x0,s0)|]; auto.
 intros R. destruct (R x0 s0); auto. subst s0. auto_tc.
Qed.

(** ** Treeify *)

Notation ifpred p n := (if p then pred n else n%nat).

Definition treeify_invariant size (f:treeify_t) :=
 forall acc,
 size <= length acc ->
 let (t,acc') := f acc in
 cardinal t = size /\ acc = elements t ++ acc'.

Lemma treeify_zero_spec : treeify_invariant 0 treeify_zero.
Proof.
 intro. simpl. auto.
Qed.

Lemma treeify_one_spec : treeify_invariant 1 treeify_one.
Proof.
 intros [|x acc]; simpl; auto; inversion 1.
Qed.

Lemma treeify_cont_spec f g size1 size2 size :
 treeify_invariant size1 f ->
 treeify_invariant size2 g ->
 size = S (size1 + size2) ->
 treeify_invariant size (treeify_cont f g).
Proof.
 intros Hf Hg EQ acc LE. unfold treeify_cont.
 specialize (Hf acc).
 destruct (f acc) as (t1,acc1).
 destruct Hf as (Hf1,Hf2).
  { transitivity size; trivial. subst. auto with arith. }
 destruct acc1 as [|x acc1].
  { exfalso. revert LE. apply Nat.lt_nge. subst.
    rewrite app_nil_r, <- elements_cardinal; auto with arith. }
 specialize (Hg acc1).
 destruct (g acc1) as (t2,acc2).
 destruct Hg as (Hg1,Hg2).
  { revert LE. subst.
    rewrite app_length, <- elements_cardinal. simpl.
    rewrite Nat.add_succ_r, <- Nat.succ_le_mono.
    apply Nat.add_le_mono_l. }
 rewrite elements_node, app_ass. now subst.
Qed.

Lemma treeify_aux_spec n (p:bool) :
 treeify_invariant (ifpred p (Pos.to_nat n)) (treeify_aux p n).
Proof.
 revert p.
 induction n as [n|n|]; intros p; simpl treeify_aux.
 - eapply treeify_cont_spec; [ apply (IHn false) | apply (IHn p) | ].
   rewrite Pos2Nat.inj_xI.
   assert (H := Pos2Nat.is_pos n). apply Nat.neq_0_lt_0 in H.
   destruct p; simpl; intros; rewrite Nat.add_0_r; trivial.
   now rewrite <- Nat.add_succ_r, Nat.succ_pred; trivial.
 - eapply treeify_cont_spec; [ apply (IHn p) | apply (IHn true) | ].
   rewrite Pos2Nat.inj_xO.
   assert (H := Pos2Nat.is_pos n). apply Nat.neq_0_lt_0 in H.
   rewrite <- Nat.add_succ_r, Nat.succ_pred by trivial.
   destruct p; simpl; intros; rewrite Nat.add_0_r; trivial.
   symmetry. now apply Nat.add_pred_l.
 - destruct p; [ apply treeify_zero_spec | apply treeify_one_spec ].
Qed.

Lemma plength_aux_spec l p :
  Pos.to_nat (plength_aux l p) = length l + Pos.to_nat p.
Proof.
 revert p. induction l; trivial. simpl plength_aux.
 intros. now rewrite IHl, Pos2Nat.inj_succ, Nat.add_succ_r.
Qed.

Lemma plength_spec l : Pos.to_nat (plength l) = S (length l).
Proof.
 unfold plength. rewrite plength_aux_spec. apply Nat.add_1_r.
Qed.

Lemma treeify_elements l : elements (treeify l) = l.
Proof.
 assert (H := treeify_aux_spec (plength l) true l).
 unfold treeify. destruct treeify_aux as (t,acc); simpl in *.
 destruct H as (H,H'). { now rewrite plength_spec. }
 subst l. rewrite plength_spec, app_length, <- elements_cardinal in *.
 destruct acc.
 * now rewrite app_nil_r.
 * exfalso. revert H. simpl.
   rewrite Nat.add_succ_r, Nat.add_comm.
   apply Nat.succ_add_discr.
Qed.

Lemma treeify_spec x l : InT x (treeify l) <-> InA X.eq x l.
Proof.
 intros. now rewrite <- elements_spec1, treeify_elements.
Qed.

Lemma treeify_ok l : sort X.lt l -> Ok (treeify l).
Proof.
 intros. apply elements_sort_ok. rewrite treeify_elements; auto.
Qed.


(** ** Filter *)

Lemma filter_app A f (l l':list A) :
 List.filter f (l ++ l') = List.filter f l ++ List.filter f l'.
Proof.
 induction l as [|x l IH]; simpl; trivial.
 destruct (f x); simpl; now rewrite IH.
Qed.

Lemma filter_aux_elements s f acc :
 filter_aux f s acc = List.filter f (elements s) ++ acc.
Proof.
 revert acc.
 induction s as [|c l IHl x r IHr]; trivial.
 intros acc.
 rewrite elements_node, filter_app. simpl.
 destruct (f x); now rewrite IHl, IHr, app_ass.
Qed.

Lemma filter_elements s f :
 elements (filter f s) = List.filter f (elements s).
Proof.
 unfold filter.
 now rewrite treeify_elements, filter_aux_elements, app_nil_r.
Qed.

Lemma filter_spec s x f :
 Proper (X.eq==>Logic.eq) f ->
 (InT x (filter f s) <-> InT x s /\ f x = true).
Proof.
 intros Hf.
 rewrite <- elements_spec1, filter_elements, filter_InA, elements_spec1;
  now auto_tc.
Qed.

Instance filter_ok s f `(Ok s) : Ok (filter f s).
Proof.
 apply elements_sort_ok.
 rewrite filter_elements.
 apply filter_sort with X.eq; auto_tc.
Qed.

(** ** Partition *)

Lemma partition_aux_spec s f acc1 acc2 :
 partition_aux f s acc1 acc2 =
  (filter_aux f s acc1, filter_aux (fun x => negb (f x)) s acc2).
Proof.
 revert acc1 acc2.
 induction s as [ | c l Hl x r Hr ]; simpl.
 - trivial.
 - intros acc1 acc2.
   destruct (f x); simpl; now rewrite Hr, Hl.
Qed.

Lemma partition_spec s f :
 partition f s = (filter f s, filter (fun x => negb (f x)) s).
Proof.
 unfold partition, filter. now rewrite partition_aux_spec.
Qed.

Lemma partition_spec1 s f :
 Proper (X.eq==>Logic.eq) f ->
 Equal (fst (partition f s)) (filter f s).
Proof. now rewrite partition_spec. Qed.

Lemma partition_spec2 s f :
 Proper (X.eq==>Logic.eq) f ->
 Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
Proof. now rewrite partition_spec. Qed.

Instance partition_ok1 s f `(Ok s) : Ok (fst (partition f s)).
Proof. rewrite partition_spec; now apply filter_ok. Qed.

Instance partition_ok2 s f `(Ok s) : Ok (snd (partition f s)).
Proof. rewrite partition_spec; now apply filter_ok. Qed.


(** ** An invariant for binary list functions with accumulator. *)

Ltac inA :=
 rewrite ?InA_app_iff, ?InA_cons, ?InA_nil, ?InA_rev in *; auto_tc.

Record INV l1 l2 acc : Prop := {
 l1_sorted : sort X.lt (rev l1);
 l2_sorted : sort X.lt (rev l2);
 acc_sorted : sort X.lt acc;
 l1_lt_acc x y : InA X.eq x l1 -> InA X.eq y acc -> X.lt x y;
 l2_lt_acc x y : InA X.eq x l2 -> InA X.eq y acc -> X.lt x y}.
Local Hint Resolve l1_sorted l2_sorted acc_sorted.

Lemma INV_init s1 s2 `(Ok s1, Ok s2) :
 INV (rev_elements s1) (rev_elements s2) nil.
Proof.
 rewrite !rev_elements_rev.
 split; rewrite ?rev_involutive; auto; intros; now inA.
Qed.

Lemma INV_sym l1 l2 acc : INV l1 l2 acc -> INV l2 l1 acc.
Proof.
 destruct 1; now split.
Qed.

Lemma INV_drop x1 l1 l2 acc :
  INV (x1 :: l1) l2 acc -> INV l1 l2 acc.
Proof.
 intros (l1s,l2s,accs,l1a,l2a). simpl in *.
 destruct (sorted_app_inv _ _ l1s) as (U & V & W); auto.
 split; auto.
Qed.

Lemma INV_eq x1 x2 l1 l2 acc :
  INV (x1 :: l1) (x2 :: l2) acc -> X.eq x1 x2 ->
  INV l1 l2 (x1 :: acc).
Proof.
 intros (U,V,W,X,Y) EQ. simpl in *.
 destruct (sorted_app_inv _ _ U) as (U1 & U2 & U3); auto.
 destruct (sorted_app_inv _ _ V) as (V1 & V2 & V3); auto.
 split; auto.
 - constructor; auto. apply InA_InfA with X.eq; auto_tc.
 - intros x y; inA; intros Hx [Hy|Hy].
   + apply U3; inA.
   + apply X; inA.
 - intros x y; inA; intros Hx [Hy|Hy].
   + rewrite Hy, EQ; apply V3; inA.
   + apply Y; inA.
Qed.

Lemma INV_lt x1 x2 l1 l2 acc :
  INV (x1 :: l1) (x2 :: l2) acc -> X.lt x1 x2 ->
  INV (x1 :: l1) l2 (x2 :: acc).
Proof.
 intros (U,V,W,X,Y) EQ. simpl in *.
 destruct (sorted_app_inv _ _ U) as (U1 & U2 & U3); auto.
 destruct (sorted_app_inv _ _ V) as (V1 & V2 & V3); auto.
 split; auto.
 - constructor; auto. apply InA_InfA with X.eq; auto_tc.
 - intros x y; inA; intros Hx [Hy|Hy].
   + rewrite Hy; clear Hy. destruct Hx; [order|].
     transitivity x1; auto. apply U3; inA.
   + apply X; inA.
 - intros x y; inA; intros Hx [Hy|Hy].
   + rewrite Hy. apply V3; inA.
   + apply Y; inA.
Qed.

Lemma INV_rev l1 l2 acc :
 INV l1 l2 acc -> Sorted X.lt (rev_append l1 acc).
Proof.
 intros. rewrite rev_append_rev.
 apply SortA_app with X.eq; eauto with *.
 intros x y. inA. eapply @l1_lt_acc; eauto.
Qed.

(** ** union *)

Lemma union_list_ok l1 l2 acc :
 INV l1 l2 acc -> sort X.lt (union_list l1 l2 acc).
Proof.
 revert l2 acc.
 induction l1 as [|x1 l1 IH1];
  [intro l2|induction l2 as [|x2 l2 IH2]];
   intros acc inv.
 - eapply INV_rev, INV_sym; eauto.
 - eapply INV_rev; eauto.
 - simpl. case X.compare_spec; intro C.
   * apply IH1. eapply INV_eq; eauto.
   * apply (IH2 (x2::acc)). eapply INV_lt; eauto.
   * apply IH1. eapply INV_sym, INV_lt; eauto. now apply INV_sym.
Qed.

Instance linear_union_ok s1 s2 `(Ok s1, Ok s2) :
 Ok (linear_union s1 s2).
Proof.
 unfold linear_union. now apply treeify_ok, union_list_ok, INV_init.
Qed.

Instance fold_add_ok s1 s2 `(Ok s1, Ok s2) :
 Ok (fold add s1 s2).
Proof.
 rewrite fold_spec, <- fold_left_rev_right.
 unfold elt in *.
 induction (rev (elements s1)); simpl; unfold flip in *; auto_tc.
Qed.

Instance union_ok s1 s2 `(Ok s1, Ok s2) : Ok (union s1 s2).
Proof.
 unfold union. destruct compare_height; auto_tc.
Qed.

Lemma union_list_spec x l1 l2 acc :
 InA X.eq x (union_list l1 l2 acc) <->
  InA X.eq x l1 \/ InA X.eq x l2 \/ InA X.eq x acc.
Proof.
 revert l2 acc.
 induction l1 as [|x1 l1 IH1].
 - intros l2 acc; simpl. rewrite rev_append_rev. inA. tauto.
 - induction l2 as [|x2 l2 IH2]; intros acc; simpl.
   * rewrite rev_append_rev. inA. tauto.
   * case X.compare_spec; intro C.
     + rewrite IH1, !InA_cons, C; tauto.
     + rewrite (IH2 (x2::acc)), !InA_cons. tauto.
     + rewrite IH1, !InA_cons; tauto.
Qed.

Lemma linear_union_spec s1 s2 x :
 InT x (linear_union s1 s2) <-> InT x s1 \/ InT x s2.
Proof.
 unfold linear_union.
 rewrite treeify_spec, union_list_spec, !rev_elements_rev.
 rewrite !InA_rev, InA_nil, !elements_spec1 by auto_tc.
 tauto.
Qed.

Lemma fold_add_spec s1 s2 x :
 InT x (fold add s1 s2) <-> InT x s1 \/ InT x s2.
Proof.
 rewrite fold_spec, <- fold_left_rev_right.
 rewrite <- (elements_spec1 s1), <- InA_rev by auto_tc.
 unfold elt in *.
 induction (rev (elements s1)); simpl.
 - rewrite InA_nil. tauto.
 - unfold flip. rewrite add_spec', IHl, InA_cons. tauto.
Qed.

Lemma union_spec' s1 s2 x :
 InT x (union s1 s2) <-> InT x s1 \/ InT x s2.
Proof.
 unfold union. destruct compare_height.
 - apply linear_union_spec.
 - apply fold_add_spec.
 - rewrite fold_add_spec. tauto.
Qed.

Lemma union_spec : forall s1 s2 y `{Ok s1, Ok s2},
 (InT y (union s1 s2) <-> InT y s1 \/ InT y s2).
Proof.
 intros; apply union_spec'.
Qed.

(** ** inter *)

Lemma inter_list_ok l1 l2 acc :
 INV l1 l2 acc -> sort X.lt (inter_list l1 l2 acc).
Proof.
 revert l2 acc.
 induction l1 as [|x1 l1 IH1]; [|induction l2 as [|x2 l2 IH2]]; simpl.
 - eauto.
 - eauto.
 - intros acc inv.
   case X.compare_spec; intro C.
   * apply IH1. eapply INV_eq; eauto.
   * apply (IH2 acc). eapply INV_sym, INV_drop, INV_sym; eauto.
   * apply IH1. eapply INV_drop; eauto.
Qed.

Instance linear_inter_ok s1 s2 `(Ok s1, Ok s2) :
 Ok (linear_inter s1 s2).
Proof.
 unfold linear_inter. now apply treeify_ok, inter_list_ok, INV_init.
Qed.

Instance inter_ok s1 s2 `(Ok s1, Ok s2) : Ok (inter s1 s2).
Proof.
 unfold inter. destruct compare_height; auto_tc.
Qed.

Lemma inter_list_spec x l1 l2 acc :
 sort X.lt (rev l1) ->
 sort X.lt (rev l2) ->
 (InA X.eq x (inter_list l1 l2 acc) <->
   (InA X.eq x l1 /\ InA X.eq x l2) \/ InA X.eq x acc).
Proof.
 revert l2 acc.
 induction l1 as [|x1 l1 IH1].
 - intros l2 acc; simpl. inA. tauto.
 - induction l2 as [|x2 l2 IH2]; intros acc.
   * simpl. inA. tauto.
   * simpl. intros U V.
     destruct (sorted_app_inv _ _ U) as (U1 & U2 & U3); auto.
     destruct (sorted_app_inv _ _ V) as (V1 & V2 & V3); auto.
     case X.compare_spec; intro C.
     + rewrite IH1, !InA_cons, C; tauto.
     + rewrite (IH2 acc); auto. inA. intuition; try order.
       assert (X.lt x x1) by (apply U3; inA). order.
     + rewrite IH1; auto. inA. intuition; try order.
       assert (X.lt x x2) by (apply V3; inA). order.
Qed.

Lemma linear_inter_spec s1 s2 x `(Ok s1, Ok s2) :
 InT x (linear_inter s1 s2) <-> InT x s1 /\ InT x s2.
Proof.
 unfold linear_inter.
 rewrite !rev_elements_rev, treeify_spec, inter_list_spec
  by (rewrite rev_involutive; auto_tc).
 rewrite !InA_rev, InA_nil, !elements_spec1 by auto_tc. tauto.
Qed.

Local Instance mem_proper s `(Ok s) :
 Proper (X.eq ==> Logic.eq) (fun k => mem k s).
Proof.
 intros x y EQ. apply Bool.eq_iff_eq_true; rewrite !mem_spec; auto.
 now rewrite EQ.
Qed.

Lemma inter_spec s1 s2 y `{Ok s1, Ok s2} :
 InT y (inter s1 s2) <-> InT y s1 /\ InT y s2.
Proof.
 unfold inter. destruct compare_height.
 - now apply linear_inter_spec.
 - rewrite filter_spec, mem_spec by auto_tc; tauto.
 - rewrite filter_spec, mem_spec by auto_tc; tauto.
Qed.

(** ** difference *)

Lemma diff_list_ok l1 l2 acc :
 INV l1 l2 acc -> sort X.lt (diff_list l1 l2 acc).
Proof.
 revert l2 acc.
 induction l1 as [|x1 l1 IH1];
  [intro l2|induction l2 as [|x2 l2 IH2]];
    intros acc inv.
 - eauto.
 - unfold diff_list. eapply INV_rev; eauto.
 - simpl. case X.compare_spec; intro C.
   * apply IH1. eapply INV_drop, INV_sym, INV_drop, INV_sym; eauto.
   * apply (IH2 acc). eapply INV_sym, INV_drop, INV_sym; eauto.
   * apply IH1. eapply INV_sym, INV_lt; eauto. now apply INV_sym.
Qed.

Instance diff_inter_ok s1 s2 `(Ok s1, Ok s2) :
 Ok (linear_diff s1 s2).
Proof.
 unfold linear_inter. now apply treeify_ok, diff_list_ok, INV_init.
Qed.

Instance fold_remove_ok s1 s2 `(Ok s2) :
 Ok (fold remove s1 s2).
Proof.
 rewrite fold_spec, <- fold_left_rev_right.
 unfold elt in *.
 induction (rev (elements s1)); simpl; unfold flip in *; auto_tc.
Qed.

Instance diff_ok s1 s2 `(Ok s1, Ok s2) : Ok (diff s1 s2).
Proof.
 unfold diff. destruct compare_height; auto_tc.
Qed.

Lemma diff_list_spec x l1 l2 acc :
 sort X.lt (rev l1) ->
 sort X.lt (rev l2) ->
 (InA X.eq x (diff_list l1 l2 acc) <->
   (InA X.eq x l1 /\ ~InA X.eq x l2) \/ InA X.eq x acc).
Proof.
 revert l2 acc.
 induction l1 as [|x1 l1 IH1].
 - intros l2 acc; simpl. inA. tauto.
 - induction l2 as [|x2 l2 IH2]; intros acc.
   * intros; simpl. rewrite rev_append_rev. inA. tauto.
   * simpl. intros U V.
     destruct (sorted_app_inv _ _ U) as (U1 & U2 & U3); auto.
     destruct (sorted_app_inv _ _ V) as (V1 & V2 & V3); auto.
     case X.compare_spec; intro C.
     + rewrite IH1; auto. f_equiv. inA. intuition; try order.
       assert (X.lt x x1) by (apply U3; inA). order.
     + rewrite (IH2 acc); auto. f_equiv. inA. intuition; try order.
       assert (X.lt x x1) by (apply U3; inA). order.
     + rewrite IH1; auto. inA. intuition; try order.
       left; split; auto. destruct 1. order.
       assert (X.lt x x2) by (apply V3; inA). order.
Qed.

Lemma linear_diff_spec s1 s2 x `(Ok s1, Ok s2) :
 InT x (linear_diff s1 s2) <-> InT x s1 /\ ~InT x s2.
Proof.
 unfold linear_diff.
 rewrite !rev_elements_rev, treeify_spec, diff_list_spec
  by (rewrite rev_involutive; auto_tc).
 rewrite !InA_rev, InA_nil, !elements_spec1 by auto_tc. tauto.
Qed.

Lemma fold_remove_spec s1 s2 x `(Ok s2) :
  InT x (fold remove s1 s2) <-> InT x s2 /\ ~InT x s1.
Proof.
 rewrite fold_spec, <- fold_left_rev_right.
 rewrite <- (elements_spec1 s1), <- InA_rev by auto_tc.
 unfold elt in *.
 induction (rev (elements s1)); simpl; intros.
 - rewrite InA_nil. intuition.
 - unfold flip in *. rewrite remove_spec, IHl, InA_cons. tauto.
   clear IHl. induction l; simpl; auto_tc.
Qed.

Lemma diff_spec s1 s2 y `{Ok s1, Ok s2} :
 InT y (diff s1 s2) <-> InT y s1 /\ ~InT y s2.
Proof.
 unfold diff. destruct compare_height.
 - now apply linear_diff_spec.
 - rewrite filter_spec, Bool.negb_true_iff,
     <- Bool.not_true_iff_false, mem_spec;
    intuition.
    intros x1 x2 EQ. f_equal. now apply mem_proper.
 - now apply fold_remove_spec.
Qed.

End MakeRaw.

(** * Balancing properties

    We now prove that all operations preserve a red-black invariant,
    and that trees have hence a logarithmic depth.
*)

Module BalanceProps(X:Orders.OrderedType)(Import M : MakeRaw X).

Local Notation Rd := (Node Red).
Local Notation Bk := (Node Black).
Import M.MX.

(** ** Red-Black invariants *)

(** In a red-black tree :
    - a red node has no red children
    - the black depth at each node is the same along all paths.
    The black depth is here an argument of the predicate. *)

Inductive rbt : nat -> tree -> Prop :=
 | RB_Leaf : rbt 0 Leaf
 | RB_Rd n l k r :
   notred l -> notred r -> rbt n l -> rbt n r -> rbt n (Rd l k r)
 | RB_Bk n l k r : rbt n l -> rbt n r -> rbt (S n) (Bk l k r).

(** A red-red tree is almost a red-black tree, except that it has
    a _red_ root node which _may_ have red children. Note that a
    red-red tree is hence non-empty, and all its strict subtrees
    are red-black. *)

Inductive rrt (n:nat) : tree -> Prop :=
 | RR_Rd l k r : rbt n l -> rbt n r -> rrt n (Rd l k r).

(** An almost-red-black tree is almost a red-black tree, except that
    it's permitted to have two red nodes in a row at the very root (only).
    We implement this notion by saying that a quasi-red-black tree
    is either a red-black tree or a red-red tree. *)

Inductive arbt (n:nat)(t:tree) : Prop :=
 | ARB_RB : rbt n t -> arbt n t
 | ARB_RR : rrt n t -> arbt n t.

(** The main exported invariant : being a red-black tree for some
    black depth. *)

Class Rbt (t:tree) :=  RBT : exists d, rbt d t.

(** ** Basic tactics and results about red-black *)

Scheme rbt_ind := Induction for rbt Sort Prop.
Local Hint Constructors rbt rrt arbt.
Local Hint Extern 0 (notred _) => (exact I).
Ltac invrb := intros; invtree rrt; invtree rbt; try contradiction.
Ltac desarb := match goal with H:arbt _ _ |- _ => destruct H end.
Ltac nonzero n := destruct n as [|n]; [try split; invrb|].

Lemma rr_nrr_rb n t :
 rrt n t -> notredred t -> rbt n t.
Proof.
 destruct 1 as [l x r Hl Hr].
 destruct l, r; descolor; invrb; auto.
Qed.

Local Hint Resolve rr_nrr_rb.

Lemma arb_nrr_rb n t :
 arbt n t -> notredred t -> rbt n t.
Proof.
 destruct 1; auto.
Qed.

Lemma arb_nr_rb n t :
 arbt n t -> notred t -> rbt n t.
Proof.
 destruct 1; destruct t; descolor; invrb; auto.
Qed.

Local Hint Resolve arb_nrr_rb arb_nr_rb.

(** ** A Red-Black tree has indeed a logarithmic depth *)

Definition redcarac s := rcase (fun _ _ _ => 1) (fun _ => 0) s.

Lemma rb_maxdepth s n : rbt n s -> maxdepth s <= 2*n + redcarac s.
Proof.
 induction 1.
 - simpl; auto.
 - replace (redcarac l) with 0 in * by now destree l.
   replace (redcarac r) with 0 in * by now destree r.
   simpl maxdepth. simpl redcarac.
   rewrite Nat.add_succ_r, <- Nat.succ_le_mono.
   now apply Nat.max_lub.
 - simpl. rewrite <- Nat.succ_le_mono.
   apply Nat.max_lub; eapply Nat.le_trans; eauto;
   [destree l | destree r]; simpl;
   rewrite !Nat.add_0_r, ?Nat.add_1_r; auto with arith.
Qed.

Lemma rb_mindepth s n : rbt n s -> n + redcarac s <= mindepth s.
Proof.
 induction 1; simpl.
 - trivial.
 - rewrite Nat.add_succ_r.
   apply -> Nat.succ_le_mono.
   replace (redcarac l) with 0 in * by now destree l.
   replace (redcarac r) with 0 in * by now destree r.
   now apply Nat.min_glb.
 - apply -> Nat.succ_le_mono. rewrite Nat.add_0_r.
   apply Nat.min_glb; eauto with arith.
Qed.

Lemma maxdepth_upperbound s : Rbt s ->
 maxdepth s <= 2 * Nat.log2 (S (cardinal s)).
Proof.
 intros (n,H).
 eapply Nat.le_trans; [eapply rb_maxdepth; eauto|].
 transitivity (2*(n+redcarac s)).
 - rewrite Nat.mul_add_distr_l. apply Nat.add_le_mono_l.
   rewrite <- Nat.mul_1_l at 1. apply Nat.mul_le_mono_r.
   auto with arith.
 - apply Nat.mul_le_mono_l.
   transitivity (mindepth s).
   + now apply rb_mindepth.
   + apply mindepth_log_cardinal.
Qed.

Lemma maxdepth_lowerbound s : s<>Leaf ->
 Nat.log2 (cardinal s) < maxdepth s.
Proof.
 apply maxdepth_log_cardinal.
Qed.


(** ** Singleton *)

Lemma singleton_rb x : Rbt (singleton x).
Proof.
 unfold singleton. exists 1; auto.
Qed.

(** ** [makeBlack] and [makeRed] *)

Lemma makeBlack_rb n t : arbt n t -> Rbt (makeBlack t).
Proof.
 destruct t as [|[|] l x r].
 - exists 0; auto.
 - destruct 1; invrb; exists (S n); simpl; auto.
 - exists n; auto.
Qed.

Lemma makeRed_rr t n :
 rbt (S n) t -> notred t -> rrt n (makeRed t).
Proof.
 destruct t as [|[|] l x r]; invrb; simpl; auto.
Qed.

(** ** Balancing *)

Lemma lbal_rb n l k r :
 arbt n l -> rbt n r -> rbt (S n) (lbal l k r).
Proof.
case lbal_match; intros; desarb; invrb; auto.
Qed.

Lemma rbal_rb n l k r :
 rbt n l -> arbt n r -> rbt (S n) (rbal l k r).
Proof.
case rbal_match; intros; desarb; invrb; auto.
Qed.

Lemma rbal'_rb n l k r :
 rbt n l -> arbt n r -> rbt (S n) (rbal' l k r).
Proof.
case rbal'_match; intros; desarb; invrb; auto.
Qed.

Lemma lbalS_rb n l x r :
 arbt n l -> rbt (S n) r -> notred r -> rbt (S n) (lbalS l x r).
Proof.
 intros Hl Hr Hr'.
 destruct r as [|[|] rl rx rr]; invrb. clear Hr'.
 revert Hl.
 case lbalS_match.
 - destruct 1; invrb; auto.
 - intros. apply rbal'_rb; auto.
Qed.

Lemma lbalS_arb n l x r :
 arbt n l -> rbt (S n) r -> arbt (S n) (lbalS l x r).
Proof.
 case lbalS_match.
 - destruct 1; invrb; auto.
 - clear l. intros l Hl Hl' Hr.
   destruct r as [|[|] rl rx rr]; invrb.
   * destruct rl as [|[|] rll rlx rlr]; invrb.
     right; auto using rbal'_rb, makeRed_rr.
   * left; apply rbal'_rb; auto.
Qed.

Lemma rbalS_rb n l x r :
 rbt (S n) l -> notred l -> arbt n r -> rbt (S n) (rbalS l x r).
Proof.
 intros Hl Hl' Hr.
 destruct l as [|[|] ll lx lr]; invrb. clear Hl'.
 revert Hr.
 case rbalS_match.
 - destruct 1; invrb; auto.
 - intros. apply lbal_rb; auto.
Qed.

Lemma rbalS_arb n l x r :
 rbt (S n) l -> arbt n r -> arbt (S n) (rbalS l x r).
Proof.
 case rbalS_match.
 - destruct 2; invrb; auto.
 - clear r. intros r Hr Hr' Hl.
   destruct l as [|[|] ll lx lr]; invrb.
   * destruct lr as [|[|] lrl lrx lrr]; invrb.
     right; auto using lbal_rb, makeRed_rr.
   * left; apply lbal_rb; auto.
Qed.


(** ** Insertion *)

(** The next lemmas combine simultaneous results about rbt and arbt.
    A first solution here: statement with [if ... then ... else] *)

Definition ifred s (A B:Prop) := rcase (fun _ _ _ => A) (fun _ => B) s.

Lemma ifred_notred s A B : notred s -> (ifred s A B <-> B).
Proof.
 destruct s; descolor; simpl; intuition.
Qed.

Lemma ifred_or s A B : ifred s A B -> A\/B.
Proof.
 destruct s; descolor; simpl; intuition.
Qed.

Lemma ins_rr_rb x s n : rbt n s ->
 ifred s (rrt n (ins x s)) (rbt n (ins x s)).
Proof.
induction 1 as [ | n l k r | n l k r Hl IHl Hr IHr ].
- simpl; auto.
- simpl. rewrite ifred_notred in * by trivial.
  elim_compare x k; auto.
- rewrite ifred_notred by trivial.
  unfold ins; fold ins. (* simpl is too much here ... *)
  elim_compare x k.
  * auto.
  * apply lbal_rb; trivial. apply ifred_or in IHl; intuition.
  * apply rbal_rb; trivial. apply ifred_or in IHr; intuition.
Qed.

Lemma ins_arb x s n : rbt n s -> arbt n (ins x s).
Proof.
 intros H. apply (ins_rr_rb x), ifred_or in H. intuition.
Qed.

Instance add_rb x s : Rbt s -> Rbt (add x s).
Proof.
 intros (n,H). unfold add. now apply (makeBlack_rb n), ins_arb.
Qed.

(** ** Deletion *)

(** A second approach here: statement with ... /\ ... *)

Lemma append_arb_rb n l r : rbt n l -> rbt n r ->
 (arbt n (append l r)) /\
 (notred l -> notred r -> rbt n (append l r)).
Proof.
revert r n.
append_tac l r.
- split; auto.
- split; auto.
- (* Red / Red *)
  intros n. invrb.
  case (IHlr n); auto; clear IHlr.
  case append_rr_match.
  + intros a x b _ H; split; invrb.
    assert (rbt n (Rd a x b)) by auto. invrb. auto.
  + split; invrb; auto.
- (* Red / Black *)
  split; invrb. destruct (IHlr n) as (_,IH); auto.
- (* Black / Red *)
  split; invrb. destruct (IHrl n) as (_,IH); auto.
- (* Black / Black *)
  nonzero n.
  invrb.
  destruct (IHlr n) as (IH,_); auto; clear IHlr.
  revert IH.
  case append_bb_match.
  + intros a x b IH; split; destruct IH; invrb; auto.
  + split; [left | invrb]; auto using lbalS_rb.
Qed.

(** A third approach : Lemma ... with ... *)

Lemma del_arb s x n : rbt (S n) s -> isblack s -> arbt n (del x s)
with del_rb s x n : rbt n s -> notblack s -> rbt n (del x s).
Proof.
{ revert n.
  induct s x; try destruct c; try contradiction; invrb.
  - apply append_arb_rb; assumption.
  - assert (IHl' := del_rb l x). clear IHr del_arb del_rb.
    destruct l as [|[|] ll lx lr]; auto.
    nonzero n. apply lbalS_arb; auto.
  - assert (IHr' := del_rb r x). clear IHl del_arb del_rb.
    destruct r as [|[|] rl rx rr]; auto.
    nonzero n. apply rbalS_arb; auto. }
{ revert n.
  induct s x; try assumption; try destruct c; try contradiction; invrb.
  - apply append_arb_rb; assumption.
  - assert (IHl' := del_arb l x). clear IHr del_arb del_rb.
    destruct l as [|[|] ll lx lr]; auto.
    nonzero n. destruct n as [|n]; [invrb|]; apply lbalS_rb; auto.
  - assert (IHr' := del_arb r x). clear IHl del_arb del_rb.
    destruct r as [|[|] rl rx rr]; auto.
    nonzero n. apply rbalS_rb; auto. }
Qed.

Instance remove_rb s x : Rbt s -> Rbt (remove x s).
Proof.
 intros (n,H). unfold remove.
 destruct s as [|[|] l y r].
 - apply (makeBlack_rb n). auto.
 - apply (makeBlack_rb n). left. apply del_rb; simpl; auto.
 - nonzero n. apply (makeBlack_rb n). apply del_arb; simpl; auto.
Qed.

(** ** Treeify *)

Definition treeify_rb_invariant size depth (f:treeify_t) :=
 forall acc,
 size <= length acc ->
  rbt depth (fst (f acc)) /\
  size + length (snd (f acc)) = length acc.

Lemma treeify_zero_rb : treeify_rb_invariant 0 0 treeify_zero.
Proof.
 intros acc _; simpl; auto.
Qed.

Lemma treeify_one_rb : treeify_rb_invariant 1 0 treeify_one.
Proof.
 intros [|x acc]; simpl; auto; inversion 1.
Qed.

Lemma treeify_cont_rb f g size1 size2 size d :
 treeify_rb_invariant size1 d f ->
 treeify_rb_invariant size2 d g ->
 size = S (size1 + size2) ->
 treeify_rb_invariant size (S d) (treeify_cont f g).
Proof.
 intros Hf Hg H acc Hacc.
 unfold treeify_cont.
 specialize (Hf acc).
 destruct (f acc) as (l, acc1). simpl in *.
 destruct Hf as (Hf1, Hf2). { subst. eauto with arith. }
 destruct acc1 as [|x acc2]; simpl in *.
 - exfalso. revert Hacc. apply Nat.lt_nge. rewrite H, <- Hf2.
   auto with arith.
 - specialize (Hg acc2).
   destruct (g acc2) as (r, acc3). simpl in *.
   destruct Hg as (Hg1, Hg2).
   { revert Hacc.
     rewrite H, <- Hf2, Nat.add_succ_r, <- Nat.succ_le_mono.
     apply Nat.add_le_mono_l. }
   split; auto.
   now rewrite H, <- Hf2, <- Hg2, Nat.add_succ_r, Nat.add_assoc.
Qed.

Lemma treeify_aux_rb n :
 exists d, forall (b:bool),
  treeify_rb_invariant (ifpred b (Pos.to_nat n)) d (treeify_aux b n).
Proof.
 induction n as [n (d,IHn)|n (d,IHn)| ].
 - exists (S d). intros b.
   eapply treeify_cont_rb; [ apply (IHn false) | apply (IHn b) | ].
   rewrite Pos2Nat.inj_xI.
   assert (H := Pos2Nat.is_pos n). apply Nat.neq_0_lt_0 in H.
   destruct b; simpl; intros; rewrite Nat.add_0_r; trivial.
   now rewrite <- Nat.add_succ_r, Nat.succ_pred; trivial.
 - exists (S d). intros b.
   eapply treeify_cont_rb; [ apply (IHn b) | apply (IHn true) | ].
   rewrite Pos2Nat.inj_xO.
   assert (H := Pos2Nat.is_pos n). apply Nat.neq_0_lt_0 in H.
   rewrite <- Nat.add_succ_r, Nat.succ_pred by trivial.
   destruct b; simpl; intros; rewrite Nat.add_0_r; trivial.
   symmetry. now apply Nat.add_pred_l.
 - exists 0; destruct b;
    [ apply treeify_zero_rb | apply treeify_one_rb ].
Qed.

(** The black depth of [treeify l] is actually a log2, but
    we don't need to mention that. *)

Instance treeify_rb l : Rbt (treeify l).
Proof.
 unfold treeify.
 destruct (treeify_aux_rb (plength l)) as (d,H).
 exists d.
 apply H.
 now rewrite plength_spec.
Qed.

(** ** Filtering *)

Instance filter_rb f s : Rbt (filter f s).
Proof.
 unfold filter; auto_tc.
Qed.

Instance partition_rb1 f s : Rbt (fst (partition f s)).
Proof.
 unfold partition. destruct partition_aux. simpl. auto_tc.
Qed.

Instance partition_rb2 f s : Rbt (snd (partition f s)).
Proof.
 unfold partition. destruct partition_aux. simpl. auto_tc.
Qed.

(** ** Union, intersection, difference *)

Instance fold_add_rb s1 s2 : Rbt s2 -> Rbt (fold add s1 s2).
Proof.
 intros. rewrite fold_spec, <- fold_left_rev_right. unfold elt in *.
 induction (rev (elements s1)); simpl; unfold flip in *; auto_tc.
Qed.

Instance fold_remove_rb s1 s2 : Rbt s2 -> Rbt (fold remove s1 s2).
Proof.
 intros. rewrite fold_spec, <- fold_left_rev_right. unfold elt in *.
 induction (rev (elements s1)); simpl; unfold flip in *; auto_tc.
Qed.

Lemma union_rb s1 s2 : Rbt s1 -> Rbt s2 -> Rbt (union s1 s2).
Proof.
 intros. unfold union, linear_union. destruct compare_height; auto_tc.
Qed.

Lemma inter_rb s1 s2 : Rbt s1 -> Rbt s2 -> Rbt (inter s1 s2).
Proof.
 intros. unfold inter, linear_inter. destruct compare_height; auto_tc.
Qed.

Lemma diff_rb s1 s2 : Rbt s1 -> Rbt s2 -> Rbt (diff s1 s2).
Proof.
 intros. unfold diff, linear_diff. destruct compare_height; auto_tc.
Qed.

End BalanceProps.

(** * Final Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of binary search trees.
   They also happen to be well-balanced, but this has no influence
   on the correctness of operations, so we won't state this here,
   see [BalanceProps] if you need more than just the MSet interface.
*)

Module Type MSetInterface_S_Ext := MSetInterface.S <+ MSetRemoveMin.

Module Make (X: Orders.OrderedType) <:
 MSetInterface_S_Ext with Module E := X.
 Module Raw. Include MakeRaw X. End Raw.
 Include MSetInterface.Raw2Sets X Raw.

 Definition opt_ok (x:option (elt * Raw.t)) :=
  match x with Some (_,s) => Raw.Ok s | None => True end.

 Definition mk_opt_t (x: option (elt * Raw.t))(P: opt_ok x) :
   option (elt * t) :=
 match x as o return opt_ok o -> option (elt * t) with
 | Some (k,s') => fun P : Raw.Ok s' => Some (k, Mkt s')
 | None => fun _ => None
 end P.

 Definition remove_min s : option (elt * t) :=
  mk_opt_t (Raw.remove_min (this s)) (Raw.remove_min_ok s).

 Lemma remove_min_spec1 s x s' :
  remove_min s = Some (x,s') ->
   min_elt s = Some x /\ Equal (remove x s) s'.
 Proof.
 destruct s as (s,Hs).
 unfold remove_min, mk_opt_t, min_elt, remove, Equal, In; simpl.
 generalize (fun x s' => @Raw.remove_min_spec1 s x s' Hs).
 set (P := Raw.remove_min_ok s). clearbody P.
 destruct (Raw.remove_min s) as [(x0,s0)|]; try easy.
 intros H U. injection U as -> <-. simpl.
 destruct (H x s0); auto. subst; intuition.
 Qed.

 Lemma remove_min_spec2 s : remove_min s = None -> Empty s.
 Proof.
 destruct s as (s,Hs).
 unfold remove_min, mk_opt_t, Empty, In; simpl.
 generalize (Raw.remove_min_spec2 s).
 set (P := Raw.remove_min_ok s). clearbody P.
 destruct (Raw.remove_min s) as [(x0,s0)|]; now intuition.
 Qed.

End Make.

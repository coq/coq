(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite map library.  *)

(** * MMapAVL *)

(** This module implements maps using AVL trees.
    It follows the implementation from Ocaml's standard library.

    See the comments at the beginning of MSetAVL for more details.
*)

Require Import Bool PeanoNat BinInt Int MMapInterface MMapList.
Require Import Orders OrdersFacts OrdersLists.

Set Implicit Arguments.
Unset Strict Implicit.
(* For nicer extraction, we create inductive principles
   only when needed *)
Local Unset Elimination Schemes.

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

(** The [mem] function is deciding membership. It exploits the [Bst] property
    to achieve logarithmic complexity. *)

Fixpoint mem x m : bool :=
  match m with
    |  Leaf => false
    |  Node l y _ r _ =>
       match X.compare x y with
         | Eq => true
         | Lt => mem x l
         | Gt => mem x r
       end
  end.

Fixpoint find x m : option elt :=
  match m with
    |  Leaf => None
    |  Node l y d r _ =>
       match X.compare x y with
         | Eq => Some d
         | Lt => find x l
         | Gt => find x r
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
  if (hr+2) <? hl then
    match l with
     | Leaf => assert_false l x d r
     | Node ll lx ld lr _ =>
       if (height lr) <=? (height ll) then
         create ll lx ld (create lr x d r)
       else
         match lr with
          | Leaf => assert_false l x d r
          | Node lrl lrx lrd lrr _ =>
              create (create ll lx ld lrl) lrx lrd (create lrr x d r)
         end
    end
  else
    if (hl+2) <? hr then
      match r with
       | Leaf => assert_false l x d r
       | Node rl rx rd rr _ =>
         if (height rl) <=? (height rr) then
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
        | Eq => Node l y d r h
        | Lt => bal (add x d l) y d' r
        | Gt => bal l y d' (add x d r)
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

  [merge0 t1 t2] builds the union of [t1] and [t2] assuming all elements
  of [t1] to be smaller than all elements of [t2], and
  [|height t1 - height t2| <= 2].
*)

Definition merge0 s1 s2 :=
  match s1,s2 with
    | Leaf, _ => s2
    | _, Leaf => s1
    | _, Node l2 x2 d2 r2 h2 =>
      let '(s2',(x,d)) := remove_min l2 x2 d2 r2 in
      bal s1 x d s2'
  end.

(** * Deletion *)

Fixpoint remove x m := match m with
  | Leaf => Leaf
  | Node l y d r h =>
      match X.compare x y with
         | Eq => merge0 l r
         | Lt => bal (remove x l) y d r
         | Gt => bal l y d (remove x r)
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
            if rh+2 <? lh then bal ll lx ld (join lr x d r)
            else if lh+2 <? rh then bal (join_aux rl) rx rd rr
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
Notation "〚 l , b , r 〛" := (mktriple l b r) (at level 9).

Fixpoint split x m : triple := match m with
  | Leaf => 〚 Leaf, None, Leaf 〛
  | Node l y d r h =>
     match X.compare x y with
      | Lt => let (ll,o,rl) := split x l in 〚 ll, o, join rl y d r 〛
      | Eq => 〚 l, Some d, r 〛
      | Gt => let (rl,o,rr) := split x r in 〚 join l y d rl, o, rr 〛
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

(** * Bindings *)

(** [bindings_aux acc t] catenates the bindings of [t] in infix
    order to the list [acc] *)

Fixpoint bindings_aux (acc : list (key*elt)) m : list (key*elt) :=
  match m with
   | Leaf => acc
   | Node l x d r _ => bindings_aux ((x,d) :: bindings_aux acc r) l
  end.

(** then [bindings] is an instantiation with an empty [acc] *)

Definition bindings := bindings_aux nil.

(** * Fold *)

Fixpoint fold {A} (f : key -> elt -> A -> A) (m : t) : A -> A :=
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
      | Eq => cmp d1 d2 &&& cont (cons r2 e2)
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
Notation "〚 l , b , r 〛" := (mktriple l b r) (at level 9).
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

Fixpoint mapo (elt elt' : Type)(f : key -> elt -> option elt')(m : t elt)
  : t elt' :=
  match m with
   | Leaf _ => Leaf _
   | Node l x d r h =>
      match f x d with
       | Some d' => join (mapo f l) x d' (mapo f r)
       | None => concat (mapo f l) (mapo f r)
      end
  end.

(** * Generalized merge

  Suggestion by B. Gregoire: a [merge] function with specialized
  arguments that allows bypassing some tree traversal. Instead of one
  [f0] of type [key -> option elt -> option elt' -> option elt''],
  we ask here for:
  - [f] which is a specialisation of [f0] when first option isn't [None]
  - [mapl] treats a [tree elt] with [f0] when second option is [None]
  - [mapr] treats a [tree elt'] with [f0] when first option is [None]

  The idea is that [mapl] and [mapr] can be instantaneous (e.g.
  the identity or some constant function).
*)

Section GMerge.
Variable elt elt' elt'' : Type.
Variable f : key -> elt -> option elt' -> option elt''.
Variable mapl : t elt -> t elt''.
Variable mapr : t elt' -> t elt''.

Fixpoint gmerge m1 m2 :=
 match m1, m2 with
  | Leaf _, _ => mapr m2
  | _, Leaf _ => mapl m1
  | Node l1 x1 d1 r1 h1, _ =>
     let (l2',o2,r2') := split x1 m2 in
     match f x1 d1 o2 with
      | Some e => join (gmerge l1 l2') x1 e (gmerge r1 r2')
      | None => concat (gmerge l1 l2') (gmerge r1 r2')
     end
 end.

End GMerge.

(** * Merge

    The [merge] function of the Map interface can be implemented
    via [gmerge] and [mapo].
*)

Section Merge.
Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.

Definition merge : t elt -> t elt' -> t elt'' :=
 gmerge
   (fun k d o => f k (Some d) o)
   (mapo (fun k d => f k (Some d) None))
   (mapo (fun k d' => f k None (Some d'))).

End Merge.



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

(** [Above x m] : [x] is strictly greater than any key in [m].
    [Below x m] : [x] is strictly smaller than any key in [m]. *)

Inductive Above (x:key) : t elt -> Prop :=
 | AbLeaf : Above x (Leaf _)
 | AbNode l r h y e : Above x l -> X.lt y x -> Above x r ->
   Above x (Node l y e r h).

Inductive Below (x:key) : t elt -> Prop :=
 | BeLeaf : Below x (Leaf _)
 | BeNode l r h y e : Below x l -> X.lt x y -> Below x r ->
   Below x (Node l y e r h).

Definition Apart (m1 m2 : t elt) : Prop :=
  forall x1 x2, In x1 m1 -> In x2 m2 -> X.lt x1 x2.

(** Alternative statements, equivalent with [LtTree] and [GtTree] *)

Definition lt_tree x m := forall y, In y m -> X.lt y x.
Definition gt_tree x m := forall y, In y m -> X.lt x y.

(** [Bst t] : [t] is a binary search tree *)

Inductive Bst : t elt -> Prop :=
  | BSLeaf : Bst (Leaf _)
  | BSNode : forall x e l r h, Bst l -> Bst r ->
     Above x l -> Below x r -> Bst (Node l x e r h).

End Invariants.


(** * Correctness proofs, isolated in a sub-module *)

Module Proofs.
 Module MX := OrderedTypeFacts X.
 Module PX := KeyOrderedType X.
 Module L := MMapList.Raw X.

Local Infix "∈" := In (at level 70).
Local Infix "==" := X.eq (at level 70).
Local Infix "<" := X.lt (at level 70).
Local Infix "<<" := Below (at level 70).
Local Infix ">>" := Above (at level 70).
Local Infix "<<<" := Apart (at level 70).

Scheme tree_ind := Induction for tree Sort Prop.
Scheme Bst_ind := Induction for Bst Sort Prop.
Scheme MapsTo_ind := Induction for MapsTo Sort Prop.
Scheme In_ind := Induction for In Sort Prop.
Scheme Above_ind := Induction for Above Sort Prop.
Scheme Below_ind := Induction for Below Sort Prop.

Functional Scheme mem_ind := Induction for mem Sort Prop.
Functional Scheme find_ind := Induction for find Sort Prop.
Functional Scheme bal_ind := Induction for bal Sort Prop.
Functional Scheme add_ind := Induction for add Sort Prop.
Functional Scheme remove_min_ind := Induction for remove_min Sort Prop.
Functional Scheme merge0_ind := Induction for merge0 Sort Prop.
Functional Scheme remove_ind := Induction for remove Sort Prop.
Functional Scheme concat_ind := Induction for concat Sort Prop.
Functional Scheme split_ind := Induction for split Sort Prop.
Functional Scheme mapo_ind := Induction for mapo Sort Prop.
Functional Scheme gmerge_ind := Induction for gmerge Sort Prop.

(** * Automation and dedicated tactics. *)

Local Hint Constructors tree MapsTo In Bst Above Below.
Local Hint Unfold lt_tree gt_tree Apart.
Local Hint Immediate MX.eq_sym.
Local Hint Resolve MX.eq_refl MX.eq_trans MX.lt_trans.

Tactic Notation "factornode" ident(s) :=
 try clear s;
 match goal with
   | |- context [Node ?l ?x ?e ?r ?h] =>
       set (s:=Node l x e r h) in *; clearbody s; clear l x e r h
   | _ : context [Node ?l ?x ?e ?r ?h] |- _ =>
       set (s:=Node l x e r h) in *; clearbody s; clear l x e r h
 end.

(** A tactic for cleaning hypothesis after use of functional induction. *)

Ltac cleanf :=
 match goal with
  | H : X.compare _ _ = Eq |- _ =>
    rewrite ?H; apply MX.compare_eq in H; cleanf
  | H : X.compare _ _ = Lt |- _ =>
    rewrite ?H; apply MX.compare_lt_iff in H; cleanf
  | H : X.compare _ _ = Gt |- _ =>
    rewrite ?H; apply MX.compare_gt_iff in H; cleanf
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

Ltac intuition_in := repeat (intuition; inv In; inv MapsTo).

(* Function/Functional Scheme can't deal with internal fix.
   Let's do its job by hand: *)

Ltac join_tac l x d r :=
 revert x d r;
 induction l as [| ll _ lx ld lr Hlr lh];
   [ | intros x d r; induction r as [| rl Hrl rx rd rr _ rh]; unfold join;
     [ | destruct (rh+2 <? lh) eqn:LT;
       [ match goal with |- context [ bal ?u ?v ?w ?z ] =>
           replace (bal u v w z)
           with (bal ll lx ld (join lr x d (Node rl rx rd rr rh))); [ | auto]
         end
       | destruct (lh+2 <? rh) eqn:LT';
         [ match goal with |- context [ bal ?u ?v ?w ?z ] =>
             replace (bal u v w z)
             with (bal (join (Node ll lx ld lr lh) x d rl) rx rd rr); [ | auto]
           end
         | ] ] ] ]; intros.

Ltac cleansplit :=
  simpl; cleanf; inv Bst;
  match goal with
  | E:split _ _ = 〚 ?l, ?o, ?r 〛 |- _ =>
    change l with (〚l,o,r〛#l); rewrite <- ?E;
    change o with (〚l,o,r〛#o); rewrite <- ?E;
    change r with (〚l,o,r〛#r); rewrite <- ?E
  | _ => idtac
  end.

(** * Basic results about [MapsTo], [In], [lt_tree], [gt_tree], [height] *)

(** Facts about [MapsTo] and [In]. *)

Lemma MapsTo_In {elt} k (e:elt) m : MapsTo k e m -> k ∈ m.
Proof.
 induction 1; auto.
Qed.
Local Hint Resolve MapsTo_In.

Lemma In_MapsTo {elt} k m : k ∈ m -> exists (e:elt), MapsTo k e m.
Proof.
 induction 1; try destruct IHIn as (e,He); exists e; auto.
Qed.

Lemma In_alt {elt} k (m:t elt) : In0 k m <-> k ∈ m.
Proof.
 split.
 intros (e,H); eauto.
 unfold In0; apply In_MapsTo; auto.
Qed.

Lemma MapsTo_1 {elt} m x y (e:elt) :
  x == y -> MapsTo x e m -> MapsTo y e m.
Proof.
 induction m; simpl; intuition_in; eauto.
Qed.
Hint Immediate MapsTo_1.

Instance MapsTo_compat {elt} :
  Proper (X.eq==>Logic.eq==>Logic.eq==>iff) (@MapsTo elt).
Proof.
 intros x x' Hx e e' He m m' Hm. subst.
 split; now apply MapsTo_1.
Qed.

Instance In_compat {elt} :
  Proper (X.eq==>Logic.eq==>iff) (@In elt).
Proof.
 intros x x' H m m' <-.
 induction m; simpl; intuition_in; eauto.
Qed.

Lemma In_node_iff {elt} l x (e:elt) r h y :
  y ∈ (Node l x e r h) <-> y ∈ l \/ y == x \/ y ∈ r.
Proof.
 intuition_in.
Qed.

(** Results about [Above] and [Below] *)

Lemma above {elt} (m:t elt) x :
  x >> m <-> forall y, y ∈ m -> y < x.
Proof.
 split.
 - induction 1; intuition_in; MX.order.
 - induction m; constructor; auto.
Qed.

Lemma below {elt} (m:t elt) x :
  x << m <-> forall y, y ∈ m -> x < y.
Proof.
 split.
 - induction 1; intuition_in; MX.order.
 - induction m; constructor; auto.
Qed.

Lemma AboveLt {elt} (m:t elt) x y : x >> m -> y ∈ m -> y < x.
Proof.
 rewrite above; intuition.
Qed.

Lemma BelowGt {elt} (m:t elt) x y : x << m -> y ∈ m -> x < y.
Proof.
 rewrite below; intuition.
Qed.

Lemma Above_not_In {elt} (m:t elt) x : x >> m -> ~ x ∈ m.
Proof.
 induction 1; intuition_in; MX.order.
Qed.

Lemma Below_not_In {elt} (m:t elt) x : x << m -> ~ x ∈ m.
Proof.
 induction 1; intuition_in; MX.order.
Qed.

Lemma Above_trans {elt} (m:t elt) x y : x < y -> x >> m -> y >> m.
Proof.
 induction 2; constructor; trivial; MX.order.
Qed.

Lemma Below_trans {elt} (m:t elt) x y : y < x -> x << m -> y << m.
Proof.
 induction 2; constructor; trivial; MX.order.
Qed.

Local Hint Resolve
 AboveLt Above_not_In Above_trans
 BelowGt Below_not_In Below_trans.

(** Helper tactic concerning order of elements. *)

Ltac order := match goal with
 | U: _ >> ?m, V: _ ∈ ?m |- _ =>
   generalize (AboveLt U V); clear U; order
 | U: _ << ?m, V: _ ∈ ?m |- _ =>
   generalize (BelowGt U V); clear U; order
 | U: _ >> ?m, V: MapsTo _ _ ?m |- _ =>
   generalize (AboveLt U (MapsTo_In V)); clear U; order
 | U: _ << ?m, V: MapsTo _ _ ?m |- _ =>
   generalize (BelowGt U (MapsTo_In V)); clear U; order
 | _ => MX.order
end.

Lemma between {elt} (m m':t elt) x :
  x >> m -> x << m' -> m <<< m'.
Proof.
 intros H H' y y' Hy Hy'. order.
Qed.

Section Elt.
Variable elt:Type.
Implicit Types m r : t elt.

(** * Membership *)

Lemma find_1 m x e : Bst m -> MapsTo x e m -> find x m = Some e.
Proof.
 functional induction (find x m); cleanf;
  intros; inv Bst; intuition_in; order.
Qed.

Lemma find_2 m x e : find x m = Some e -> MapsTo x e m.
Proof.
 functional induction (find x m); cleanf; subst; intros; auto.
 - discriminate.
 - injection H as ->. auto.
Qed.

Lemma find_spec m x e : Bst m ->
 (find x m = Some e <-> MapsTo x e m).
Proof.
 split; auto using find_1, find_2.
Qed.

Lemma find_in m x : find x m <> None -> x ∈ m.
Proof.
 destruct (find x m) eqn:F; intros H.
 - apply MapsTo_In with e. now apply find_2.
 - now elim H.
Qed.

Lemma in_find m x : Bst m -> x ∈ m -> find x m <> None.
Proof.
 intros H H'.
 destruct (In_MapsTo H') as (d,Hd).
 now rewrite (find_1 H Hd).
Qed.

Lemma find_in_iff m x : Bst m ->
 (find x m <> None <-> x ∈ m).
Proof.
 split; auto using find_in, in_find.
Qed.

Lemma not_find_iff m x : Bst m ->
 (find x m = None <-> ~ x ∈ m).
Proof.
 intros H. rewrite <- find_in_iff; trivial.
 destruct (find x m); split; try easy. now destruct 1.
Qed.

Lemma eq_option_alt (o o':option elt) :
 o=o' <-> (forall e, o=Some e <-> o'=Some e).
Proof.
split; intros.
- now subst.
- destruct o, o'; rewrite ?H; auto. symmetry; now apply H.
Qed.

Lemma find_mapsto_equiv : forall m m' x, Bst m -> Bst m' ->
 (find x m = find x m' <->
  (forall d, MapsTo x d m <-> MapsTo x d m')).
Proof.
 intros m m' x Hm Hm'. rewrite eq_option_alt.
 split; intros H d. now rewrite <- 2 find_spec. now rewrite 2 find_spec.
Qed.

Lemma find_in_equiv : forall m m' x, Bst m -> Bst m' ->
 find x m = find x m' ->
 (x ∈ m <-> x ∈ m').
Proof.
 split; intros; apply find_in; [ rewrite <- H1 | rewrite H1 ];
  apply in_find; auto.
Qed.

Lemma find_compat m x x' : Bst m -> X.eq x x' -> find x m = find x' m.
Proof.
  intros B E.
  destruct (find x' m) eqn:H.
  - apply find_1; trivial. rewrite E. now apply find_2.
  - rewrite not_find_iff in *; trivial. now rewrite E.
Qed.

Lemma mem_spec m x : Bst m -> mem x m = true <-> x ∈ m.
Proof.
 functional induction (mem x m); auto; intros; cleanf;
  inv Bst; intuition_in; try discriminate; order.
Qed.

(** * Empty map *)

Lemma empty_bst : Bst (empty elt).
Proof.
 constructor.
Qed.

Lemma empty_spec x : find x (empty elt) = None.
Proof.
 reflexivity.
Qed.

(** * Emptyness test *)

Lemma is_empty_spec m : is_empty m = true <-> forall x, find x m = None.
Proof.
 destruct m as [|r x e l h]; simpl; split; try easy.
 intros H. specialize (H x). now rewrite MX.compare_refl in H.
Qed.

(** * Helper functions *)

Lemma create_bst l x e r :
 Bst l -> Bst r -> x >> l -> x << r -> Bst (create l x e r).
Proof.
 unfold create; auto.
Qed.
Hint Resolve create_bst.

Lemma create_in l x e r y :
  y ∈ (create l x e r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 unfold create; split; [ inversion_clear 1 | ]; intuition.
Qed.

Lemma bal_bst l x e r : Bst l -> Bst r ->
 x >> l -> x << r -> Bst (bal l x e r).
Proof.
 functional induction (bal l x e r); intros; cleanf;
 inv Bst; inv Above; inv Below;
 repeat apply create_bst; auto; unfold create; constructor; eauto.
Qed.
Hint Resolve bal_bst.

Lemma bal_in l x e r y :
 y ∈ (bal l x e r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 functional induction (bal l x e r); intros; cleanf;
 rewrite !create_in; intuition_in.
Qed.

Lemma bal_mapsto l x e r y e' :
 MapsTo y e' (bal l x e r) <-> MapsTo y e' (create l x e r).
Proof.
 functional induction (bal l x e r); intros; cleanf;
 unfold assert_false, create; intuition_in.
Qed.

Lemma bal_find l x e r y :
 Bst l -> Bst r -> x >> l -> x << r ->
 find y (bal l x e r) = find y (create l x e r).
Proof.
 functional induction (bal l x e r); intros; cleanf; trivial;
 inv Bst; inv Above; inv Below;
 simpl; repeat case X.compare_spec; intuition; order.
Qed.

(** * Insertion *)

Lemma add_in m x y e :
 y ∈ (add x e m) <-> y == x \/ y ∈ m.
Proof.
 functional induction (add x e m); auto; intros; cleanf;
 rewrite ?bal_in; intuition_in. setoid_replace y with x; auto.
Qed.

Lemma add_lt m x e y : y >> m -> x < y -> y >> add x e m.
Proof.
 intros. apply above. intros z. rewrite add_in. destruct 1; order.
Qed.

Lemma add_gt m x e y : y << m -> y < x -> y << add x e m.
Proof.
 intros. apply below. intros z. rewrite add_in. destruct 1; order.
Qed.

Lemma add_bst m x e : Bst m -> Bst (add x e m).
Proof.
 functional induction (add x e m); intros; cleanf;
  inv Bst; try apply bal_bst; auto using add_lt, add_gt.
Qed.
Hint Resolve add_lt add_gt add_bst.

Lemma add_spec1 m x e : Bst m -> find x (add x e m) = Some e.
Proof.
 functional induction (add x e m); simpl; intros; cleanf; trivial.
 - now rewrite MX.compare_refl.
 - inv Bst. rewrite bal_find; auto.
   simpl. case X.compare_spec; try order; auto.
 - inv Bst. rewrite bal_find; auto.
   simpl. case X.compare_spec; try order; auto.
Qed.

Lemma add_spec2 m x y e : Bst m -> ~ x == y ->
 find y (add x e m) = find y m.
Proof.
 functional induction (add x e m); simpl; intros; cleanf; trivial.
 - case X.compare_spec; trivial; order.
 - case X.compare_spec; trivial; order.
 - inv Bst. rewrite bal_find by auto. simpl. now rewrite IHt.
 - inv Bst. rewrite bal_find by auto. simpl. now rewrite IHt.
Qed.

Lemma add_find m x y e : Bst m ->
 find y (add x e m) =
  match X.compare y x with Eq => Some e | _ => find y m end.
Proof.
 intros.
 case X.compare_spec; intros.
 - apply find_spec; auto. rewrite H0. apply find_spec; auto.
   now apply add_spec1.
 - apply add_spec2; trivial; order.
 - apply add_spec2; trivial; order.
Qed.

(** * Extraction of minimum binding *)

Definition RemoveMin m res :=
 match m with
 | Leaf _ => False
 | Node l x e r h => remove_min l x e r = res
 end.

Lemma RemoveMin_step l x e r h m' p :
 RemoveMin (Node l x e r h) (m',p) ->
 (l = Leaf _ /\ m' = r /\ p = (x,e) \/
  exists m0, RemoveMin l (m0,p) /\ m' = bal m0 x e r).
Proof.
 simpl. destruct l as [|ll lx le lr lh]; simpl.
 - intros [= -> ->]. now left.
 - destruct (remove_min ll lx le lr) as (l',p').
   intros [= <- <-]. right. now exists l'.
Qed.

Lemma remove_min_mapsto m m' p : RemoveMin m (m',p) ->
 forall y e,
 MapsTo y e m <-> (y == p#1 /\ e = p#2) \/ MapsTo y e m'.
Proof.
 revert m'.
 induction m as [|l IH x d r _ h]; [destruct 1|].
 intros m' R. apply RemoveMin_step in R.
 destruct R as [(->,(->,->))|[m0 (R,->)]]; intros y e; simpl.
 - intuition_in. subst. now constructor.
 - rewrite bal_mapsto. unfold create. specialize (IH _ R y e).
   intuition_in.
Qed.

Lemma remove_min_in m m' p : RemoveMin m (m',p) ->
 forall y, y ∈ m <-> y == p#1 \/ y ∈ m'.
Proof.
 revert m'.
 induction m as [|l IH x e r _ h]; [destruct 1|].
 intros m' R y. apply RemoveMin_step in R.
 destruct R as [(->,(->,->))|[m0 (R,->)]].
 + intuition_in.
 + rewrite bal_in, In_node_iff, (IH _ R); intuition.
Qed.

Lemma remove_min_lt m m' p : RemoveMin m (m',p) ->
 forall y, y >> m -> y >> m'.
Proof.
 intros R y L. apply above. intros z Hz.
 apply (AboveLt L).
 apply (remove_min_in R). now right.
Qed.

Lemma remove_min_gt m m' p : RemoveMin m (m',p) ->
 Bst m -> p#1 << m'.
Proof.
 revert m'.
 induction m as [|l IH x e r _ h]; [destruct 1|].
 intros m' R H. inv Bst. apply RemoveMin_step in R.
 destruct R as [(_,(->,->))|[m0 (R,->)]]; auto.
 assert (p#1 << m0) by now apply IH.
 assert (In p#1 l) by (apply (remove_min_in R); now left).
 apply below. intros z. rewrite bal_in.
 intuition_in; order.
Qed.

Lemma remove_min_bst m m' p : RemoveMin m (m',p) ->
 Bst m -> Bst m'.
Proof.
 revert m'.
 induction m as [|l IH x e r _ h]; [destruct 1|].
 intros m' R H. inv Bst. apply RemoveMin_step in R.
 destruct R as [(_,(->,->))|[m0 (R,->)]]; auto.
 apply bal_bst; eauto using remove_min_lt.
Qed.

Lemma remove_min_find m m' p : RemoveMin m (m',p) ->
 Bst m ->
 forall y,
 find y m =
   match X.compare y p#1 with
    | Eq => Some p#2
    | Lt => None
    | Gt => find y m'
   end.
Proof.
 revert m'.
 induction m as [|l IH x e r _ h]; [destruct 1|].
 intros m' R B y. inv Bst. apply RemoveMin_step in R.
 destruct R as [(->,(->,->))|[m0 (R,->)]]; auto.
 assert (Bst m0) by now apply (remove_min_bst R).
 assert (p#1 << m0) by now apply (remove_min_gt R).
 assert (x >> m0) by now apply (remove_min_lt R).
 assert (In p#1 l) by (apply (remove_min_in R); now left).
 simpl in *.
 rewrite (IH _ R), bal_find by trivial. clear IH. simpl.
 do 2 case X.compare_spec; trivial; try order.
Qed.

(** * Merging two trees *)

Ltac factor_remove_min m R := match goal with
 | h:int, H:remove_min ?l ?x ?e ?r = ?p |- _ =>
   assert (R:RemoveMin (Node l x e r h) p) by exact H;
   set (m:=Node l x e r h) in *; clearbody m; clear H l x e r
end.

Lemma merge0_in m1 m2 y :
  y ∈ (merge0 m1 m2) <-> y ∈ m1 \/ y ∈ m2.
Proof.
 functional induction (merge0 m1 m2); intros; try factornode m1.
 - intuition_in.
 - intuition_in.
 - factor_remove_min l R. rewrite bal_in, (remove_min_in R).
   simpl; intuition.
Qed.

Lemma merge0_mapsto m1 m2 y e :
 MapsTo y e (merge0 m1 m2) <-> MapsTo y e m1 \/ MapsTo y e m2.
Proof.
 functional induction (merge0 m1 m2); intros; try factornode m1.
 - intuition_in.
 - intuition_in.
 - factor_remove_min l R. rewrite bal_mapsto, (remove_min_mapsto R).
   simpl. unfold create; intuition_in. subst. now constructor.
Qed.

Lemma merge0_bst m1 m2 : Bst m1 -> Bst m2 -> m1 <<< m2 ->
 Bst (merge0 m1 m2).
Proof.
 functional induction (merge0 m1 m2); intros B1 B2 B12; trivial.
 factornode m1. factor_remove_min l R.
 apply bal_bst; auto.
 - eapply remove_min_bst; eauto.
 - apply above. intros z Hz. apply B12; trivial.
   rewrite (remove_min_in R). now left.
 - now apply (remove_min_gt R).
Qed.
Hint Resolve merge0_bst.

(** * Deletion *)

Lemma remove_in m x y : Bst m ->
 (y ∈ remove x m <-> ~ y == x /\ y ∈ m).
Proof.
 functional induction (remove x m); simpl; intros; cleanf; inv Bst;
  rewrite ?merge0_in, ?bal_in, ?IHt; intuition_in; order.
Qed.

Lemma remove_lt m x y : Bst m -> y >> m -> y >> remove x m.
Proof.
  intros. apply above. intro. rewrite remove_in by trivial.
   destruct 1; order.
Qed.

Lemma remove_gt m x y : Bst m -> y << m -> y << remove x m.
Proof.
  intros. apply below. intro. rewrite remove_in by trivial.
   destruct 1; order.
Qed.

Lemma remove_bst m x : Bst m -> Bst (remove x m).
Proof.
 functional induction (remove x m); simpl; intros; cleanf; inv Bst.
 - trivial.
 - apply merge0_bst; eauto.
 - apply bal_bst; auto using remove_lt.
 - apply bal_bst; auto using remove_gt.
Qed.
Hint Resolve remove_bst remove_gt remove_lt.

Lemma remove_spec1 m x : Bst m -> find x (remove x m) = None.
Proof.
 intros. apply not_find_iff; auto. rewrite remove_in; intuition.
Qed.

Lemma remove_spec2 m x y : Bst m -> ~ x == y ->
 find y (remove x m) = find y m.
Proof.
 functional induction (remove x m); simpl; intros; cleanf; inv Bst.
 - trivial.
 - case X.compare_spec; intros; try order;
   rewrite find_mapsto_equiv; auto.
   + intros. rewrite merge0_mapsto; intuition; order.
   + apply merge0_bst; auto. red; intros; transitivity y0; order.
   + intros. rewrite merge0_mapsto; intuition; order.
   + apply merge0_bst; auto. now apply between with y0.
 - rewrite bal_find by auto. simpl. case X.compare_spec; auto.
 - rewrite bal_find by auto. simpl. case X.compare_spec; auto.
Qed.

(** * join *)

Lemma join_in l x d r y :
 y ∈ (join l x d r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 join_tac l x d r.
 - simpl join. rewrite add_in. intuition_in.
 - rewrite add_in. intuition_in.
 - rewrite bal_in, Hlr. clear Hlr Hrl. intuition_in.
 - rewrite bal_in, Hrl; clear Hlr Hrl; intuition_in.
 - apply create_in.
Qed.

Lemma join_bst l x d r :
 Bst (create l x d r) -> Bst (join l x d r).
Proof.
  join_tac l x d r; unfold create in *;
  inv Bst; inv Above; inv Below; auto.
  - simpl. auto.
  - apply bal_bst; auto.
    apply below. intro. rewrite join_in. intuition_in; order.
  - apply bal_bst; auto.
    apply above. intro. rewrite join_in. intuition_in; order.
Qed.
Hint Resolve join_bst.

Lemma join_find l x d r y :
 Bst (create l x d r) ->
 find y (join l x d r) = find y (create l x d r).
Proof.
 unfold create at 1.
 join_tac l x d r; trivial.
 - simpl in *. inv Bst.
   rewrite add_find; trivial.
   case X.compare_spec; intros; trivial.
   apply not_find_iff; auto. intro. order.
 - clear Hlr. factornode l. simpl. inv Bst.
   rewrite add_find by auto.
   case X.compare_spec; intros; trivial.
   apply not_find_iff; auto. intro. order.
 - clear Hrl LT. factornode r. inv Bst; inv Above; inv Below.
   rewrite bal_find; auto; simpl.
   + rewrite Hlr; auto; simpl.
     repeat (case X.compare_spec; trivial; try order).
   + apply below. intro. rewrite join_in. intuition_in; order.
 - clear Hlr LT LT'. factornode l. inv Bst; inv Above; inv Below.
   rewrite bal_find; auto; simpl.
   + rewrite Hrl; auto; simpl.
     repeat (case X.compare_spec; trivial; try order).
   + apply above. intro. rewrite join_in. intuition_in; order.
Qed.

(** * split *)

Lemma split_in_l0 m x y : y ∈ (split x m)#l -> y ∈ m.
Proof.
  functional induction (split x m); cleansplit;
  rewrite ?join_in; intuition.
Qed.

Lemma split_in_r0 m x y : y ∈ (split x m)#r -> y ∈ m.
Proof.
  functional induction (split x m); cleansplit;
  rewrite ?join_in; intuition.
Qed.

Lemma split_in_l m x y : Bst m ->
 (y ∈ (split x m)#l <-> y ∈ m /\ y < x).
Proof.
  functional induction (split x m); intros; cleansplit;
  rewrite ?join_in, ?IHt; intuition_in; order.
Qed.

Lemma split_in_r m x y : Bst m ->
 (y ∈ (split x m)#r <-> y ∈ m /\ x < y).
Proof.
  functional induction (split x m); intros; cleansplit;
  rewrite ?join_in, ?IHt; intuition_in; order.
Qed.

Lemma split_in_o m x : (split x m)#o = find x m.
Proof.
  functional induction (split x m); intros; cleansplit; auto.
Qed.

Lemma split_lt_l m x : Bst m -> x >> (split x m)#l.
Proof.
  intro. apply above. intro. rewrite split_in_l; intuition; order.
Qed.

Lemma split_lt_r m x y : y >> m -> y >> (split x m)#r.
Proof.
  intro. apply above. intros z Hz. apply split_in_r0 in Hz. order.
Qed.

Lemma split_gt_r m x : Bst m -> x << (split x m)#r.
Proof.
  intro. apply below. intro. rewrite split_in_r; intuition; order.
Qed.

Lemma split_gt_l m x y : y << m -> y << (split x m)#l.
Proof.
  intro. apply below. intros z Hz. apply split_in_l0 in Hz. order.
Qed.
Hint Resolve split_lt_l split_lt_r split_gt_l split_gt_r.

Lemma split_bst_l m x : Bst m -> Bst (split x m)#l.
Proof.
  functional induction (split x m); intros; cleansplit; intuition;
  auto using join_bst.
Qed.

Lemma split_bst_r m x : Bst m -> Bst (split x m)#r.
Proof.
  functional induction (split x m); intros; cleansplit; intuition;
  auto using join_bst.
Qed.
Hint Resolve split_bst_l split_bst_r.

Lemma split_find m x y : Bst m ->
 find y m = match X.compare y x with
              | Eq => (split x m)#o
              | Lt => find y (split x m)#l
              | Gt => find y (split x m)#r
            end.
Proof.
 functional induction (split x m); intros; cleansplit.
 - now case X.compare.
 - repeat case X.compare_spec; trivial; order.
 - simpl in *. rewrite join_find, IHt; auto.
   simpl. repeat case X.compare_spec; trivial; order.
 - rewrite join_find, IHt; auto.
   simpl; repeat case X.compare_spec; trivial; order.
Qed.

(** * Concatenation *)

Lemma concat_in m1 m2 y :
 y ∈ (concat m1 m2) <-> y ∈ m1 \/ y ∈ m2.
Proof.
 functional induction (concat m1 m2); intros; try factornode m1.
 - intuition_in.
 - intuition_in.
 - factor_remove_min m2 R.
   rewrite join_in, (remove_min_in R); simpl; intuition.
Qed.

Lemma concat_bst m1 m2 : Bst m1 -> Bst m2 -> m1 <<< m2 ->
 Bst (concat m1 m2).
Proof.
  functional induction (concat m1 m2); intros B1 B2 LT; auto;
  try factornode m1.
  factor_remove_min m2 R.
  apply join_bst, create_bst; auto.
  - now apply (remove_min_bst R).
  - apply above. intros y Hy. apply LT; trivial.
    rewrite (remove_min_in R); now left.
  - now apply (remove_min_gt R).
Qed.
Hint Resolve concat_bst.

Definition oelse {A} (o1 o2:option A) :=
  match o1 with
  | Some x => Some x
  | None => o2
  end.

Lemma concat_find m1 m2 y : Bst m1 -> Bst m2 -> m1 <<< m2 ->
 find y (concat m1 m2) = oelse (find y m2) (find y m1).
Proof.
 functional induction (concat m1 m2); intros B1 B2 B; auto; try factornode m1.
 - destruct (find y m2); auto.
 - factor_remove_min m2 R.
   assert (xd#1 >> m1).
   { apply above. intros z Hz. apply B; trivial.
     rewrite (remove_min_in R). now left. }
   rewrite join_find; simpl; auto.
   + rewrite (remove_min_find R B2 y).
     case X.compare_spec; intros; auto.
     destruct (find y m2'); trivial.
     simpl. symmetry. apply not_find_iff; eauto.
   + apply create_bst; auto.
     * now apply (remove_min_bst R).
     * now apply (remove_min_gt R).
Qed.


(** * Elements *)

Notation eqk := (PX.eqk (elt:= elt)).
Notation eqke := (PX.eqke (elt:= elt)).
Notation ltk := (PX.ltk (elt:= elt)).

Lemma bindings_aux_mapsto : forall (s:t elt) acc x e,
 InA eqke (x,e) (bindings_aux acc s) <-> MapsTo x e s \/ InA eqke (x,e) acc.
Proof.
 induction s as [ | l Hl x e r Hr h ]; simpl; auto.
 intuition.
 inversion H0.
 intros.
 rewrite Hl.
 destruct (Hr acc x0 e0); clear Hl Hr.
 intuition; inversion_clear H3; intuition.
 compute in H0. destruct H0; simpl in *; subst; intuition.
Qed.

Lemma bindings_mapsto : forall (s:t elt) x e,
 InA eqke (x,e) (bindings s) <-> MapsTo x e s.
Proof.
 intros; generalize (bindings_aux_mapsto s nil x e); intuition.
 inversion_clear H0.
Qed.

Lemma bindings_in : forall (s:t elt) x, L.PX.In x (bindings s) <-> x ∈ s.
Proof.
 intros.
 unfold L.PX.In.
 rewrite <- In_alt; unfold In0.
 split; intros (y,H); exists y.
 - now rewrite <- bindings_mapsto.
 - unfold L.PX.MapsTo; now rewrite bindings_mapsto.
Qed.

Lemma bindings_aux_sort : forall (s:t elt) acc,
 Bst s -> sort ltk acc ->
 (forall x e y, InA eqke (x,e) acc -> y ∈ s -> y < x) ->
 sort ltk (bindings_aux acc s).
Proof.
 induction s as [ | l Hl y e r Hr h]; simpl; intuition.
 inv Bst.
 apply Hl; auto.
 - constructor.
   + apply Hr; eauto.
   + clear Hl Hr.
     apply InA_InfA with (eqA:=eqke); auto with *.
     intros (y',e') Hy'.
     apply bindings_aux_mapsto in Hy'. compute. intuition; eauto.
 - clear Hl Hr. intros x e' y' Hx Hy'.
   inversion_clear Hx.
   + compute in H. destruct H; simpl in *. order.
   + apply bindings_aux_mapsto in H. intuition eauto.
Qed.

Lemma bindings_sort : forall s : t elt, Bst s -> sort ltk (bindings s).
Proof.
 intros; unfold bindings; apply bindings_aux_sort; auto.
 intros; inversion H0.
Qed.
Hint Resolve bindings_sort.

Lemma bindings_nodup : forall s : t elt, Bst s -> NoDupA eqk (bindings s).
Proof.
 intros; apply PX.Sort_NoDupA; auto.
Qed.

Lemma bindings_aux_cardinal m acc :
 (length acc + cardinal m)%nat = length (bindings_aux acc m).
Proof.
 revert acc. induction m; simpl; intuition.
 rewrite <- IHm1; simpl.
 rewrite <- IHm2. rewrite Nat.add_succ_r, <- Nat.add_assoc.
 f_equal. f_equal. apply Nat.add_comm.
Qed.

Lemma bindings_cardinal m : cardinal m = length (bindings m).
Proof.
 exact (bindings_aux_cardinal m nil).
Qed.

Lemma bindings_app :
 forall (s:t elt) acc, bindings_aux acc s = bindings s ++ acc.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1, IHs2.
 unfold bindings; simpl.
 rewrite 2 IHs1, IHs2, !app_nil_r, !app_ass; auto.
Qed.

Lemma bindings_node :
 forall (t1 t2:t elt) x e z l,
 bindings t1 ++ (x,e) :: bindings t2 ++ l =
 bindings (Node t1 x e t2 z) ++ l.
Proof.
 unfold bindings; simpl; intros.
 rewrite !bindings_app, !app_nil_r, !app_ass; auto.
Qed.

(** * Fold *)

Definition fold' {A} (f : key -> elt -> A -> A)(s : t elt) :=
  L.fold f (bindings s).

Lemma fold_equiv_aux {A} (s : t elt) (f : key -> elt -> A -> A) (a : A) acc :
 L.fold f (bindings_aux acc s) a = L.fold f acc (fold f s a).
Proof.
 revert a acc.
 induction s; simpl; trivial.
 intros. rewrite IHs1. simpl. apply IHs2.
Qed.

Lemma fold_equiv {A} (s : t elt) (f : key -> elt -> A -> A) (a : A) :
 fold f s a = fold' f s a.
Proof.
 unfold fold', bindings. now rewrite fold_equiv_aux.
Qed.

Lemma fold_spec (s:t elt)(Hs:Bst s){A}(i:A)(f : key -> elt -> A -> A) :
 fold f s i = fold_left (fun a p => f p#1 p#2 a) (bindings s) i.
Proof.
 rewrite fold_equiv. unfold fold'. now rewrite L.fold_spec.
Qed.

(** * Comparison *)

(** [flatten_e e] returns the list of bindings of the enumeration [e]
    i.e. the list of bindings actually compared *)

Fixpoint flatten_e (e : enumeration elt) : list (key*elt) := match e with
  | End _ => nil
  | More x e t r => (x,e) :: bindings t ++ flatten_e r
 end.

Lemma flatten_e_bindings :
 forall (l:t elt) r x d z e,
 bindings l ++ flatten_e (More x d r e) =
 bindings (Node l x d r z) ++ flatten_e e.
Proof.
 intros; apply bindings_node.
Qed.

Lemma cons_1 : forall (s:t elt) e,
  flatten_e (cons s e) = bindings s ++ flatten_e e.
Proof.
  induction s; auto; intros.
  simpl flatten_e; rewrite IHs1; apply flatten_e_bindings; auto.
Qed.

(** Proof of correction for the comparison *)

Variable cmp : elt->elt->bool.

Definition IfEq b l1 l2 := L.equal cmp l1 l2 = b.

Lemma cons_IfEq : forall b x1 x2 d1 d2 l1 l2,
  X.eq x1 x2 -> cmp d1 d2 = true ->
  IfEq b l1 l2 ->
    IfEq b ((x1,d1)::l1) ((x2,d2)::l2).
Proof.
 unfold IfEq; destruct b; simpl; intros; case X.compare_spec; simpl;
  try rewrite H0; auto; order.
Qed.

Lemma equal_end_IfEq : forall e2,
  IfEq (equal_end e2) nil (flatten_e e2).
Proof.
 destruct e2; red; auto.
Qed.

Lemma equal_more_IfEq :
 forall x1 d1 (cont:enumeration elt -> bool) x2 d2 r2 e2 l,
  IfEq (cont (cons r2 e2)) l (bindings r2 ++ flatten_e e2) ->
    IfEq (equal_more cmp x1 d1 cont (More x2 d2 r2 e2)) ((x1,d1)::l)
       (flatten_e (More x2 d2 r2 e2)).
Proof.
 unfold IfEq; simpl; intros; destruct X.compare; simpl; auto.
 rewrite <-andb_lazy_alt; f_equal; auto.
Qed.

Lemma equal_cont_IfEq : forall m1 cont e2 l,
  (forall e, IfEq (cont e) l (flatten_e e)) ->
  IfEq (equal_cont cmp m1 cont e2) (bindings m1 ++ l) (flatten_e e2).
Proof.
 induction m1 as [|l1 Hl1 x1 d1 r1 Hr1 h1]; intros; auto.
 rewrite <- bindings_node; simpl.
 apply Hl1; auto.
 clear e2; intros [|x2 d2 r2 e2].
 simpl; red; auto.
 apply equal_more_IfEq.
 rewrite <- cons_1; auto.
Qed.

Lemma equal_IfEq : forall (m1 m2:t elt),
  IfEq (equal cmp m1 m2) (bindings m1) (bindings m2).
Proof.
 intros; unfold equal.
 rewrite <- (app_nil_r (bindings m1)).
 replace (bindings m2) with (flatten_e (cons m2 (End _)))
  by (rewrite cons_1; simpl; rewrite app_nil_r; auto).
 apply equal_cont_IfEq.
 intros.
 apply equal_end_IfEq; auto.
Qed.

Definition Equivb m m' :=
  (forall k, In k m <-> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Lemma Equivb_bindings : forall s s',
 Equivb s s' <-> L.Equivb cmp (bindings s) (bindings s').
Proof.
unfold Equivb, L.Equivb; split; split; intros.
do 2 rewrite bindings_in; firstorder.
destruct H.
apply (H2 k); rewrite <- bindings_mapsto; auto.
do 2 rewrite <- bindings_in; firstorder.
destruct H.
apply (H2 k); unfold L.PX.MapsTo; rewrite bindings_mapsto; auto.
Qed.

Lemma equal_Equivb : forall (s s': t elt), Bst s -> Bst s' ->
  (equal cmp s s' = true <-> Equivb s s').
Proof.
 intros s s' B B'.
 rewrite Equivb_bindings, <- equal_IfEq.
 split; [apply L.equal_2|apply L.equal_1]; auto.
Qed.

End Elt.

Section Map.
Variable elt elt' : Type.
Variable f : elt -> elt'.

Lemma map_spec m x :
 find x (map f m) = option_map f (find x m).
Proof.
induction m; simpl; trivial. case X.compare_spec; auto.
Qed.

Lemma map_in m x : x ∈ (map f m) <-> x ∈ m.
Proof.
induction m; simpl; intuition_in.
Qed.

Lemma map_bst m : Bst m -> Bst (map f m).
Proof.
induction m; simpl; auto. intros; inv Bst; constructor; auto.
- apply above. intro. rewrite map_in. intros. order.
- apply below. intro. rewrite map_in. intros. order.
Qed.

End Map.
Section Mapi.
Variable elt elt' : Type.
Variable f : key -> elt -> elt'.

Lemma mapi_spec m x :
  exists y:key,
    X.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).
Proof.
  induction m; simpl.
  - now exists x.
  - case X.compare_spec; simpl; auto. intros. now exists k.
Qed.

Lemma mapi_in m x : x ∈ (mapi f m) <-> x ∈ m.
Proof.
induction m; simpl; intuition_in.
Qed.

Lemma mapi_bst m : Bst m -> Bst (mapi f m).
Proof.
induction m; simpl; auto. intros; inv Bst; constructor; auto.
- apply above. intro. rewrite mapi_in. intros. order.
- apply below. intro. rewrite mapi_in. intros. order.
Qed.

End Mapi.

Section Mapo.
Variable elt elt' : Type.
Variable f : key -> elt -> option elt'.

Lemma mapo_in m x :
 x ∈ (mapo f m) ->
 exists y d, X.eq y x /\ MapsTo x d m /\ f y d <> None.
Proof.
functional induction (mapo f m); simpl; auto; intro H.
- inv In.
- rewrite join_in in H; destruct H as [H|[H|H]].
  + exists x0, d. do 2 (split; auto). congruence.
  + destruct (IHt H) as (y & e & ? & ? & ?). exists y, e. auto.
  + destruct (IHt0 H) as (y & e & ? & ? & ?). exists y, e. auto.
- rewrite concat_in in H; destruct H as [H|H].
  + destruct (IHt H) as (y & e & ? & ? & ?). exists y, e. auto.
  + destruct (IHt0 H) as (y & e & ? & ? & ?). exists y, e. auto.
Qed.

Lemma mapo_lt m x : x >> m -> x >> mapo f m.
Proof.
  intros H. apply above. intros y Hy.
  destruct (mapo_in Hy) as (y' & e & ? & ? & ?). order.
Qed.

Lemma mapo_gt m x : x << m -> x << mapo f m.
Proof.
  intros H. apply below. intros y Hy.
  destruct (mapo_in Hy) as (y' & e & ? & ? & ?). order.
Qed.
Hint Resolve mapo_lt mapo_gt.

Lemma mapo_bst m : Bst m -> Bst (mapo f m).
Proof.
functional induction (mapo f m); simpl; auto; intro H; inv Bst.
- apply join_bst, create_bst; auto.
- apply concat_bst; auto. apply between with x; auto.
Qed.
Hint Resolve mapo_bst.

Ltac nonify e :=
 replace e with (@None elt) by
  (symmetry; rewrite not_find_iff; auto; intro; order).

Definition obind {A B} (o:option A) (f:A->option B) :=
  match o with Some a => f a | None => None end.

Lemma mapo_find m x :
  Bst m ->
  exists y, X.eq y x /\
            find x (mapo f m) = obind (find x m) (f y).
Proof.
functional induction (mapo f m); simpl; auto; intros B;
 inv Bst.
- now exists x.
- rewrite join_find; auto.
  + simpl. case X.compare_spec; simpl; intros.
    * now exists x0.
    * destruct IHt as (y' & ? & ?); auto.
      exists y'; split; trivial.
    * destruct IHt0 as (y' & ? & ?); auto.
      exists y'; split; trivial.
  + constructor; auto using mapo_lt, mapo_gt.
- rewrite concat_find; auto.
  + destruct IHt0 as (y' & ? & ->); auto.
    destruct IHt as (y'' & ? & ->); auto.
    case X.compare_spec; simpl; intros.
    * nonify (find x r). nonify (find x l). simpl. now exists x0.
    * nonify (find x r). now exists y''.
    * nonify (find x l). exists y'. split; trivial.
      destruct (find x r); simpl; trivial.
      now destruct (f y' e).
  + apply between with x0; auto.
Qed.

End Mapo.

Section Gmerge.
Variable elt elt' elt'' : Type.
Variable f0 : key -> option elt -> option elt' -> option elt''.
Variable f : key -> elt -> option elt' -> option elt''.
Variable mapl : t elt -> t elt''.
Variable mapr : t elt' -> t elt''.
Hypothesis f0_f : forall x d o, f x d o = f0 x (Some d) o.
Hypothesis mapl_bst : forall m, Bst m -> Bst (mapl m).
Hypothesis mapr_bst : forall m', Bst m' -> Bst (mapr m').
Hypothesis mapl_f0 : forall x m, Bst m ->
 exists y, X.eq y x /\
           find x (mapl m) = obind (find x m) (fun d => f0 y (Some d) None).
Hypothesis mapr_f0 : forall x m, Bst m ->
 exists y, X.eq y x /\
           find x (mapr m) = obind (find x m) (fun d => f0 y None (Some d)).

Notation gmerge := (gmerge f mapl mapr).

Lemma gmerge_in m m' y : Bst m -> Bst m' ->
  y ∈ (gmerge m m') -> y ∈ m \/ y ∈ m'.
Proof.
  functional induction (gmerge m m'); intros B1 B2 H;
  try factornode m2; inv Bst.
  - right. apply find_in.
    generalize (in_find (mapr_bst B2) H).
    destruct (@mapr_f0 y m2) as (y' & ? & ->); trivial.
    intros A B. rewrite B in A. now elim A.
  - left. apply find_in.
    generalize (in_find (mapl_bst B1) H).
    destruct (@mapl_f0 y m2) as (y' & ? & ->); trivial.
    intros A B. rewrite B in A. now elim A.
  - rewrite join_in in *. revert IHt1 IHt0 H. cleansplit.
    generalize (split_bst_l x1 B2) (split_bst_r x1 B2).
    rewrite split_in_r, split_in_l; intuition_in.
  - rewrite concat_in in *. revert IHt1 IHt0 H; cleansplit.
    generalize (split_bst_l x1 B2) (split_bst_r x1 B2).
    rewrite split_in_r, split_in_l; intuition_in.
Qed.

Lemma gmerge_lt m m' x : Bst m -> Bst m' ->
  x >> m -> x >> m' -> x >> gmerge m m'.
Proof.
  intros. apply above. intros y Hy.
  apply gmerge_in in Hy; intuition_in; order.
Qed.

Lemma gmerge_gt m m' x : Bst m -> Bst m' ->
  x << m -> x << m' -> x << gmerge m m'.
Proof.
  intros. apply below. intros y Hy.
  apply gmerge_in in Hy; intuition_in; order.
Qed.
Hint Resolve gmerge_lt gmerge_gt.
Hint Resolve split_bst_l split_bst_r split_lt_l split_gt_r.

Lemma gmerge_bst m m' : Bst m -> Bst m' -> Bst (gmerge m m').
Proof.
  functional induction (gmerge m m'); intros B1 B2; auto;
  factornode m2; inv Bst;
  (apply join_bst, create_bst || apply concat_bst);
  revert IHt1 IHt0; cleansplit; intuition.
  apply between with x1; auto.
Qed.
Hint Resolve gmerge_bst.

Lemma oelse_none_r {A} (o:option A) : oelse o None = o.
Proof. now destruct o. Qed.

Ltac nonify e :=
 let E := fresh "E" in
 assert (E : e = None);
   [ rewrite not_find_iff; auto; intro U;
     try apply gmerge_in in U; intuition_in; order
   | rewrite E; clear E ].

Lemma gmerge_find m m' x : Bst m -> Bst m' ->
 In x m \/ In x m' ->
 exists y, X.eq y x /\
           find x (gmerge m m') = f0 y (find x m) (find x m').
Proof.
  functional induction (gmerge m m'); intros B1 B2 H;
  try factornode m2; inv Bst.
  - destruct H; [ intuition_in | ].
    destruct (@mapr_f0 x m2) as (y,(Hy,E)); trivial.
    exists y; split; trivial.
    rewrite E. simpl. apply in_find in H; trivial.
    destruct (find x m2); simpl; intuition.
  - destruct H; [ | intuition_in ].
    destruct (@mapl_f0 x m2) as (y,(Hy,E)); trivial.
    exists y; split; trivial.
    rewrite E. simpl. apply in_find in H; trivial.
    destruct (find x m2); simpl; intuition.
  - generalize (split_bst_l x1 B2) (split_bst_r x1 B2).
    rewrite (split_find x1 x B2).
    rewrite e1 in *; simpl in *. intros.
    rewrite join_find by (cleansplit; constructor; auto).
    simpl. case X.compare_spec; intros.
    + exists x1. split; auto. now rewrite <- e3, f0_f.
    + apply IHt1; auto. clear IHt1 IHt0.
      cleansplit; rewrite split_in_l; trivial.
      intuition_in; order.
    + apply IHt0; auto. clear IHt1 IHt0.
      cleansplit; rewrite split_in_r; trivial.
      intuition_in; order.
  - generalize (split_bst_l x1 B2) (split_bst_r x1 B2).
    rewrite (split_find x1 x B2).
    pose proof (split_lt_l x1 B2).
    pose proof (split_gt_r x1 B2).
    rewrite e1 in *; simpl in *. intros.
    rewrite concat_find by (try apply between with x1; auto).
    case X.compare_spec; intros.
    + clear IHt0 IHt1.
      exists x1. split; auto. rewrite <- f0_f, e2.
      nonify (find x (gmerge r1 r2')).
      nonify (find x (gmerge l1 l2')). trivial.
    + nonify (find x (gmerge r1 r2')).
      simpl. apply IHt1; auto. clear IHt1 IHt0.
      intuition_in; try order.
      right. cleansplit. now apply split_in_l.
    + nonify (find x (gmerge l1 l2')). simpl.
      rewrite oelse_none_r.
      apply IHt0; auto. clear IHt1 IHt0.
      intuition_in; try order.
      right. cleansplit. now apply split_in_r.
Qed.

End Gmerge.

Section Merge.
Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.

Lemma merge_bst m m' : Bst m -> Bst m' -> Bst (merge f m m').
Proof.
unfold merge; intros.
apply gmerge_bst with f;
 auto using mapo_bst, mapo_find.
Qed.

Lemma merge_spec1 m m' x : Bst m -> Bst m' ->
 In x m \/ In x m' ->
 exists y, X.eq y x /\
           find x (merge f m m') = f y (find x m) (find x m').
Proof.
  unfold merge; intros.
  edestruct (gmerge_find (f0:=f)) as (y,(Hy,E));
    eauto using mapo_bst.
  - reflexivity.
  - intros. now apply mapo_find.
  - intros. now apply mapo_find.
Qed.

Lemma merge_spec2 m m' x : Bst m -> Bst m' ->
  In x (merge f m m') -> In x m \/ In x m'.
Proof.
unfold merge; intros.
eapply gmerge_in with (f0:=f); try eassumption;
 auto using mapo_bst, mapo_find.
Qed.

End Merge.
End Proofs.
End Raw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of balanced binary search trees. *)

Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.

 Module E := X.
 Module Raw := Raw I X.
 Import Raw.Proofs.

 Record tree (elt:Type) :=
  Mk {this :> Raw.tree elt; is_bst : Raw.Bst this}.

 Definition t := tree.
 Definition key := E.t.

 Section Elt.
 Variable elt elt' elt'': Type.

 Implicit Types m : t elt.
 Implicit Types x y : key.
 Implicit Types e : elt.

 Definition empty : t elt := Mk (empty_bst elt).
 Definition is_empty m : bool := Raw.is_empty m.(this).
 Definition add x e m : t elt := Mk (add_bst x e m.(is_bst)).
 Definition remove x m : t elt := Mk (remove_bst x m.(is_bst)).
 Definition mem x m : bool := Raw.mem x m.(this).
 Definition find x m : option elt := Raw.find x m.(this).
 Definition map f m : t elt' := Mk (map_bst f m.(is_bst)).
 Definition mapi (f:key->elt->elt') m : t elt' :=
  Mk (mapi_bst f m.(is_bst)).
 Definition merge f m (m':t elt') : t elt'' :=
  Mk (merge_bst f m.(is_bst) m'.(is_bst)).
 Definition bindings m : list (key*elt) := Raw.bindings m.(this).
 Definition cardinal m := Raw.cardinal m.(this).
 Definition fold {A} (f:key->elt->A->A) m i := Raw.fold (A:=A) f m.(this) i.
 Definition equal cmp m m' : bool := Raw.equal cmp m.(this) m'.(this).

 Definition MapsTo x e m : Prop := Raw.MapsTo x e m.(this).
 Definition In x m : Prop := Raw.In0 x m.(this).

 Definition eq_key : (key*elt) -> (key*elt) -> Prop := @PX.eqk elt.
 Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop := @PX.eqke elt.
 Definition lt_key : (key*elt) -> (key*elt) -> Prop := @PX.ltk elt.

 Instance MapsTo_compat :
   Proper (E.eq==>Logic.eq==>Logic.eq==>iff) MapsTo.
 Proof.
   intros k k' Hk e e' He m m' Hm. unfold MapsTo; simpl.
   now rewrite Hk, He, Hm.
 Qed.

 Lemma find_spec m x e : find x m = Some e <-> MapsTo x e m.
 Proof. apply find_spec. apply is_bst. Qed.

 Lemma mem_spec m x : mem x m = true <-> In x m.
 Proof.
 unfold In, mem; rewrite In_alt. apply mem_spec. apply is_bst.
 Qed.

 Lemma empty_spec x : find x empty = None.
 Proof. apply empty_spec. Qed.

 Lemma is_empty_spec m : is_empty m = true <-> forall x, find x m = None.
 Proof. apply is_empty_spec. Qed.

 Lemma add_spec1 m x e : find x (add x e m) = Some e.
 Proof. apply add_spec1. apply is_bst. Qed.
 Lemma add_spec2 m x y e : ~ E.eq x y -> find y (add x e m) = find y m.
 Proof. apply add_spec2. apply is_bst. Qed.

 Lemma remove_spec1 m x : find x (remove x m) = None.
 Proof. apply remove_spec1. apply is_bst. Qed.
 Lemma remove_spec2 m x y : ~E.eq x y -> find y (remove x m) = find y m.
 Proof. apply remove_spec2. apply is_bst. Qed.

 Lemma bindings_spec1 m x e :
   InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
 Proof. apply bindings_mapsto. Qed.

 Lemma bindings_spec2 m : sort lt_key (bindings m).
 Proof. apply bindings_sort. apply is_bst. Qed.

 Lemma bindings_spec2w m : NoDupA eq_key (bindings m).
 Proof. apply bindings_nodup. apply is_bst. Qed.

 Lemma fold_spec m {A} (i : A) (f : key -> elt -> A -> A) :
   fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
 Proof. apply fold_spec. apply is_bst. Qed.

 Lemma cardinal_spec m : cardinal m = length (bindings m).
 Proof. apply bindings_cardinal. Qed.

 Definition Equal m m' := forall y, find y m = find y m'.
 Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
   (forall k, In k m <-> In k m') /\
   (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
 Definition Equivb cmp := Equiv (Cmp cmp).

 Lemma Equivb_Equivb cmp m m' :
  Equivb cmp m m' <-> Raw.Proofs.Equivb cmp m m'.
 Proof.
 unfold Equivb, Equiv, Raw.Proofs.Equivb, In. intuition.
 generalize (H0 k); do 2 rewrite In_alt; intuition.
 generalize (H0 k); do 2 rewrite In_alt; intuition.
 generalize (H0 k); do 2 rewrite <- In_alt; intuition.
 generalize (H0 k); do 2 rewrite <- In_alt; intuition.
 Qed.

 Lemma equal_spec m m' cmp :
   equal cmp m m' = true <-> Equivb cmp m m'.
 Proof. rewrite Equivb_Equivb. apply equal_Equivb; apply is_bst. Qed.

 End Elt.

 Lemma map_spec {elt elt'} (f:elt->elt') m x :
   find x (map f m) = option_map f (find x m).
 Proof. apply map_spec. Qed.

 Lemma mapi_spec {elt elt'} (f:key->elt->elt') m x :
   exists y:key, E.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).
 Proof. apply mapi_spec. Qed.

 Lemma merge_spec1 {elt elt' elt''}
       (f:key->option elt->option elt'->option elt'') m m' x :
   In x m \/ In x m' ->
   exists y:key, E.eq y x /\
                 find x (merge f m m') = f y (find x m) (find x m').
 Proof.
   unfold In. rewrite !In_alt. apply merge_spec1; apply is_bst.
 Qed.

 Lemma merge_spec2 {elt elt' elt''}
       (f:key -> option elt->option elt'->option elt'') m m' x :
   In x (merge f m m') -> In x m \/ In x m'.
 Proof.
   unfold In. rewrite !In_alt. apply merge_spec2; apply is_bst.
 Qed.

End IntMake.


Module IntMake_ord (I:Int)(X: OrderedType)(D : OrderedType) <:
    Sord with Module Data := D
         with Module MapS.E := X.

  Module Data := D.
  Module Import MapS := IntMake(I)(X).
  Module LO := MMapList.Make_ord(X)(D).
  Module R := Raw.
  Module P := Raw.Proofs.

  Definition t := MapS.t D.t.

  Definition cmp e e' :=
   match D.compare e e' with Eq => true | _ => false end.

  (** One step of comparison of bindings *)

  Definition compare_more x1 d1 (cont:R.enumeration D.t -> comparison) e2 :=
   match e2 with
    | R.End _ => Gt
    | R.More x2 d2 r2 e2 =>
       match X.compare x1 x2 with
        | Eq => match D.compare d1 d2 with
                   | Eq => cont (R.cons r2 e2)
                   | Lt => Lt
                   | Gt => Gt
                  end
        | Lt => Lt
        | Gt => Gt
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

  Definition compare m1 m2 :=
    compare_cont m1.(this) compare_end (R.cons m2 .(this) (Raw.End _)).

  (** Correctness of this comparison *)

  Definition Cmp c :=
   match c with
    | Eq => LO.eq_list
    | Lt => LO.lt_list
    | Gt => (fun l1 l2 => LO.lt_list l2 l1)
   end.

  Lemma cons_Cmp c x1 x2 d1 d2 l1 l2 :
   X.eq x1 x2 -> D.eq d1 d2 ->
   Cmp c l1 l2 -> Cmp c ((x1,d1)::l1) ((x2,d2)::l2).
  Proof.
    destruct c; simpl; intros; case X.compare_spec; auto; try P.MX.order.
    intros. right. split; auto. now symmetry.
  Qed.
  Hint Resolve cons_Cmp.

  Lemma compare_end_Cmp e2 :
   Cmp (compare_end e2) nil (P.flatten_e e2).
  Proof.
   destruct e2; simpl; auto.
  Qed.

  Lemma compare_more_Cmp x1 d1 cont x2 d2 r2 e2 l :
    Cmp (cont (R.cons r2 e2)) l (R.bindings r2 ++ P.flatten_e e2) ->
     Cmp (compare_more x1 d1 cont (R.More x2 d2 r2 e2)) ((x1,d1)::l)
       (P.flatten_e (R.More x2 d2 r2 e2)).
  Proof.
   simpl; case X.compare_spec; simpl;
   try case D.compare_spec; simpl; auto;
   case X.compare_spec; try P.MX.order; auto.
  Qed.

  Lemma compare_cont_Cmp : forall s1 cont e2 l,
   (forall e, Cmp (cont e) l (P.flatten_e e)) ->
   Cmp (compare_cont s1 cont e2) (R.bindings s1 ++ l) (P.flatten_e e2).
  Proof.
    induction s1 as [|l1 Hl1 x1 d1 r1 Hr1 h1] using P.tree_ind;
    intros; auto.
    rewrite <- P.bindings_node; simpl.
    apply Hl1; auto. clear e2. intros [|x2 d2 r2 e2].
    simpl; auto.
    apply compare_more_Cmp.
    rewrite <- P.cons_1; auto.
  Qed.

  Lemma compare_Cmp m1 m2 :
   Cmp (compare m1 m2) (bindings m1) (bindings m2).
  Proof.
    destruct m1 as (s1,H1), m2 as (s2,H2).
    unfold compare, bindings; simpl.
    rewrite <- (app_nil_r (R.bindings s1)).
    replace (R.bindings s2) with (P.flatten_e (R.cons s2 (R.End _))) by
    (rewrite P.cons_1; simpl; rewrite app_nil_r; auto).
    auto using compare_cont_Cmp, compare_end_Cmp.
  Qed.

  Definition eq (m1 m2 : t) := LO.eq_list (bindings m1) (bindings m2).
  Definition lt (m1 m2 : t) := LO.lt_list (bindings m1) (bindings m2).

  Lemma compare_spec m1 m2 : CompSpec eq lt m1 m2 (compare m1 m2).
  Proof.
    assert (H := compare_Cmp m1 m2).
    unfold Cmp in H.
    destruct (compare m1 m2); auto.
  Qed.

  (* Proofs about [eq] and [lt] *)

  Definition sbindings (m1 : t) :=
   LO.MapS.Mk (P.bindings_sort m1.(is_bst)).

  Definition seq (m1 m2 : t) := LO.eq (sbindings m1) (sbindings m2).
  Definition slt (m1 m2 : t) := LO.lt (sbindings m1) (sbindings m2).

  Lemma eq_seq : forall m1 m2, eq m1 m2 <-> seq m1 m2.
  Proof.
   unfold eq, seq, sbindings, bindings, LO.eq; intuition.
  Qed.

  Lemma lt_slt : forall m1 m2, lt m1 m2 <-> slt m1 m2.
  Proof.
   unfold lt, slt, sbindings, bindings, LO.lt; intuition.
  Qed.

  Lemma eq_spec m m' : eq m m' <-> Equivb cmp m m'.
  Proof.
  rewrite eq_seq; unfold seq.
  rewrite Equivb_Equivb.
  rewrite P.Equivb_bindings. apply LO.eq_spec.
  Qed.

  Instance eq_equiv : Equivalence eq.
  Proof.
    constructor; red; [intros x|intros x y| intros x y z];
    rewrite !eq_seq; apply LO.eq_equiv.
  Qed.

  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros m1 m2 H1 m1' m2' H2. rewrite !lt_slt. rewrite eq_seq in *.
    now apply LO.lt_compat.
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof.
    constructor; red; [intros x; red|intros x y z];
    rewrite !lt_slt; apply LO.lt_strorder.
  Qed.

End IntMake_ord.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (X: OrderedType) <: S with Module E := X
 :=IntMake(Z_as_Int)(X).

Module Make_ord (X: OrderedType)(D: OrderedType)
 <: Sord with Module Data := D
            with Module MapS.E := X
 :=IntMake_ord(Z_as_Int)(X)(D).

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

(** * FSetFullAVL

   This file contains some complements to [FSetAVL].

   - Functor [AvlProofs] proves that trees of [FSetAVL] are not only
   binary search trees, but moreover well-balanced ones. This is done
   by proving that all operations preserve the balancing.

   - Functor [OcamlOps] contains variants of [union], [subset],
   [compare] and [equal] that are faithful to the original ocaml codes,
   while the versions in FSetAVL have been adapted to perform only
   structural recursive code.

   - Finally, we pack the previous elements in a [Make] functor
   similar to the one of [FSetAVL], but richer.
*)

Require Import Recdef FSetInterface FSetList ZArith Int FSetAVL ROmega.

Set Implicit Arguments.
Unset Strict Implicit.

Module AvlProofs (Import I:Int)(X:OrderedType).
Module Import Raw := Raw I X.
Import Raw.Proofs.
Module Import II := MoreInt I.
Open Local Scope pair_scope.
Open Local Scope Int_scope.

Ltac omega_max := i2z_refl; romega with Z.

(** * AVL trees *)

(** [avl s] : [s] is a properly balanced AVL tree,
    i.e. for any node the heights of the two children
    differ by at most 2 *)

Inductive avl : tree -> Prop :=
  | RBLeaf : avl Leaf
  | RBNode : forall x l r h, avl l -> avl r ->
      -(2) <= height l - height r <= 2 ->
      h = max (height l) (height r) + 1 ->
      avl (Node l x r h).

(** * Automation and dedicated tactics *)

Hint Constructors avl.

(** A tactic for cleaning hypothesis after use of functional induction. *)

Ltac clearf :=
 match goal with
  | H : (@Logic.eq (Compare _ _ _ _) _ _) |- _ => clear H; clearf
  | H : (@Logic.eq (sumbool _ _) _ _) |- _ => clear H; clearf
  | _ => idtac
 end.

(** Tactics about [avl] *)

Lemma height_non_negative : forall s : tree, avl s -> height s >= 0.
Proof.
 induction s; simpl; intros; auto with zarith.
 inv avl; intuition; omega_max.
Qed.
Implicit Arguments height_non_negative.

(** When [H:avl r], typing [avl_nn H] or [avl_nn r] adds [height r>=0] *)

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

(** Results about [height] *)

Lemma height_0 : forall s, avl s -> height s = 0 -> s = Leaf.
Proof.
 destruct 1; intuition; simpl in *.
 avl_nns; simpl in *; elimtype False; omega_max.
Qed.

(** * Results about [avl] *)

Lemma avl_node :
 forall x l r, avl l -> avl r ->
 -(2) <= height l - height r <= 2 ->
 avl (Node l x r (max (height l) (height r) + 1)).
Proof.
  intros; auto.
Qed.
Hint Resolve avl_node.


(** empty *)

Lemma empty_avl : avl empty.
Proof.
 auto.
Qed.

(** singleton *)

Lemma singleton_avl : forall x : elt, avl (singleton x).
Proof.
 unfold singleton; intro.
 constructor; auto; try red; simpl; omega_max.
Qed.

(** create *)

Lemma create_avl :
 forall l x r, avl l -> avl r ->  -(2) <= height l - height r <= 2 ->
 avl (create l x r).
Proof.
 unfold create; auto.
Qed.

Lemma create_height :
 forall l x r, avl l -> avl r ->  -(2) <= height l - height r <= 2 ->
 height (create l x r) = max (height l) (height r) + 1.
Proof.
 unfold create; auto.
Qed.

(** bal *)

Lemma bal_avl : forall l x r, avl l -> avl r ->
 -(3) <= height l - height r <= 3 -> avl (bal l x r).
Proof.
 intros l x r; functional induction bal l x r; intros; clearf;
 inv avl; simpl in *;
 match goal with |- avl (assert_false _ _ _) => avl_nns
  | _ => repeat apply create_avl; simpl in *; auto
 end; omega_max.
Qed.

Lemma bal_height_1 : forall l x r, avl l -> avl r ->
 -(3) <= height l - height r <= 3 ->
 0 <= height (bal l x r) - max (height l) (height r) <= 1.
Proof.
 intros l x r; functional induction bal l x r; intros; clearf;
 inv avl; avl_nns; simpl in *; omega_max.
Qed.

Lemma bal_height_2 :
 forall l x r, avl l -> avl r -> -(2) <= height l - height r <= 2 ->
 height (bal l x r) == max (height l) (height r) +1.
Proof.
 intros l x r; functional induction bal l x r; intros; clearf;
 inv avl; simpl in *; omega_max.
Qed.

Ltac omega_bal := match goal with
  | H:avl ?l, H':avl ?r |- context [ bal ?l ?x ?r ] =>
     generalize (bal_height_1 x H H') (bal_height_2 x H H');
     omega_max
  end.

(** add *)

Lemma add_avl_1 :  forall s x, avl s ->
 avl (add x s) /\ 0 <= height (add x s) - height s <= 1.
Proof.
 intros s x; functional induction (add x s); subst;intros; inv avl; simpl in *.
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

Lemma add_avl : forall s x, avl s -> avl (add x s).
Proof.
 intros; destruct (add_avl_1 x H); auto.
Qed.
Hint Resolve add_avl.

(** join *)

Lemma join_avl_1 : forall l x r, avl l -> avl r -> avl (join l x r) /\
 0<= height (join l x r) - max (height l) (height r) <= 1.
Proof.
 join_tac.

 split; simpl; auto.
 destruct (add_avl_1 x H0).
 avl_nns; omega_max.
 set (l:=Node ll lx lr lh) in *.
 split; auto.
 destruct (add_avl_1 x H).
 simpl (height Leaf).
 avl_nns; omega_max.

 inversion_clear H.
 assert (height (Node rl rx rr rh) = rh); auto.
 set (r := Node rl rx rr rh) in *; clearbody r.
 destruct (Hlr x r H2 H0); clear Hrl Hlr.
 set (j := join lr x r) in *; clearbody j.
 simpl.
 assert (-(3) <= height ll - height j <= 3) by omega_max.
 split.
 apply bal_avl; auto.
 omega_bal.

 inversion_clear H0.
 assert (height (Node ll lx lr lh) = lh); auto.
 set (l := Node ll lx lr lh) in *; clearbody l.
 destruct (Hrl H H1); clear Hrl Hlr.
 set (j := join l x rl) in *; clearbody j.
 simpl.
 assert (-(3) <= height j - height rr <= 3) by omega_max.
 split.
 apply bal_avl; auto.
 omega_bal.

 clear Hrl Hlr.
 assert (height (Node ll lx lr lh) = lh); auto.
 assert (height (Node rl rx rr rh) = rh); auto.
 set (l := Node ll lx lr lh) in *; clearbody l.
 set (r := Node rl rx rr rh) in *; clearbody r.
 assert (-(2) <= height l - height r <= 2) by omega_max.
 split.
 apply create_avl; auto.
 rewrite create_height; auto; omega_max.
Qed.

Lemma join_avl : forall l x r, avl l -> avl r -> avl (join l x r).
Proof.
 intros; destruct (join_avl_1 x H H0); auto.
Qed.
Hint Resolve join_avl.

(** remove_min *)

Lemma remove_min_avl_1 : forall l x r h, avl (Node l x r h) ->
 avl (remove_min l x r)#1 /\
 0 <= height (Node l x r h) - height (remove_min l x r)#1 <= 1.
Proof.
 intros l x r; functional induction (remove_min l x r); subst;simpl in *; intros.
 inv avl; simpl in *; split; auto.
 avl_nns; omega_max.
 inversion_clear H.
 rewrite e0 in IHp;simpl in IHp;destruct (IHp _x); auto.
 split; simpl in *.
 apply bal_avl; auto; omega_max.
 omega_bal.
Qed.

Lemma remove_min_avl : forall l x r h, avl (Node l x r h) ->
    avl (remove_min l x r)#1.
Proof.
 intros; destruct (remove_min_avl_1 H); auto.
Qed.

(** merge *)

Lemma merge_avl_1 : forall s1 s2, avl s1 -> avl s2 ->
 -(2) <= height s1 - height s2 <= 2 ->
 avl (merge s1 s2) /\
 0<= height (merge s1 s2) - max (height s1) (height s2) <=1.
Proof.
 intros s1 s2; functional induction (merge s1 s2); intros;
 try factornode _x _x0 _x1 _x2 as s1.
 simpl; split; auto; avl_nns; omega_max.
 simpl; split; auto; avl_nns; simpl in *; omega_max.
 generalize (remove_min_avl_1 H0).
 rewrite e1; destruct 1.
 split.
 apply bal_avl; auto.
 simpl; omega_max.
 simpl in *; omega_bal.
Qed.

Lemma merge_avl : forall s1 s2, avl s1 -> avl s2 ->
  -(2) <= height s1 - height s2 <= 2 -> avl (merge s1 s2).
Proof.
 intros; destruct (merge_avl_1 H H0 H1); auto.
Qed.


(** remove *)

Lemma remove_avl_1 : forall s x, avl s ->
 avl (remove x s) /\ 0 <= height s - height (remove x s) <= 1.
Proof.
 intros s x; functional induction (remove x s); intros.
 intuition; omega_max.
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

Lemma remove_avl : forall s x, avl s -> avl (remove x s).
Proof.
 intros; destruct (remove_avl_1 x H); auto.
Qed.
Hint Resolve remove_avl.

(** concat *)

Lemma concat_avl : forall s1 s2, avl s1 -> avl s2 -> avl (concat s1 s2).
Proof.
 intros s1 s2; functional induction (concat s1 s2); auto.
 intros; apply join_avl; auto.
 generalize (remove_min_avl H0); rewrite e1; simpl; auto.
Qed.
Hint Resolve concat_avl.

(** split *)

Lemma split_avl : forall s x, avl s ->
  avl (split x s)#l /\ avl (split x s)#r.
Proof.
 intros s x; functional induction (split x s); simpl; auto.
 rewrite e1 in IHt;simpl in IHt;inversion_clear 1; intuition.
 simpl; inversion_clear 1; auto.
 rewrite e1 in IHt;simpl in IHt;inversion_clear 1; intuition.
Qed.

(** inter *)

Lemma inter_avl : forall s1 s2, avl s1 -> avl s2 -> avl (inter s1 s2).
Proof.
 intros s1 s2; functional induction inter s1 s2; auto; intros A1 A2;
 generalize (split_avl x1 A2); rewrite e1; simpl; destruct 1;
 inv avl; auto.
Qed.

(** diff *)

Lemma diff_avl : forall s1 s2, avl s1 -> avl s2 -> avl (diff s1 s2).
Proof.
 intros s1 s2; functional induction diff s1 s2; auto; intros A1 A2;
 generalize (split_avl x1 A2); rewrite e1; simpl; destruct 1;
 inv avl; auto.
Qed.

(** union *)

Lemma union_avl : forall s1 s2, avl s1 -> avl s2 -> avl (union s1 s2).
Proof.
 intros s1 s2; functional induction union s1 s2; auto; intros A1 A2;
 generalize (split_avl x1 A2); rewrite e1; simpl; destruct 1;
 inv avl; auto.
Qed.

(** filter *)

Lemma filter_acc_avl : forall f s acc, avl s -> avl acc ->
 avl (filter_acc f acc s).
Proof.
 induction s; simpl; auto.
 intros.
 inv avl.
 destruct (f t); auto.
Qed.
Hint Resolve filter_acc_avl.

Lemma filter_avl : forall f s, avl s -> avl (filter f s).
Proof.
 unfold filter; intros; apply filter_acc_avl; auto.
Qed.

(** partition *)

Lemma partition_acc_avl_1 : forall f s acc, avl s ->
 avl acc#1 -> avl (partition_acc f acc s)#1.
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros.
 inv avl.
 apply IHs2; auto.
 apply IHs1; auto.
 destruct (f t); simpl; auto.
Qed.

Lemma partition_acc_avl_2 : forall f s acc, avl s ->
 avl acc#2 -> avl (partition_acc f acc s)#2.
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros.
 inv avl.
 apply IHs2; auto.
 apply IHs1; auto.
 destruct (f t); simpl; auto.
Qed.

Lemma partition_avl_1 : forall f s, avl s -> avl (partition f s)#1.
Proof.
 unfold partition; intros; apply partition_acc_avl_1; auto.
Qed.

Lemma partition_avl_2 : forall f s, avl s -> avl (partition f s)#2.
Proof.
 unfold partition; intros; apply partition_acc_avl_2; auto.
Qed.

End AvlProofs.


Module OcamlOps (Import I:Int)(X:OrderedType).
Module Import AvlProofs := AvlProofs I X.
Import Raw.
Import Raw.Proofs.
Import II.
Open Local Scope pair_scope.
Open Local Scope nat_scope.

(** Properties of cardinal *)

Lemma bal_cardinal : forall l x r,
 cardinal (bal l x r) = S (cardinal l + cardinal r).
Proof.
 intros l x r; functional induction bal l x r; intros; clearf;
 simpl; auto with arith; romega with *.
Qed.

Lemma add_cardinal : forall x s,
 cardinal (add x s) <= S (cardinal s).
Proof.
 intros; functional induction add x s; simpl; auto with arith;
 rewrite bal_cardinal; romega with *.
Qed.

Lemma join_cardinal : forall l x r,
 cardinal (join l x r) <= S (cardinal l + cardinal r).
Proof.
 join_tac; auto with arith.
 simpl; apply add_cardinal.
 simpl; destruct X.compare; simpl; auto with arith.
 generalize (bal_cardinal (add x ll) lx lr) (add_cardinal x ll);
  romega with *.
 generalize (bal_cardinal ll lx (add x lr)) (add_cardinal x lr);
  romega with *.
 generalize (bal_cardinal ll lx (join lr x (Node rl rx rr rh)))
  (Hlr x (Node rl rx rr rh)); simpl; romega with *.
 simpl S in *; generalize (bal_cardinal (join (Node ll lx lr lh) x rl) rx rr).
 romega with *.
Qed.

Lemma split_cardinal_1 : forall x s,
 (cardinal (split x s)#l <= cardinal s)%nat.
Proof.
 intros x s; functional induction split x s; simpl; auto.
 rewrite e1 in IHt; simpl in *.
 romega with *.
 romega with *.
 rewrite e1 in IHt; simpl in *.
 generalize (@join_cardinal l y rl); romega with *.
Qed.

Lemma split_cardinal_2 : forall x s,
 (cardinal (split x s)#r <= cardinal s)%nat.
Proof.
 intros x s; functional induction split x s; simpl; auto.
 rewrite e1 in IHt; simpl in *.
 generalize (@join_cardinal rl y r); romega with *.
 romega with *.
 rewrite e1 in IHt; simpl in *; romega with *.
Qed.

(** * [ocaml_union], an union faithful to the original ocaml code *)

Definition cardinal2 (s:t*t) := (cardinal s#1 + cardinal s#2)%nat.

Ltac ocaml_union_tac :=
 intros; unfold cardinal2; simpl fst in *; simpl snd in *;
 match goal with H: split ?x ?s = _ |- _ =>
  generalize (split_cardinal_1 x s) (split_cardinal_2 x s);
  rewrite H; simpl; romega with *
 end.

Function ocaml_union (s : t * t) { measure cardinal2 s } : t  :=
 match s with
  | (Leaf, Leaf) => s#2
  | (Leaf, Node _ _ _ _) => s#2
  | (Node _ _ _ _, Leaf) => s#1
  | (Node l1 x1 r1 h1, Node l2 x2 r2 h2) =>
        if ge_lt_dec h1 h2 then
          if eq_dec h2 1%I then add x2 s#1 else
          let (l2',_,r2') := split x1 s#2 in
             join (ocaml_union (l1,l2')) x1 (ocaml_union (r1,r2'))
        else
          if eq_dec h1 1%I then add x1 s#2 else
          let (l1',_,r1') := split x2 s#1 in
             join (ocaml_union (l1',l2)) x2 (ocaml_union (r1',r2))
 end.
Proof.
abstract ocaml_union_tac.
abstract ocaml_union_tac.
abstract ocaml_union_tac.
abstract ocaml_union_tac.
Defined.

Lemma ocaml_union_in : forall s y,
 bst s#1 -> avl s#1 -> bst s#2 -> avl s#2 ->
 (In y (ocaml_union s) <-> In y s#1 \/ In y s#2).
Proof.
 intros s; functional induction ocaml_union s; intros y B1 A1 B2 A2;
  simpl fst in *; simpl snd in *; try clear e0 e1.
 intuition_in.
 intuition_in.
 intuition_in.
 (* add x2 s#1 *)
 inv avl.
 rewrite (height_0 H); [ | avl_nn l2; omega_max].
 rewrite (height_0 H0); [ | avl_nn r2; omega_max].
 rewrite add_in; intuition_in.
 (* join (union (l1,l2')) x1 (union (r1,r2')) *)
 generalize
  (split_avl x1 A2) (split_bst x1 B2)
  (split_in_1 x1 y B2) (split_in_2 x1 y B2).
 rewrite e2; simpl.
 destruct 1; destruct 1; inv avl; inv bst.
 rewrite join_in, IHt, IHt0; auto.
 do 2 (intro Eq; rewrite Eq; clear Eq).
 case (X.compare y x1); intuition_in.
 (* add x1 s#2 *)
 inv avl.
 rewrite (height_0 H3); [ | avl_nn l1; omega_max].
 rewrite (height_0 H4); [ | avl_nn r1; omega_max].
 rewrite add_in; auto; intuition_in.
 (* join (union (l1',l2)) x1 (union (r1',r2)) *)
 generalize
  (split_avl x2 A1) (split_bst x2 B1)
  (split_in_1 x2 y B1) (split_in_2 x2 y B1).
 rewrite e2; simpl.
 destruct 1; destruct 1; inv avl; inv bst.
 rewrite join_in, IHt, IHt0; auto.
 do 2 (intro Eq; rewrite Eq; clear Eq).
 case (X.compare y x2); intuition_in.
Qed.

Lemma ocaml_union_bst : forall s,
 bst s#1 -> avl s#1 -> bst s#2 -> avl s#2 -> bst (ocaml_union s).
Proof.
 intros s; functional induction ocaml_union s; intros B1 A1 B2 A2;
  simpl fst in *; simpl snd in *; try clear e0 e1;
  try apply add_bst; auto.
 (* join (union (l1,l2')) x1 (union (r1,r2')) *)
 clear _x _x0; factornode l2 x2 r2 h2 as s2.
 generalize (split_avl x1 A2) (split_bst x1 B2)
  (@split_in_1 s2 x1)(@split_in_2 s2 x1).
 rewrite e2; simpl.
 destruct 1; destruct 1; intros.
 inv bst; inv avl.
 apply join_bst; auto.
 intro y; rewrite ocaml_union_in, H3; intuition_in.
 intro y; rewrite ocaml_union_in, H4; intuition_in.
 (* join (union (l1',l2)) x1 (union (r1',r2)) *)
 clear _x _x0; factornode l1 x1 r1 h1 as s1.
 generalize (split_avl x2 A1) (split_bst x2 B1)
  (@split_in_1 s1 x2)(@split_in_2 s1 x2).
 rewrite e2; simpl.
 destruct 1; destruct 1; intros.
 inv bst; inv avl.
 apply join_bst; auto.
 intro y; rewrite ocaml_union_in, H3; intuition_in.
 intro y; rewrite ocaml_union_in, H4; intuition_in.
Qed.

Lemma ocaml_union_avl : forall s,
 avl s#1 -> avl s#2 -> avl (ocaml_union s).
Proof.
 intros s; functional induction ocaml_union s;
  simpl fst in *; simpl snd in *; auto.
 intros A1 A2; generalize (split_avl x1 A2); rewrite e2; simpl.
 inv avl; destruct 1; auto.
 intros A1 A2; generalize (split_avl x2 A1); rewrite e2; simpl.
 inv avl; destruct 1; auto.
Qed.

Lemma ocaml_union_alt : forall s, bst s#1 -> avl s#1 -> bst s#2 -> avl s#2 ->
 Equal (ocaml_union s) (union s#1 s#2).
Proof.
 red; intros; rewrite ocaml_union_in, union_in; simpl; intuition.
Qed.


(** * [ocaml_subset], a subset faithful to the original ocaml code *)

Function ocaml_subset (s:t*t) { measure cardinal2 s } : bool :=
 match s with
  | (Leaf, _) => true
  | (Node _ _ _ _, Leaf) => false
  | (Node l1 x1 r1 h1, Node l2 x2 r2 h2) =>
     match X.compare x1 x2 with
      | EQ _ => ocaml_subset (l1,l2) && ocaml_subset (r1,r2)
      | LT _ => ocaml_subset (Node l1 x1 Leaf 0%I, l2) && ocaml_subset (r1,s#2)
      | GT _ => ocaml_subset (Node Leaf x1 r1 0%I, r2) && ocaml_subset (l1,s#2)
     end
 end.

Proof.
 intros; unfold cardinal2; simpl; abstract romega with *.
 intros; unfold cardinal2; simpl; abstract romega with *.
 intros; unfold cardinal2; simpl; abstract romega with *.
 intros; unfold cardinal2; simpl; abstract romega with *.
 intros; unfold cardinal2; simpl; abstract romega with *.
 intros; unfold cardinal2; simpl; abstract romega with *.
Defined.

Lemma ocaml_subset_12 : forall s,
 bst s#1 -> bst s#2 ->
 (ocaml_subset s = true <-> Subset s#1 s#2).
Proof.
 intros s; functional induction ocaml_subset s; simpl;
  intros B1 B2; try clear e0.
 intuition.
 red; auto; inversion 1.
 split; intros; try discriminate.
 assert (H': In _x0 Leaf) by auto; inversion H'.
 (**)
 simpl in *; inv bst.
 rewrite andb_true_iff, IHb, IHb0; auto; clear IHb IHb0.
 unfold Subset; intuition_in.
 assert (X.eq a x2) by order; intuition_in.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 (**)
 simpl in *; inv bst.
 rewrite andb_true_iff, IHb, IHb0; auto; clear IHb IHb0.
 unfold Subset; intuition_in.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 (**)
 simpl in *; inv bst.
 rewrite andb_true_iff, IHb, IHb0; auto; clear IHb IHb0.
 unfold Subset; intuition_in.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
 assert (In a (Node l2 x2 r2 h2)) by auto; intuition_in; order.
Qed.

Lemma ocaml_subset_alt : forall s, bst s#1 -> bst s#2 ->
 ocaml_subset s = subset s#1 s#2.
Proof.
 intros.
 generalize (ocaml_subset_12 H H0); rewrite <-subset_12 by auto.
 destruct ocaml_subset; destruct subset; intuition.
Qed.



(** [ocaml_compare], a compare faithful to the original ocaml code *)

(** termination of [compare_aux] *)

Fixpoint cardinal_e e := match e with
  | End => 0
  | More _ s r => S (cardinal s + cardinal_e r)
 end.

Lemma cons_cardinal_e : forall s e,
 cardinal_e (cons s e) = cardinal s + cardinal_e e.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1; simpl; rewrite <- plus_n_Sm; auto with arith.
Qed.

Definition cardinal_e_2 e := cardinal_e e#1 + cardinal_e e#2.

Function ocaml_compare_aux
 (e:enumeration*enumeration) { measure cardinal_e_2 e } : comparison :=
 match e with
 | (End,End) => Eq
 | (End,More _ _ _) => Lt
 | (More _ _ _, End) => Gt
 | (More x1 r1 e1, More x2 r2 e2) =>
       match X.compare x1 x2 with
        | EQ _ => ocaml_compare_aux (cons r1 e1, cons r2 e2)
        | LT _ => Lt
        | GT _ => Gt
       end
 end.

Proof.
intros; unfold cardinal_e_2; simpl;
abstract (do 2 rewrite cons_cardinal_e; romega with *).
Defined.

Definition ocaml_compare s1 s2 :=
 ocaml_compare_aux (cons s1 End, cons s2 End).

Lemma ocaml_compare_aux_Cmp : forall e,
 Cmp (ocaml_compare_aux e) (flatten_e e#1) (flatten_e e#2).
Proof.
 intros e; functional induction ocaml_compare_aux e; simpl; intros;
  auto; try discriminate.
 apply L.eq_refl.
 simpl in *.
 apply cons_Cmp; auto.
 rewrite <- 2 cons_1; auto.
Qed.

Lemma ocaml_compare_Cmp : forall s1 s2,
 Cmp (ocaml_compare s1 s2) (elements s1) (elements s2).
Proof.
 unfold ocaml_compare; intros.
 assert (H1:=cons_1 s1 End).
 assert (H2:=cons_1 s2 End).
 simpl in *; rewrite <- app_nil_end in *; rewrite <-H1,<-H2.
 apply (@ocaml_compare_aux_Cmp (cons s1 End, cons s2 End)).
Qed.

Lemma ocaml_compare_alt : forall s1 s2, bst s1 -> bst s2 ->
 ocaml_compare s1 s2 = compare s1 s2.
Proof.
 intros s1 s2 B1 B2.
 generalize (ocaml_compare_Cmp s1 s2)(compare_Cmp s1 s2).
 unfold Cmp.
 destruct ocaml_compare; destruct compare; auto; intros; elimtype False.
 elim (lt_not_eq B1 B2 H0); auto.
 elim (lt_not_eq B2 B1 H0); auto.
  apply eq_sym; auto.
 elim (lt_not_eq B1 B2 H); auto.
  elim (lt_not_eq B1 B1).
  red; eapply L.lt_trans; eauto.
  apply eq_refl.
 elim (lt_not_eq B2 B1 H); auto.
  apply eq_sym; auto.
 elim (lt_not_eq B1 B2 H0); auto.
  elim (lt_not_eq B1 B1).
  red; eapply L.lt_trans; eauto.
  apply eq_refl.
Qed.


(** * Equality test *)

Definition ocaml_equal s1 s2 : bool :=
 match ocaml_compare s1 s2 with
  | Eq => true
  | _ => false
 end.

Lemma ocaml_equal_1 : forall s1 s2, bst s1 -> bst s2 ->
 Equal s1 s2 -> ocaml_equal s1 s2 = true.
Proof.
unfold ocaml_equal; intros s1 s2 B1 B2 E.
generalize (ocaml_compare_Cmp s1 s2).
destruct (ocaml_compare s1 s2); auto; intros.
elim (lt_not_eq B1 B2 H E); auto.
elim (lt_not_eq B2 B1 H (eq_sym E)); auto.
Qed.

Lemma ocaml_equal_2 : forall s1 s2,
 ocaml_equal s1 s2 = true -> Equal s1 s2.
Proof.
unfold ocaml_equal; intros s1 s2 E.
generalize (ocaml_compare_Cmp s1 s2);
 destruct ocaml_compare; auto; discriminate.
Qed.

Lemma ocaml_equal_alt : forall s1 s2, bst s1 -> bst s2 ->
 ocaml_equal s1 s2 = equal s1 s2.
Proof.
intros; unfold ocaml_equal, equal; rewrite ocaml_compare_alt; auto.
Qed.

End OcamlOps.



(** * Encapsulation

   We can implement [S] with balanced binary search trees.
   When compared to [FSetAVL], we maintain here two invariants
   (bst and avl) instead of only bst, which is enough for fulfilling
   the FSet interface.

   This encapsulation propose the non-structural variants
   [ocaml_union], [ocaml_subset], [ocaml_compare], [ocaml_equal].
*)

Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.

 Module E := X.
 Module Import OcamlOps := OcamlOps I X.
 Import AvlProofs.
 Import Raw.
 Import Raw.Proofs.

 Record bbst := Bbst {this :> Raw.t; is_bst : bst this; is_avl : avl this}.
 Definition t := bbst.
 Definition elt := E.t.

 Definition In (x : elt) (s : t) : Prop := In x s.
 Definition Equal (s s':t) : Prop := forall a : elt, In a s <-> In a s'.
 Definition Subset (s s':t) : Prop := forall a : elt, In a s -> In a s'.
 Definition Empty (s:t) : Prop := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop) (s:t) : Prop := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop) (s:t) : Prop := exists x, In x s /\ P x.

 Lemma In_1 : forall (s:t)(x y:elt), E.eq x y -> In x s -> In y s.
 Proof. intro s; exact (@In_1 s). Qed.

 Definition mem (x:elt)(s:t) : bool := mem x s.

 Definition empty : t := Bbst empty_bst empty_avl.
 Definition is_empty (s:t) : bool := is_empty s.
 Definition singleton (x:elt) : t :=
   Bbst (singleton_bst x) (singleton_avl x).
 Definition add (x:elt)(s:t) : t :=
   Bbst (add_bst x (is_bst s)) (add_avl x (is_avl s)).
 Definition remove (x:elt)(s:t) : t :=
   Bbst (remove_bst x (is_bst s)) (remove_avl x (is_avl s)).
 Definition inter (s s':t) : t :=
   Bbst (inter_bst (is_bst s) (is_bst s'))
        (inter_avl (is_avl s) (is_avl s')).
 Definition union (s s':t) : t :=
   Bbst (union_bst (is_bst s) (is_bst s'))
        (union_avl (is_avl s) (is_avl s')).
 Definition ocaml_union (s s':t) : t :=
   Bbst (@ocaml_union_bst (s.(this),s'.(this))
          (is_bst s) (is_avl s) (is_bst s') (is_avl s'))
        (@ocaml_union_avl (s.(this),s'.(this)) (is_avl s) (is_avl s')).
 Definition diff (s s':t) : t :=
   Bbst (diff_bst (is_bst s) (is_bst s'))
        (diff_avl (is_avl s) (is_avl s')).
 Definition elements (s:t) : list elt := elements s.
 Definition min_elt (s:t) : option elt := min_elt s.
 Definition max_elt (s:t) : option elt := max_elt s.
 Definition choose (s:t) : option elt := choose s.
 Definition fold (B : Type) (f : elt -> B -> B) (s:t) : B -> B := fold f s.
 Definition cardinal (s:t) : nat := cardinal s.
 Definition filter (f : elt -> bool) (s:t) : t :=
   Bbst (filter_bst f (is_bst s)) (filter_avl f (is_avl s)).
 Definition for_all (f : elt -> bool) (s:t) : bool := for_all f s.
 Definition exists_ (f : elt -> bool) (s:t) : bool := exists_ f s.
 Definition partition (f : elt -> bool) (s:t) : t * t :=
   let p := partition f s in
   (@Bbst (fst p) (partition_bst_1 f (is_bst s))
                 (partition_avl_1 f (is_avl s)),
    @Bbst (snd p) (partition_bst_2 f (is_bst s))
                 (partition_avl_2 f (is_avl s))).

 Definition equal (s s':t) : bool := equal s s'.
 Definition ocaml_equal (s s':t) : bool := ocaml_equal s s'.
 Definition subset (s s':t) : bool := subset s s'.
 Definition ocaml_subset (s s':t) : bool :=
  ocaml_subset (s.(this),s'.(this)).

 Definition eq (s s':t) : Prop := Equal s s'.
 Definition lt (s s':t) : Prop := lt s s'.

 Definition compare (s s':t) : Compare lt eq s s'.
 Proof.
  intros (s,b,a) (s',b',a').
  generalize (compare_Cmp s s').
  destruct Raw.compare; intros; [apply EQ|apply LT|apply GT]; red; auto.
  change (Raw.Equal s s'); auto.
 Defined.

 Definition ocaml_compare (s s':t) : Compare lt eq s s'.
 Proof.
  intros (s,b,a) (s',b',a').
  generalize (ocaml_compare_Cmp s s').
  destruct ocaml_compare; intros; [apply EQ|apply LT|apply GT]; red; auto.
  change (Raw.Equal s s'); auto.
 Defined.

 Definition eq_dec (s s':t) : { eq s s' } + { ~ eq s s' }.
 Proof.
  intros (s,b,a) (s',b',a'); unfold eq; simpl.
  case_eq (Raw.equal s s'); intro H; [left|right].
  apply equal_2; auto.
  intro H'; rewrite equal_1 in H; auto; discriminate.
 Defined.

 (* specs *)
 Section Specs.
 Variable s s' s'': t.
 Variable x y : elt.

 Hint Resolve is_bst is_avl.

 Lemma mem_1 : In x s -> mem x s = true.
 Proof. exact (mem_1 (is_bst s)). Qed.
 Lemma mem_2 : mem x s = true -> In x s.
 Proof. exact (@mem_2 s x). Qed.

 Lemma equal_1 : Equal s s' -> equal s s' = true.
 Proof. exact (equal_1 (is_bst s) (is_bst s')). Qed.
 Lemma equal_2 : equal s s' = true -> Equal s s'.
 Proof. exact (@equal_2 s s'). Qed.

 Lemma ocaml_equal_alt : ocaml_equal s s' = equal s s'.
 Proof.
  destruct s; destruct s'; unfold ocaml_equal, equal; simpl.
  apply ocaml_equal_alt; auto.
 Qed.

 Lemma ocaml_equal_1 : Equal s s' -> ocaml_equal s s' = true.
 Proof. exact (ocaml_equal_1 (is_bst s) (is_bst s')). Qed.
 Lemma ocaml_equal_2 : ocaml_equal s s' = true -> Equal s s'.
 Proof. exact (@ocaml_equal_2 s s'). Qed.

 Ltac wrap t H := unfold t, In; simpl; rewrite H; auto; intuition.

 Lemma subset_1 : Subset s s' -> subset s s' = true.
 Proof. wrap subset subset_12. Qed.
 Lemma subset_2 : subset s s' = true -> Subset s s'.
 Proof. wrap subset subset_12. Qed.

 Lemma ocaml_subset_alt : ocaml_subset s s' = subset s s'.
 Proof.
  destruct s; destruct s'; unfold ocaml_subset, subset; simpl.
  rewrite ocaml_subset_alt; auto.
 Qed.

 Lemma ocaml_subset_1 : Subset s s' -> ocaml_subset s s' = true.
 Proof. wrap ocaml_subset ocaml_subset_12; simpl; auto. Qed.
 Lemma ocaml_subset_2 : ocaml_subset s s' = true -> Subset s s'.
 Proof. wrap ocaml_subset ocaml_subset_12; simpl; auto. Qed.

 Lemma empty_1 : Empty empty.
 Proof. exact empty_1. Qed.

 Lemma is_empty_1 : Empty s -> is_empty s = true.
 Proof. exact (@is_empty_1 s). Qed.
 Lemma is_empty_2 : is_empty s = true -> Empty s.
 Proof. exact (@is_empty_2 s). Qed.

 Lemma add_1 : E.eq x y -> In y (add x s).
 Proof. wrap add add_in. Qed.
 Lemma add_2 : In y s -> In y (add x s).
 Proof. wrap add add_in. Qed.
 Lemma add_3 : ~ E.eq x y -> In y (add x s) -> In y s.
 Proof. wrap add add_in. elim H; auto. Qed.

 Lemma remove_1 : E.eq x y -> ~ In y (remove x s).
 Proof. wrap remove remove_in. Qed.
 Lemma remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
 Proof. wrap remove remove_in. Qed.
 Lemma remove_3 : In y (remove x s) -> In y s.
 Proof. wrap remove remove_in. Qed.

 Lemma singleton_1 : In y (singleton x) -> E.eq x y.
 Proof. exact (@singleton_1 x y). Qed.
 Lemma singleton_2 : E.eq x y -> In y (singleton x).
 Proof. exact (@singleton_2 x y). Qed.

 Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
 Proof. wrap union union_in. Qed.
 Lemma union_2 : In x s -> In x (union s s').
 Proof. wrap union union_in. Qed.
 Lemma union_3 : In x s' -> In x (union s s').
 Proof. wrap union union_in. Qed.

 Lemma ocaml_union_alt : Equal (ocaml_union s s') (union s s').
 Proof.
  unfold ocaml_union, union, Equal, In.
  destruct s as (s0,b,a); destruct s' as (s0',b',a'); simpl.
  exact (@ocaml_union_alt (s0,s0') b a b' a').
 Qed.

 Lemma ocaml_union_1 : In x (ocaml_union s s') -> In x s \/ In x s'.
 Proof. wrap ocaml_union ocaml_union_in; simpl; auto. Qed.
 Lemma ocaml_union_2 : In x s -> In x (ocaml_union s s').
 Proof. wrap ocaml_union ocaml_union_in; simpl; auto. Qed.
 Lemma ocaml_union_3 : In x s' -> In x (ocaml_union s s').
 Proof. wrap ocaml_union ocaml_union_in; simpl; auto. Qed.

 Lemma inter_1 : In x (inter s s') -> In x s.
 Proof. wrap inter inter_in. Qed.
 Lemma inter_2 : In x (inter s s') -> In x s'.
 Proof. wrap inter inter_in. Qed.
 Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
 Proof. wrap inter inter_in. Qed.

 Lemma diff_1 : In x (diff s s') -> In x s.
 Proof. wrap diff diff_in. Qed.
 Lemma diff_2 : In x (diff s s') -> ~ In x s'.
 Proof. wrap diff diff_in. Qed.
 Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
 Proof. wrap diff diff_in. Qed.

 Lemma fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.
 Proof.
 unfold fold, elements; intros; apply fold_1; auto.
 Qed.

 Lemma cardinal_1 : cardinal s = length (elements s).
 Proof.
 unfold cardinal, elements; intros; apply elements_cardinal; auto.
 Qed.

 Section Filter.
 Variable f : elt -> bool.

 Lemma filter_1 : compat_bool E.eq f -> In x (filter f s) -> In x s.
 Proof. intro. wrap filter filter_in. Qed.
 Lemma filter_2 : compat_bool E.eq f -> In x (filter f s) -> f x = true.
 Proof. intro. wrap filter filter_in. Qed.
 Lemma filter_3 : compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).
 Proof. intro. wrap filter filter_in. Qed.

 Lemma for_all_1 : compat_bool E.eq f -> For_all (fun x => f x = true) s -> for_all f s = true.
 Proof. exact (@for_all_1 f s). Qed.
 Lemma for_all_2 : compat_bool E.eq f -> for_all f s = true -> For_all (fun x => f x = true) s.
 Proof. exact (@for_all_2 f s). Qed.

 Lemma exists_1 : compat_bool E.eq f -> Exists (fun x => f x = true) s -> exists_ f s = true.
 Proof. exact (@exists_1 f s). Qed.
 Lemma exists_2 : compat_bool E.eq f -> exists_ f s = true -> Exists (fun x => f x = true) s.
 Proof. exact (@exists_2 f s). Qed.

 Lemma partition_1 : compat_bool E.eq f ->
  Equal (fst (partition f s)) (filter f s).
 Proof.
 unfold partition, filter, Equal, In; simpl ;intros H a.
 rewrite partition_in_1, filter_in; intuition.
 Qed.

 Lemma partition_2 : compat_bool E.eq f ->
  Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
 Proof.
 unfold partition, filter, Equal, In; simpl ;intros H a.
 rewrite partition_in_2, filter_in; intuition.
 rewrite H2; auto.
 destruct (f a); auto.
 red; intros; f_equal.
 rewrite (H _ _ H0); auto.
 Qed.

 End Filter.

 Lemma elements_1 : In x s -> InA E.eq x (elements s).
 Proof. wrap elements elements_in. Qed.
 Lemma elements_2 : InA E.eq x (elements s) -> In x s.
 Proof. wrap elements elements_in. Qed.
 Lemma elements_3 : sort E.lt (elements s).
 Proof. exact (elements_sort (is_bst s)). Qed.
 Lemma elements_3w : NoDupA E.eq (elements s).
 Proof. exact (elements_nodup (is_bst s)). Qed.

 Lemma min_elt_1 : min_elt s = Some x -> In x s.
 Proof. exact (@min_elt_1 s x). Qed.
 Lemma min_elt_2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
 Proof. exact (@min_elt_2 s x y (is_bst s)). Qed.
 Lemma min_elt_3 : min_elt s = None -> Empty s.
 Proof. exact (@min_elt_3 s). Qed.

 Lemma max_elt_1 : max_elt s = Some x -> In x s.
 Proof. exact (@max_elt_1 s x). Qed.
 Lemma max_elt_2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
 Proof. exact (@max_elt_2 s x y (is_bst s)). Qed.
 Lemma max_elt_3 : max_elt s = None -> Empty s.
 Proof. exact (@max_elt_3 s). Qed.

 Lemma choose_1 : choose s = Some x -> In x s.
 Proof. exact (@choose_1 s x). Qed.
 Lemma choose_2 : choose s = None -> Empty s.
 Proof. exact (@choose_2 s). Qed.
 Lemma choose_3 : choose s = Some x -> choose s' = Some y ->
  Equal s s' -> E.eq x y.
 Proof. exact (@choose_3 _ _ (is_bst s) (is_bst s') x y). Qed.

 Lemma eq_refl : eq s s.
 Proof. exact (eq_refl s). Qed.
 Lemma eq_sym : eq s s' -> eq s' s.
 Proof. exact (@eq_sym s s'). Qed.
 Lemma eq_trans : eq s s' -> eq s' s'' -> eq s s''.
 Proof. exact (@eq_trans s s' s''). Qed.

 Lemma lt_trans : lt s s' -> lt s' s'' -> lt s s''.
 Proof. exact (@lt_trans s s' s''). Qed.
 Lemma lt_not_eq : lt s s' -> ~eq s s'.
 Proof. exact (@lt_not_eq _ _ (is_bst s) (is_bst s')). Qed.

 End Specs.
End IntMake.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (X: OrderedType) <: S with Module E := X
 :=IntMake(Z_as_Int)(X).


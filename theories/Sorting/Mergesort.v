(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** A modular implementation of mergesort (the complexity is O(n.log n) in
   the length of the list) *)

(* Initial author: Hugo Herbelin, Oct 2009 *)

Require Import List Setoid Permutation Sorted.

(** Notations and conventions *)

Local Notation "[ ]" := nil.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).

Open Scope bool_scope.

Local Coercion eq_true : bool >-> Sortclass.

(** A total relation *)

Module Type TotalOrder.
  Parameter A : Type.
  Parameter le_bool : A -> A -> bool.
  Infix "<=?" := le_bool (at level 35).
  Axiom le_bool_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
End TotalOrder.

(** The main module defining [mergesort] on a given total order.
    We require minimal hypotheses
 *)

Module Sort (Import X:TotalOrder).

Fixpoint merge l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if a1 <=? a2 then a1 :: merge l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2.

(** We implement mergesort using an explicit stack of pending mergings.
    Pending merging are represented like a binary number where digits are
    either None (denoting 0) or Some list to merge (denoting 1). The n-th
    digit represents the pending list to be merged at level n, if any.
    Merging a list to a stack is like adding 1 to the binary number
    represented by the stack but the carry is propagated by merging the
    lists. In practice, when used in mergesort, the n-th digit, if non 0,
    carries a list of length 2^n. For instance, adding singleton list
    [3] to the stack Some [4]::Some [2;6]::None::Some [1;3;5;5]
    reduces to propagate the carry [3;4] (resulting of the merge of [3]
    and [4]) to the list Some [2;6]::None::Some [1;3;5;5], which reduces
    to propagating the carry [2;3;4;6] (resulting of the merge of [3;4] and
    [2;6]) to the list None::Some [1;3;5;5], which locally produces
    Some [2;3;4;6]::Some [1;3;5;5], i.e. which produces the final result
    None::None::Some [2;3;4;6]::Some [1;3;5;5].

    For instance, here is how [6;2;3;1;5] is sorted:

       operation             stack                list
       iter_merge            []                   [6;2;3;1;5]
    =  append_list_to_stack  [ + [6]]             [2;3;1;5]
    -> iter_merge            [[6]]                [2;3;1;5]
    =  append_list_to_stack  [[6] + [2]]          [3;1;5]
    =  append_list_to_stack  [ + [2;6];]          [3;1;5]
    -> iter_merge            [[2;6];]             [3;1;5]
    =  append_list_to_stack  [[2;6]; + [3]]       [1;5]
    -> merge_list            [[2;6];[3]]          [1;5]
    =  append_list_to_stack  [[2;6];[3] + [1]     [5]
    =  append_list_to_stack  [[2;6] + [1;3];]     [5]
    =  append_list_to_stack  [ + [1;2;3;6];;]     [5]
    -> merge_list            [[1;2;3;6];;]        [5]
    =  append_list_to_stack  [[1;2;3;6];; + [5]]  []
    -> merge_stack           [[1;2;3;6];;[5]]
    =                                             [1;2;3;5;6]

    The complexity of the algorithm is n*log n, since there are
    2^(p-1) mergings to do of length 2, 2^(p-2) of length 4, ..., 2^0
    of length 2^p for a list of length 2^p. The algorithm does not need
    explicitly cutting the list in 2 parts at each step since it the
    successive accumulation of fragments on the stack which ensures
    that lists are merged on a dichotomic basis.
*)

Fixpoint merge_list_to_stack stack l :=
  match stack with
  | [] => [Some l]
  | None :: stack' => Some l :: stack'
  | Some l' :: stack' => None :: merge_list_to_stack stack' (merge l' l)
  end.

Fixpoint merge_stack stack :=
  match stack with
  | [] => []
  | None :: stack' => merge_stack stack'
  | Some l :: stack' => merge l (merge_stack stack')
  end.

Fixpoint iter_merge stack l :=
  match l with
  | [] => merge_stack stack
  | a::l' => iter_merge (merge_list_to_stack stack [a]) l'
  end.

Definition sort := iter_merge [].

(** The proof of correctness *)

Local Notation Sorted := (LocallySorted le_bool) (only parsing).

Fixpoint SortedStack stack :=
  match stack with
  | [] => True
  | None :: stack' => SortedStack stack'
  | Some l :: stack' => Sorted l /\ SortedStack stack'
  end.

Local Ltac invert H := inversion H; subst; clear H.

Fixpoint flatten_stack (stack : list (option (list A))) :=
  match stack with
  | [] => []
  | None :: stack' => flatten_stack stack'
  | Some l :: stack' => l ++ flatten_stack stack'
  end.

Theorem Sorted_merge : forall l1 l2,
  Sorted l1 -> Sorted l2 -> Sorted (merge l1 l2).
Proof.
induction l1; induction l2; intros; simpl; auto.
  destruct (a <=? a0) as ()_eqn:Heq1.
    invert H.
      simpl. constructor; trivial; rewrite Heq1; constructor.
      assert (Sorted (merge (b::l) (a0::l2))) by (apply IHl1; auto).
      clear H0 H3 IHl1; simpl in *.
      destruct (b <=? a0); constructor; auto || rewrite Heq1; constructor.
    assert (a0 <=? a) by
      (destruct (le_bool_total a0 a) as [H'|H']; trivial || (rewrite Heq1 in H'; inversion H')).
    invert H0.
      constructor; trivial.
      assert (Sorted (merge (a::l1) (b::l))) by auto using IHl1.
      clear IHl2; simpl in *.
      destruct (a <=? b) as ()_eqn:Heq2;
        constructor; auto.
Qed.

Theorem Permuted_merge : forall l1 l2, Permutation (l1++l2) (merge l1 l2).
Proof.
  induction l1; simpl merge; intro.
    assert (forall l, (fix merge_aux (l0 : list A) : list A := l0) l = l)
    as -> by (destruct l; trivial). (* Technical lemma *)
    apply Permutation_refl.
  induction l2.
    rewrite app_nil_r. apply Permutation_refl.
    destruct (a <=? a0).
      constructor; apply IHl1.
      apply Permutation_sym, Permutation_cons_app, Permutation_sym, IHl2.
Qed.

Theorem Sorted_merge_list_to_stack : forall stack l,
  SortedStack stack -> Sorted l -> SortedStack (merge_list_to_stack stack l).
Proof.
  induction stack as [|[|]]; intros; simpl.
    auto.
    apply IHstack. destruct H as (_,H1). fold SortedStack in H1. auto.
      apply Sorted_merge; auto; destruct H; auto.
      auto.
Qed.

Theorem Permuted_merge_list_to_stack : forall stack l,
  Permutation (l ++ flatten_stack stack) (flatten_stack (merge_list_to_stack stack l)).
Proof.
  induction stack as [|[]]; simpl; intros.
    reflexivity.
    rewrite app_assoc.
    etransitivity.
      apply Permutation_app_tail.
      etransitivity.
        apply Permutation_app_comm.
      apply Permuted_merge.
    apply IHstack.
    reflexivity.
Qed.

Theorem Sorted_merge_stack : forall stack,
  SortedStack stack -> Sorted (merge_stack stack).
Proof.
induction stack as [|[|]]; simpl; intros.
  constructor; auto.
  apply Sorted_merge; tauto.
  auto.
Qed.

Theorem Permuted_merge_stack : forall stack,
  Permutation (flatten_stack stack) (merge_stack stack).
Proof.
induction stack as [|[]]; simpl.
  trivial.
  transitivity (l ++ merge_stack stack).
    apply Permutation_app_head; trivial.
    apply Permuted_merge.
  assumption.
Qed.

Theorem Sorted_iter_merge : forall stack l,
  SortedStack stack -> Sorted (iter_merge stack l).
Proof.
  intros stack l H; induction l in stack, H |- *; simpl.
    auto using Sorted_merge_stack.
    assert (Sorted [a]) by constructor.
    auto using Sorted_merge_list_to_stack.
Qed.

Theorem Permuted_iter_merge : forall l stack,
  Permutation (flatten_stack stack ++ l) (iter_merge stack l).
Proof.
  induction l; simpl; intros.
    rewrite app_nil_r. apply Permuted_merge_stack.
    change (a::l) with ([a]++l).
    rewrite app_assoc.
    etransitivity.
      apply Permutation_app_tail.
    etransitivity.
    apply Permutation_app_comm.
    apply Permuted_merge_list_to_stack.
    apply IHl.
Qed.

Theorem Sorted_sort : forall l, Sorted (sort l).
Proof.
intro; apply Sorted_iter_merge. constructor.
Qed.

Corollary LocallySorted_sort : forall l, Sorted.Sorted le_bool (sort l).
Proof. intro; eapply Sorted_LocallySorted_iff, Sorted_sort; auto. Qed.

Theorem Permuted_sort : forall l, Permutation l (sort l).
Proof.
intro; apply (Permuted_iter_merge l []).
Qed.

Corollary StronglySorted_sort : forall l,
  Transitive le_bool -> StronglySorted le_bool (sort l).
Proof. auto using Sorted_StronglySorted, LocallySorted_sort. Qed.

End Sort.

(** An example *)

Module NatOrder.
  Definition A := nat.
  Fixpoint le_bool x y :=
    match x, y with
    | 0, _ => true
    | S x', 0 => false
    | S x', S y' => le_bool x' y'
    end.
  Infix "<=?" := le_bool (at level 35).
  Theorem le_bool_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
  Proof.
    induction a1; destruct a2; simpl; auto using is_eq_true.
  Qed.

End NatOrder.

Module Import NatSort := Sort NatOrder.

Example SimpleMergeExample := Eval compute in sort [5;3;6;1;8;6;0].


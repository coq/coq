(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** A development of Treesort on Heap trees *)

(* G. Huet 1-9-95 uses Multiset *)

Require PolyList.
Require Multiset.
Require Permutation.
Require Relations.
Require Sorting.


Section defs.

Variable A : Set.
Variable leA : (relation A).
Variable eqA : (relation A).

Local gtA := [x,y:A]~(leA x y).

Hypothesis leA_dec : (x,y:A){(leA x y)}+{(leA y x)}.
Hypothesis eqA_dec : (x,y:A){(eqA x y)}+{~(eqA x y)}.
Hypothesis leA_refl : (x,y:A) (eqA x y) -> (leA x y).
Hypothesis leA_trans : (x,y,z:A) (leA x y) -> (leA y z) -> (leA x z).
Hypothesis leA_antisym : (x,y:A)(leA x y) -> (leA y x) -> (eqA x y).

Hints Resolve leA_refl.
Hints Immediate eqA_dec leA_dec leA_antisym.

Local emptyBag := (EmptyBag A).
Local singletonBag := (SingletonBag eqA_dec).

Inductive Tree : Set :=
      Tree_Leaf : Tree
    | Tree_Node : A -> Tree -> Tree -> Tree.

(** [a] is lower than a Tree [T] if [T] is a Leaf
    or [T] is a Node holding [b>a] *)

Definition leA_Tree := [a:A; t:Tree]
 Cases t of 
   Tree_Leaf           => True
 | (Tree_Node b T1 T2) => (leA a b)
 end.

Lemma leA_Tree_Leaf : (a:A)(leA_Tree a Tree_Leaf).
Proof.
Simpl; Auto with datatypes.
Qed.

Lemma leA_Tree_Node : (a,b:A)(G,D:Tree)(leA a b) ->
                        (leA_Tree a (Tree_Node b G D)).
Proof.
Simpl; Auto with datatypes.
Qed.

Hints Resolve leA_Tree_Leaf leA_Tree_Node.


(** The heap property *)

Inductive is_heap : Tree -> Prop :=
      nil_is_heap : (is_heap Tree_Leaf)
    | node_is_heap : (a:A)(T1,T2:Tree)
                     (leA_Tree a T1) ->
                     (leA_Tree a T2) ->
                     (is_heap T1) -> (is_heap T2) ->
                     (is_heap (Tree_Node a T1 T2)).

Hint constr_is_heap := Constructors is_heap.

Lemma invert_heap : (a:A)(T1,T2:Tree)(is_heap (Tree_Node a T1 T2))->
  (leA_Tree a T1) /\ (leA_Tree a T2) /\
  (is_heap T1) /\ (is_heap T2).
Proof.
Intros; Inversion H; Auto with datatypes.
Qed.

(* This lemma ought to be generated automatically by the Inversion tools *)
Lemma is_heap_rec : (P:Tree->Set)
        (P Tree_Leaf)->
         ((a:A)
           (T1:Tree)
            (T2:Tree)
             (leA_Tree a T1)->
              (leA_Tree a T2)->
               (is_heap T1)->
                (P T1)->(is_heap T2)->(P T2)->(P (Tree_Node a T1 T2)))
         -> (T:Tree)(is_heap T) -> (P T).
Proof.
Induction T; Auto with datatypes.
Intros a G PG D PD PN. 
Elim (invert_heap a G D); Auto with datatypes.
Intros H1 H2; Elim H2; Intros H3 H4; Elim H4; Intros.
Apply H0; Auto with datatypes.
Qed.

Lemma low_trans : 
  (T:Tree)(a,b:A)(leA a b) -> (leA_Tree b T) -> (leA_Tree a T).
Proof.
Induction T; Auto with datatypes.
Intros; Simpl; Apply leA_trans with b; Auto with datatypes.
Qed.

(** contents of a tree as a multiset *)

(** Nota Bene : In what follows the definition of SingletonBag
    in not used. Actually, we could just take as postulate:
    [Parameter SingletonBag : A->multiset].  *)

Fixpoint  contents [t:Tree] : (multiset A) :=
 Cases t of
   Tree_Leaf           => emptyBag
 | (Tree_Node a t1 t2) => (munion (contents t1) 
                          (munion (contents t2) (singletonBag a)))
end.


(** equivalence of two trees is equality of corresponding multisets *)

Definition equiv_Tree := [t1,t2:Tree](meq (contents t1) (contents t2)).


(** specification of heap insertion *)

Inductive insert_spec [a:A; T:Tree] : Set :=
   insert_exist : (T1:Tree)(is_heap T1) ->
                  (meq (contents T1) (munion (contents T) (singletonBag a))) ->
                  ((b:A)(leA b a)->(leA_Tree b T)->(leA_Tree b T1)) ->
                  (insert_spec a T).


Lemma insert : (T:Tree)(is_heap T) -> (a:A)(insert_spec a T).
Proof.
Induction 1; Intros.
Apply insert_exist with (Tree_Node a Tree_Leaf Tree_Leaf); Auto with datatypes.
Simpl; Unfold meq munion; Auto with datatypes.
Elim (leA_dec a a0); Intros.
Elim (H3 a0); Intros.
Apply insert_exist with (Tree_Node a T2 T0); Auto with datatypes.
Simpl; Apply treesort_twist1; Trivial with datatypes. 
Elim (H3 a); Intros T3 HeapT3 ConT3 LeA.
Apply insert_exist with (Tree_Node a0 T2 T3); Auto with datatypes.
Apply node_is_heap; Auto with datatypes.
Apply low_trans with a; Auto with datatypes.
Apply LeA; Auto with datatypes.
Apply low_trans with a; Auto with datatypes.
Simpl; Apply treesort_twist2; Trivial with datatypes. 
Qed.

(** building a heap from a list *)

Inductive build_heap [l:(list A)] : Set :=
   heap_exist : (T:Tree)(is_heap T) ->
                (meq (list_contents eqA_dec l)(contents T)) ->
                (build_heap l).

Lemma list_to_heap : (l:(list A))(build_heap l).
Proof.
Induction l.
Apply (heap_exist (nil  A) Tree_Leaf); Auto with datatypes.
Simpl; Unfold meq; Auto with datatypes.
Induction 1.
Intros T i m; Elim (insert T i a).
Intros; Apply heap_exist with T1; Simpl; Auto with datatypes.
Apply meq_trans with (munion (contents T) (singletonBag a)).
Apply meq_trans with (munion (singletonBag a) (contents T)).
Apply meq_right; Trivial with datatypes.
Apply munion_comm.
Apply meq_sym; Trivial with datatypes.
Qed.


(** building the sorted list *)

Inductive flat_spec [T:Tree] : Set :=
 flat_exist : (l:(list A))(sort leA l) ->
              ((a:A)(leA_Tree a T)->(lelistA leA a l)) ->
              (meq (contents T) (list_contents eqA_dec l)) ->
              (flat_spec T).

Lemma heap_to_list : (T:Tree)(is_heap T) -> (flat_spec T).
Proof.
  Intros T h; Elim h; Intros.
  Apply flat_exist with (nil A); Auto with datatypes.
  Elim H2; Intros l1 s1 i1 m1; Elim H4; Intros l2 s2 i2 m2.
  Elim (merge leA_dec eqA_dec s1 s2); Intros.
  Apply flat_exist with (cons a l); Simpl; Auto with datatypes.
  Apply meq_trans with 
    (munion (list_contents eqA_dec l1) (munion (list_contents eqA_dec l2) 
                                               (singletonBag a))).
  Apply meq_congr; Auto with datatypes.
  Apply meq_trans with 
    (munion (singletonBag a) (munion (list_contents eqA_dec l1) 
                                     (list_contents eqA_dec  l2))).
  Apply munion_rotate.
  Apply meq_right; Apply meq_sym; Trivial with datatypes.
Qed.

(** specification of treesort *)

Theorem treesort : (l:(list A))
  {m:(list A) | (sort leA m) & (permutation eqA_dec l m)}.
Proof.
  Intro l; Unfold permutation.
  Elim (list_to_heap l).
  Intros.
  Elim (heap_to_list T); Auto with datatypes.
  Intros.
  Exists l0; Auto with datatypes.
  Apply meq_trans with (contents T); Trivial with datatypes.
Qed.

End defs.

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require PolyList.
Require Multiset.
Require Permutation.
Require Relations.

Set Implicit Arguments.

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

(** [lelistA] *)

Inductive lelistA [a:A] : (list A) -> Prop :=
      nil_leA : (lelistA a (nil A))
    | cons_leA : (b:A)(l:(list A))(leA a b)->(lelistA a (cons b l)).
Hint constr_lelistA := Constructors lelistA.

Lemma lelistA_inv : (a,b:A)(l:(list A))
      (lelistA a (cons b l)) -> (leA a b).
Proof.
  Intros; Inversion H; Trivial with datatypes.
Qed.

(** definition for a list to be sorted *)

Inductive sort : (list A) -> Prop :=
   nil_sort : (sort (nil A))
 | cons_sort : (a:A)(l:(list A))(sort l) -> (lelistA a l) -> (sort (cons a l)).
Hint constr_sort := Constructors sort.

Lemma sort_inv : (a:A)(l:(list A))(sort (cons a l))->(sort l) /\ (lelistA a l).
Proof.
Intros; Inversion H; Auto with datatypes.
Qed.

Lemma sort_rec : (P:(list A)->Set)
     (P (nil A)) ->
     ((a:A)(l:(list A))(sort l)->(P l)->(lelistA a l)->(P (cons a l))) ->
     (y:(list A))(sort y) -> (P y).
Proof.
Induction y; Auto with datatypes.
Intros; Elim (!sort_inv a l); Auto with datatypes.
Qed.

(** merging two sorted lists *)

Inductive merge_lem [l1:(list A);l2:(list A)] : Set :=
  merge_exist : (l:(list A))(sort l) ->
    (meq (list_contents eqA_dec l)
         (munion (list_contents eqA_dec l1) (list_contents eqA_dec l2))) ->
    ((a:A)(lelistA a l1)->(lelistA a l2)->(lelistA a l)) ->
    (merge_lem l1 l2).

Lemma merge : (l1:(list A))(sort l1)->(l2:(list A))(sort l2)->(merge_lem l1 l2).
Proof.
  Induction 1; Intros.
  Apply merge_exist with l2; Auto with datatypes.
  Elim H3; Intros.
  Apply merge_exist with (cons a l); Simpl; Auto with datatypes.
  Elim (leA_dec a a0); Intros.

(* 1 (leA a a0) *)
  Cut (merge_lem l (cons a0 l0)); Auto with datatypes.
  Intros (l3, l3sorted, l3contents, Hrec).
  Apply merge_exist with (cons a l3); Simpl; Auto with datatypes.
  Apply meq_trans with (munion (singletonBag a)
	                       (munion (list_contents eqA_dec l)
                                       (list_contents eqA_dec (cons a0 l0)))).
  Apply meq_right; Trivial with datatypes.
  Apply meq_sym; Apply munion_ass.
  Intros; Apply cons_leA.
  Apply lelistA_inv with l; Trivial with datatypes.

(* 2 (leA a0 a) *)
  Elim H5; Simpl; Intros.
  Apply merge_exist with (cons a0 l3); Simpl; Auto with datatypes.
  Apply meq_trans with (munion (singletonBag a0)
                               (munion (munion (singletonBag a) 
                                               (list_contents eqA_dec l))
                               (list_contents eqA_dec l0))).
  Apply meq_right; Trivial with datatypes.
  Apply munion_perm_left.
  Intros; Apply cons_leA; Apply lelistA_inv with l0; Trivial with datatypes.
Qed.

End defs.

Unset Implicit Arguments.
Hint constr_sort : datatypes v62 := Constructors sort.
Hint constr_lelistA : datatypes v62 := Constructors lelistA.

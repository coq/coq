(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Relations.
Require PolyList.
Require Multiset.

Set Implicit Arguments.

Section defs.

Variable A : Set.
Variable leA : (relation A).
Variable eqA : (relation A).

Local gtA := [x,y:A]~(leA x y).

Hypothesis leA_dec : (x,y:A){(leA x y)}+{~(leA x y)}.
Hypothesis eqA_dec : (x,y:A){(eqA x y)}+{~(eqA x y)}.
Hypothesis leA_refl : (x,y:A) (eqA x y) -> (leA x y).
Hypothesis leA_trans : (x,y,z:A) (leA x y) -> (leA y z) -> (leA x z).
Hypothesis leA_antisym : (x,y:A)(leA x y) -> (leA y x) -> (eqA x y).

Hints Resolve leA_refl : default.
Hints Immediate eqA_dec leA_dec leA_antisym : default.

Local emptyBag := (EmptyBag A).
Local singletonBag := (SingletonBag eqA_dec).

(** contents of a list *)

Fixpoint list_contents [l:(list A)] : (multiset A) :=
 Cases l of
   nil        => emptyBag
 | (cons a l) => (munion (singletonBag a) (list_contents l))
 end.

Lemma list_contents_app : (l,m:(list A))
  (meq (list_contents (app l m)) (munion (list_contents l) (list_contents m))).
Proof.
Induction l; Simpl; Auto with datatypes.
Intros.
Apply meq_trans with  
 (munion (singletonBag a) (munion (list_contents l0) (list_contents m))); Auto with datatypes.
Qed.
Hints Resolve list_contents_app.

Definition permutation := [l,m:(list A)](meq (list_contents l) (list_contents m)).

Lemma permut_refl : (l:(list A))(permutation l l).
Proof.
Unfold permutation; Auto with datatypes.
Qed.
Hints Resolve permut_refl.

Lemma permut_tran : (l,m,n:(list A))
   (permutation l m) -> (permutation m n) -> (permutation l n).
Proof.
Unfold permutation; Intros.
Apply meq_trans with (list_contents m); Auto with datatypes.
Qed.

Lemma permut_right : (l,m:(list A))
   (permutation l m) -> (a:A)(permutation (cons a l) (cons a m)).
Proof.
Unfold permutation; Simpl; Auto with datatypes.
Qed.
Hints Resolve permut_right.

Lemma permut_app : (l,l',m,m':(list A))
   (permutation l l') -> (permutation m m') ->
   (permutation (app l m) (app l' m')).
Proof.
Unfold permutation; Intros.
Apply meq_trans with (munion (list_contents l) (list_contents m)); Auto with datatypes.
Apply meq_trans with (munion (list_contents l') (list_contents m')); Auto with datatypes.
Apply meq_trans with (munion (list_contents l') (list_contents m)); Auto with datatypes.
Qed.
Hints Resolve permut_app.

Lemma permut_cons : (l,m:(list A))(permutation l m) ->
    (a:A)(permutation (cons a l) (cons a m)).
Proof.
Intros l m H a.
Change (permutation (app (cons a (nil A)) l) (app (cons a (nil A)) m)).
Apply permut_app; Auto with datatypes.
Qed.
Hints Resolve permut_cons.

Lemma permut_middle : (l,m:(list A))
   (a:A)(permutation (cons a (app l m)) (app l (cons a m))).
Proof.
Unfold permutation.
Induction l; Simpl; Auto with datatypes.
Intros.
Apply meq_trans with (munion (singletonBag a)
          (munion (singletonBag a0) (list_contents (app l0 m)))); Auto with datatypes.
Apply munion_perm_left; Auto with datatypes.
Qed.
Hints Resolve permut_middle.

End defs.
Unset Implicit Arguments.


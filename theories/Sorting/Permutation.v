(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Relations.
Require Import List.
Require Import Multiset.

Set Implicit Arguments.

Section defs.

Variable A : Set.
Variable leA : relation A.
Variable eqA : relation A.

Let gtA (x y:A) := ~ leA x y.

Hypothesis leA_dec : forall x y:A, {leA x y} + {~ leA x y}.
Hypothesis eqA_dec : forall x y:A, {eqA x y} + {~ eqA x y}.
Hypothesis leA_refl : forall x y:A, eqA x y -> leA x y.
Hypothesis leA_trans : forall x y z:A, leA x y -> leA y z -> leA x z.
Hypothesis leA_antisym : forall x y:A, leA x y -> leA y x -> eqA x y.

Hint Resolve leA_refl: default.
Hint Immediate eqA_dec leA_dec leA_antisym: default.

Let emptyBag := EmptyBag A.
Let singletonBag := SingletonBag _ eqA_dec.

(** contents of a list *)

Fixpoint list_contents (l:list A) : multiset A :=
  match l with
  | nil => emptyBag
  | a :: l => munion (singletonBag a) (list_contents l)
  end.

Lemma list_contents_app :
 forall l m:list A,
   meq (list_contents (l ++ m)) (munion (list_contents l) (list_contents m)).
Proof.
simple induction l; simpl in |- *; auto with datatypes.
intros.
apply meq_trans with
 (munion (singletonBag a) (munion (list_contents l0) (list_contents m)));
 auto with datatypes.
Qed.
Hint Resolve list_contents_app.

Definition permutation (l m:list A) :=
  meq (list_contents l) (list_contents m).

Lemma permut_refl : forall l:list A, permutation l l.
Proof.
unfold permutation in |- *; auto with datatypes.
Qed.
Hint Resolve permut_refl.

Lemma permut_tran :
 forall l m n:list A, permutation l m -> permutation m n -> permutation l n.
Proof.
unfold permutation in |- *; intros.
apply meq_trans with (list_contents m); auto with datatypes.
Qed.

Lemma permut_right :
 forall l m:list A,
   permutation l m -> forall a:A, permutation (a :: l) (a :: m).
Proof.
unfold permutation in |- *; simpl in |- *; auto with datatypes.
Qed.
Hint Resolve permut_right.

Lemma permut_app :
 forall l l' m m':list A,
   permutation l l' -> permutation m m' -> permutation (l ++ m) (l' ++ m').
Proof.
unfold permutation in |- *; intros.
apply meq_trans with (munion (list_contents l) (list_contents m));
 auto with datatypes.
apply meq_trans with (munion (list_contents l') (list_contents m'));
 auto with datatypes.
apply meq_trans with (munion (list_contents l') (list_contents m));
 auto with datatypes.
Qed.
Hint Resolve permut_app.

Lemma permut_cons :
 forall l m:list A,
   permutation l m -> forall a:A, permutation (a :: l) (a :: m).
Proof.
intros l m H a.
change (permutation ((a :: nil) ++ l) ((a :: nil) ++ m)) in |- *.
apply permut_app; auto with datatypes.
Qed.
Hint Resolve permut_cons.

Lemma permut_middle :
 forall (l m:list A) (a:A), permutation (a :: l ++ m) (l ++ a :: m).
Proof.
unfold permutation in |- *.
simple induction l; simpl in |- *; auto with datatypes.
intros.
apply meq_trans with
 (munion (singletonBag a)
    (munion (singletonBag a0) (list_contents (l0 ++ m))));
 auto with datatypes.
apply munion_perm_left; auto with datatypes.
Qed.
Hint Resolve permut_middle.

End defs.
Unset Implicit Arguments.

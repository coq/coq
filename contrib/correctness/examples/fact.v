(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(* Proof of an imperative program computing the factorial (over type nat) *)

Require Correctness.
Require Omega.
Require Arith.

Fixpoint fact [n:nat] : nat :=
  Cases n of
    O     => (S O)
  | (S p) => (mult n (fact p))
  end.

(* (x * y) * (x-1)! = y * x!  *)

Lemma fact_rec : (x,y:nat)(lt O x) ->
  (mult (mult x y) (fact (pred x))) = (mult y (fact x)).
Proof.
Intros x y H.
Generalize (mult_sym x y). Intro H1. Rewrite H1.
Generalize (mult_assoc_r y x (fact (pred x))). Intro H2. Rewrite H2.
Apply (f_equal nat nat [x:nat](mult y x)).
Generalize H. Elim x; Auto with arith.
Save.


(* we declare two variables x and y *)

Global Variable x : nat ref.
Global Variable y : nat ref.

(* we give the annotated program *)

Correctness factorielle 
  begin
    y := (S O);
    while (notzerop_bool !x) do
      { invariant (mult y (fact x)) = (fact x@0) as I
        variant x for lt }
      y := (mult !x !y);
      x := (pred !x)
    done
  end
  { y = (fact x@0) }.
Proof.
Split.
(* decreasing of the variant *)
Omega.
(* preservation of the invariant *)
Rewrite <- I. Exact (fact_rec x0 y1 Test1).
(* entrance of loop *)
Auto with arith.
(* exit of loop *)
Elim I. Intros H1 H2.
Rewrite H2 in H1.
Rewrite <- H1.
Auto with arith.
Save.

(* Destruct and primitive projections *)

(* Checking the (superficial) part of #5707:
   "destruct" should be able to use non-dependent case analysis when
   dependent case analysis is not available and unneeded *)

Set Primitive Projections.

Inductive foo := Foo { proj1 : nat; proj2 : nat }.

Goal forall x : foo, True.
Proof. intros x. destruct x.

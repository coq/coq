Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 5302 lines to 4649 lines, then from 4660 lines to 355 lines, then from 360 lines to 269 lines, then from 269 lines to 175 lines, then from 144 lines to 119 lines, then from 103 lines to 83 lines, then from 86 lines to 36 lines, then from 37 lines to 17 lines *)

Axiom admit : forall {T}, T.
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) := forall x : A, r (s x) = x.
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv { equiv_inv : B -> A ; eisretr : Sect equiv_inv f }.
Record Equiv A B := BuildEquiv { equiv_fun :> A -> B ; equiv_isequiv :> IsEquiv equiv_fun }.
Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.
Definition equiv_path (A B : Type) (p : A = B) : Equiv A B := admit.
Class Univalence := { isequiv_equiv_path :> forall (A B : Type), IsEquiv (equiv_path A B) }.
Definition path_universe `{Univalence} {A B : Type} (f : A -> B) {feq : IsEquiv f} : (A = B) := admit.
Context `{ua:Univalence}.
Variable A:Type.
Goal forall (I : Type) (f : I -> A),
       {p : I = {a : A & @hfiber I A f a} & True }.
intros.
clear.
try exists (path_universe admit). (* Toplevel input, characters 15-44:
Anomaly: Uncaught exception Not_found(_). Please report. *)

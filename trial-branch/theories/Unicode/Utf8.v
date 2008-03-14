(* -*- coding:utf-8 -* *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Logic *)
Notation "∀ x , P" := 
  (forall x , P) (at level 200, x ident) : type_scope.
Notation "∀ x y , P" := 
  (forall x y , P) (at level 200, x ident, y ident) : type_scope.
Notation "∀ x y z , P" := 
  (forall x y z , P) (at level 200, x ident, y ident, z ident) : type_scope.
Notation "∀ x y z u , P" := 
  (forall x y z u , P) (at level 200, x ident, y ident, z ident, u ident) : type_scope.
Notation "∀ x : t , P" := 
  (forall x : t , P) (at level 200, x ident) : type_scope.
Notation "∀ x y : t , P" := 
  (forall x y : t , P) (at level 200, x ident, y ident) : type_scope.
Notation "∀ x y z : t , P" := 
  (forall x y z : t , P) (at level 200, x ident, y ident, z ident) : type_scope.
Notation "∀ x y z u : t , P" := 
  (forall x y z u : t , P) (at level 200, x ident, y ident, z ident, u ident) : type_scope.

Notation "∃ x , P" := (exists x , P) (at level 200, x ident) : type_scope.
Notation "∃ x : t , P" := (exists x : t, P) (at level 200, x ident) : type_scope.

Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.
Notation "x → y" := (x -> y) (at level 90, right associativity): type_scope.
Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "⌉ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

(* Abstraction *)
(* Not nice
Notation  "'λ' x : T , y" := ([x:T] y) (at level 1, x,T,y at level 10).
Notation  "'λ' x := T , y" := ([x:=T] y) (at level 1, x,T,y at level 10).
*)

(* Arithmetic *)
Notation "x ≤ y" := (le x y) (at level 70, no associativity).
Notation "x ≥ y" := (ge x y) (at level 70, no associativity).

(* test *)
(*
Goal ∀ x, True -> (∃ y , x ≥ y + 1) ∨ x ≤ 0.
*)

(* Integer Arithmetic *)
(* TODO: this should come after ZArith
Notation "x ≤ y" := (Zle x y) (at level 1, y at level 10).
*)

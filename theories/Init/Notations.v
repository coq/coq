(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** These are the notations whose level and associativity is imposed by Coq *)

(** Notations for logical connectives *)

Uninterpreted Notation "x /\ y" (at level 6, right associativity) 
  V8only (at level 80, right associativity).
Uninterpreted Notation "x \/ y" (at level 7, right associativity)
  V8only (at level 85, right associativity).

Uninterpreted Notation "x <-> y" (at level 8, right associativity)
  V8only (at level 95, no associativity).

Uninterpreted Notation "~ x" (at level 5, right associativity)
  V8only (at level 75, right associativity).

(** Notations for equality and inequalities *)

Uninterpreted Notation "x = y  :> T" 
  (at level 5, y at next level, no associativity).
Uninterpreted Notation "x = y"
  (at level 5, no associativity).
Uninterpreted Notation "x = y = z"
  (at level 5, no associativity, y at next level).

Uninterpreted Notation "x <> y  :> T" 
  (at level 5, y at next level, no associativity).
Uninterpreted Notation "x <> y"
  (at level 5, no associativity).

Uninterpreted V8Notation "x <= y" (at level 70, no associativity).
Uninterpreted V8Notation "x < y" (at level 70, no associativity).
Uninterpreted V8Notation "x >= y" (at level 70, no associativity).
Uninterpreted V8Notation "x > y" (at level 70, no associativity).

Uninterpreted V8Notation "x <= y <= z" (at level 70, y at next level).
Uninterpreted V8Notation "x <= y < z"  (at level 70, y at next level).
Uninterpreted V8Notation "x < y < z"   (at level 70, y at next level).
Uninterpreted V8Notation "x < y <= z"  (at level 70, y at next level).

(** Arithmetical notations (also used for type constructors) *)

Uninterpreted Notation "x * y" (at level 3, right associativity)
  V8only (at level 40, left associativity).
Uninterpreted V8Notation "x / y" (at level 40, left associativity).
Uninterpreted Notation "x + y" (at level 4, left associativity).
Uninterpreted V8Notation "x - y" (at level 50, left associativity).
Uninterpreted V8Notation "- x" (at level 10, x at level 0).
Uninterpreted V8Notation "/ x" (at level 10, right associativity).

Uninterpreted V8Notation "x ^ y" (at level 30, left associativity).

(** Notations for pairs *)

Uninterpreted Notation "( x , y )" (at level 0)
  V8only "x , y" (at level 250, left associativity).

(** Notations for sum-types *)

(* Home-made factorization at level 4 to parse B+{x:A|P} without parentheses *)

Uninterpreted Notation "B + { x : A | P }"
  (at level 4, left associativity, only parsing)
  V8only (at level 50, x at level 99, left associativity, only parsing).

Uninterpreted Notation "B + { x : A | P & Q }"
  (at level 4, left associativity, only parsing)
  V8only (at level 50, x at level 99, left associativity, only parsing).

Uninterpreted Notation "B + { x : A & P }"
  (at level 4, left associativity, only parsing)
  V8only (at level 50, x at level 99, left associativity, only parsing).

Uninterpreted Notation "B + { x : A & P & Q }"
  (at level 4, left associativity, only parsing)
  V8only (at level 50, x at level 99, left associativity, only parsing).

(* At level 1 to factor with {x:A|P} etc *)

Uninterpreted Notation "{ A }  + { B }" (at level 1)
  V8only (at level 0, A at level 99).

Uninterpreted Notation "A + { B }" (at level 4, left associativity)
  V8only (at level 50, B at level 99, left associativity).

(** Notations for sigma-types or subsets *)

Uninterpreted Notation "{ x : A  |  P }" (at level 1)
  V8only (at level 0, x at level 99).
Uninterpreted Notation "{ x : A  |  P  &  Q }" (at level 1)
  V8only (at level 0, x at level 99).

Uninterpreted Notation "{ x : A  &  P }" (at level 1)
  V8only (at level 0, x at level 99).
Uninterpreted Notation "{ x : A  &  P  &  Q }" (at level 1)
  V8only (at level 0, x at level 99).

Delimits Scope type_scope with type.
Delimits Scope core_scope with core.

Open Scope core_scope.
Open Scope type_scope.

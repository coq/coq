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

Uninterpreted Notation "x /\ y" (at level 6, right associativity).
Uninterpreted Notation "x \/ y" (at level 7, right associativity).

Uninterpreted Notation "x <-> y" (at level 8, right associativity).

Uninterpreted Notation "~ x" (at level 5, right associativity)
  V8only (at level 55, right associativity).

(** Notations for equality and inequalities *)

Uninterpreted Notation "x = y  :> T" 
  (at level 5, y at next level, no associativity).
Uninterpreted Notation "x = y"
  (at level 5, no associativity).

Uninterpreted Notation "x <> y  :> T" 
  (at level 5, y at next level, no associativity).
Uninterpreted Notation "x <> y"
  (at level 5, no associativity).

Uninterpreted Notation "x <= y" (at level 5, no associativity).
Uninterpreted Notation "x < y" (at level 5, no associativity).
Uninterpreted Notation "x >= y" (at level 5, no associativity).
Uninterpreted Notation "x > y" (at level 5, no associativity).

(** Arithmetical notations (also used for type constructors) *)

Uninterpreted Notation "x * y" (at level 3, right associativity)
  V8only (at level 30, left associativity).
Uninterpreted Notation "x / y" (at level 3, left associativity).
Uninterpreted Notation "x + y" (at level 4, left associativity).
Uninterpreted Notation "x - y" (at level 4, left associativity).
Uninterpreted Notation "- x" (at level 0) V8only (at level 40).

(** Notations for pairs *)

Uninterpreted Notation "( x , y )" (at level 0)
  V8only "x , y" (at level 150, left associativity).

(** Notations for sum-types *)

(* Home-made factorization at level 4 to parse B+{x:A|P} without parentheses *)

Uninterpreted Notation "B + { x : A | P }"
  (at level 4, left associativity, only parsing)
  V8only (at level 40, x at level 80, left associativity, only parsing).

Uninterpreted Notation "B + { x : A | P & Q }"
  (at level 4, left associativity, only parsing)
  V8only (at level 40, x at level 80, left associativity, only parsing).

Uninterpreted Notation "B + { x : A & P }"
  (at level 4, left associativity, only parsing)
  V8only (at level 40, x at level 80, left associativity, only parsing).

Uninterpreted Notation "B + { x : A & P & Q }"
  (at level 4, left associativity, only parsing)
  V8only (at level 40, x at level 80, left associativity, only parsing).

(* At level 1 to factor with {x:A|P} etc *)

Uninterpreted Notation "{ A } + { B }" (at level 1)
  V8only (at level 10, A at level 80).

Uninterpreted Notation "A + { B }" (at level 4, left associativity)
  V8only (at level 40, B at level 80, left associativity).

(** Notations for sigma-types or subsets *)

Uninterpreted Notation "{ x : A  |  P }" (at level 1)
  V8only (at level 10, x at level 80).
Uninterpreted Notation "{ x : A  |  P  &  Q }" (at level 1)
  V8only (at level 10, x at level 80).

Uninterpreted Notation "{ x : A  &  P }" (at level 1)
  V8only (at level 10, x at level 80).
Uninterpreted Notation "{ x : A  &  P  &  Q }" (at level 1)
  V8only (at level 10, x at level 80).

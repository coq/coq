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

Reserved Notation "x <-> y" (at level 95, no associativity).
Reserved Notation "x /\ y" (at level 80, right associativity).
Reserved Notation "x \/ y" (at level 85, right associativity).
Reserved Notation "~ x" (at level 75, right associativity).

(** Notations for equality and inequalities *)

Reserved Notation "x = y  :> T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level).

Reserved Notation "x <> y  :> T"
(at level 70, y at next level, no associativity).
Reserved Notation "x <> y" (at level 70, no associativity).

Reserved Notation "x <= y" (at level 70, no associativity).
Reserved Notation "x < y" (at level 70, no associativity).
Reserved Notation "x >= y" (at level 70, no associativity).
Reserved Notation "x > y" (at level 70, no associativity).

Reserved Notation "x <= y <= z" (at level 70, y at next level).
Reserved Notation "x <= y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y <= z" (at level 70, y at next level).

(** Arithmetical notations (also used for type constructors) *)

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x - y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x / y" (at level 40, left associativity).
Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation "/ x" (at level 35, right associativity).
Reserved Notation "x ^ y" (at level 30, left associativity).

(** Notations for pairs *)

Reserved Notation "x , y" (at level 250, left associativity).

(** Notations for sum-types *)

(* Home-made factorization at level 4 to parse B+{x:A|P} without parentheses *)

Reserved Notation "B + { x : A | P }"
(at level 50, x at level 99, left associativity, only parsing).

Reserved Notation "B + { x : A | P & Q }"
(at level 50, x at level 99, left associativity, only parsing).

Reserved Notation "B + { x : A & P }"
(at level 50, x at level 99, left associativity, only parsing).

Reserved Notation "B + { x : A & P & Q }"
(at level 50, x at level 99, left associativity, only parsing).

(* At level 1 to factor with {x:A|P} etc *)

Reserved Notation "{ A }  + { B }" (at level 0, A at level 99).

Reserved Notation "A + { B }"
(at level 50, B at level 99, left associativity).

(** Notations for sigma-types or subsets *)

Reserved Notation "{ x : A  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  |  P  &  Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  &  P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  &  P  &  Q }" (at level 0, x at level 99).

Delimit Scope type_scope with type.
Delimit Scope core_scope with core.

Open Scope core_scope.
Open Scope type_scope.
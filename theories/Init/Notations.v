(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** These are the notations whose level and associativity are imposed by Rocq *)

(** Notations for propositional connectives *)

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x <-> y" (at level 95, no associativity).
Reserved Notation "x /\ y" (at level 80, right associativity).
Reserved Notation "x \/ y" (at level 85, right associativity).
Reserved Notation "~ x" (at level 75, right associativity).

(** Notations for equality and inequalities *)

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level).

Reserved Notation "x <> y  :>  T"
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
Reserved Notation "x ^ y" (at level 30, right associativity).

(** Notations for booleans *)

Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x && y" (at level 40, left associativity).

(** Notations for pairs *)

Reserved Notation "( x , y , .. , z )"
  (at level 0, format "( '[' x ,  '/' y ,  '/' .. ,  '/' z ']' )").

(** Notation "{ x }" is reserved and has a special status as component
    of other notations such as "{ A } + { B }" and "A + { B }" (which
    are at the same level as "x + y");
    "{ x }" is at level 0 to factor with "{ x : A | P }" *)

Reserved Notation "{ x }" (at level 0, x at level 99).

(** Notations for sigma-types or subsets *)

#[warning="-closed-notation-not-level-0"]
Reserved Notation "{ A }  +  { B }" (at level 50, left associativity).
#[warning="-postfix-notation-not-level-1"]
Reserved Notation "A  +  { B }" (at level 50, left associativity).

Reserved Notation "{ x | P }" (at level 0, x at level 99).
Reserved Notation "{ x | P & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A | P }" (at level 0, x at level 99).
Reserved Notation "{ x : A | P & Q }" (at level 0, x at level 99).

Reserved Notation "{ x & P }" (at level 0, x at level 99).
Reserved Notation "{ x & P & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A & P }" (at level 0, x at level 99).
Reserved Notation "{ x : A & P & Q }" (at level 0, x at level 99).

Reserved Notation "{ ' pat | P }"
  (at level 0, pat strict pattern, format "{ ' pat  |  P }").
Reserved Notation "{ ' pat | P & Q }"
  (at level 0, pat strict pattern, format "{ ' pat  |  P  &  Q }").

Reserved Notation "{ ' pat : A | P }"
  (at level 0, pat strict pattern, format "{ ' pat  :  A  |  P }").
Reserved Notation "{ ' pat : A | P & Q }"
  (at level 0, pat strict pattern, format "{ ' pat  :  A  |  P  &  Q }").

Reserved Notation "{ ' pat & P }"
  (at level 0, pat strict pattern, format "{ ' pat  &  P }").
Reserved Notation "{ ' pat & P & Q }"
  (at level 0, pat strict pattern, format "{ ' pat  &  P  &  Q }").

Reserved Notation "{ ' pat : A & P }"
  (at level 0, pat strict pattern, format "{ ' pat  :  A  &  P }").
Reserved Notation "{ ' pat : A & P & Q }"
  (at level 0, pat strict pattern, format "{ ' pat  :  A  &  P  &  Q }").

(** Support for Gonthier-Ssreflect's "if c is pat then u else v" *)

Module IfNotations.

Notation "'if' c 'is' p 'then' u 'else' v" :=
  (match c with p => u | _ => v end)
  (at level 200, p pattern at level 100).

End IfNotations.

(** Notations for first and second projections *)

Reserved Notation "p .1" (at level 1, left associativity, format "p .1").
Reserved Notation "p .2" (at level 1, left associativity, format "p .2").

(** Scopes *)

Declare Scope core_scope.
Delimit Scope core_scope with core.

Declare Scope function_scope.
Delimit Scope function_scope with function.
Bind Scope function_scope with Funclass.

Declare Scope type_scope.
Delimit Scope type_scope with type.
Bind Scope type_scope with Sortclass.

Open Scope core_scope.
Open Scope function_scope.
Open Scope type_scope.

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** These are the notations whose level and associativity are imposed by Coq *)

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

Reserved Notation "( x , y , .. , z )" (at level 0).

(** Notation "{ x }" is reserved and has a special status as component
    of other notations such as "{ A } + { B }" and "A + { B }" (which
    are at the same level as "x + y");
    "{ x }" is at level 0 to factor with "{ x : A | P }" *)

Reserved Notation "{ x }" (at level 0, x at level 99).

(** Notations for sigma-types or subsets *)

Reserved Notation "{ A }  + { B }" (at level 50, left associativity).
Reserved Notation "A + { B }" (at level 50, left associativity).

Reserved Notation "{ x  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x  &  P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  & P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  & P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ ' pat | P }"
  (at level 0, pat strict pattern, format "{ ' pat  |  P  }").
Reserved Notation "{ ' pat | P & Q }"
  (at level 0, pat strict pattern, format "{ ' pat  |  P  & Q }").

Reserved Notation "{ ' pat : A | P }"
  (at level 0, pat strict pattern, format "{ ' pat  :  A  |  P }").
Reserved Notation "{ ' pat : A | P & Q }"
  (at level 0, pat strict pattern, format "{ ' pat  :  A  |  P  & Q }").

Reserved Notation "{ ' pat : A & P }"
  (at level 0, pat strict pattern, format "{ ' pat  :  A  & P }").
Reserved Notation "{ ' pat : A & P & Q }"
  (at level 0, pat strict pattern, format "{ ' pat  :  A  & P  & Q }").

(** Support for Gonthier-Ssreflect's "if c is pat then u else v" *)

Module IfNotations.

Notation "'if' c 'is' p 'then' u 'else' v" :=
  (match c with p => u | _ => v end)
  (at level 200, p pattern at level 100).

End IfNotations.

(** Scopes *)

Delimit Scope type_scope with type.
Delimit Scope function_scope with function.
Delimit Scope core_scope with core.

Bind Scope type_scope with Sortclass.
Bind Scope function_scope with Funclass.

Open Scope core_scope.
Open Scope function_scope.
Open Scope type_scope.

(** ML Tactic Notations *)

Declare ML Module "ltac_plugin".

Global Set Default Proof Mode "Classic".

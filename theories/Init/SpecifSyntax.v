(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Datatypes.
Require Specif.

(** Extra factorization of parsing rules *)

(* Factorizing "sumor" at level 4 to parse B+{x:A|P} without parentheses *)

Notation "B + { x : A | P }"     := B + (sig A [x:A]P)
  (at level 4, left associativity, only parsing)
  V8only (at level 40, x at level 80, left associativity, only parsing).

Notation "B + { x : A | P & Q }" := B + (sig2 A [x:A]P [x:A]Q)
  (at level 4, left associativity, only parsing)
  V8only (at level 40, x at level 80, left associativity, only parsing).

Notation "B + { x : A & P }"     := B + (sigS A [x:A]P)
  (at level 4, left associativity, only parsing)
  V8only (at level 40, x at level 80, left associativity, only parsing).

Notation "B + { x : A & P & Q }" := B + (sigS2 A [x:A]P [x:A]Q)
  (at level 4, left associativity, only parsing)
  V8only (at level 40, x at level 80, left associativity, only parsing).

(** Symbolic notations for things in [Specif.v] *)

(* At level 1 to factor with {x:A|P} etc *)
Notation "{ A } + { B }" := (sumbool A B) (at level 1)
  V8only (at level 10, A at level 80).

Notation "A + { B }" := (sumor A B) (at level 4, left associativity)
  V8only (at level 40, B at level 80, left associativity).

Notation ProjS1 := (projS1 ? ?).
Notation ProjS2 := (projS2 ? ?).
Notation Except := (except ?).
Notation Error := (error ?).
Notation Value := (value ?).

Arguments Scope sig [type_scope type_scope].
Arguments Scope sig2 [type_scope type_scope type_scope].

Notation "{ x : A  |  P }"       := (sig A [x:A]P)          (at level 1)
  V8only (at level 10, x at level 80).
Notation "{ x : A  |  P  &  Q }" := (sig2 A [x:A]P [x:A]Q)  (at level 1)
  V8only (at level 10, x at level 80).

Arguments Scope sigS [type_scope type_scope].
Arguments Scope sigS2 [type_scope type_scope type_scope].

Notation "{ x : A  &  P }"       := (sigS A [x:A]P)         (at level 1)
  V8only (at level 10, x at level 80).
Notation "{ x : A  &  P  &  Q }" := (sigS2 A [x:A]P [x:A]Q) (at level 1)
  V8only (at level 10, x at level 80).

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require DatatypesSyntax.
Require Specif.

(** Symbolic notations for things in [Specif.v] *)

(* At level 1 to factor with {x:A|P} etc *)
Notation "{ A } + { B }" := (sumbool A B)
  (at level 1, A at level 10, B at level 10).

Notation "A + { B }" := (sumor A B)
  (at level 4, B at level 10, left associativity).

Notation ProjS1 := (projS1 ? ?).
Notation ProjS2 := (projS2 ? ?).
Notation Except := (except ?).
Notation Error := (error ?).
Notation Value := (value ?).

Notation "{ x : A  |  P }"       := (sig A [x:A]P)
  (at level 1, x at level 10).

Notation "{ x : A  |  P  &  Q }" := (sig2 A [x:A]P [x:A]Q)
  (at level 1, x at level 10).

Notation "{ x : A  &  P }"       := (sigS A [x:A]P)
  (at level 1, x at level 10).

Notation "{ x : A  &  P  &  Q }" := (sigS2 A [x:A]P [x:A]Q)
  (at level 1, x at level 10).

(** Extra factorization of parsing rules *)

(* Factorizing "sumor" at level 4 to parse B+{x:A|P} without parentheses *)

Notation "B + { x : A | P }"     := B + ({x:A | P})
  (at level 4, x at level 10, left associativity, only parsing).

Notation "B + { x : A | P & Q }" := B + ({x:A | P & Q})
  (at level 4, x at level 10, left associativity, only parsing).

Notation "B + { x : A & P }"     := B + ({x:A & P})
  (at level 4, x at level 10, left associativity, only parsing).

Notation "B + { x : A & P & Q }" := B + ({x:A & P & Q})
  (at level 4, x at level 10, left associativity, only parsing).


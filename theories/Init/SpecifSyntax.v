(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Notations.
Require Datatypes.
Require Specif.

(** Extra factorization of parsing rules *)

(* Factorizing "sumor" at level 4 to parse B+{x:A|P} without parentheses *)

Notation "B + { x : A | P }"     := B + (sig A [x:A]P) (only parsing).
Notation "B + { x : A | P & Q }" := B + (sig2 A [x:A]P [x:A]Q) (only parsing).
Notation "B + { x : A & P }"     := B + (sigS A [x:A]P) (only parsing).
Notation "B + { x : A & P & Q }" := B + (sigS2 A [x:A]P [x:A]Q) (only parsing).

(** Symbolic notations for definitions in [Specif.v] *)

(*
Notation "{ A } + { B }" := (sumbool A B).
Notation "A + { B }" := (sumor A B).
*)

V7only [
Notation ProjS1 := (projS1 ? ?).
Notation ProjS2 := (projS2 ? ?).
Notation Value := (value ?).
].

Notation Except := (except ?).
Notation Error := (error ?).

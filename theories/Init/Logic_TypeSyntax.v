(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Logic_Type.

(** Symbolic notations for things in [Logic_type.v] *)

Notation "x == y"  := (eq ? x y) (at level 5, no associativity, only parsing).
Notation "x === y" := (identityT ? x y) (at level 5, no associativity).

(* Order is important to give printing priority to fully typed ALL and EX *)

Notation AllT := (all ?).
Notation "'ALLT' x | p"     := (all ? [x]p)   (at level 10, p at level 8)
  V8only (at level 200, x at level 80).
Notation "'ALLT' x : t | p" := (all t [x:t]p) (at level 10, p at level 8)
  V8only (at level 200, x at level 80).

Notation ExT  := (ex ?).
Notation "'EXT' x | p"      := (ex ? [x]p)    (at level 10, p at level 8)
  V8only (at level 200, x at level 80).
Notation "'EXT' x : t | p"  := (ex t [x:t]p)  (at level 10, p at level 8)
  V8only (at level 200, x at level 80).

Notation ExT2 := (ex2 ?).
Notation "'EXT' x | p & q"     := (ex2 ? [x]p [x]q)
  (at level 10, p, q at level 8)
  V8only "'EXT2' x | p & q" (at level 200, x at level 80).
Notation "'EXT' x : t | p & q" := (ex2 t [x:t]p [x:t]q)
  (at level 10, p, q at level 8)
  V8only "'EXT2' x : t | p & q" (at level 200, x at level 80).

(** Parsing only of things in [Logic_type.v] *)

V7only[
Notation "< A > x == y"  := (eq A x y)
   (A annot, at level 1, x at level 0, only parsing).

Notation "< A > x === y" := (identityT A x y)
   (A annot, at level 1, x at level 0, only parsing).
].

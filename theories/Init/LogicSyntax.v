(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Export Notations.
Require Export Logic.

(** Symbolic notations for things in [Logic.v] *)

(* Order is important to give printing priority to fully typed ALL and
   exists *)

V7only [ Notation All := (all ?). ].
Notation "'ALL' x | p"     := (all ? [x]p)   (at level 10, p at level 8)
  V8only "'ALL' x , p" (at level 200, p at level 200).
Notation "'ALL' x : t | p" := (all ? [x:t]p) (at level 10, p at level 8)
  V8only "'ALL' x : t , p" (at level 200).

V7only [ Notation Ex  := (ex ?). ].
Notation "'EX' x | p"      := (ex ? [x]p)    (at level 10, p at level 8)
  V8only "'exists' x , p" (at level 200, x at level 99).
Notation "'EX' x : t | p"  := (ex ? [x:t]p)  (at level 10, p at level 8)
  V8only "'exists' x : t , p" (at level 200, x at level 99).

V7only [ Notation Ex2 := (ex2 ?). ].
Notation "'EX' x | p & q"       := (ex2 ? [x]p [x]q)
  (at level 10, p, q at level 8)
  V8only "'exists2' x , p & q" (at level 200, x at level 99).
Notation "'EX' x : t | p & q"   := (ex2 ? [x:t]p [x:t]q)
  (at level 10, p, q at level 8)
  V8only "'exists2' x : t , p & q" (at level 200, x at level 99).

V7only[
(** Parsing only of things in [Logic.v] *)

Notation "< A > 'All' ( P )" := (all A P) (A annot, at level 1, only parsing).
Notation "< A > x = y" := (eq A x y)
  (A annot, at level 1, x at level 0, only parsing).
Notation "< A > x <> y" := ~(eq A x y)
  (A annot, at level 1, x at level 0, only parsing).
].

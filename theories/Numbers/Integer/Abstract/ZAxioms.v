(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export NZAxioms.

Set Implicit Arguments.

Module Type ZAxiomsSig.
Declare Module Export NZOrdAxiomsMod : NZOrdAxiomsSig.

Delimit Scope IntScope with Int.
Notation Z := NZ.
Notation Zeq := NZeq.
Notation Z0 := NZ0.
Notation Z1 := (NZsucc NZ0).
Notation S := NZsucc.
Notation P := NZpred.
Notation Zplus := NZplus.
Notation Ztimes := NZtimes.
Notation Zminus := NZminus.
Notation Zlt := NZlt.
Notation Zle := NZle.
Notation Zmin := NZmin.
Notation Zmax := NZmax.
Notation "x == y"  := (NZeq x y) (at level 70) : IntScope.
Notation "x ~= y" := (~ NZeq x y) (at level 70) : IntScope.
Notation "0" := NZ0 : IntScope.
Notation "1" := (NZsucc NZ0) : IntScope.
Notation "x + y" := (NZplus x y) : IntScope.
Notation "x - y" := (NZminus x y) : IntScope.
Notation "x * y" := (NZtimes x y) : IntScope.
Notation "x < y" := (NZlt x y) : IntScope.
Notation "x <= y" := (NZle x y) : IntScope.
Notation "x > y" := (NZlt y x) (only parsing) : IntScope.
Notation "x >= y" := (NZle y x) (only parsing) : IntScope.

Parameter Zopp : Z -> Z.

(*Notation "- 1" := (Zopp 1) : IntScope.
Check (-1).*)

Add Morphism Zopp with signature Zeq ==> Zeq as Zopp_wd.

Notation "- x" := (Zopp x) (at level 35, right associativity) : IntScope.
Notation "- 1" := (Zopp (NZsucc NZ0)) : IntScope.

Open Local Scope IntScope.

(* Integers are obtained by postulating that every number has a predecessor *)
Axiom Zsucc_pred : forall n : Z, S (P n) == n.

Axiom Zopp_0 : - 0 == 0.
Axiom Zopp_succ : forall n : Z, - (S n) == P (- n).

End ZAxiomsSig.


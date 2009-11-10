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
Include Type NZOrdAxiomsSig.
Local Open Scope NumScope.

Parameter Inline opp : t -> t.
Instance opp_wd : Proper (eq==>eq) opp.

Notation "- x" := (opp x) (at level 35, right associativity) : NumScope.
Notation "- 1" := (- (1)) : NumScope.

(* Integers are obtained by postulating that every number has a predecessor *)

Axiom succ_pred : forall n, S (P n) == n.

Axiom opp_0 : - 0 == 0.
Axiom opp_succ : forall n, - (S n) == P (- n).

End ZAxiomsSig.


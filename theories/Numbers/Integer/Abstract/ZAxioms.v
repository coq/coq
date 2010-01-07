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

Module Type Opp (Import T:Typ).
 Parameter Inline opp : t -> t.
End Opp.

Module Type OppNotation (T:Typ)(Import O : Opp T).
 Notation "- x" := (opp x) (at level 35, right associativity).
End OppNotation.

Module Type Opp' (T:Typ) := Opp T <+ OppNotation T.

(** We obtain integers by postulating that every number has a predecessor. *)

Module Type IsOpp (Import Z : NZAxiomsSig')(Import O : Opp' Z).
 Declare Instance opp_wd : Proper (eq==>eq) opp.
 Axiom succ_pred : forall n, S (P n) == n.
 Axiom opp_0 : - 0 == 0.
 Axiom opp_succ : forall n, - (S n) == P (- n).
End IsOpp.

Module Type ZAxiomsSig := NZOrdAxiomsSig <+ Opp <+ IsOpp.
Module Type ZAxiomsSig' := NZOrdAxiomsSig' <+ Opp' <+ IsOpp.


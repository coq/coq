(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(* The main tactic: takes a name N, a program P, creates a goal
 * of name N with the functional specification of P, then apply the Refine
 * tactic with the partial proof term obtained by the translation of
 * P into a functional program.
 *
 * Then an ad-hoc automatic tactic is applied on each subgoal to solve the
 * trivial proof obligations *)

val correctness : string -> Past.program -> Tacmach.tactic option -> unit


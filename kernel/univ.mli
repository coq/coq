(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Universes. *)

type universe

val prop_univ : universe
val make_univ : Names.dir_path * int -> universe

(* The type of a universe *)
val super : universe -> universe
(* The max of 2 universes *)
val sup   : universe -> universe -> universe

(*s Graphs of universes. *)

type universes

(* The empty graph of universes *)
val initial_universes : universes

(*s Constraints. *)

module Constraint : Set.S

type constraints = Constraint.t

type constraint_function = universe -> universe -> constraints -> constraints

val enforce_geq : constraint_function
val enforce_eq : constraint_function

(*s Merge of constraints in a universes graph. 
  The function [merge_constraints] merges a set of constraints in a given
  universes graph. It raises the exception [UniverseInconsistency] if the
  constraints are not satisfiable. *)

exception UniverseInconsistency

val merge_constraints : constraints -> universes -> universes

(*s Pretty-printing of universes. *)

val pr_uni : universe -> Pp.std_ppcmds
val pr_universes : universes -> Pp.std_ppcmds

val string_of_univ : universe -> string

(*s Dumping to a file *)

val dump_universes : out_channel -> universes -> unit

val hcons1_univ : universe -> universe

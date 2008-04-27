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

val type0_univ : universe  (* predicative Set seen as a universe *)
val type1_univ : universe  (* the universe of the type of Prop/Set *)
val lower_univ : universe  (* image of Prop in the predicative hierarchy *)
val make_univ : Names.dir_path * int -> universe

val is_type0_univ : universe -> bool
val is_lower_univ : universe -> bool
val is_univ_variable : universe -> bool

(* The type of a universe *)
val super : universe -> universe

(* The max of 2 universes *)
val sup   : universe -> universe -> universe

(*s Graphs of universes. *)

type universes

type check_function = universes -> universe -> universe -> bool
val check_geq : check_function
val check_eq : check_function

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

type order_request = Lt | Le | Eq

exception UniverseInconsistency of order_request * universe * universe

val merge_constraints : constraints -> universes -> universes

(*s Support for sort-polymorphic inductive types *)

val fresh_local_univ : unit -> universe

val solve_constraints_system : universe option array -> universe array -> 
  universe array

val subst_large_constraint : universe -> universe -> universe -> universe

val subst_large_constraints : 
  (universe * universe) list -> universe -> universe

(*s Pretty-printing of universes. *)

val pr_uni : universe -> Pp.std_ppcmds
val pr_universes : universes -> Pp.std_ppcmds

(*s Dumping to a file *)

val dump_universes : out_channel -> universes -> unit

val hcons1_univ : universe -> universe

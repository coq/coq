(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
(*i*)

(* Universes. *)

type universe

val dummy_univ : universe
val implicit_univ : universe

val prop_univ : universe
val prop_univ_univ : universe

val set_module : module_path -> unit

(* [with_module mp f x] changes the module to [mp] during the 
   application [f x] and restores the old [module] afterwards *)
val with_module : module_path -> ('a -> 'b) -> 'a -> 'b

val new_univ : unit -> universe

(*s Graphs of universes. *)

type universes

val initial_universes : universes

(*s Constraints. *)

type constraint_type = Gt | Geq | Eq

type univ_constraint = universe * constraint_type * universe

module Constraint : Set.S with type elt = univ_constraint

type constraints = Constraint.t

type constraint_function = universe -> universe -> constraints -> constraints

val enforce_gt : constraint_function
val enforce_geq : constraint_function
val enforce_eq : constraint_function

val super : universe -> universe * constraints

val sup : universe -> universe -> universes -> universe * constraints

(*s Merge of constraints in a universes graph. 
  The function [merge_constraints] merges a set of constraints in a given
  universes graph. It raises the exception [UniverseInconsistency] if the
  constraints are not satisfiable. *)

exception UniverseInconsistency

val merge_constraints : 
  constraints -> universes -> universes

(* [merge_module_constraints mp c g] merges the constraints in c
   verifying  if they did not impose new conditions on old universes *)
val merge_module_constraints : 
  module_path -> constraints -> universes -> universes


(*s Pretty-printing of universes. *)

val pr_uni : universe -> Pp.std_ppcmds
val pr_universes : universes -> Pp.std_ppcmds

val string_of_univ : universe -> string

(*s Dumping to a file *)

val dump_universes : out_channel -> universes -> unit

val hcons1_univ : universe -> universe

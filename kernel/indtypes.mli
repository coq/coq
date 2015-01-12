(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Declarations
open Environ
open Entries

(** Inductive type checking and errors *)

(** The different kinds of errors that may result of a malformed inductive
  definition. *)

(** Errors related to inductive constructions *)
type inductive_error =
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * Id.t * constr * constr * int * int
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of Id.t
  | SameNamesConstructors of Id.t
  | SameNamesOverlap of Id.t list
  | NotAnArity of env * constr
  | BadEntry
  | LargeNonPropInductiveNotInType

exception InductiveError of inductive_error

(** The following function does checks on inductive declarations. *)

val check_inductive : env -> mutual_inductive -> mutual_inductive_entry -> mutual_inductive_body

(** The following enforces a system compatible with the univalent model *)

val enforce_indices_matter : unit -> unit
val is_indices_matter : unit -> bool

val compute_projections : pinductive -> Id.t -> Id.t ->
  int -> Context.rel_context -> int array -> int array -> 
  Context.rel_context -> 
  (constant array * projection_body array)

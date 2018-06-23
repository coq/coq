(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
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

val check_inductive : env -> MutInd.t -> mutual_inductive_entry -> mutual_inductive_body

(** The following enforces a system compatible with the univalent model *)

val enforce_indices_matter : unit -> unit
val is_indices_matter : unit -> bool

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Univ
open Term
open Declarations
open Environ
open Entries
open Typeops

(** Inductive type checking and errors *)

(** The different kinds of errors that may result of a malformed inductive
  definition. *)

(** Errors related to inductive constructions *)
type inductive_error =
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * identifier * constr * constr * int * int
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier
  | SameNamesOverlap of identifier list
  | NotAnArity of identifier
  | BadEntry
  | LargeNonPropInductiveNotInType

exception InductiveError of inductive_error

(** The following function does checks on inductive declarations. *)

val check_inductive :
  env -> mutual_inductive -> mutual_inductive_entry -> mutual_inductive_body

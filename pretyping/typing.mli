(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ
open Evd

(** This module provides the typing machine with existential variables
    and universes. *)

(** Typecheck a term and return its type *)
val type_of : env -> evar_map -> constr -> types

(** Typecheck a term and return its type + updated evars, optionally refreshing
    universes *)
val e_type_of : ?refresh:bool -> env -> evar_map -> constr -> evar_map * types

(** Typecheck a type and return its sort *)
val sort_of : env -> evar_map ref -> types -> sorts

(** Typecheck a term has a given type (assuming the type is OK) *)
val check   : env -> evar_map ref -> constr -> types -> unit

(** Returns the instantiated type of a metavariable *)
val meta_type : evar_map -> metavariable -> types

(** Solve existential variables using typing *)
val solve_evars : env -> evar_map ref -> constr -> constr

(** Raise an error message if incorrect elimination for this inductive *)
(** (first constr is term to match, second is return predicate) *)
val check_allowed_sort : env -> evar_map -> pinductive -> constr -> constr ->
  unit

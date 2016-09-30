(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Environ
open Evd

(** This module provides the typing machine with existential variables
    and universes. *)

(** Typecheck a term and return its type. May trigger an evarmap leak. *)
val unsafe_type_of : env -> evar_map -> constr -> types

(** Typecheck a term and return its type + updated evars, optionally refreshing
    universes *)
val type_of : ?refresh:bool -> env -> evar_map -> constr -> evar_map * types

(** Variant of [type_of] using references instead of state-passing. *)
val e_type_of : ?refresh:bool -> env -> evar_map ref -> constr -> types

(** Typecheck a type and return its sort *)
val e_sort_of : env -> evar_map ref -> types -> sorts

(** Typecheck a term has a given type (assuming the type is OK) *)
val e_check   : env -> evar_map ref -> constr -> types -> unit

(** Returns the instantiated type of a metavariable *)
val meta_type : evar_map -> metavariable -> types

(** Solve existential variables using typing *)
val e_solve_evars : env -> evar_map ref -> constr -> constr

(** Raise an error message if incorrect elimination for this inductive *)
(** (first constr is term to match, second is return predicate) *)
val check_allowed_sort : env -> evar_map -> pinductive -> constr -> constr ->
  unit

(** Raise an error message if bodies have types not unifiable with the
    expected ones *)
val check_type_fixpoint : Loc.t -> env -> evar_map ref ->
  Names.Name.t array -> types array -> unsafe_judgment array -> unit

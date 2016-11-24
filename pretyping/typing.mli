(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
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

(** Typecheck a term and return its type. May trigger an evarmap leak. *)
val unsafe_type_of : env -> evar_map -> EConstr.constr -> types

(** Typecheck a term and return its type + updated evars, optionally refreshing
    universes *)
val type_of : ?refresh:bool -> env -> evar_map -> EConstr.constr -> evar_map * EConstr.types

(** Variant of [type_of] using references instead of state-passing. *)
val e_type_of : ?refresh:bool -> env -> evar_map ref -> EConstr.constr -> EConstr.types

(** Typecheck a type and return its sort *)
val e_sort_of : env -> evar_map ref -> EConstr.types -> sorts

(** Typecheck a term has a given type (assuming the type is OK) *)
val e_check   : env -> evar_map ref -> EConstr.constr -> EConstr.types -> unit

(** Returns the instantiated type of a metavariable *)
val meta_type : evar_map -> metavariable -> EConstr.types

(** Solve existential variables using typing *)
val e_solve_evars : env -> evar_map ref -> EConstr.constr -> constr

(** Raise an error message if incorrect elimination for this inductive *)
(** (first constr is term to match, second is return predicate) *)
val check_allowed_sort : env -> evar_map -> pinductive -> EConstr.constr -> EConstr.constr ->
  unit

(** Raise an error message if bodies have types not unifiable with the
    expected ones *)
val check_type_fixpoint : Loc.t -> env -> evar_map ref ->
  Names.Name.t array -> EConstr.types array -> EConstr.unsafe_judgment array -> unit

val judge_of_prop : EConstr.unsafe_judgment
val judge_of_set : EConstr.unsafe_judgment
val judge_of_abstraction : Environ.env -> Name.t ->
  EConstr.unsafe_type_judgment -> EConstr.unsafe_judgment -> EConstr.unsafe_judgment
val judge_of_product : Environ.env -> Name.t ->
  EConstr.unsafe_type_judgment -> EConstr.unsafe_type_judgment -> EConstr.unsafe_judgment

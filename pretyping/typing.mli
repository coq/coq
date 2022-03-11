(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open EConstr
open Evd

(** This module provides the typing machine with existential variables
    and universes. *)

(** Typecheck a term and return its type + updated evars, optionally refreshing
    universes *)
val type_of : ?refresh:bool -> env -> evar_map -> constr -> evar_map * types

(** Typecheck a type and return its sort *)
val sort_of : env -> evar_map -> types -> evar_map * Sorts.t

(** Typecheck a term has a given type (assuming the type is OK) *)
val check : env -> evar_map -> constr -> types -> evar_map

(** Type of a variable. *)
val type_of_variable : env -> variable -> types

(** Returns the instantiated type of a metavariable *)
val meta_type : env -> evar_map -> metavariable -> types

(** Solve existential variables using typing *)
val solve_evars : env -> evar_map -> constr -> evar_map * constr

(** Raise an error message if incorrect elimination for this inductive
    (first constr is term to match, second is return predicate) *)
val check_allowed_sort : env -> evar_map -> pinductive -> constr -> constr ->
  Sorts.relevance

(** Raise an error message if bodies have types not unifiable with the
    expected ones *)
val check_type_fixpoint : ?loc:Loc.t -> env -> evar_map ->
  Names.Name.t Context.binder_annot array -> types array -> unsafe_judgment array -> evar_map

(** Variant of {!check} that assumes that the argument term is well-typed. *)
val check_actual_type : env -> evar_map -> unsafe_judgment -> types -> evar_map

val judge_of_sprop : unsafe_judgment
val judge_of_prop : unsafe_judgment
val judge_of_set : unsafe_judgment
val judge_of_apply : env -> evar_map -> unsafe_judgment -> unsafe_judgment array ->
  evar_map * unsafe_judgment
val judge_of_abstraction : Environ.env -> Name.t ->
  unsafe_type_judgment -> unsafe_judgment -> unsafe_judgment
val judge_of_product : Environ.env -> Name.t ->
  unsafe_type_judgment -> unsafe_type_judgment -> unsafe_judgment
val judge_of_projection : env -> evar_map -> Projection.t -> unsafe_judgment -> unsafe_judgment
val judge_of_int : Environ.env -> Uint63.t -> unsafe_judgment
val judge_of_float : Environ.env -> Float64.t -> unsafe_judgment

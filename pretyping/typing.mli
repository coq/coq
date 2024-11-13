(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Environ
open EConstr
open Evd

(** This module provides the typing machine with existential variables
    and universes. *)

(** Typecheck a term and return its type + updated evars, optionally refreshing
    universes *)
val type_of : ?refresh:bool -> env -> evar_map -> constr -> evar_map * types

(** Typecheck a type and return its sort *)
val sort_of : env -> evar_map -> types -> evar_map * ESorts.t

(** Typecheck a term has a given type (assuming the type is OK) *)
val check : env -> evar_map -> constr -> types -> evar_map

(** Type of a variable. *)
val type_of_variable : env -> variable -> types

(** Solve existential variables using typing *)
val solve_evars : env -> evar_map -> constr -> evar_map * constr

(** Raise an error message if incorrect elimination for this inductive
    (first constr is term to match, second is return predicate) *)
val check_allowed_sort : env -> evar_map -> inductive puniverses -> constr -> constr ->
  evar_map * ERelevance.t

(** Raise an error message if bodies have types not unifiable with the
    expected ones *)
val check_type_fixpoint : ?loc:Loc.t -> env -> evar_map ->
  Names.Name.t EConstr.binder_annot array -> types array -> unsafe_judgment array -> evar_map

(** Variant of {!check} that assumes that the argument term is well-typed. *)
val check_actual_type : env -> evar_map -> unsafe_judgment -> types -> evar_map

val type_judgment : env -> evar_map -> unsafe_judgment -> evar_map * unsafe_type_judgment

val judge_of_sprop : unsafe_judgment
val judge_of_prop : unsafe_judgment
val judge_of_set : unsafe_judgment
val judge_of_variable : env -> Id.t -> unsafe_judgment
val judge_of_apply : env -> evar_map -> unsafe_judgment -> unsafe_judgment array ->
  evar_map * unsafe_judgment
val judge_of_abstraction : Environ.env -> evar_map -> Name.t ->
  unsafe_type_judgment -> unsafe_judgment -> unsafe_judgment
val judge_of_product : Environ.env -> evar_map -> Name.t ->
  unsafe_type_judgment -> unsafe_type_judgment -> unsafe_judgment
val judge_of_projection : env -> evar_map -> Projection.t -> unsafe_judgment -> unsafe_judgment
val judge_of_int : Environ.env -> Uint63.t -> unsafe_judgment
val judge_of_float : Environ.env -> Float64.t -> unsafe_judgment
val judge_of_string : Environ.env -> Pstring.t -> unsafe_judgment

val checked_appvect : env -> evar_map -> constr -> constr array -> evar_map * constr
val checked_applist : env -> evar_map -> constr -> constr list -> evar_map * constr

(** hack *)
val recheck_against : Environ.env -> evar_map -> constr -> constr -> evar_map * types

type ('constr,'types,'r) bad_relevance =
| BadRelevanceBinder of 'r * ('constr,'types,'r) Context.Rel.Declaration.pt
| BadRelevanceCase of 'r * 'constr

val bad_relevance_msg : (Environ.env * evar_map * (constr, types, ERelevance.t) bad_relevance) CWarnings.msg

(** Template typing *)

val get_template_parameters : env -> evar_map -> inductive -> unsafe_judgment array -> evar_map * Inductive.param_univs

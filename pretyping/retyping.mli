(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Evd
open Environ
open EConstr

(** This family of functions assumes its constr argument is known to be
   well-typable. It does not type-check, just recompute the type
   without any costly verifications. On non well-typable terms, it
   either produces a wrong result or raise an anomaly. Use with care.
   It doesn't handle predicative universes too. *)

(** The "polyprop" optional argument is used by the extraction to
    disable "Prop-polymorphism" *)

(** The "lax" optional argument provides a relaxed version of
    [get_type_of] that won't raise any anomaly but RetypeError instead *)

type retype_error
exception RetypeError of retype_error

val get_type_of :
  ?metas:(Constr.metavariable -> types option) ->
  ?polyprop:bool -> ?lax:bool -> env -> evar_map -> constr -> types

(** No-evar version of [get_type_of] *)
val get_type_of_constr : ?polyprop:bool -> ?lax:bool
  -> env -> ?uctx:UState.t -> Constr.t -> Constr.types

val get_sort_of :
  ?polyprop:bool -> env -> evar_map -> types -> ESorts.t

val get_sort_family_of :
  ?polyprop:bool -> env -> evar_map -> types -> Sorts.family

(** Makes an unsafe judgment from a constr *)
val get_judgment_of : env -> evar_map -> constr -> unsafe_judgment

val type_of_global_reference_knowing_parameters : env -> evar_map -> constr ->
  constr array -> types

val sorts_of_context : env -> evar_map -> rel_context -> ESorts.t list

val expand_projection : env -> evar_map -> Names.Projection.t -> constr -> constr list -> constr

val reinterpret_get_type_of : src:Names.Id.t -> env -> evar_map -> constr -> types

val print_retype_error : retype_error -> Pp.t

val relevance_of_projection_repr : env -> Names.Projection.Repr.t EConstr.puniverses -> ERelevance.t

val relevance_of_term : env -> evar_map -> constr -> ERelevance.t
val relevance_of_type : env -> evar_map -> types -> ERelevance.t
val relevance_of_sort : ESorts.t -> ERelevance.t
val relevance_of_sort_family : evar_map -> Sorts.family -> ERelevance.t

val is_term_irrelevant : env -> Evd.evar_map -> Evd.econstr -> bool

(** The "polyprop" optional argument above controls
    the "Prop-polymorphism". By default, it is allowed.
    But when "polyprop=false", the following exception is raised
    when a polymorphic singleton inductive type becomes Prop due to
    parameter instantiation. This is used by the Ocaml extraction,
    which cannot handle (yet?) Prop-polymorphism. *)

exception SingletonInductiveBecomesProp of Names.inductive

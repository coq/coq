(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
    disable "Prop-polymorphism", cf comment in [inductive.ml] *)

(** The "lax" optional argument provides a relaxed version of
    [get_type_of] that won't raise any anomaly but RetypeError instead *)

type retype_error
exception RetypeError of retype_error

val get_type_of :
  ?polyprop:bool -> ?lax:bool -> env -> evar_map -> constr -> types

val get_sort_of :
  ?polyprop:bool -> env -> evar_map -> types -> Sorts.t

(* When [truncation_style] is [true], tells if the type has been explicitly
   truncated to Prop or (impredicative) Set; in particular, singleton type and
   small inductive types, which have all eliminations to Type, are in Type *)
val get_sort_family_of :
  ?truncation_style:bool -> ?polyprop:bool -> env -> evar_map -> types -> Sorts.family

(** Makes an unsafe judgment from a constr *)
val get_judgment_of : env -> evar_map -> constr -> unsafe_judgment

val type_of_global_reference_knowing_parameters : env -> evar_map -> constr ->
  constr array -> types

val type_of_global_reference_knowing_conclusion :
  env -> evar_map -> constr -> types -> evar_map * types

val sorts_of_context : env -> evar_map -> rel_context -> Sorts.t list

val expand_projection : env -> evar_map -> Names.Projection.t -> constr -> constr list -> constr

val print_retype_error : retype_error -> Pp.t

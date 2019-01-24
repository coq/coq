(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Evd
open Environ

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

module type S = sig
  (** Retyping operations apply as well on constr and econstr, so we
      use a parameterized module type. *)

  type constr
  type types

  type 'a in_env
  (** On Constr we only take an environment, on EConstr we also take an evar map. *)

  val get_type_of :
    ?polyprop:bool -> ?lax:bool -> (constr -> types) in_env

  val get_sort_of :
    ?polyprop:bool -> (types -> Sorts.t) in_env

  (* When [truncation_style] is [true], tells if the type has been explicitly
     truncated to Prop or (impredicative) Set; in particular, singleton type and
     small inductive types, which have all eliminations to Type, are in Type. *)
  val get_sort_family_of :
    ?truncation_style:bool -> ?polyprop:bool -> (types -> Sorts.family) in_env

  (** Makes an unsafe judgment from a constr. *)
  val get_judgment_of : (constr -> (constr,types) Environ.punsafe_judgment) in_env

  val type_of_global_reference_knowing_parameters : (constr -> constr array -> types) in_env

  val sorts_of_context : ((constr,types) Context.Rel.pt -> Sorts.t list) in_env

  val expand_projection : (Names.Projection.t -> constr -> constr list -> constr) in_env

end

(** Functions in Retyping operate on EConstr. *)
include S with type constr := EConstr.constr
           and type types := EConstr.types
           and type 'a in_env = env -> evar_map -> 'a
(* NB: can't use := for in_env until ocaml 4.06 (see https://github.com/ocaml/ocaml/pull/792) *)

val type_of_global_reference_knowing_conclusion :
  env -> evar_map -> EConstr.constr -> EConstr.types -> evar_map * EConstr.types
(** This modifies the evar map so there is no Constr version. *)

(** Functions in Retyping.C operate on Constr. *)
module C : S with type constr := Constr.t
              and type types := Constr.types
              and type 'a in_env = env -> 'a

val print_retype_error : retype_error -> Pp.t

(** Use Retypeops for relevance operations on Constr *)
val relevance_of_term : env -> evar_map -> EConstr.constr -> Sorts.relevance
val relevance_of_type : env -> evar_map -> EConstr.types -> Sorts.relevance
val relevance_of_sort : EConstr.ESorts.t -> Sorts.relevance
val relevance_of_sort_family : Sorts.family -> Sorts.relevance

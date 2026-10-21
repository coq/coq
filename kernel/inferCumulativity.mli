(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open UVars

type mode = Check | Infer

(** [Infer <= Check] orderring *)
val mode_sup : mode -> mode -> mode

(** Not the same as Type_errors.BadVariance because we don't have the env where we raise. *)
exception BadVariance of Level.t * VariancePos.t * VariancePos.t

type infer_binders = (mode * (VariancePair.t option * int list))

type infer_variance_occurrence =
  { infer_binders : infer_binders;
    infer_topfix_binders : infer_binders;
    infer_term : mode * VariancePair.t option;
    infer_type : mode * VariancePair.t option;
    infer_under_impred_qvars : impred_qvars }

val default_occ : infer_variance_occurrence
val make_checked_occ : VariancePos.t -> infer_variance_occurrence

val sup_occs : infer_variance_occurrence -> infer_variance_occurrence -> infer_variance_occurrence

val occurrence_to_variance_pos : infer_variance_occurrence -> mode * VariancePos.t

type pre_variances = (Univ.Level.t * VarianceOccurrence.t option) array

type infer_variance_occurrences = infer_variance_occurrence array

val pr_variance_occurrence : infer_variance_occurrence -> Pp.t

val forget_infer_variance_occurrence : infer_variance_occurrence -> VarianceOccurrence.t

(* The position records the last position in the term where the variable was used relevantly. *)

type variances = infer_variance_occurrence Univ.Level.Map.t

val empty_variances : variances
val is_empty_variances : variances -> bool

val pr_variances : (Univ.Level.t -> Pp.t) -> variances -> Pp.t

val union_variances : variances -> variances -> variances

(* Compute the variance in the binders and term and separately, the variance in the type.
   The last variance represents the supremum of the variances associated to each occurrence
   of the level within the term, useful for determining if a level can be minimized without
  affecting the principal type of the subexpressions. *)
val term_type_variances : infer_variance_occurrence ->
    Variance.t option * Variance.t option * Variance.t option

val of_variance_occurrences : infer_in_type:bool -> pre_variances -> variances

module Inf : sig
  type status

  val pr : (Level.t -> Pp.t) -> status -> Pp.t

  val get_infer_mode : status -> bool
  val set_infer_mode : bool -> status -> status

  val set_position : Position.t -> status -> status

  val start : infer_in_type:bool -> pre_variances -> Position.t -> status
  val start_inference : Level.Set.t -> Position.t -> status
  val start_variances : variances -> Position.t -> status

  val inferred : status -> variances
  val finish : Environ.env -> status -> UVars.variances
end

type cumul_pb =
  | Conv (* Invariance/equivariance *)
  | Cumul (* Covariance *)
  | InvCumul (* Contravariance *)

val infer_term
  : cumul_pb * cumul_pb
  -> Environ.env
  (** Environment containing the polymorphic universes *)
  -> evars:CClosure.evar_handler
  -> Inf.status
  -> Constr.t
  -> Inf.status

val infer_body
  : cumul_pb * cumul_pb
  -> Environ.env
  (** Environment containing the polymorphic universes *)
  -> evars:CClosure.evar_handler
  -> shift:int (* Shifting for binder indices in variances *)
  -> Inf.status
  -> Constr.t
  -> Inf.status

val infer_definition :
  Environ.env ->
  (** Environment containing the polymorphic universes *)
  ?evars : CClosure.evar_handler ->
  (** By default, CClosure.default_evar_handler *)
  ?infer_in_type : bool ->
  (** Infer the universes in the type *)
  ?in_ctx:Constr.named_context ->
  (** The section context in which the definition is checked *)
  typ:Constr.t ->
  ?body:Constr.t ->
  pre_variances ->
  int * UVars.Variances.t (* Variance position are shifted by [i] due to context [in_ctx], if present *)

val infer_inductive
  : env_params : Environ.env
  (** Environment containing the polymorphic universes and the
      parameters. *)
  -> env_ar_par : Environ.env
  (** Environment containing the polymorphic universes and the inductives then the parameters. *)
  -> ?evars:CClosure.evar_handler
  (** By default, CClosure.default_evar_handler *)
  -> arities : Constr.t list
  -> ctors : Constr.t list list
  -> pre_variances
  (** Universes whose cumulativity we want to infer or check. *)
  -> UVars.Variances.t

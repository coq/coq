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

(** Not the same as Type_errors.BadVariance because we don't have the env where we raise. *)
exception BadVariance of Level.t * VariancePos.t * VariancePos.t

type variance_occurrence =
  { in_binder : (int * UVars.Variance.t) option;
    in_term : UVars.Variance.t option;
    in_type : UVars.Variance.t option }

val default_occ : variance_occurrence
val make_occ : Variance.t -> Position.t -> variance_occurrence

val pr_variance_occurrence : variance_occurrence -> Pp.t

(* The position records the last position in the term where the variable was used relevantly. *)
type level_variances = variance_occurrence Univ.Level.Map.t

val pr_variances : (Univ.Level.t -> Pp.t) -> level_variances -> Pp.t

val empty_level_variances : level_variances

(* Compute the variance in the binders and term and separately, the variance in the type *)
val term_type_variances : variance_occurrence -> Variance.t option * Variance.t option

module Inf : sig
  type variances

  val pr : (Level.t -> Pp.t) -> variances -> Pp.t

  val infer_level_eq : Level.t -> variances -> variances
  val infer_level_leq : Level.t -> variances -> variances
  val infer_level_geq : Level.t -> variances -> variances

  val get_infer_mode : variances -> bool
  val set_infer_mode : bool -> variances -> variances

  val set_position : Position.t -> variances -> variances

  val start_map : (mode * variance_occurrence) Level.Map.t -> Position.t -> variances
  val start : (Level.t * VariancePos.t option) array -> Position.t -> variances

  val start_inference : Level.Set.t -> Position.t -> variances

  val inferred : variances -> level_variances
  val finish : variances -> Variances.t

end

type cumul_pb =
  | Conv (* Invariance/equivariance *)
  | Cumul (* Covariance *)
  | InvCumul (* Contravariance *)

val infer_term
  : cumul_pb
  -> Environ.env
  (** Environment containing the polymorphic universes *)
  -> evars:CClosure.evar_handler
  -> Inf.variances
  -> Constr.t
  -> Inf.variances

val infer_inductive
  : env_params : Environ.env
  (** Environment containing the polymorphic universes and the
      parameters. *)
  -> env_ar_par : Environ.env
  (** Environment containing the polymorphic universes and the inductives then the parameters. *)
  -> evars:CClosure.evar_handler
  -> arities : Constr.t list
  -> ctors : Constr.t list list
  -> (Univ.Level.t * UVars.VariancePos.t option) array
  (** Universes whose cumulativity we want to infer or check. *)
  -> UVars.Variances.t

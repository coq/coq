(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Environ

(***********************************************************************
  s conversion functions *)

type 'a kernel_conversion_function = env -> 'a -> 'a -> (unit, unit) result
type 'a extended_conversion_function =
  ?l2r:bool -> ?reds:TransparentState.t -> env ->
  ?evars:CClosure.evar_handler ->
  'a -> 'a -> (unit, unit) result

type conv_pb = CONV | CUMUL

type ('a, 'err) universe_compare = {
  compare_sorts : env -> conv_pb -> Sorts.t -> Sorts.t -> 'a -> ('a, 'err option) result;
  compare_instances: flex:bool -> UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err option) result;
  compare_cumul_instances : conv_pb -> UVars.Variance.t array ->
    UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err option) result;
}

type ('a, 'err) universe_state = 'a * ('a, 'err) universe_compare

type ('a, 'err) generic_conversion_function = ('a, 'err) universe_state -> constr -> constr -> ('a, 'err option) result

val get_cumulativity_constraints : conv_pb -> UVars.Variance.t array ->
  UVars.Instance.t -> UVars.Instance.t -> Sorts.QUConstraints.t

val inductive_cumulativity_arguments : (Declarations.mutual_inductive_body * int) -> int
val constructor_cumulativity_arguments : (Declarations.mutual_inductive_body * int * int) -> int

val sort_cmp_universes : env -> conv_pb -> Sorts.t -> Sorts.t ->
  'a * ('a, 'err) universe_compare -> ('a, 'err option) result * ('a, 'err) universe_compare

(* [flex] should be true for constants, false for inductive types and
constructors. *)
val convert_instances : flex:bool -> UVars.Instance.t -> UVars.Instance.t ->
  'a * ('a, 'err) universe_compare -> ('a, 'err option) result * ('a, 'err) universe_compare

(** This function never returns an non-empty error. *)
val checked_universes : (UGraph.t, 'err) universe_compare

(** These two functions can only fail with unit *)
val conv : constr extended_conversion_function

val conv_leq : types extended_conversion_function

(** The failure values depend on the universe state functions
    (for better error messages). *)
val generic_conv : conv_pb -> l2r:bool
  -> TransparentState.t -> env -> ?evars:CClosure.evar_handler
  -> ('a, 'err) generic_conversion_function

val default_conv     : conv_pb -> types kernel_conversion_function
val default_conv_leq : types kernel_conversion_function

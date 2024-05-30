(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

exception NotConvertible

type conversion_error =
| ConvErrDefault
| ConvErrUniverses of UGraph.univ_inconsistency

type 'a kernel_conversion_function = env -> 'a -> 'a -> (unit, unit) result
type 'a extended_conversion_function =
  ?l2r:bool -> ?reds:TransparentState.t -> env ->
  ?evars:CClosure.evar_handler ->
  'a -> 'a -> (unit, unit) result

type conv_pb = CONV | CUMUL

type 'a universe_compare = {
  (* Might raise NotConvertible *)
  compare_sorts : env -> conv_pb -> Sorts.t -> Sorts.t -> 'a -> ('a, conversion_error) result;
  compare_instances: flex:bool -> UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, conversion_error) result;
  compare_cumul_instances : conv_pb -> UVars.Variance.t array ->
    UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, conversion_error) result;
}

type 'a universe_state = 'a * 'a universe_compare

type 'a generic_conversion_function = 'a universe_state -> constr -> constr -> ('a, conversion_error) result

type 'a infer_conversion_function = env -> 'a -> 'a -> (Univ.Constraints.t, conversion_error) result

val get_cumulativity_constraints : conv_pb -> UVars.Variance.t array ->
  UVars.Instance.t -> UVars.Instance.t -> Sorts.QUConstraints.t

val inductive_cumulativity_arguments : (Declarations.mutual_inductive_body * int) -> int
val constructor_cumulativity_arguments : (Declarations.mutual_inductive_body * int * int) -> int

val sort_cmp_universes : env -> conv_pb -> Sorts.t -> Sorts.t ->
  'a * 'a universe_compare -> ('a, conversion_error) result * 'a universe_compare

(* [flex] should be true for constants, false for inductive types and
constructors. *)
val convert_instances : flex:bool -> UVars.Instance.t -> UVars.Instance.t ->
  'a * 'a universe_compare -> ('a, conversion_error) result * 'a universe_compare

(** This function never returns an ConvErrUniverses error. *)
val checked_universes : UGraph.t universe_compare

(** These two functions can only fail with ConvErrDefault *)
val conv : constr extended_conversion_function

val conv_leq : types extended_conversion_function

(** Depending on the universe state functions, this might fail with
  [ConvErrUniverses] in addition to [ConvErrDefault] (for better error
  messages). *)
val generic_conv : conv_pb -> l2r:bool
  -> TransparentState.t -> env -> ?evars:CClosure.evar_handler
  -> 'a generic_conversion_function

val default_conv     : conv_pb -> types kernel_conversion_function
val default_conv_leq : types kernel_conversion_function

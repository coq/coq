(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ

type conv_pb =
  | CONV
  | CUMUL

val pr_conv_pb : conv_pb -> Pp.t

type ('a, 'err) convert_instances = UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err) Result.t
type ('a, 'err) convert_instances_cumul = nargs:UVars.application -> conv_pb -> UVars.Variances.t -> UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err) Result.t

type ('a, 'err) universe_compare = {
  compare_sorts : env -> conv_pb -> Sorts.t -> Sorts.t -> 'a -> ('a, 'err option) result;
  compare_instances: flex:bool -> ('a, 'err option) convert_instances;
  compare_cumul_instances : flex:bool -> ('a, 'err option) convert_instances_cumul;
}

type ('a, 'err) universe_state = 'a * ('a, 'err) universe_compare

val get_cumulativity_constraints : conv_pb -> nargs:UVars.application -> UVars.Variances.t ->
    UVars.Instance.t -> UVars.Instance.t -> Sorts.QUConstraints.t

val inductive_cumulativity_arguments : (Declarations.mutual_inductive_body * int) -> int
val constructor_cumulativity_arguments : (Declarations.mutual_inductive_body * int * int) -> int

val sort_cmp_universes : env -> conv_pb -> Sorts.t -> Sorts.t ->
    'a * ('a, 'err) universe_compare -> ('a, 'err option) result * ('a, 'err) universe_compare

(* [flex] should be true for constants, false for inductive types and
constructors. *)
val convert_instances : flex:bool -> UVars.Instance.t -> UVars.Instance.t ->
    'a * ('a, 'err) universe_compare -> ('a, 'err option) result * ('a, 'err) universe_compare

val convert_instances_cumul : flex:bool -> conv_pb -> nargs:UVars.application -> UVars.Variances.t ->
    UVars.Instance.t -> UVars.Instance.t ->
    'a * ('a, 'err) universe_compare -> ('a, 'err option) result * ('a, 'err) universe_compare

exception MustExpand
(** raised by convert_inductives or convert_constructors in case the inductive or constructor is not sufficiently applied to trigger cumulativity. *)

val convert_inductives_gen :
  ('a, 'err) convert_instances ->
  ('a, 'err) convert_instances_cumul ->
  env ->
  conv_pb ->
  Names.inductive ->
  nargs:UVars.application ->
  UVars.Instance.t ->
  UVars.Instance.t ->
  'a ->
  ('a, 'err) Result.t

val convert_inductives :
  env ->
  conv_pb ->
  Names.inductive ->
  nargs:UVars.application ->
  UVars.Instance.t ->
  UVars.Instance.t ->
  'a * ('a, 'b) universe_compare ->
  ('a, 'b option) Result.t * ('a, 'b) universe_compare

val convert_constructors_gen :
  ('a, 'err) convert_instances ->
  ('a, 'err) convert_instances_cumul ->
  env ->
  Names.constructor ->
  nargs:UVars.application ->
  UVars.Instance.t ->
  UVars.Instance.t ->
  'a -> ('a, 'err) Result.t

val convert_constructors :
  env ->
  Names.constructor ->
  nargs:UVars.application ->
  UVars.Instance.t ->
  UVars.Instance.t ->
  'a * ('a, 'b) universe_compare ->
  ('a, 'b option) Result.t * ('a, 'b) universe_compare

val convert_constants_gen :
  ('a, 'err) convert_instances ->
  ('a, 'err) convert_instances_cumul ->
  env ->
  conv_pb ->
  Names.Constant.t ->
  nargs:UVars.application ->
  UVars.Instance.t ->
  UVars.Instance.t ->
  'a -> ('a, 'err) Result.t

val convert_constants :
  env ->
  conv_pb ->
  Names.Constant.t ->
  flex:bool ->
  nargs:UVars.application ->
  UVars.Instance.t ->
  UVars.Instance.t ->
  'a * ('a, 'b) universe_compare ->
  ('a, 'b option) Result.t * ('a, 'b) universe_compare

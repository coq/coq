(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr

(** This module provides support for registering inductive scheme builders,
   declaring schemes and generating schemes on demand *)

(** A scheme is either a "mutual scheme_kind" or an "individual scheme_kind" *)

type mutual
type individual
type 'a scheme_kind

type internal_flag =
  | UserAutomaticRequest
  | InternalTacticRequest
  | UserIndividualRequest

type mutual_scheme_object_function =
  internal_flag -> MutInd.t -> constr array Evd.in_evar_universe_context * Evd.side_effects
type individual_scheme_object_function =
  internal_flag -> inductive -> constr Evd.in_evar_universe_context * Evd.side_effects

(** Main functions to register a scheme builder *)

val declare_mutual_scheme_object : string -> ?aux:string ->
  mutual_scheme_object_function -> mutual scheme_kind

val declare_individual_scheme_object : string -> ?aux:string ->
  individual_scheme_object_function ->
  individual scheme_kind

(** Force generation of a (mutually) scheme with possibly user-level names *)

val define_individual_scheme : individual scheme_kind -> 
  internal_flag (** internal *) ->
  Id.t option -> inductive -> Constant.t * Evd.side_effects

val define_mutual_scheme : mutual scheme_kind -> internal_flag (** internal *) ->
  (int * Id.t) list -> MutInd.t -> Constant.t array * Evd.side_effects

(** Main function to retrieve a scheme in the cache or to generate it *)
val find_scheme : ?mode:internal_flag -> 'a scheme_kind -> inductive -> Constant.t * Evd.side_effects

val check_scheme : 'a scheme_kind -> inductive -> bool


val pr_scheme_kind : 'a scheme_kind -> Pp.t

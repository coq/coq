(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Names

(** This module provides support for registering inductive scheme builders,
   declaring schemes and generating schemes on demand *)

(** A scheme is either a "mutual scheme_kind" or an "individual scheme_kind" *)

type mutual
type individual
type 'a scheme_kind

type mutual_scheme_object_function =
  mutual_inductive -> constr array Evd.in_evar_universe_context * Declareops.side_effects
type individual_scheme_object_function =
  inductive -> constr Evd.in_evar_universe_context * Declareops.side_effects

(** Main functions to register a scheme builder *)

val declare_mutual_scheme_object : string -> ?aux:string ->
  mutual_scheme_object_function -> mutual scheme_kind

val declare_individual_scheme_object : string -> ?aux:string ->
  individual_scheme_object_function ->
  individual scheme_kind

(*
val declare_scheme : 'a scheme_kind -> (inductive * constant) array -> unit
*)

(** Force generation of a (mutually) scheme with possibly user-level names *)

val define_individual_scheme : individual scheme_kind -> 
  Declare.internal_flag (** internal *) ->
  Id.t option -> inductive -> constant * Declareops.side_effects

val define_mutual_scheme : mutual scheme_kind -> Declare.internal_flag (** internal *) ->
  (int * Id.t) list -> mutual_inductive -> constant array * Declareops.side_effects

(** Main function to retrieve a scheme in the cache or to generate it *)
val find_scheme : 'a scheme_kind -> inductive -> constant * Declareops.side_effects

val check_scheme : 'a scheme_kind -> inductive -> bool


val pr_scheme_kind : 'a scheme_kind -> Pp.std_ppcmds

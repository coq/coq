(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Misctypes

val dump_global : Libnames.reference or_by_notation -> unit

(** Vernacular entries *)
val vernac_require :
  Libnames.reference option -> bool option -> Libnames.reference list -> unit

(** The main interpretation function of vernacular expressions *)
val interp :
  ?verbosely:bool ->
  ?proof:Proof_global.closed_proof ->
  st:Vernacstate.t -> Vernacexpr.vernac_control CAst.t -> Vernacstate.t

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

val make_cases : string -> string list list

(* XXX STATE: this type hints that restoring the state should be the
   caller's responsibility *)
val with_fail : Vernacstate.t -> bool -> (unit -> unit) -> unit

val command_focus : unit Proof.focus_kind

val interp_redexp_hook : (Environ.env -> Evd.evar_map -> Genredexpr.raw_red_expr ->
  Evd.evar_map * Redexpr.red_expr) Hook.t

val universe_polymorphism_option_name : string list

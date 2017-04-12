(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
    Loc.t * Vernacexpr.vernac_expr -> unit

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

val make_cases : string -> string list list

val with_fail : bool -> (unit -> unit) -> unit

val command_focus : unit Proof.focus_kind

val interp_redexp_hook : (Environ.env -> Evd.evar_map -> Genredexpr.raw_red_expr ->
  Evd.evar_map * Redexpr.red_expr) Hook.t

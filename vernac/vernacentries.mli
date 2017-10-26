(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Misctypes

val dump_global : Libnames.reference or_by_notation -> unit

(** Vernacular entries *)
val vernac_require :
  Libnames.reference option -> bool option -> Libnames.reference list -> unit

type interp_state = { (* TODO: inline records in OCaml 4.03 *)
  system  : States.state;        (* summary + libstack *)
  proof   : Proof_global.state;  (* proof state *)
  shallow : bool                 (* is the state trimmed down (libstack) *)
}

val freeze_interp_state : Summary.marshallable -> interp_state
val unfreeze_interp_state : interp_state -> unit

(** The main interpretation function of vernacular expressions *)
val interp :
  ?verbosely:bool ->
  ?proof:Proof_global.closed_proof ->
  interp_state ->
    Vernacexpr.vernac_expr Loc.located -> interp_state

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

val make_cases : string -> string list list

(* XXX STATE: this type hints that restoring the state should be the
   caller's responsibility *)
val with_fail : interp_state -> bool -> (unit -> unit) -> unit

val command_focus : unit Proof.focus_kind

val interp_redexp_hook : (Environ.env -> Evd.evar_map -> Genredexpr.raw_red_expr ->
  Evd.evar_map * Redexpr.red_expr) Hook.t

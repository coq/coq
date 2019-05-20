(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val dump_global : Libnames.qualid Constrexpr.or_by_notation -> unit

(** Default proof mode set by `start_proof` *)
val get_default_proof_mode : unit -> Pvernac.proof_mode

val proof_mode_opt_name : string list

(** Vernacular entries *)
val vernac_require :
  Libnames.qualid option -> bool option -> Libnames.qualid list -> unit

(** The main interpretation function of vernacular expressions *)
val interp :
  ?verbosely:bool ->
  ?proof:Proof_global.closed_proof ->
  st:Vernacstate.t -> Vernacexpr.vernac_control -> Vernacstate.t

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

val make_cases : string -> string list list

(** [with_fail ~st f] runs [f ()] and expects it to fail, otherwise it fails. *)
val with_fail : st:Vernacstate.t -> (unit -> 'a) -> unit

val command_focus : unit Proof.focus_kind

val interp_redexp_hook : (Environ.env -> Evd.evar_map -> Genredexpr.raw_red_expr ->
  Evd.evar_map * Redexpr.red_expr) Hook.t

(** Helper *)
val vernac_require_open_proof : pstate:Proof_global.stack option -> (pstate:Proof_global.stack -> 'a) -> 'a

val with_pstate : pstate:Proof_global.stack option -> (pstate:Proof_global.t -> 'a) -> 'a

val modify_pstate : pstate:Proof_global.stack option -> (pstate:Proof_global.t -> Proof_global.t) -> Proof_global.stack option

(* Flag set when the test-suite is called. Its only effect to display
   verbose information for `Fail` *)
val test_mode : bool ref

(** For mlg *)

type functional_vernac =
  | VtDefault of (unit -> unit)
  | VtModifyProofStack of (pstate:Proof_global.stack option -> Proof_global.stack option)
  | VtMaybeOpenProof of (unit -> Proof_global.t option)
  | VtOpenProof of (unit -> Proof_global.t)
  | VtModifyProof of (pstate:Proof_global.t -> Proof_global.t)
  | VtReadProofOpt of (pstate:Proof_global.t option -> unit)
  | VtReadProof of (pstate:Proof_global.t -> unit)

val interp_functional_vernac
  : functional_vernac
  -> pstate:Proof_global.stack option
  -> Proof_global.stack option

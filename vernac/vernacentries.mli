(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Vernac Translation into the Vernac DSL *)
val translate_vernac
  : atts:Attributes.vernac_flags
  -> Vernacexpr.vernac_expr
  -> Vernacextend.typed_vernac

(** Vernacular require command *)
val vernac_require :
  Libnames.qualid option -> bool option -> Libnames.qualid list -> unit

(** Hook to dissappear when #8240 is fixed *)
val interp_redexp_hook : (Environ.env -> Evd.evar_map -> Genredexpr.raw_red_expr ->
  Evd.evar_map * Redexpr.red_expr) Hook.t

(** Miscellaneous stuff *)
val command_focus : unit Proof.focus_kind

val allow_sprop_opt_name : string list
val cumul_sprop_opt_name : string list

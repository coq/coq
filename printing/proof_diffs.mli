(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* diff options *)

(** Name of Diffs option *)
val opt_name : string list

(** Returns true if the diffs option is "on" or "removed" *)
val show_diffs : unit -> bool

(** Returns true if the diffs option is "removed" *)
val show_removed : unit -> bool

(** controls whether color output is enabled *)
val write_color_enabled : bool -> unit

(** true indicates that color output is enabled *)
val color_enabled : unit -> bool

type diffOpt = DiffOff | DiffOn | DiffRemoved

val string_to_diffs : string -> diffOpt

type goal

val make_goal : Environ.env -> Evd.evar_map -> Evar.t -> goal

(** Computes the diff between the goals of two Proofs and returns
the highlighted lists of hypotheses and conclusions.

If the strings used to display the goal are not lexable (this is believed
unlikely), this routine will generate a Diff_Failure.  This routine may also
raise Diff_Failure under some "impossible" conditions.

If you want to make your call especially bulletproof, catch these
exceptions, print a user-visible message, then recall this routine with
the first argument set to None, which will skip the diff.
*)
val diff_goal : ?og_s:goal -> goal -> Pp.t list * Pp.t

(** Convert a string to a list of token strings using the lexer *)
val tokenize_string : string -> string list

(** Computes diffs for a single conclusion *)
val diff_concl : ?og_s:goal -> goal -> Pp.t

type goal_map

(** Generates a map from [np] to [op] that maps changed goals to their prior
forms.  The map doesn't include entries for unchanged goals; unchanged goals
will have the same goal id in both versions.

[op] and [np] must be from the same proof document and [op] must be for a state
before [np]. *)
val make_goal_map : Proof.t -> Proof.t -> goal_map

val map_goal : Evar.t -> goal_map -> goal option

(* Exposed for unit test, don't use these otherwise *)
(* output channel for the test log file *)
val log_out_ch : out_channel ref


type hyp_info = {
  idents: string list;
  rhs_pp: Pp.t;
}

val diff_hyps : string list list -> hyp_info CString.Map.t -> string list list -> hyp_info CString.Map.t -> Pp.t list

val diff_proofs : diff_opt:diffOpt -> ?old:Proof.t -> Proof.t -> Pp.t

val notify_proof_diff_failure : string -> unit

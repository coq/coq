(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* diff options *)

(** Controls whether to show diffs.  Takes values "on", "off", "removed" *)
val write_diffs_option : string -> unit
(** Returns true if the diffs option is "on" or "removed" *)
val show_diffs : unit -> bool

open Evd
open Proof_type
open Environ
open Constr

(** Computes the diff between the goals of two Proofs and returns
the highlighted lists of hypotheses and conclusions.

If the strings used to display the goal are not lexable (this is believed
unlikely), this routine will generate a Diff_Failure.  This routine may also
raise Diff_Failure under some "impossible" conditions.

If you want to make your call especially bulletproof, catch these
exceptions, print a user-visible message, then recall this routine with
the first argument set to None, which will skip the diff.
*)
val diff_goal_ide : goal sigma option -> goal -> Evd.evar_map -> Pp.t list * Pp.t

(** Computes the diff between two goals

If the strings used to display the goal are not lexable (this is believed
unlikely), this routine will generate a Diff_Failure.  This routine may also
raise Diff_Failure under some "impossible" conditions.

If you want to make your call especially bulletproof, catch these
exceptions, print a user-visible message, then recall this routine with
the first argument set to None, which will skip the diff.
*)
val diff_goal : ?og_s:(goal sigma) -> goal -> Evd.evar_map -> Pp.t

(** Convert a string to a list of token strings using the lexer *)
val tokenize_string : string -> string list

val pr_letype_core         : bool -> Environ.env -> Evd.evar_map -> EConstr.types -> Pp.t
val pr_leconstr_core       : bool -> Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.t
val pr_lconstr_env         : env -> evar_map -> constr -> Pp.t

(** Computes diffs for a single conclusion *)
val diff_concl : ?og_s:goal sigma -> Evd.evar_map -> Goal.goal -> Pp.t

(** Generates a map from [np] to [op] that maps changed goals to their prior
forms.  The map doesn't include entries for unchanged goals; unchanged goals
will have the same goal id in both versions.

[op] and [np] must be from the same proof document and [op] must be for a state
before [np]. *)
val make_goal_map : Proof.t option -> Proof.t -> Evar.t Evar.Map.t

(* Exposed for unit test, don't use these otherwise *)
(* output channel for the test log file *)
val log_out_ch : out_channel ref


type hyp_info = {
  idents: string list;
  rhs_pp: Pp.t;
  mutable done_: bool;
}

module StringMap :
sig
  type +'a t
  val empty: hyp_info t
  val add : string -> hyp_info -> hyp_info t -> hyp_info t
end

val diff_hyps : string list list -> hyp_info StringMap.t -> string list list -> hyp_info StringMap.t -> Pp.t list

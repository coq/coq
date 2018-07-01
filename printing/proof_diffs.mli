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

(** Computes the diff between the first goal of two Proofs and returns
the highlighted hypotheses and conclusion.

If the strings used to display the goal are not lexable (this is believed
unlikely), this routine will generate a Diff_Failure.  This routine may also
raise Diff_Failure under some "impossible" conditions.

If you want to make your call especially bulletproof, catch these
exceptions, print a user-visible message, then recall this routine with
the first argument set to None, which will skip the diff.
*)
val diff_first_goal : Proof.t option -> Proof.t option -> Pp.t list * Pp.t

open Evd
open Proof_type

(** Computes the diff between two goals

If the strings used to display the goal are not lexable (this is believed
unlikely), this routine will generate a Diff_Failure.  This routine may also
raise Diff_Failure under some "impossible" conditions.

If you want to make your call especially bulletproof, catch these
exceptions, print a user-visible message, then recall this routine with
the first argument set to None, which will skip the diff.
*)
val diff_goals : ?prev_gs:(goal sigma) -> goal sigma option -> Pp.t

(** Convert a string to a list of token strings using the lexer *)
val tokenize_string : string -> string list

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

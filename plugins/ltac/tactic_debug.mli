(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ
open Pattern
open Names
open Tacexpr
open EConstr
open Evd

(** TODO: Move those definitions somewhere sensible *)

val ltac_trace_info : ltac_trace Exninfo.t

(** This module intends to be a beginning of debugger for tactic expressions.
   Currently, it is quite simple and we can hope to have, in the future, a more
   complete panel of commands dedicated to a proof assistant framework *)

(** Debug information *)
type debug_info =
  | DebugOn of int
  | DebugOff

(** Prints the state and waits *)
val debug_prompt :
  int -> glob_tactic_expr -> (debug_info -> 'a Proofview.tactic) -> 'a Proofview.tactic

(** Initializes debugger *)
val db_initialize : unit Proofview.NonLogical.t

(** Prints a constr *)
val db_constr : debug_info -> env -> evar_map -> constr -> unit Proofview.NonLogical.t

(** Prints the pattern rule *)
val db_pattern_rule :
  debug_info -> int -> (Tacexpr.glob_constr_and_expr * constr_pattern,glob_tactic_expr) match_rule -> unit Proofview.NonLogical.t

(** Prints a matched hypothesis *)
val db_matched_hyp :
  debug_info -> env -> evar_map -> Id.t * constr option * constr -> Name.t -> unit Proofview.NonLogical.t

(** Prints the matched conclusion *)
val db_matched_concl : debug_info -> env -> evar_map -> constr -> unit Proofview.NonLogical.t

(** Prints a success message when the goal has been matched *)
val db_mc_pattern_success : debug_info -> unit Proofview.NonLogical.t

(** Prints a failure message for an hypothesis pattern *)
val db_hyp_pattern_failure :
  debug_info -> env -> evar_map -> Name.t * constr_pattern match_pattern -> unit Proofview.NonLogical.t

(** Prints a matching failure message for a rule *)
val db_matching_failure : debug_info -> unit Proofview.NonLogical.t

(** Prints an evaluation failure message for a rule *)
val db_eval_failure : debug_info -> Pp.t -> unit Proofview.NonLogical.t

(** An exception handler *)
val explain_logic_error: exn -> Pp.t

(** For use in the Ltac debugger: some exception that are usually
   consider anomalies are acceptable because they are caught later in
   the process that is being debugged.  One should not require
   from users that they report these anomalies. *)
val explain_logic_error_no_anomaly : exn -> Pp.t

(** Prints a logic failure message for a rule *)
val db_logic_failure : debug_info -> exn -> unit Proofview.NonLogical.t

(** Prints a logic failure message for a rule *)
val db_breakpoint : debug_info ->
  lident message_token list -> unit Proofview.NonLogical.t

val extract_ltac_trace :
  ?loc:Loc.t -> Tacexpr.ltac_trace -> Pp.t option Loc.located

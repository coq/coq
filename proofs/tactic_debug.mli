(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Environ
open Pattern
open Evd
open Names
open Tacexpr
open Term

(* arnaud: trucs factices *)
type goal = Evd.evar_info
(*arnaud:/trucs factices *)

(* This module intends to be a beginning of debugger for tactic expressions.
   Currently, it is quite simple and we can hope to have, in the future, a more
   complete panel of commands dedicated to a proof assistant framework *)

val set_tactic_printer : (glob_tactic_expr ->Pp.std_ppcmds) -> unit
val set_match_pattern_printer :
  (env -> constr_pattern match_pattern -> Pp.std_ppcmds) -> unit
val set_match_rule_printer :
  ((constr_pattern,glob_tactic_expr) match_rule -> Pp.std_ppcmds) ->
    unit

(* Debug information *)
type debug_info =
  | DebugOn of int
  | DebugOff

(* Prints the state and waits *)
val debug_prompt :
  int -> goal sigma -> glob_tactic_expr -> (debug_info -> 'a) -> 'a

(* Prints a constr *)
val db_constr : debug_info -> env -> constr -> unit

(* Prints the pattern rule *)
val db_pattern_rule :
  debug_info -> int -> (constr_pattern,glob_tactic_expr) match_rule -> unit

(* Prints a matched hypothesis *)
val db_matched_hyp :
  debug_info -> env -> identifier * constr -> name -> unit

(* Prints the matched conclusion *)
val db_matched_concl : debug_info -> env -> constr -> unit

(* Prints a success message when the goal has been matched *)
val db_mc_pattern_success : debug_info -> unit

(* Prints a failure message for an hypothesis pattern *)
val db_hyp_pattern_failure :
  debug_info -> env -> name * constr_pattern match_pattern -> unit

(* Prints a matching failure message for a rule *)
val db_matching_failure : debug_info -> unit

(* Prints an evaluation failure message for a rule *)
val db_eval_failure : debug_info -> Pp.std_ppcmds -> unit

(* An exception handler *)
val explain_logic_error: (exn -> Pp.std_ppcmds) ref

(* For use in the Ltac debugger: some exception that are usually
   consider anomalies are acceptable because they are caught later in
   the process that is being debugged.  One should not require
   from users that they report these anomalies. *)
val explain_logic_error_no_anomaly : (exn -> Pp.std_ppcmds) ref

(* Prints a logic failure message for a rule *)
val db_logic_failure : debug_info -> exn -> unit

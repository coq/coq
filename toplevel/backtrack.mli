(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Command history stack

    We maintain a stack of the past states of the system after each
    (non-state-preserving) interpreted commands
*)

(** [mark_command ast] marks the end of a command:
    - it stores a frozen state and a end of command in the Lib stack,
    - it stores the current state information in the command history
    stack *)

val mark_command : Vernacexpr.vernac_expr -> unit

(** The [Invalid] exception is raised when one of the following function
    tries to empty the history stack, or reach an unknown states, etc.
    The stack is preserved in these cases. *)

exception Invalid

(** Nota Bene: it is critical for the following functions that proofs
    are nested in a regular way (i.e. no more Resume or Suspend commands
    as earlier). *)

(** Backtracking by a certain number of (non-state-preserving) commands.
    This is used by Coqide.
    It may actually undo more commands than asked : for instance instead
    of jumping back in the middle of a finished proof, we jump back before
    this proof. The number of extra backtracked command is returned at
    the end. *)

val back : int -> int

(** Backtracking to a certain state number, and reset proofs accordingly.
    We may end on some earlier state if needed to avoid re-opening proofs.
    Return the state number on which we finally end. *)

val backto : int -> int

(** Old [Backtrack] code with corresponding update of the history stack.
    [Backtrack] is now deprecated (in favor of [BackTo]) but is kept for
    compatibility with ProofGeneral. It's completely up to ProofGeneral
    to decide where to go and how to adapt proofs. Note that the choices
    of ProofGeneral are currently not always perfect (for instance when
    backtracking an Undo). *)

val backtrack : int -> int -> int -> unit

(** [reset_initial] resets the system and clears the command history
    stack, only pushing back the initial entry. It should be equivalent
    to [backto Lib.first_command_label], but sligthly more efficient. *)

val reset_initial : unit -> unit

(** Reset to the last known state just before defining [id] *)

val reset_name : Names.identifier Pp.located -> unit

(** When a proof is ended (via either Qed/Admitted/Restart/Abort),
    old proof steps should be marked differently to avoid jumping back
    to them:
     - either this proof isn't there anymore in the proof engine
     - either a proof with the same name is there, but it's a more recent
       attempt after a Restart/Abort, we shouldn't mix the two.
    We also mark as unreachable the proof steps cancelled via a Undo.
*)

val mark_unreachable : ?after:int -> Names.identifier list -> unit

(** Parse the history stack for printing the script of a proof *)

val get_script : Names.identifier -> Vernacexpr.vernac_expr list


(** For debug purpose, a dump of the history *)

type info = {
  label : int;
  nproofs : int;
  prfname : Names.identifier option;
  prfdepth : int;
  cmd : Vernacexpr.vernac_expr;
  mutable reachable : bool;
}

val dump_history : unit -> info list

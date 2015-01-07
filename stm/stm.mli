(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr
open Names
open Feedback

(** state-transaction-machine interface *)

(* [add ontop check vebose eid s] adds a new command [s] on the state [ontop]
   having edit id [eid].  [check] is called on the AST.
   The [ontop] parameter is just for asserting the GUI is on sync, but
   will eventually call edit_at on the fly if needed.
   The sentence [s] is parsed in the state [ontop].
   If [newtip] is provided, then the returned state id is guaranteed to be
   [newtip] *)
val add : ontop:Stateid.t -> ?newtip:Stateid.t -> ?check:(located_vernac_expr -> unit) ->
  bool -> edit_id -> string ->
    Stateid.t * [ `NewTip | `Unfocus of Stateid.t ]

(* parses and executes a command at a given state, throws away its side effects
   but for the printings.  Feedback is sent with report_with (defaults to dummy
   state id)  *)
val query :
  at:Stateid.t -> ?report_with:(Stateid.t * Feedback.route_id) -> string -> unit

(* [edit_at id] is issued to change the editing zone.  [`NewTip] is returned if
   the requested id is the new document tip hence the document portion following
   [id] is dropped by Coq.  [`Focus fo] is returned to say that [fo.tip] is the
   new document tip, the document between [id] and [fo.stop] has been dropped.
   The portion between [fo.stop] and [fo.tip] has been kept.  [fo.start] is
   just to tell the gui where the editing zone starts, in case it wants to
   graphically denote it.  All subsequent [add] happen on top of [id]. *)
type focus = { start : Stateid.t; stop : Stateid.t; tip : Stateid.t }
val edit_at : Stateid.t -> [ `NewTip | `Focus of focus ]

(* Evaluates the tip of the current branch *)
val finish : unit -> unit

val observe : Stateid.t -> unit

val stop_worker : string -> unit

(* Joins the entire document.  Implies finish, but also checks proofs *)
val join : unit -> unit

(* Saves on the dist a .vio corresponding to the current status:
   - if the worker prool is empty, all tasks are saved
   - if the worker proof is not empty, then it waits until all workers
     are done with their current jobs and then dumps (or fails if one
     of the completed tasks is a failuere) *)
val snapshot_vio : DirPath.t -> string -> unit

(* Empties the task queue, can be used only if the worker pool is empty (E.g.
 * after having built a .vio in batch mode *)
val reset_task_queue : unit -> unit

(* A .vio contains tasks to be completed *)
type tasks
val check_task : string -> tasks -> int -> bool
val info_tasks : tasks -> (string * float * int) list
val finish_tasks : string ->
  Library.seg_univ -> Library.seg_discharge -> Library.seg_proofs ->
    tasks -> Library.seg_univ * Library.seg_proofs

(* Id of the tip of the current branch *)
val get_current_state : unit -> Stateid.t

(* Misc *)
val init : unit -> unit
val print_ast : Stateid.t -> Xml_datatype.xml

(* Filename *)
val set_compilation_hints : string -> unit

(* Reorders the task queue putting forward what is in the perspective *)
val set_perspective : Stateid.t list -> unit

(** workers **************************************************************** **)

module ProofTask : AsyncTaskQueue.Task
module TacTask   : AsyncTaskQueue.Task
module QueryTask : AsyncTaskQueue.Task

(** customization ********************************************************** **)

(* From the master (or worker, but beware that to install the hook
 * into a worker one has to build the worker toploop to do so and
 * the alternative toploop for the worker can be selected by changing
 * the name of the Task(s) above) *)

val state_computed_hook : (Stateid.t -> in_cache:bool -> unit) Hook.t
val parse_error_hook :
  (Feedback.edit_or_state_id -> Loc.t -> Pp.std_ppcmds -> unit) Hook.t
val execution_error_hook : (Stateid.t -> Loc.t -> Pp.std_ppcmds -> unit) Hook.t
val unreachable_state_hook : (Stateid.t -> unit) Hook.t
(* ready means that master has it at hand *)
val state_ready_hook : (Stateid.t -> unit) Hook.t

(* Messages from the workers to the master *)
val forward_feedback_hook : (Feedback.feedback -> unit) Hook.t

type state = {
  system : States.state;
  proof : Proof_global.state;
  shallow : bool
}
val state_of_id : Stateid.t -> [ `Valid of state option | `Expired ]

(** read-eval-print loop compatible interface ****************************** **)

(* Adds a new line to the document.  It replaces the core of Vernac.interp.
   [finish] is called as the last bit of this function is the system
   is running interactively (-emacs or coqtop). *)
val interp : bool -> located_vernac_expr -> unit

(* Queries for backward compatibility *)
val current_proof_depth : unit -> int
val get_all_proof_names : unit -> Id.t list
val get_current_proof_name : unit -> Id.t option
val show_script : ?proof:Proof_global.closed_proof -> unit -> unit

(** Reverse dependency hooks *)
val process_error_hook : Future.fix_exn Hook.t
val interp_hook : (?verbosely:bool -> ?proof:Proof_global.closed_proof ->
  Loc.t * Vernacexpr.vernac_expr -> unit) Hook.t
val with_fail_hook : (bool -> (unit -> unit) -> unit) Hook.t

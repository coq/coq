(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** state-transaction-machine interface *)

(* [parse_sentence sid pa] Reads a sentence from [pa] with parsing
   state [sid] Returns [End_of_input] if the stream ends *)
val parse_sentence : Stateid.t -> Pcoq.Gram.coq_parsable ->
  Vernacexpr.vernac_expr Loc.located

(* Reminder: A parsable [pa] is constructed using
   [Pcoq.Gram.coq_parsable stream], where [stream : char Stream.t]. *)

exception End_of_input

(* [add ~ontop ?newtip verbose cmd] adds a new command [cmd] ontop of
   the state [ontop].
   The [ontop] parameter just asserts that the GUI is on
   sync, but it will eventually call edit_at on the fly if needed.
   If [newtip] is provided, then the returned state id is guaranteed
   to be [newtip] *)
val add : ontop:Stateid.t -> ?newtip:Stateid.t ->
  bool -> Vernacexpr.vernac_expr Loc.located ->
  Stateid.t * [ `NewTip | `Unfocus of Stateid.t ]

(* [query at ?report_with cmd] Executes [cmd] at a given state [at],
   throwing away side effects except messages. Feedback will
   be sent with [report_with], which defaults to the dummy state id *)
val query :
  at:Stateid.t -> ?report_with:(Stateid.t * Feedback.route_id) -> Pcoq.Gram.coq_parsable -> unit

(* [edit_at id] is issued to change the editing zone.  [`NewTip] is returned if
   the requested id is the new document tip hence the document portion following
   [id] is dropped by Coq.  [`Focus fo] is returned to say that [fo.tip] is the
   new document tip, the document between [id] and [fo.stop] has been dropped.
   The portion between [fo.stop] and [fo.tip] has been kept.  [fo.start] is
   just to tell the gui where the editing zone starts, in case it wants to
   graphically denote it.  All subsequent [add] happen on top of [id].
   If Flags.async_proofs_full is set, then [id] is not [observe]d, else it is.
*)
type focus = { start : Stateid.t; stop : Stateid.t; tip : Stateid.t }
val edit_at : Stateid.t -> [ `NewTip | `Focus of focus ]

(* Evaluates the tip of the current branch *)
val finish : unit -> unit

val observe : Stateid.t -> unit

val stop_worker : string -> unit

(* Joins the entire document.  Implies finish, but also checks proofs *)
val join : unit -> unit

(* Saves on the disk a .vio corresponding to the current status:
   - if the worker pool is empty, all tasks are saved
   - if the worker proof is not empty, then it waits until all workers
     are done with their current jobs and then dumps (or fails if one
     of the completed tasks is a failure) *)
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

(* This returns the node at that position *)
val get_ast : Stateid.t -> (Vernacexpr.vernac_expr Loc.located) option

(* Filename *)
val set_compilation_hints : string -> unit

(* Reorders the task queue putting forward what is in the perspective *)
val set_perspective : Stateid.t list -> unit

type document
val backup : unit -> document
val restore : document -> unit

(** workers **************************************************************** **)

module ProofTask : AsyncTaskQueue.Task
module TacTask   : AsyncTaskQueue.Task
module QueryTask : AsyncTaskQueue.Task

(** document structure customization *************************************** **)

(* A proof block delimiter defines a syntactic delimiter for sub proofs
   that, when contain an error, do not impact the rest of the proof.
   While checking a proof, if an error occurs in a (valid) block then
   processing can skip the entire block and go on to give feedback
   on the rest of the proof.
  
   static_block_detection and dynamic_block_validation are run when
   the closing block marker is parsed/executed respectively.
  
   static_block_detection is for example called when "}" is parsed and
   declares a block containing all proof steps between it and the matching
   "{".
  
   dynamic_block_validation is called when an error "crosses" the "}" statement.
   Depending on the nature of the goal focused by "{" the block may absorb the
   error or not.  For example if the focused goal occurs in the type of
   another goal, then the block is leaky.
   Note that one can design proof commands that need no dynamic validation.
  
   Example of document:

      .. { tac1. tac2. } ..

   Corresponding DAG:

      .. (3) <-- { -- (4) <-- tac1 -- (5) <-- tac2 -- (6) <-- } -- (7) ..
                       
   Declaration of block  [-------------------------------------------]

      start = 5            the first state_id that could fail in the block
      stop = 7             the node that may absorb the error
      dynamic_switch = 4   dynamic check on this node
      carry_on_data = ()   no need to carry extra data from static to dynamic
                           checks
*)

module DynBlockData : Dyn.S

type static_block_declaration = {
  block_start : Stateid.t;
  block_stop : Stateid.t;
  dynamic_switch : Stateid.t;
  carry_on_data : DynBlockData.t;
}

type document_node = {
  indentation : int;
  ast : Vernacexpr.vernac_expr;
  id : Stateid.t;
}

type document_view = {
  entry_point : document_node;
  prev_node : document_node -> document_node option;
}

type static_block_detection =
  document_view -> static_block_declaration option

type recovery_action = {
  base_state : Stateid.t;
  goals_to_admit : Goal.goal list;
  recovery_command : Vernacexpr.vernac_expr option;
}

type dynamic_block_error_recovery =
  static_block_declaration -> [ `ValidBlock of recovery_action | `Leaks ]

val register_proof_block_delimiter :
  Vernacexpr.proof_block_name ->
  static_block_detection ->
  dynamic_block_error_recovery ->
    unit

(** customization ********************************************************** **)

(* From the master (or worker, but beware that to install the hook
 * into a worker one has to build the worker toploop to do so and
 * the alternative toploop for the worker can be selected by changing
 * the name of the Task(s) above) *)

val state_computed_hook : (Stateid.t -> in_cache:bool -> unit) Hook.t
val unreachable_state_hook : (Stateid.t -> Exninfo.iexn -> unit) Hook.t

(* ready means that master has it at hand *)
val state_ready_hook : (Stateid.t -> unit) Hook.t

(* Messages from the workers to the master *)
val forward_feedback_hook : (Feedback.feedback -> unit) Hook.t

type state = {
  system : States.state;
  proof : Proof_global.state;
  shallow : bool
}
val state_of_id :
  Stateid.t -> [ `Valid of state option | `Expired | `Error of exn ]

(* Queries for backward compatibility *)
val current_proof_depth : unit -> int
val get_all_proof_names : unit -> Id.t list

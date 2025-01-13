(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Rocq : Interaction with the Rocq toplevel *)

(** {5 General structures} *)

type rocqtop
(** The structure describing a rocqtop sub-process .

    Liveness management of rocqtop is automatic. Whenever a rocqtop dies abruptly,
    this module is responsible for relaunching the whole process. The reset
    handler set through [set_reset_handler] will be called after such an
    abrupt failure. It is also called when explicitly requesting rocqtop to
    reset. *)

type status = New | Ready | Busy | Closed
(** Rocqtop process status :
  - New    : a process has been spawned, but not initialized via [init_rocqtop].
             It will reject tasks given via [try_grab].
  - Ready  : no current task, accepts new tasks via [try_grab].
  - Busy   : has accepted a task via [init_rocqtop] or [try_grab],
  - Closed : the rocqide buffer has been closed, we discard any further task.
*)

type 'a task
(** Rocqtop tasks.

    A task is a group of sequential calls to be performed on a rocqtop process,
    that ultimately return some content.

    If a task is already sent to rocqtop, it is considered busy
    ([is_computing] will answer [true]), and any other task submission
    will be rejected by [try_grab].

    Any exception occurring within the task will trigger a rocqtop reset.

    Beware, because of the GTK scheduler, you never know when a task will
    actually be executed. If you need to sequentialize imperative actions, you
    should do so using the monadic primitives.
*)

val return : 'a -> 'a task
(** Monadic return of values as tasks. *)

val bind : 'a task -> ('a -> 'b task) -> 'b task
(** Monadic binding of tasks *)

val lift : (unit -> 'a) -> 'a task
(** Return the imperative computation waiting to be processed. *)

val seq : unit task -> 'a task -> 'a task
(** Sequential composition *)

(** {5 Rocqtop process management} *)

type reset_kind = Planned | Unexpected
(** A reset may occur accidentally or voluntarily, so we discriminate between
    these. *)

val is_computing : rocqtop -> bool
(** Check if rocqtop is computing, i.e. already has a current task *)

val is_stopped_in_debugger : rocqtop -> bool
(** Returns true if rocqtop is stopped in the debugger *)

val is_ready_or_stopped_in_debugger : rocqtop -> bool
(** Check if rocqtop is Ready or stopped in the debugger *)

val set_stopped_in_debugger : rocqtop -> bool -> unit
(** Records whether rocqtop is stopped in the debugger *)

val spawn_rocqtop : string -> string list -> rocqtop
(** Create a rocqtop process with some command-line arguments. *)

val set_restore_bpts : rocqtop -> (unit -> unit) -> unit
(** Register callback to restore breakpoints after a session has been reset *)

val set_reset_handler : rocqtop -> unit task -> unit
(** Register a handler called when a rocqtop dies (badly or on purpose) *)

val set_feedback_handler : rocqtop -> (Feedback.feedback -> unit) -> unit
(** Register a handler called when rocqtop sends a feedback message *)

val set_debug_prompt_handler : rocqtop -> (tag:string -> Pp.t -> unit) -> unit
(** Register a handler called when the Ltac debugger sends a feedback message *)

val add_do_when_ready : rocqtop -> (unit -> unit) -> unit
(** Register a function to be called when rocqtop becomes Ready *)

val setup_script_editable : rocqtop -> (bool -> unit) -> unit
(** Register setter function to make proof script panel editable or not,
    e.g. to disable editing while any non-debugger message is being processed *)

val init_rocqtop : rocqtop -> unit task -> unit
(** Finish initializing a freshly spawned rocqtop, by running a first task on it.
    The task should run its inner continuation at the end. *)

val interrupt_rocqtop : rocqtop -> string list -> unit
(** Terminate the current computation of rocqtop or the worker if rocqtop is not running. *)

val close_rocqtop : rocqtop -> unit
(** Close rocqtop. Subsequent requests will be discarded. Hook ignored. *)

val reset_rocqtop : rocqtop -> unit
(** Reset rocqtop. Pending requests will be discarded. The reset handler
    of rocqtop will be called with [Planned] as first argument *)

val get_arguments : rocqtop -> string list
(** Get the current arguments used by rocqtop. *)

val set_arguments : rocqtop -> string list -> unit
(** Set process arguments. This also forces a planned reset. *)

(** {5 Task processing} *)

val try_grab : ?db:bool -> rocqtop -> unit task -> (unit -> unit) -> bool
(** Try to schedule a task on a rocqtop. If rocqtop is available, the task
    callback is run (asynchronously), otherwise the [(unit->unit)] callback
    is triggered.  Returns true if the task is run.
    - If rocqtop ever dies during the computation, this function restarts rocqtop
      and calls the restart hook with the fresh rocqtop.
    - If the argument function raises an exception, a rocqtop reset occurs.
    - The task may be discarded if a [close_rocqtop] or [reset_rocqtop] occurs
      before its completion.
    - The task callback should run its inner continuation at the end. *)

(** {5 Atomic calls to rocqtop} *)

(**
  These atomic calls can be combined to form arbitrary multi-call tasks.
  They correspond to the protocol calls (cf [Serialize] for more details).
  Note that each call is asynchronous: it will return immediately,
  but the inner callback will be executed later to handle the call answer
  when this answer is available.
  Except for interp, we use the default logger for any call. *)

type 'a query = 'a Interface.value task
(** A type abbreviation for rocqtop specific answers *)

val add        : Interface.add_sty        -> Interface.add_rty query
val edit_at    : Interface.edit_at_sty    -> Interface.edit_at_rty query
val query      : Interface.query_sty      -> Interface.query_rty query
val status     : Interface.status_sty     -> Interface.status_rty query
val goals      : Interface.goals_sty      -> Interface.goals_rty query
val subgoals   : Interface.subgoals_sty   -> Interface.subgoals_rty query
val evars      : Interface.evars_sty      -> Interface.evars_rty query
val hints      : Interface.hints_sty      -> Interface.hints_rty query
val mkcases    : Interface.mkcases_sty    -> Interface.mkcases_rty query
val search     : Interface.search_sty     -> Interface.search_rty query
val init       : Interface.init_sty       -> Interface.init_rty query
val proof_diff : Interface.proof_diff_sty -> Interface.proof_diff_rty query
val db_cmd     : Interface.db_cmd_sty     -> Interface.db_cmd_rty query
val db_upd_bpts: Interface.db_upd_bpts_sty-> Interface.db_upd_bpts_rty query
val db_continue: Interface.db_continue_sty-> Interface.db_continue_rty query
val db_stack   : Interface.db_stack_sty   -> Interface.db_stack_rty query
val db_vars    : Interface.db_vars_sty    -> Interface.db_vars_rty query
val db_configd : Interface.db_configd_sty -> Interface.db_configd_rty query

val stop_worker: Interface.stop_worker_sty-> Interface.stop_worker_rty query

(** A specialized version of [raw_interp] dedicated to set/unset options. *)

module PrintOpt :
sig
  type 'a t (** Representation of an option *)

  type 'a descr = { opts : 'a t list; init : 'a; label : string }

  val bool_items : bool descr list

  val diff_item : string descr

  val set : 'a t -> 'a -> unit

  val get : 'a t -> Interface.option_value

  val diff : string t

  val printing_unfocused: unit -> bool

  (** [enforce] transmits to rocq the current option values.
      It is also called by [goals] and [evars] above. *)

  val enforce : unit task
end

(** {5 Miscellaneous} *)

val short_version : unit -> string
(** Return a short phrase identifying rocqtop version and date of compilation, as
    given by the [configure] script. *)

val version : unit -> string
(** More verbose description, including details about libraries and
    architecture. *)

val filter_rocq_opts : string list -> string list
(** * Launch a test rocqtop processes, ask for a correct rocqtop if it fails.
    @return the list of arguments that rocqtop did not understand
    (the files probably ..). This command may terminate rocqide in
    case of trouble.  *)

val check_connection : string list -> unit
(** Launch a rocqtop with the user args in order to be sure that it works,
    checking in particular that Prelude.vo is found. This command
    may terminate rocqide in case of trouble *)

val interrupter : (int -> unit) ref
val breaker : (int -> unit) ref
val send_break : rocqtop -> unit

val save_all : (unit -> unit) ref

(* Flags to be used for ideslave *)
val ideslave_rocqtop_flags : string option ref

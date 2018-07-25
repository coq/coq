(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Coq : Interaction with the Coq toplevel *)

(** {5 General structures} *)

type coqtop
(** The structure describing a coqtop sub-process .

    Liveness management of coqtop is automatic. Whenever a coqtop dies abruptly,
    this module is responsible for relaunching the whole process. The reset
    handler set through [set_reset_handler] will be called after such an
    abrupt failure. It is also called when explicitly requesting coqtop to
    reset. *)

type 'a task
(** Coqtop tasks.

    A task is a group of sequential calls to be performed on a coqtop process,
    that ultimately return some content.

    If a task is already sent to coqtop, it is considered busy
    ([is_computing] will answer [true]), and any other task submission
    will be rejected by [try_grab].

    Any exception occurring within the task will trigger a coqtop reset.

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

(** {5 Coqtop process management} *)

type reset_kind = Planned | Unexpected
(** A reset may occur accidentally or voluntarily, so we discriminate between
    these. *)

val is_computing : coqtop -> bool
(** Check if coqtop is computing, i.e. already has a current task *)

val spawn_coqtop : string list -> coqtop
(** Create a coqtop process with some command-line arguments. *)

val set_reset_handler : coqtop -> unit task -> unit
(** Register a handler called when a coqtop dies (badly or on purpose) *)

val set_feedback_handler : coqtop -> (Feedback.feedback -> unit) -> unit
(** Register a handler called when coqtop sends a feedback message *)

val init_coqtop : coqtop -> unit task -> unit
(** Finish initializing a freshly spawned coqtop, by running a first task on it.
    The task should run its inner continuation at the end. *)

val break_coqtop : coqtop -> string list -> unit
(** Interrupt the current computation of coqtop or the worker if coqtop it not running. *)

val close_coqtop : coqtop -> unit
(** Close coqtop. Subsequent requests will be discarded. Hook ignored. *)

val reset_coqtop : coqtop -> unit
(** Reset coqtop. Pending requests will be discarded. The reset handler
    of coqtop will be called with [Planned] as first argument *)

val get_arguments : coqtop -> string list
(** Get the current arguments used by coqtop. *)

val set_arguments : coqtop -> string list -> unit
(** Set process arguments. This also forces a planned reset. *)

(** In win32, sockets are not like regular files *)
val gio_channel_of_descr_socket : (Unix.file_descr -> Glib.Io.channel) ref

(** {5 Task processing} *)

val try_grab : coqtop -> unit task -> (unit -> unit) -> unit
(** Try to schedule a task on a coqtop. If coqtop is available, the task
    callback is run (asynchronously), otherwise the [(unit->unit)] callback
    is triggered.
    - If coqtop ever dies during the computation, this function restarts coqtop
      and calls the restart hook with the fresh coqtop.
    - If the argument function raises an exception, a coqtop reset occurs.
    - The task may be discarded if a [close_coqtop] or [reset_coqtop] occurs
      before its completion.
    - The task callback should run its inner continuation at the end. *)

(** {5 Atomic calls to coqtop} *)

(**
  These atomic calls can be combined to form arbitrary multi-call tasks.
  They correspond to the protocol calls (cf [Serialize] for more details).
  Note that each call is asynchronous: it will return immediately,
  but the inner callback will be executed later to handle the call answer
  when this answer is available.
  Except for interp, we use the default logger for any call. *)

type 'a query = 'a Interface.value task
(** A type abbreviation for coqtop specific answers *)

val add        : Interface.add_sty        -> Interface.add_rty query
val edit_at    : Interface.edit_at_sty    -> Interface.edit_at_rty query
val query      : Interface.query_sty      -> Interface.query_rty query
val status     : Interface.status_sty     -> Interface.status_rty query
val goals      : Interface.goals_sty      -> Interface.goals_rty query
val evars      : Interface.evars_sty      -> Interface.evars_rty query
val hints      : Interface.hints_sty      -> Interface.hints_rty query
val mkcases    : Interface.mkcases_sty    -> Interface.mkcases_rty query
val search     : Interface.search_sty     -> Interface.search_rty query
val init       : Interface.init_sty       -> Interface.init_rty query

val stop_worker: Interface.stop_worker_sty-> Interface.stop_worker_rty query

(** A specialized version of [raw_interp] dedicated to set/unset options. *)

module PrintOpt :
sig
  type 'a t (** Representation of an option *)

  type 'a descr = { opts : 'a t list; init : 'a; label : string }

  val bool_items : bool descr list

  val diff_item : string descr

  val set : 'a t -> 'a -> unit

  val printing_unfocused: unit -> bool

  (** [enforce] transmits to coq the current option values.
      It is also called by [goals] and [evars] above. *)

  val enforce : unit task
end

(** {5 Miscellaneous} *)

val short_version : unit -> string
(** Return a short phrase identifying coqtop version and date of compilation, as
    given by the [configure] script. *)

val version : unit -> string
(** More verbose description, including details about libraries and
    architecture. *)

val filter_coq_opts : string list -> string list
(** * Launch a test coqtop processes, ask for a correct coqtop if it fails.
    @return the list of arguments that coqtop did not understand
    (the files probably ..). This command may terminate coqide in
    case of trouble.  *)

val check_connection : string list -> unit
(** Launch a coqtop with the user args in order to be sure that it works,
    checking in particular that Prelude.vo is found. This command
    may terminate coqide in case of trouble *)

val interrupter : (int -> unit) ref
val save_all : (unit -> unit) ref

(* Flags to be used for ideslave *)
val ideslave_coqtop_flags : string option ref

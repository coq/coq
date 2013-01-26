(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Coq : Interaction with the Coq toplevel *)

(** * Version and date *)

val short_version : unit -> string
val version : unit -> string

(** * Launch a test coqtop processes, ask for a correct coqtop if it fails.
    @return the list of arguments that coqtop did not understand
    (the files probably ..). This command may terminate coqide in
    case of trouble.  *)
val filter_coq_opts : string list -> string list

(** Launch a coqtop with the user args in order to be sure that it works,
    checking in particular that Prelude.vo is found. This command
    may terminate coqide in case of trouble *)
val check_connection : string list -> unit

(** * The structure describing a coqtop sub-process *)

(** Liveness management of coqtop is automatic. Whenever a Coqtop dies abruptly,
    this module is responsible for relaunching the whole process. The hook
    passed as an argument in coqtop construction will be called after such an
    abrupt failure. In particular, it is NOT called when explicitely requesting
    coqtop to close or to reset. *)

type coqtop
type handle

(** * Coqtop tasks

  A task is a group of sequential calls to be perform on a coqtop.
  If a task is already sent to coqtop, it is considered busy
  ([is_computing] will answer [true]), and other task submission
  will be rejected.

  A task is represented as a continuation, with a coqtop [handle]
  as first argument, and a final inner continuation as 2nd argument.
  This inner continuation should be runned at the end of the task.
  Any exception occuring within the task will trigger a coqtop reset.
*)

type void
type 'a task

val return : 'a -> 'a task
(** Monadic return of values as tasks. *)

val bind : 'a task -> ('a -> 'b task) -> 'b task
(** Monadic binding of tasks *)

val lift : (unit -> 'a) -> 'a task
(** Return the impertative computation waiting to be processed. *)

val seq : unit task -> 'a task -> 'a task
(** Sequential composition *)

(** Check if coqtop is computing, i.e. already has a current task *)
val is_computing : coqtop -> bool

(** * Starting / signaling / ending a real coqtop sub-process *)

(** Create a coqtop process with some command-line arguments. *)
val spawn_coqtop : string list -> coqtop

(** Register a handler called when a coqtop dies (badly or on purpose) *)
type reset_kind = Planned | Unexpected
val set_reset_handler : coqtop -> (reset_kind -> unit task) -> unit

(** Finish initializing a freshly spawned coqtop, by running a first task on it.
    The task should run its inner continuation at the end. *)
val init_coqtop : coqtop -> unit task -> unit

(** Interrupt the current computation of coqtop. *)
val break_coqtop : coqtop -> unit

(** Close coqtop. Subsequent requests will be discarded. Hook ignored. *)
val close_coqtop : coqtop -> unit

(** Reset coqtop. Pending requests will be discarded. The reset handler
    of coqtop will be called with [Planned] as first argument *)
val reset_coqtop : coqtop -> unit

(** In win32, we'll use a different kill function than Unix.kill *)

val killer : (int -> unit) ref
val soft_killer : (int -> unit) ref
val interrupter : (int -> unit) ref

(** [set_final_countdown] triggers an exit of coqide after
    some last cycles for closing remaining coqtop zombies *)

val final_countdown : unit -> unit

(** * Coqtop commmunication *)

(** Try to schedule a task on a coqtop. If coqtop is available, the task
    callback is run (asynchronously), otherwise the [(unit->unit)] callback
    is triggered.
    - If coqtop ever dies during the computation, this function restarts coqtop
      and calls the restart hook with the fresh coqtop.
    - If the argument function raises an exception, a coqtop reset occurs.
    - The task may be discarded if a [close_coqtop] or [reset_coqtop] occurs
      before its completion.
    - The task callback should run its inner continuation at the end. *)

val try_grab : coqtop -> unit task -> (unit -> unit) -> unit

(** * Atomic calls to coqtop

  These atomic calls can be combined to form arbitrary multi-call tasks.
  They correspond to the protocol calls (cf [Serialize] for more details).
  Note that each call is asynchronous: it will return immediately,
  but the inner callback will be executed later to handle the call answer
  when this answer is available.
  Except for interp, we use the default logger for any call. *)

type 'a query = 'a Interface.value task

val interp : ?logger:Ideutils.logger -> ?raw:bool -> ?verbose:bool ->
  string -> string query
val rewind : int -> int query
val status : Interface.status query
val goals : Interface.goals option query
val evars : Interface.evar list option query
val hints : (Interface.hint list * Interface.hint) option query
val inloadpath : string -> bool query
val mkcases : string -> string list list query
val search : Interface.search_flags -> string Interface.coq_object list query

(** A specialized version of [raw_interp] dedicated to set/unset options. *)

module PrintOpt :
sig
  type t (** Representation of an option *)

  type bool_descr = { opts : t list; init : bool; label : string }

  val bool_items : bool_descr list

  val set : t -> bool -> unit
  val set_printing_width : int -> unit

  (** [enforce] transmits to coq the current option values.
      It is also called by [goals] and [evars] above. *)

  val enforce : unit task
end

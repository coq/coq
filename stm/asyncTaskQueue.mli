(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Default flags for workers *)
val async_proofs_flags_for_workers : string list ref

(** This file provides an API for defining and managing a queue of
    tasks to be done by external workers.

    A queue of items of type [task] is maintained, then for each task,
    a request is generated, then sent to a worker using marshalling.

    The workers will then eventually return a result, using marshalling
    again:
     ____ ____ ____                    ________
    | T1 | T2 | T3 | => [request ] => | Worker |
    |____|____|____| <= [response] <= |________|
    | Master Proc. |
    \--------------/

    Thus [request] and [response] must be safely marshallable.

    Operations for managing the task queue are provide, see below
    for more details.

 *)

(** The [Task] module type defines an abstract message-processing
    queue. *)
module type Task = sig

  (** Main description of a task. Elements are stored in the "master"
      process, and then converted into a request.
  *)
  type task

  (** [competence] stores the information about what kind of work a
      worker has completed / has available. *)
  type competence

  (** A worker_status is:

    - [`Fresh] when a worker is born.

    - [`Old of competence]: When a worker ends a job it can either die
      (and be replaced by a fresh new worker) or hang there as an [`Old]
      worker. In such case some data can be carried by the [`Old]
      constructor, typically used to implement [request_of_task].

      This allows to implement both one-shot workers and "persistent"
      ones. E.g. par: is implement using workers that don't
      "reboot". Proof workers do reboot mainly because the vm has some
      C state that cannot be cleared, so you have a real memory leak if
      you don't reboot the worker. *)
  type worker_status = Fresh | Old of competence

  (** Type of input and output data for workers.

      The data must be marshallable as it send through the network
      using [Marshal] . *)
  type request
  type response

  (** UID of the task kind, for -toploop *)
  val name : string ref
  (** Extra arguments of the task kind, for -toploop *)
  val extra_env : unit -> string array

  (** {5 Master API, it is run by the master, on a thread} *)

  (** [request_of_task status t] takes the [status] of the worker
      and a task [t] and creates the corresponding [Some request] to be
      sent to the worker or it is not valid anymore [None]. *)
  val request_of_task : worker_status -> task -> request option

  (** [task_match status tid] Allows to discard tasks based on the
      worker status.  *)
  val task_match : worker_status -> task -> bool

  (** [use_response status t out]

      For a response [out] to a task [t] with [status] we can choose
      to end the worker of to keep it alive with some data and
      immediately inject extra tasks in the queue.

      For example, the proof worker runs a proof and finds an error,
      the response signals that, e.g.

      [ReponseError {state = 34; msg = "oops"}]

      When the manager uses such a response he can tell the worker to
      stay there and inject into the queue an extra task requesting
      state 33 (to implement efficient proof repair).  *)
  val use_response : worker_status -> task -> response ->
    [ `Stay of competence * task list | `End ]

  (** [on_marshal_error err_msg tid] notifies of marshaling failure. *)
  val on_marshal_error : string -> task -> unit

  (** [on_task_cancellation_or_expiration_or_slave_death tid]

      These functions are meant to parametrize the worker manager on
      the actions to be taken when things go wrong or are cancelled
      (you can kill a worker in CoqIDE, or using kill -9...)

      E.g. master can decide to inhabit the (delegate) Future.t with a
      closure (to be run in master), i.e. make the document still
      checkable. This is what I do for marshaling errors.  *)
  val on_task_cancellation_or_expiration_or_slave_death : task option -> unit

  (** [forward_feedback fb] sends fb to all the workers. *)
  val forward_feedback : Feedback.feedback -> unit

  (** {5 Worker API, it is run by worker, on a different fresh
      process} *)

  (** [perform in] synchronously processes a request [in] *)
  val perform : request -> response

  (** debugging *)
  val name_of_task : task -> string
  val name_of_request : request -> string

end

(** [cancel_switch] to be flipped to true by anyone to signal the task
    is not relevant anymore. When the STM performs an undo/edit-at, it
    crawls the document and flips these flags (the Qed node carries a
    pointer to the flag IIRC).
*)
type cancel_switch = bool ref

(** Client-side functor. [MakeQueue T] creates a task queue for task [T]  *)
module MakeQueue(T : Task) () : sig

  (** [queue] is the abstract queue type. *)
  type queue

  (** [create n] will initialize the queue with [n] workers. If [n] is
      0, the queue won't spawn any process, working in a lazy local
      manner. [not imposed by the this API] *)
  val create : int -> queue

  (** [destroy q] Deallocates [q], cancelling all pending tasks. *)
  val destroy : queue -> unit

  (** [n_workers q] returns the number of workers of [q] *)
  val n_workers : queue -> int

  (** [enqueue_task q t ~cancel_switch] schedules [t] for execution in
      [q]. [cancel_switch] can be flipped to true to cancel the task. *)
  val enqueue_task : queue -> T.task -> cancel_switch:cancel_switch -> unit

  (** [join q] blocks until the task queue is empty *)
  val join : queue -> unit

  (** [cancel_all q] Cancels all tasks *)
  val cancel_all : queue -> unit

  (** [cancel_worker q wid] cancels a particular worker [wid] *)
  val cancel_worker : queue -> WorkerPool.worker_id -> unit

  (** [set_order q cmp] reorders [q] using ordering [cmp] *)
  val set_order : queue -> (T.task -> T.task -> int) -> unit

  (** [broadcast q]

      This is nasty. Workers can be picky, e.g. pick tasks only when
      they are "on screen". Of course the screen is scrolled, and that
      changes the potential choice of workers to pick up a task or
      not.

      This function wakes up the workers (the managers) that give a
      look (again) to the tasks in the queue.

      The STM calls it when the perspective (as in PIDE) changes.

      A problem here is that why task_match has access to the
      competence data in order to decide if the task is palatable to
      the worker or not... such data is local to the worker (manager).
      The perspective is global, so it does not quite fit this
      picture. This API to make all managers reconsider the tasks in
      the queue is the best I could came up with.

      This API is crucial to Coqoon (or any other UI that invokes
      Stm.finish eagerly but wants the workers to "focus" on the visible
      part of the document).
  *)
  val broadcast : queue -> unit

  (** [snapshot q] Takes a snapshot (non destructive but waits until
      all workers are enqueued) *)
  val snapshot : queue -> T.task list

  (** [clear q] Clears [q], only if the worker prool is empty *)
  val clear : queue -> unit

  (** [with_n_workers n f] create a queue, run the function, destroy
      the queue. The user should call join *)
  val with_n_workers : int -> (queue -> 'a) -> 'a

end

(** Server-side functor. [MakeWorker T] creates the server task
    dispatcher. *)
module MakeWorker(T : Task) () : sig

  (** [init_stdout ()] is called at [Coqtop.toploop_init] time. *)
  val init_stdout : unit -> unit

  (** [main_loop ()] is called at [Coqtop.toploop_run] time. *)
  val main_loop : unit -> unit

end

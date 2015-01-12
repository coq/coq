(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type 'a worker_status = [ `Fresh | `Old of 'a ]

module type Task = sig

  type task
  type competence

  (* Marshallable *)
  type request
  type response

  val name : string ref (* UID of the task kind, for -toploop *)
  val extra_env : unit -> string array

  (* run by the master, on a thread *)
  val request_of_task : competence worker_status -> task -> request option
  val task_match : competence worker_status -> task -> bool
  val use_response :
    competence worker_status -> task -> response ->
      [ `Stay of competence * task list | `End ]
  val on_marshal_error : string -> task -> unit
  val on_task_cancellation_or_expiration_or_slave_death : task option -> unit
  val forward_feedback : Feedback.feedback -> unit
 
  (* run by the worker *)
  val perform : request -> response

  (* debugging *)
  val name_of_task : task -> string
  val name_of_request : request -> string

end

type expiration = bool ref

module MakeQueue(T : Task) : sig

  type queue

  (* Number of workers, 0 = lazy local *)
  val create : int -> queue
  val destroy : queue -> unit

  val n_workers : queue -> int

  val enqueue_task : queue -> T.task * expiration -> unit

  (* blocking function that waits for the task queue to be empty *)
  val join : queue -> unit
  val cancel_all : queue -> unit

  val cancel_worker : queue -> WorkerPool.worker_id -> unit

  val set_order : queue -> (T.task -> T.task -> int) -> unit

  (* Take a snapshot (non destructive but waits until all workers are
   * enqueued) *)
  val snapshot : queue -> T.task list

  (* Clears the queue, only if the worker prool is empty *)
 val clear : queue -> unit
 
  (* create a queue, run the function, destroy the queue.
   * the user should call join *)
  val with_n_workers : int -> (queue -> 'a) -> 'a

end

module MakeWorker(T : Task) : sig

  val main_loop : unit -> unit
  val init_stdout : unit -> unit
  
end

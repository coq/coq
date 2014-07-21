(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type Task = sig

  type task

  (* Marshallable *)
  type request
  type response

  val name : string (* UID of the task kind, for -toploop *)
  val extra_env : unit -> string array

  (* run by the master, on a thread *)
  val request_of_task : [ `Fresh | `Old ] -> task -> request option
  val use_response : task -> response -> [ `Stay | `StayReset ]
  val on_marshal_error : string -> task -> unit
  val on_slave_death : task option -> [ `Exit of int | `Stay ]
  val on_task_cancellation_or_expiration : task option -> unit
  val forward_feedback : Stateid.t -> Feedback.feedback_content -> unit
 
  (* run by the worker *)
  val perform : request -> response

  (* debugging *)
  val name_of_task : task -> string
  val name_of_request : request -> string

end

type cancel_switch = bool ref

module Make(T : Task) : sig

  (* Number of workers, 0 = lazy local *)
  val init : int -> unit
  val destroy : unit -> unit

  val with_n_workers :
    int -> (join:(unit -> unit) -> cancel_all:(unit -> unit) -> 'a) -> 'a

  val n_workers : unit -> int

  val enqueue_task : T.task -> cancel_switch -> unit

  (* blocking function that waits for the task queue to be empty *)
  val join : unit -> unit
  val cancel_all : unit -> unit

  (* slave process main loop *)
  val slave_main_loop : (unit -> unit) -> unit
  val slave_init_stdout : unit -> unit
  
  val cancel_worker : string -> unit

  val set_order : (T.task -> T.task -> int) -> unit

  val dump : unit -> T.task list

end

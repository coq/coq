(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type sentence_id = Stateid.t
type link
(* Coqtop module not in scope *)
type ('a,'b) coqtop_extra_args_fn = opts:'b -> string list -> 'a * string list
(** Promises that can be resolved across process boundaries *)
type 'a remote_mapping

module type Job = sig
  type t
  val name : string
  val binary_name : string
  val pool_size : int
end

module Make (Job : Job) : sig


(* When resolved (asynchronously) the hook is called to notify the UI *)
val empty_remote_mapping :
  progress_hook:(unit -> unit Lwt.t) -> 'a remote_mapping

(* Like Lwt.wait() but remotely resolvable *)
val lwt_remotely_wait : 'a remote_mapping -> sentence_id -> 'a remote_mapping * ('a Lwt.t * 'a Lwt.u)

(* Event for the main loop *)
type event
type events = event Lwt.t list

val handle_event : event -> events Lwt.t
val pr_event : event -> Pp.t

(* When a worker is available [job] is called and when it returns the
   event becomes ready; in turn the event triggers the action.
   If we can fork, job is passed to fork_action. Things are automatically
   wired up so that all the promises in the mapping are remotely fullfilled.

   Otherwise we create a new process. That process must be a Coq toplevel (see
   Coqtop module) parsing extra argument using [parse_options] then sets up
   a link with master via [setup_plumbing] and finally calls
   [new_process_workers] to setup remote promise fullfillment.
   See ExecutionManager.init_worker *)
val worker_available :
  job:(unit -> ('a remote_mapping * Job.t) Lwt.t) ->
  fork_action:(Job.t  -> unit Lwt.t) ->
  events

(* for worker toplevels *)
type options
val parse_options : (options,'b) coqtop_extra_args_fn
(* the sentence ids of the remote_mapping being delegated *)
val setup_plumbing : options -> (sentence_id list * link * Job.t) Lwt.t
val new_process_worker : 'a remote_mapping -> link -> unit

end

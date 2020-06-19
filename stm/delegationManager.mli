(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Promises that can be resolved across process boundaries *)
type 'a remote_mapping

(* When resolved (asynchronously) the hook is called to notify the UI *)
val empty_remote_mapping :
  progress_hook:(unit -> unit Lwt.t) -> 'a remote_mapping

(* Like Lwt.wait() but remotely resolvable *)
type sentence_id = Stateid.t
val lwt_remotely_wait : 'a remote_mapping -> sentence_id -> 'a remote_mapping * ('a Lwt.t * 'a Lwt.u)

(* Event for the main loop *)
type event
type 'a events = ([> `DelegationManager of event ] as 'a) Lwt.t list

val handle_event : event -> 'a events Lwt.t

(* When a worker is available [job] is called and when it returns the
   event becomes ready; in turn the event triggers the action.
   If we can fork, job is passed to fork_action. Things are automatically
   wired up so that all the promises in the mapping are remotely fullfilled.

   Otherwise we create a new process passing the -vscoqtop_master <port>
   flag. The process must connect back to localhost:port, it then receives
   the marshalable_remote_mapping corresponding to the job and the job.
   This process has then to recreate a remote_mapping and call
   new_process_worker to set up remote promise fullfillment. See
   ExecutionManager.init_worker *)
val worker_available :
  job:(unit -> ('a remote_mapping * 'job) Lwt.t) ->
  fork_action:('job  -> unit Lwt.t) ->
  process_action:string ->
  'c events

(* for worker toplevels *)
type link = {
  write_to :  Lwt_io.output_channel;
  read_from:  Lwt_io.input_channel;
}

type 'a marshalable_remote_mapping
val marshalable_remote_mapping : 'a remote_mapping -> 'a marshalable_remote_mapping
val new_process_worker : 'a remote_mapping -> link -> unit
val ids_of_mapping : 'a marshalable_remote_mapping -> sentence_id list

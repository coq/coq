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
val lwt_remotely_wait : 'a remote_mapping -> 'a remote_mapping * ('a Lwt.t * 'a Lwt.u)

(* Event for the main loop *)
type event
type 'a events = ([> `DelegationManager of event ] as 'a) Lwt.t list

val handle_event : event -> 'a events Lwt.t

type role = Master | Worker

(* When a worker is available [job] is called and when it returns the
   event becomes ready; in turn the event triggers the action *)
val worker_available :
  job:(unit -> ('a remote_mapping * 'job) Lwt.t) ->
  action:(role -> 'job  -> unit Lwt.t) ->
  'c events
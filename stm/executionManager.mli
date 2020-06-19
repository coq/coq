(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The execution manager is in charge of the actual execution of tasks (as
    defined by the scheduler), caching execution states and invalidating
    them. *)

open Scheduler
open Document

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

type state
(** Execution state, includes the cache *)

type progress_hook = state option -> unit Lwt.t

val init : Vernacstate.t -> state


val observe : progress_hook -> document -> sentence_id -> state ->
  (state * 'a DelegationManager.events) Lwt.t
val query : sentence_id -> state -> ast -> state

val invalidate : schedule -> sentence_id -> state -> state Lwt.t

val errors : state -> (sentence_id * Loc.t option * string) list
val shift_locs : state -> int -> int -> state
val executed_ids : state -> sentence_id list
val is_executed : state -> sentence_id -> bool
val is_remotely_executed : state -> sentence_id -> bool

val get_parsing_state_after : state -> sentence_id -> Vernacstate.Parser.t option
val get_proofview : state -> sentence_id -> Proof.data option

type job
val worker_main : state -> job -> unit Lwt.t

type execution_status
val new_process_worker : state -> execution_status DelegationManager.marshalable_remote_mapping -> DelegationManager.link -> state
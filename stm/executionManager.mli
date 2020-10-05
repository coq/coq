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

type event
type events = event Lwt.t list

val handle_event : event -> events Lwt.t

val observe : progress_hook -> Document.document -> sentence_id -> state ->
  (state * events) Lwt.t
val query : sentence_id -> state -> ast -> state

val invalidate : schedule -> sentence_id -> state -> state Lwt.t

val errors : state -> (sentence_id * Loc.t option * string) list
val warnings : state -> (sentence_id * Loc.t option * string) list
val shift_locs : state -> int -> int -> state
val executed_ids : state -> sentence_id list
val is_executed : state -> sentence_id -> bool
val is_remotely_executed : state -> sentence_id -> bool

val get_parsing_state_after : state -> sentence_id -> Vernacstate.Parser.t option
val get_proofview : state -> sentence_id -> Proof.data option

val init_master : Vernacstate.t -> state
val handle_feedback : Stateid.t -> Feedback.feedback_content -> state -> state

module WorkerProcess : sig
  type options
  val parse_options : (options,'b) DelegationManager.coqtop_extra_args_fn
  val main : doc_id:int -> st:Vernacstate.t -> options -> unit Lwt.t
end

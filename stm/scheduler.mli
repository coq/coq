(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The scheduler is the component in charge of planning the execution of
    sentences. It also defines the task delegation strategy, and computes
    dependencies between tasks. Scheduling can be done incrementally. *)

type state
(** State for incremental schedule construction *)

val initial_state : state

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

type task =
  | Skip of sentence_id
  | Exec of sentence_id * ast
  | OpaqueProof of sentence_id * sentence_id list
  | Query of sentence_id * ast

type schedule
(** Holds the dependencies among sentences and a schedule to evaluate all
    sentences *)

val initial_schedule : schedule

val schedule_sentence : sentence_id * ast option -> state -> schedule -> state * schedule
(** Identifies the structure of the document and dependencies between sentences
    in order to easily compute the tasks to interpret the a sentence.
    Input sentence is None on parsing error. *)

val task_for_sentence : schedule -> sentence_id -> sentence_id option * task
(** Finds the task to be performed and the state on which the task should run *)

val dependents : schedule -> sentence_id -> Stateid.Set.t
(** Computes what should be invalidated *)

val string_of_schedule : schedule -> string

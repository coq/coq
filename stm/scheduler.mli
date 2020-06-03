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
  | DelegateOpaqueProof of {
      proof_script: sentence_id * ast list;
      section_info: string list;
    }
  | DelegateQuery of sentence_id * ast

type schedule

val initial_schedule : schedule
val schedule_sentence : sentence_id * ast option -> state -> schedule -> state * schedule

val task_for_sentence : schedule -> sentence_id -> sentence_id option * task
val dependents : schedule -> sentence_id -> Stateid.Set.t

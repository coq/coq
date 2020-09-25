(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Tactic interpreters have to register their interpretation function *)
type 'a tactic_interpreter
type interpretable = I : 'a tactic_interpreter * 'a -> interpretable

(** ['a] should be marshallable if ever used with [par:] *)
val register_tactic_interpreter :
  string -> ('a -> unit Proofview.tactic) -> 'a tactic_interpreter

(** Entry point for toplevel tactic expression execution. It calls Proof.solve
    after having interpreted the tactic, and after the tactic runs it
    unfocus as much as needed to put a goal under focus. *)
val solve :
  pstate:Declare.Proof.t ->
  Goal_select.t ->
  info:int option ->
  interpretable ->
  with_end_tac:bool ->
  Declare.Proof.t

(** [par: tac] runs tac on all goals, possibly in parallel using a worker pool.
    If tac is [abstract tac1], then [abstract] is passed
    explicitly to the solver and [tac1] passed to worker since it is up to
    master to opacify the sub proofs produced by the workers. *)
type parallel_solver =
  pstate:Declare.Proof.t ->
  info:int option ->
  interpretable ->
  abstract:bool -> (* the tactic result has to be opacified as per abstract *)
  with_end_tac:bool ->
  Declare.Proof.t

(** Entry point when the goal selector is par: *)
val solve_parallel : parallel_solver

(** By default par: is implemented with all: (sequential).
    The STM and LSP document manager provide "more parallel" implementations *)
val set_par_implementation : parallel_solver -> unit

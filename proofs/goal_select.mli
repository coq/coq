(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(* spiwack: I'm choosing, for now, to have [goal_selector] be a
   different type than [goal_reference] mostly because if it makes sense
   to print a goal that is out of focus (or already solved) it doesn't
   make sense to apply a tactic to it. Hence it the types may look very
   similar, they do not seem to mean the same thing. *)
type t =
  | SelectAlreadyFocused
  | SelectNth of int
  | SelectList of (int * int) list
  | SelectId of Id.t
  | SelectAll

val pr_goal_selector : t -> Pp.t
val get_default_goal_selector : unit -> t

val tclSELECT : ?nosuchgoal:'a Proofview.tactic -> t -> 'a Proofview.tactic -> 'a Proofview.tactic

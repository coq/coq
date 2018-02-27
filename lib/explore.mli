(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 Search strategies. } *)

(** {6 ... } *)
(** A search problem implements the following signature [SearchProblem].
    [state] is the type of states of the search tree.
    [branching] is the branching function; if [branching s] returns an
    empty list, then search from [s] is aborted; successors of [s] are
    recursively searched in the order they appear in the list.
    [success] determines whether a given state is a success.

    [pp] is a pretty-printer for states used in debugging versions of the
    search functions. *)

module type SearchProblem = sig

  type state

  val branching : state -> state list

  val success : state -> bool

  val pp : state -> Pp.t

end

(** {6 ... } *)
(** Functor [Make] returns some search functions given a search problem.
    Search functions raise [Not_found] if no success is found.
    States are always visited in the order they appear in the
    output of [branching] (whatever the search method is).
    Debugging versions of the search functions print the position of the
    visited state together with the state it-self (using [S.pp]). *)

module Make : functor(S : SearchProblem) -> sig

  val depth_first : S.state -> S.state
  val debug_depth_first : S.state -> S.state

  val breadth_first : S.state -> S.state
  val debug_breadth_first : S.state -> S.state

end

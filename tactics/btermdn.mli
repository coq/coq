(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pattern

(** Discrimination nets with bounded depth. *)

(** This module registers actions (typically tactics) mapped to patterns *)

(** Patterns are stocked linearly as the list of its node in prefix
order in such a way patterns having the same prefix have this common
prefix shared and the seek for the action associated to the patterns
that a term matches are found in time proportional to the maximal
number of nodes of the patterns matching the term. The [TransparentState.t]
indicates which constants and variables can be considered as rigid.
These dnets are able to cope with existential variables as well, which match
[Everything]. *)

module Make :
  functor (Z : Map.OrderedType) ->
sig
  type t

  type pattern

  val pattern : Environ.env -> TransparentState.t option -> constr_pattern -> pattern
  val pattern_syntactic : Environ.env -> constr_pattern -> pattern
  val constr_pattern : Environ.env -> Evd.evar_map -> TransparentState.t option -> EConstr.t -> pattern

  val empty : t

  val add : t -> pattern -> Z.t -> t
  val rmv : t -> pattern -> Z.t -> t

  val lookup : Environ.env -> Evd.evar_map -> TransparentState.t option -> t -> EConstr.constr -> Z.t list
end

val dnet_depth : int ref

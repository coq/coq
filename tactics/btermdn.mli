(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pattern
open Names

(** Discrimination nets with bounded depth. *)

(** This module registers actions (typically tactics) mapped to patterns *)

(** Patterns are stocked linearly as the list of its node in prefix
order in such a way patterns having the same prefix have this common
prefix shared and the seek for the action associated to the patterns
that a term matches are found in time proportional to the maximal
number of nodes of the patterns matching the term. The [transparent_state]
indicates which constants and variables can be considered as rigid.
These dnets are able to cope with existential variables as well, which match
[Everything]. *)

module Make :
  functor (Z : Map.OrderedType) ->
sig
  type t

  val empty : t

  val add : transparent_state option -> t -> (constr_pattern * Z.t) -> t
  val rmv : transparent_state option -> t -> (constr_pattern * Z.t) -> t

  val lookup : Evd.evar_map -> transparent_state option -> t -> EConstr.constr -> Z.t list
  val app : (Z.t -> unit) -> t -> unit
end

val dnet_depth : int ref

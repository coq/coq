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
open EConstr
open Constrexpr
open Tactypes

val lemInv_clause :
  quantified_hypothesis -> constr -> Id.t list -> unit Proofview.tactic

val add_inversion_lemma_exn : poly:bool ->
  Id.t -> constr_expr -> Sorts.family -> bool -> (Id.t -> unit Proofview.tactic) ->
    unit

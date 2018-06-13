(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

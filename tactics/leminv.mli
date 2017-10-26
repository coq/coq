(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open EConstr
open Constrexpr
open Misctypes

val lemInv_clause :
  quantified_hypothesis -> constr -> Id.t list -> unit Proofview.tactic

val add_inversion_lemma_exn :
  Id.t -> constr_expr -> Sorts.family -> bool -> (Id.t -> unit Proofview.tactic) ->
    unit

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Term
open Misctypes
open Tacexpr

type inversion_status = Dep of constr option | NoDep

val inv_clause :
  inversion_kind -> or_and_intro_pattern option -> Id.t list ->
    quantified_hypothesis -> unit Proofview.tactic

val inv : inversion_kind -> or_and_intro_pattern option ->
  quantified_hypothesis -> unit Proofview.tactic

val dinv : inversion_kind -> constr option ->
  or_and_intro_pattern option -> quantified_hypothesis -> unit Proofview.tactic

val inv_tac : Id.t -> unit Proofview.tactic
val inv_clear_tac : Id.t -> unit Proofview.tactic
val dinv_tac : Id.t -> unit Proofview.tactic
val dinv_clear_tac : Id.t -> unit Proofview.tactic

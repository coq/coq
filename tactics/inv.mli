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
open Tactypes

type inversion_status = Dep of constr option | NoDep

type inversion_kind =
  | SimpleInversion
  | FullInversion
  | FullInversionClear

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

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Proof_type
open Evd
open Hints

val hintbases : hint_db_name list option Pcoq.Gram.entry

val wit_hintbases : hint_db_name list option Genarg.uniform_genarg_type

val e_assumption : unit Proofview.tactic

val registered_e_assumption : unit Proofview.tactic

val e_give_exact : ?flags:Unification.unify_flags -> constr -> unit Proofview.tactic

val gen_eauto : ?debug:Tacexpr.debug -> bool * int -> Tacexpr.delayed_open_constr list ->
  hint_db_name list option -> tactic

val eauto_with_bases :
  ?debug:Tacexpr.debug ->
  bool * int ->
  Tacexpr.delayed_open_constr list -> hint_db list -> Proof_type.tactic

val autounfold : hint_db_name list -> Locus.clause -> tactic

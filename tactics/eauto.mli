(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Proof_type
open Hints

val e_assumption : unit Proofview.tactic

val registered_e_assumption : unit Proofview.tactic

val e_give_exact : ?flags:Unification.unify_flags -> constr -> unit Proofview.tactic

val prolog_tac : Tacexpr.delayed_open_constr list -> int -> unit Proofview.tactic

val gen_eauto :
  ?debug:Tacexpr.debug -> ?dfs:bool -> ?depth:int -> Tacexpr.delayed_open_constr list ->
  hint_db_name list option -> unit Proofview.tactic

val eauto_with_bases :
  ?debug:Tacexpr.debug ->
  bool * int ->
  Tacexpr.delayed_open_constr list -> hint_db list -> Proof_type.tactic

val autounfold : hint_db_name list -> Locus.clause -> unit Proofview.tactic
val autounfold_tac : hint_db_name list option -> Locus.clause -> unit Proofview.tactic
val autounfold_one : hint_db_name list -> Locus.hyp_location option -> unit Proofview.tactic


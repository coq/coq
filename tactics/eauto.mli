(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Proof_type
open Auto
open Evd
open Hints

val hintbases : hint_db_name list option Pcoq.Gram.entry

val wit_hintbases : hint_db_name list option Genarg.uniform_genarg_type

val wit_auto_using :
  (Tacexpr.open_constr_expr list,
  Tacexpr.open_glob_constr list, Evd.open_constr list)
    Genarg.genarg_type


val e_assumption : tactic

val registered_e_assumption : tactic

val e_give_exact : ?flags:Unification.unify_flags -> constr -> tactic

val gen_eauto : ?debug:Tacexpr.debug -> bool * int -> open_constr list ->
  hint_db_name list option -> tactic

val eauto_with_bases :
  ?debug:Tacexpr.debug ->
  bool * int ->
  open_constr list -> hint_db list -> Proof_type.tactic

val autounfold : hint_db_name list -> Locus.clause -> tactic

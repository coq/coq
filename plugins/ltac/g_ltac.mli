(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val genarg_of_unit : unit -> Genarg.rlevel Genarg.generic_argument

val genarg_of_int : int -> Genarg.rlevel Genarg.generic_argument

val genarg_of_ipattern :
  Constrexpr.constr_expr Tactypes.intro_pattern_expr CAst.t ->
  Genarg.rlevel Genarg.generic_argument

val genarg_of_uconstr :
  Constrexpr.constr_expr -> Genarg.rlevel Genarg.generic_argument

val in_tac :
  Tacexpr.raw_tactic_expr ->
  Genarg.rlevel Genarg.generic_argument

val tactic_mode : Vernacexpr.vernac_expr Pcoq.Entry.t

val tacdef_body : Tacexpr.tacdef_body Pcoq.Entry.t

val classic_proof_mode : Pvernac.proof_mode

val hint : Vernacexpr.hints_expr Pcoq.Entry.t

val wit_ltac_info : (int, unit, unit) Genarg.genarg_type

val ltac_info : int Pcoq.Entry.t

val wit_ltac_tactic_level : (int, unit, unit) Genarg.genarg_type

val ltac_tactic_level : int Pcoq.Entry.t

val wit_ltac_production_sep : (string, unit, unit) Genarg.genarg_type

val ltac_production_sep : string Pcoq.Entry.t

val wit_ltac_production_item :
  ((string * string option)
   Tacentries.grammar_tactic_prod_item_expr, unit, unit)
  Genarg.genarg_type

val ltac_production_item :
  (string * string option)
  Tacentries.grammar_tactic_prod_item_expr Pcoq.Entry.t

val wit_ltac_tacdef_body :
  (Tacexpr.tacdef_body, unit, unit) Genarg.genarg_type

val ltac_tacdef_body : Tacexpr.tacdef_body Pcoq.Entry.t

(** extraargs needs g_ltac to initialize tactic_value *)
val for_extraargs : unit

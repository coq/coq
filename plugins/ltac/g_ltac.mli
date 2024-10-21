(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

val tactic_mode : Vernacexpr.vernac_expr Procq.Entry.t

val tacdef_body : Tacexpr.tacdef_body Procq.Entry.t

val classic_proof_mode : Pvernac.proof_mode

val hint : Vernacexpr.hints_expr Procq.Entry.t

val wit_ltac_selector : Goal_select.t Genarg.vernac_genarg_type

val ltac_selector : Goal_select.t Procq.Entry.t

val wit_ltac_info : int Genarg.vernac_genarg_type

val ltac_info : int Procq.Entry.t

val wit_ltac_use_default : bool Genarg.vernac_genarg_type

val ltac_use_default : bool Procq.Entry.t

val wit_ltac_tactic_level : int Genarg.vernac_genarg_type

val ltac_tactic_level : int Procq.Entry.t

val wit_ltac_production_sep : string Genarg.vernac_genarg_type

val ltac_production_sep : string Procq.Entry.t

val wit_ltac_production_item :
  (string * string option) Tacentries.grammar_tactic_prod_item_expr
    Genarg.vernac_genarg_type

val ltac_production_item :
  (string * string option)
  Tacentries.grammar_tactic_prod_item_expr Procq.Entry.t

val wit_ltac_tacdef_body :
  Tacexpr.tacdef_body Genarg.vernac_genarg_type

val ltac_tacdef_body : Tacexpr.tacdef_body Procq.Entry.t

(** extraargs needs g_ltac to initialize tactic_value *)
val for_extraargs : unit

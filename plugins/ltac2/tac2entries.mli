(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Libnames
open Tac2expr

(** {5 Toplevel definitions} *)

val register_ltac : ?deprecation:Deprecation.t -> ?local:bool -> ?mut:bool -> rec_flag ->
  (Names.lname * raw_tacexpr) list -> unit

val register_type : ?local:bool -> rec_flag ->
  (qualid * redef_flag * raw_quant_typedef) list -> unit

val register_primitive : ?deprecation:Deprecation.t -> ?local:bool ->
  Names.lident -> raw_typexpr -> ml_tactic_name -> unit

val register_struct : Attributes.vernac_flags -> strexpr -> unit

type notation_interpretation_data

val register_notation : Attributes.vernac_flags -> sexpr list ->
  int option -> raw_tacexpr -> notation_interpretation_data

val register_notation_interpretation : notation_interpretation_data -> unit

val perform_eval : pstate:Declare.Proof.t option -> raw_tacexpr -> unit

(** {5 Notations} *)

type scope_rule =
| ScopeRule : (raw_tacexpr, _, 'a) Pcoq.Symbol.t * ('a -> raw_tacexpr) -> scope_rule

type scope_interpretation = sexpr list -> scope_rule

val register_scope : Id.t -> scope_interpretation -> unit
(** Create a new scope with the provided name *)

val parse_scope : sexpr -> scope_rule
(** Use this to interpret the subscopes for interpretation functions *)

(** {5 Inspecting} *)

val print_located_tactic : Libnames.qualid -> unit
(** Display the absolute name of a tactic. *)

val print_ltac2 : Libnames.qualid -> unit
(** Display the definition of a tactic. *)

val print_signatures : unit -> unit
(** Print types of all definitions in scope. *)

(** {5 Eval loop} *)

(** Evaluate a tactic expression in the current environment *)
val call : pstate:Declare.Proof.t -> Goal_select.t option -> with_end_tac:bool -> raw_tacexpr
  -> Declare.Proof.t

val call_par : pstate:Declare.Proof.t -> with_end_tac:bool -> raw_tacexpr
  -> Declare.Proof.t

(** {5 Toplevel exceptions} *)

val backtrace : backtrace Exninfo.t

(** {5 Parsing entries} *)

module Pltac :
sig
val ltac2_expr : raw_tacexpr Pcoq.Entry.t
val tac2expr_in_env : (Id.t CAst.t list * raw_tacexpr) Pcoq.Entry.t

(** Quoted entries. To be used for complex notations. *)

open Tac2qexpr

val q_ident : Id.t CAst.t or_anti Pcoq.Entry.t
val q_bindings : bindings Pcoq.Entry.t
val q_with_bindings : bindings Pcoq.Entry.t
val q_intropattern : intro_pattern Pcoq.Entry.t
val q_intropatterns : intro_pattern list CAst.t Pcoq.Entry.t
val q_destruction_arg : destruction_arg Pcoq.Entry.t
val q_induction_clause : induction_clause Pcoq.Entry.t
val q_conversion : conversion Pcoq.Entry.t
val q_rewriting : rewriting Pcoq.Entry.t
val q_clause : clause Pcoq.Entry.t
val q_dispatch : dispatch Pcoq.Entry.t
val q_occurrences : occurrences Pcoq.Entry.t
val q_reference : reference or_anti Pcoq.Entry.t
val q_strategy_flag : strategy_flag Pcoq.Entry.t
val q_constr_matching : constr_matching Pcoq.Entry.t
val q_goal_matching : goal_matching Pcoq.Entry.t
val q_hintdb : hintdb Pcoq.Entry.t
val q_move_location : move_location Pcoq.Entry.t
val q_pose : pose Pcoq.Entry.t
val q_assert : assertion Pcoq.Entry.t
end

(** {5 Hooks} *)

val register_constr_quotations : (unit -> unit) Hook.t

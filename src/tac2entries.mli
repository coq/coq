(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Libnames
open Tac2expr

(** {5 Toplevel definitions} *)

val register_ltac : ?local:bool -> ?mut:bool -> rec_flag ->
  (Names.lname * raw_tacexpr) list -> unit

val register_type : ?local:bool -> rec_flag ->
  (qualid * redef_flag * raw_quant_typedef) list -> unit

val register_primitive : ?local:bool ->
  Names.lident -> raw_typexpr -> ml_tactic_name -> unit

val register_struct : ?local:bool -> strexpr -> unit

val register_notation : ?local:bool -> sexpr list -> int option ->
  raw_tacexpr -> unit

(** {5 Notations} *)

type scope_rule =
| ScopeRule : (raw_tacexpr, 'a) Extend.symbol * ('a -> raw_tacexpr) -> scope_rule

type scope_interpretation = sexpr list -> scope_rule

val register_scope : Id.t -> scope_interpretation -> unit
(** Create a new scope with the provided name *)

val parse_scope : sexpr -> scope_rule
(** Use this to interpret the subscopes for interpretation functions *)

(** {5 Inspecting} *)

val print_ltac : Libnames.qualid -> unit

(** {5 Eval loop} *)

(** Evaluate a tactic expression in the current environment *)
val call : default:bool -> raw_tacexpr -> unit

(** {5 Toplevel exceptions} *)

val backtrace : backtrace Exninfo.t

(** {5 Parsing entries} *)

module Pltac :
sig
val tac2expr : raw_tacexpr Pcoq.Gram.entry

(** Quoted entries. To be used for complex notations. *)

open Tac2qexpr

val q_ident : Id.t CAst.t or_anti Pcoq.Gram.entry
val q_bindings : bindings Pcoq.Gram.entry
val q_with_bindings : bindings Pcoq.Gram.entry
val q_intropattern : intro_pattern Pcoq.Gram.entry
val q_intropatterns : intro_pattern list CAst.t Pcoq.Gram.entry
val q_destruction_arg : destruction_arg Pcoq.Gram.entry
val q_induction_clause : induction_clause Pcoq.Gram.entry
val q_conversion : conversion Pcoq.Gram.entry
val q_rewriting : rewriting Pcoq.Gram.entry
val q_clause : clause Pcoq.Gram.entry
val q_dispatch : dispatch Pcoq.Gram.entry
val q_occurrences : occurrences Pcoq.Gram.entry
val q_reference : reference or_anti Pcoq.Gram.entry
val q_strategy_flag : strategy_flag Pcoq.Gram.entry
val q_constr_matching : constr_matching Pcoq.Gram.entry
val q_goal_matching : goal_matching Pcoq.Gram.entry
val q_hintdb : hintdb Pcoq.Gram.entry
val q_move_location : move_location Pcoq.Gram.entry
val q_pose : pose Pcoq.Gram.entry
val q_assert : assertion Pcoq.Gram.entry
end

(** {5 Hooks} *)

val register_constr_quotations : (unit -> unit) Hook.t

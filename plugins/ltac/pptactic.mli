(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module implements pretty-printers for ltac_expr syntactic
    objects and their subcomponents. *)

open Genarg
open Geninterp
open Names
open Environ
open Constrexpr
open Genintern
open Tacexpr
open Tactypes

type 'a grammar_tactic_prod_item_expr =
| TacTerm of string
| TacNonTerm of ('a * Names.Id.t option) Loc.located

type 'a raw_extra_genarg_printer =
  Environ.env -> Evd.evar_map ->
  (Environ.env -> Evd.evar_map -> constr_expr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> constr_expr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> entry_relative_level -> raw_tactic_expr -> Pp.t) ->
  'a -> Pp.t

type 'a glob_extra_genarg_printer =
  Environ.env -> Evd.evar_map ->
  (Environ.env -> Evd.evar_map -> glob_constr_and_expr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> glob_constr_and_expr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> entry_relative_level -> glob_tactic_expr -> Pp.t) ->
  'a -> Pp.t

type 'a extra_genarg_printer =
  Environ.env -> Evd.evar_map ->
  (Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> entry_relative_level -> Val.t -> Pp.t) ->
  'a -> Pp.t

type 'a raw_extra_genarg_printer_with_level =
  Environ.env -> Evd.evar_map ->
  (Environ.env -> Evd.evar_map -> constr_expr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> constr_expr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> entry_relative_level -> raw_tactic_expr -> Pp.t) ->
  entry_relative_level -> 'a -> Pp.t

type 'a glob_extra_genarg_printer_with_level =
  Environ.env -> Evd.evar_map ->
  (Environ.env -> Evd.evar_map -> glob_constr_and_expr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> glob_constr_and_expr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> entry_relative_level -> glob_tactic_expr -> Pp.t) ->
  entry_relative_level -> 'a -> Pp.t

type 'a extra_genarg_printer_with_level =
  Environ.env -> Evd.evar_map ->
  (Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.t) ->
  (Environ.env -> Evd.evar_map -> entry_relative_level -> Val.t -> Pp.t) ->
  entry_relative_level -> 'a -> Pp.t

val declare_extra_genarg_pprule :
  ('a, 'b, 'c) genarg_type ->
  'a raw_extra_genarg_printer ->
  'b glob_extra_genarg_printer ->
  'c extra_genarg_printer -> unit

val declare_extra_genarg_pprule_with_level :
  ('a, 'b, 'c) genarg_type ->
  'a raw_extra_genarg_printer_with_level ->
  'b glob_extra_genarg_printer_with_level ->
  'c extra_genarg_printer_with_level ->
  (* surrounded *) entry_relative_level -> (* non-surrounded *) entry_relative_level -> unit

type grammar_terminals = Genarg.ArgT.any Extend.user_symbol grammar_tactic_prod_item_expr list

type pp_tactic = {
  pptac_level : int;
  pptac_prods : grammar_terminals;
}

val pr_goal_selector : toplevel:bool -> Goal_select.t -> Pp.t

val declare_notation_tactic_pprule : KerName.t -> pp_tactic -> unit

val pr_with_occurrences :
  ('v -> Pp.t) -> ('a -> Pp.t) -> 'v Locus.occurrences_gen * 'a -> Pp.t
val pr_red_expr : env -> Evd.evar_map ->
  (env -> Evd.evar_map -> 'a -> Pp.t) *
  (env -> Evd.evar_map -> 'a -> Pp.t) *
  ('b -> Pp.t) *
  (env -> Evd.evar_map -> 'c -> Pp.t) *
  ('occvar -> Pp.t) ->
  ('a,'b,'c,'occvar) Genredexpr.red_expr_gen -> Pp.t
val pr_may_eval :
  env -> Evd.evar_map ->
  (env -> Evd.evar_map -> 'a -> Pp.t) -> (env -> Evd.evar_map -> 'a -> Pp.t) -> ('b -> Pp.t) ->
  (env -> Evd.evar_map -> 'c -> Pp.t) -> ('occvar -> Pp.t) ->
  ('a,'b,'c,'occvar) Genredexpr.may_eval -> Pp.t

val pr_and_short_name : ('a -> Pp.t) -> 'a Genredexpr.and_short_name -> Pp.t

val pr_evaluable_reference_env : env -> Evaluable.t -> Pp.t

val pr_quantified_hypothesis : quantified_hypothesis -> Pp.t

val pr_in_clause :
  ('a -> Pp.t) -> 'a Locus.clause_expr -> Pp.t

val pr_clauses : (* default: *) bool option ->
  ('a -> Pp.t) -> 'a Locus.clause_expr -> Pp.t
  (* Some true = default is concl; Some false = default is all; None = no default *)

val pr_raw_generic : env -> Evd.evar_map -> rlevel generic_argument -> Pp.t

val pr_glb_generic : env -> Evd.evar_map -> glevel generic_argument -> Pp.t

val pr_raw_extend: env -> Evd.evar_map -> int ->
  ml_tactic_entry -> raw_tactic_arg list -> Pp.t

val pr_glob_extend: env -> int ->
  ml_tactic_entry -> glob_tactic_arg list -> Pp.t

val pr_extend :
  (Val.t -> Pp.t) -> int -> ml_tactic_entry -> Val.t list -> Pp.t

val pr_alias_key : Names.KerName.t -> Pp.t

val pr_alias : (Val.t -> Pp.t) ->
  int -> Names.KerName.t -> Val.t list -> Pp.t

val pr_ltac_constant : ltac_constant -> Pp.t

val pr_raw_tactic : env -> Evd.evar_map -> raw_tactic_expr -> Pp.t

val pr_raw_tactic_level : env -> Evd.evar_map -> entry_relative_level -> raw_tactic_expr -> Pp.t

val pr_glob_tactic : env -> glob_tactic_expr -> Pp.t

val pr_atomic_tactic : env -> Evd.evar_map -> atomic_tactic_expr -> Pp.t

val pr_hintbases : string list option -> Pp.t

val pr_auto_using : ('constr -> Pp.t) -> 'constr list -> Pp.t

val pr_match_pattern : ('a -> Pp.t) -> 'a match_pattern -> Pp.t

val pr_match_rule : bool -> ('a -> Pp.t) -> ('b -> Pp.t) ->
  ('b, 'a) match_rule -> Pp.t

val pr_value : entry_relative_level -> Val.t -> Pp.t

val pp_ltac_call_kind : ltac_call_kind -> Pp.t

val ltop : entry_relative_level

val make_constr_printer : (env -> Evd.evar_map -> entry_relative_level -> 'a -> Pp.t) ->
  'a Genprint.top_printer

val ssr_loaded_hook : (unit -> bool) -> unit

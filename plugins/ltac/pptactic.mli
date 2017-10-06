(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module implements pretty-printers for tactic_expr syntactic
    objects and their subcomponents. *)

open Genarg
open Geninterp
open Names
open Misctypes
open Environ
open Constrexpr
open Tacexpr
open Notation_term

type 'a grammar_tactic_prod_item_expr =
| TacTerm of string
| TacNonTerm of ('a * Names.Id.t option) Loc.located

type 'a raw_extra_genarg_printer =
    (constr_expr -> Pp.t) ->
    (constr_expr -> Pp.t) ->
    (tolerability -> raw_tactic_expr -> Pp.t) ->
    'a -> Pp.t

type 'a glob_extra_genarg_printer =
    (glob_constr_and_expr -> Pp.t) ->
    (glob_constr_and_expr -> Pp.t) ->
    (tolerability -> glob_tactic_expr -> Pp.t) ->
    'a -> Pp.t

type 'a extra_genarg_printer =
    (EConstr.t -> Pp.t) ->
    (EConstr.t -> Pp.t) ->
    (tolerability -> Val.t -> Pp.t) ->
    'a -> Pp.t

val declare_extra_genarg_pprule :
  ('a, 'b, 'c) genarg_type ->
  'a raw_extra_genarg_printer ->
  'b glob_extra_genarg_printer ->
  'c extra_genarg_printer -> unit

type grammar_terminals = Genarg.ArgT.any Extend.user_symbol grammar_tactic_prod_item_expr list

type pp_tactic = {
  pptac_level : int;
  pptac_prods : grammar_terminals;
}

val pr_goal_selector : toplevel:bool -> goal_selector -> Pp.t

val declare_notation_tactic_pprule : KerName.t -> pp_tactic -> unit

val pr_with_occurrences :
  ('a -> Pp.t) -> 'a Locus.with_occurrences -> Pp.t
val pr_red_expr :
  ('a -> Pp.t) * ('a -> Pp.t) * ('b -> Pp.t) * ('c -> Pp.t) ->
  ('a,'b,'c) Genredexpr.red_expr_gen -> Pp.t
val pr_may_eval :
  ('a -> Pp.t) -> ('a -> Pp.t) -> ('b -> Pp.t) ->
  ('c -> Pp.t) -> ('a,'b,'c) Genredexpr.may_eval -> Pp.t

val pr_and_short_name : ('a -> Pp.t) -> 'a and_short_name -> Pp.t
val pr_or_by_notation : ('a -> Pp.t) -> 'a or_by_notation -> Pp.t

val pr_in_clause :
  ('a -> Pp.t) -> 'a Locus.clause_expr -> Pp.t

val pr_clauses :  bool option ->
  ('a -> Pp.t) -> 'a Locus.clause_expr -> Pp.t

val pr_raw_generic : env -> rlevel generic_argument -> Pp.t

val pr_glb_generic : env -> glevel generic_argument -> Pp.t

val pr_raw_extend: env -> int ->
  ml_tactic_entry -> raw_tactic_arg list -> Pp.t

val pr_glob_extend: env -> int ->
  ml_tactic_entry -> glob_tactic_arg list -> Pp.t

val pr_extend :
  (Val.t -> Pp.t) -> int -> ml_tactic_entry -> Val.t list -> Pp.t

val pr_alias_key : Names.KerName.t -> Pp.t

val pr_alias : (Val.t -> Pp.t) ->
  int -> Names.KerName.t -> Val.t list -> Pp.t

val pr_ltac_constant : ltac_constant -> Pp.t

val pr_raw_tactic : raw_tactic_expr -> Pp.t

val pr_raw_tactic_level : tolerability -> raw_tactic_expr -> Pp.t

val pr_glob_tactic : env -> glob_tactic_expr -> Pp.t

val pr_atomic_tactic : env -> Evd.evar_map -> atomic_tactic_expr -> Pp.t

val pr_hintbases : string list option -> Pp.t

val pr_auto_using : ('constr -> Pp.t) -> 'constr list -> Pp.t

val pr_match_pattern : ('a -> Pp.t) -> 'a match_pattern -> Pp.t

val pr_match_rule : bool -> ('a -> Pp.t) -> ('b -> Pp.t) ->
  ('b, 'a) match_rule -> Pp.t

val pr_value : tolerability -> Val.t -> Pp.t


val ltop : tolerability

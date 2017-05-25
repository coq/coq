(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module implements pretty-printers for tactic_expr syntactic
    objects and their subcomponents. *)

open Pp
open Genarg
open Geninterp
open Names
open Misctypes
open Environ
open Constrexpr
open Tacexpr
open Ppextend

type 'a grammar_tactic_prod_item_expr =
| TacTerm of string
| TacNonTerm of ('a * Names.Id.t option) Loc.located

type 'a raw_extra_genarg_printer =
    (constr_expr -> std_ppcmds) ->
    (constr_expr -> std_ppcmds) ->
    (tolerability -> raw_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

type 'a glob_extra_genarg_printer =
    (glob_constr_and_expr -> std_ppcmds) ->
    (glob_constr_and_expr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

type 'a extra_genarg_printer =
    (EConstr.t -> std_ppcmds) ->
    (EConstr.t -> std_ppcmds) ->
    (tolerability -> Val.t -> std_ppcmds) ->
    'a -> std_ppcmds

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

val declare_notation_tactic_pprule : KerName.t -> pp_tactic -> unit

val pr_with_occurrences :
  ('a -> std_ppcmds) -> 'a Locus.with_occurrences -> std_ppcmds
val pr_red_expr :
  ('a -> std_ppcmds) * ('a -> std_ppcmds) * ('b -> std_ppcmds) * ('c -> std_ppcmds) ->
  ('a,'b,'c) Genredexpr.red_expr_gen -> std_ppcmds
val pr_may_eval :
  ('a -> std_ppcmds) -> ('a -> std_ppcmds) -> ('b -> std_ppcmds) ->
  ('c -> std_ppcmds) -> ('a,'b,'c) Genredexpr.may_eval -> std_ppcmds

val pr_and_short_name : ('a -> std_ppcmds) -> 'a and_short_name -> std_ppcmds
val pr_or_by_notation : ('a -> std_ppcmds) -> 'a or_by_notation -> std_ppcmds

val pr_in_clause :
  ('a -> Pp.std_ppcmds) -> 'a Locus.clause_expr -> Pp.std_ppcmds

val pr_clauses :  bool option ->
  ('a -> Pp.std_ppcmds) -> 'a Locus.clause_expr -> Pp.std_ppcmds

val pr_raw_generic : env -> rlevel generic_argument -> std_ppcmds

val pr_glb_generic : env -> glevel generic_argument -> std_ppcmds

val pr_raw_extend: env -> int ->
  ml_tactic_entry -> raw_tactic_arg list -> std_ppcmds

val pr_glob_extend: env -> int ->
  ml_tactic_entry -> glob_tactic_arg list -> std_ppcmds

val pr_extend :
  (Val.t -> std_ppcmds) -> int -> ml_tactic_entry -> Val.t list -> std_ppcmds

val pr_alias_key : Names.KerName.t -> std_ppcmds

val pr_alias : (Val.t -> std_ppcmds) ->
  int -> Names.KerName.t -> Val.t list -> std_ppcmds

val pr_ltac_constant : Nametab.ltac_constant -> std_ppcmds

val pr_raw_tactic : raw_tactic_expr -> std_ppcmds

val pr_raw_tactic_level : tolerability -> raw_tactic_expr -> std_ppcmds

val pr_glob_tactic : env -> glob_tactic_expr -> std_ppcmds

val pr_atomic_tactic : env -> Evd.evar_map -> atomic_tactic_expr -> std_ppcmds

val pr_hintbases : string list option -> std_ppcmds

val pr_auto_using : ('constr -> std_ppcmds) -> 'constr list -> std_ppcmds

val pr_bindings :
  ('constr -> std_ppcmds) ->
  ('constr -> std_ppcmds) -> 'constr bindings -> std_ppcmds

val pr_match_pattern : ('a -> std_ppcmds) -> 'a match_pattern -> std_ppcmds

val pr_match_rule : bool -> ('a -> std_ppcmds) -> ('b -> std_ppcmds) ->
  ('b, 'a) match_rule -> std_ppcmds

val pr_value : tolerability -> Val.t -> std_ppcmds


val ltop : tolerability

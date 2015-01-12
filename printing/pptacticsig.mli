(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Genarg
open Names
open Constrexpr
open Tacexpr
open Ppextend
open Environ
open Pattern
open Misctypes

module type Pp = sig

  val pr_with_occurrences :
    ('a -> std_ppcmds) -> 'a Locus.with_occurrences -> std_ppcmds
  val pr_red_expr :
    ('a -> std_ppcmds) * ('a -> std_ppcmds) * ('b -> std_ppcmds) * ('c -> std_ppcmds) ->
    ('a,'b,'c) Genredexpr.red_expr_gen -> std_ppcmds
  val pr_may_eval :
    ('a -> std_ppcmds) -> ('a -> std_ppcmds) -> ('b -> std_ppcmds) ->
    ('c -> std_ppcmds) -> ('a,'b,'c) Genredexpr.may_eval -> std_ppcmds

  val pr_or_var : ('a -> std_ppcmds) -> 'a or_var -> std_ppcmds
  val pr_and_short_name : ('a -> std_ppcmds) -> 'a and_short_name -> std_ppcmds
  val pr_or_by_notation : ('a -> std_ppcmds) -> 'a or_by_notation -> std_ppcmds

  val pr_clauses :  bool option ->
    ('a -> Pp.std_ppcmds) -> 'a Locus.clause_expr -> Pp.std_ppcmds
  val pr_raw_generic :
    (constr_expr -> std_ppcmds) ->
    (constr_expr -> std_ppcmds) ->
    (tolerability -> raw_tactic_expr -> std_ppcmds) ->
    (constr_expr -> std_ppcmds) ->
    (Libnames.reference -> std_ppcmds) -> rlevel generic_argument ->
    std_ppcmds

  val pr_glb_generic :
    (glob_constr_and_expr -> Pp.std_ppcmds) ->
    (glob_constr_and_expr -> Pp.std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    (glob_constr_pattern_and_expr -> std_ppcmds) ->
    glevel generic_argument -> std_ppcmds

  val pr_top_generic :
    (Term.constr -> std_ppcmds) ->
    (Term.constr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    (Pattern.constr_pattern -> std_ppcmds) ->
    tlevel generic_argument ->
    std_ppcmds

  val pr_raw_extend:
    (constr_expr -> std_ppcmds) -> (constr_expr -> std_ppcmds) ->
    (tolerability -> raw_tactic_expr -> std_ppcmds) ->
    (constr_expr -> std_ppcmds) -> int ->
    ml_tactic_name -> raw_generic_argument list -> std_ppcmds

  val pr_glob_extend:
    (glob_constr_and_expr -> std_ppcmds) -> (glob_constr_and_expr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    (glob_constr_pattern_and_expr -> std_ppcmds) -> int ->
    ml_tactic_name -> glob_generic_argument list -> std_ppcmds

  val pr_extend :
    (Term.constr -> std_ppcmds) -> (Term.constr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    (constr_pattern -> std_ppcmds) -> int ->
    ml_tactic_name -> typed_generic_argument list -> std_ppcmds

  val pr_ltac_constant : Nametab.ltac_constant -> std_ppcmds

  val pr_raw_tactic : raw_tactic_expr -> std_ppcmds

  val pr_raw_tactic_level : tolerability -> raw_tactic_expr -> std_ppcmds

  val pr_glob_tactic : env -> glob_tactic_expr -> std_ppcmds

  val pr_tactic : env -> tactic_expr -> std_ppcmds

  val pr_hintbases : string list option -> std_ppcmds

  val pr_auto_using : ('constr -> std_ppcmds) -> 'constr list -> std_ppcmds

  val pr_bindings :
    ('constr -> std_ppcmds) ->
    ('constr -> std_ppcmds) -> 'constr bindings -> std_ppcmds

end

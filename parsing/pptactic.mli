(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pp
open Genarg
open Tacexpr
open Pretyping
open Proof_type
open Topconstr
open Rawterm
open Pattern
open Ppextend
open Environ
open Evd

val pr_or_var : ('a -> std_ppcmds) -> 'a or_var -> std_ppcmds
val pr_or_metaid : ('a -> std_ppcmds) -> 'a or_metaid -> std_ppcmds
val pr_and_short_name : ('a -> std_ppcmds) -> 'a and_short_name -> std_ppcmds
val pr_or_by_notation : ('a -> std_ppcmds) -> 'a or_by_notation -> std_ppcmds

type 'a raw_extra_genarg_printer =
    (constr_expr -> std_ppcmds) ->
    (constr_expr -> std_ppcmds) ->
    (tolerability -> raw_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

type 'a glob_extra_genarg_printer =
    (rawconstr_and_expr -> std_ppcmds) ->
    (rawconstr_and_expr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

type 'a extra_genarg_printer =
    (Term.constr -> std_ppcmds) ->
    (Term.constr -> std_ppcmds) ->
    (tolerability -> glob_tactic_expr -> std_ppcmds) ->
    'a -> std_ppcmds

  (* if the boolean is false then the extension applies only to old syntax *)
val declare_extra_genarg_pprule :
  ('c raw_abstract_argument_type * 'c raw_extra_genarg_printer) ->
  ('a glob_abstract_argument_type * 'a glob_extra_genarg_printer) ->
  ('b typed_abstract_argument_type * 'b extra_genarg_printer) -> unit

type grammar_terminals = string option list

  (* if the boolean is false then the extension applies only to old syntax *)
val declare_extra_tactic_pprule :
  string * argument_type list * (int * grammar_terminals) -> unit

val exists_extra_tactic_pprule : string -> argument_type list -> bool

val pr_raw_generic :
  (constr_expr -> std_ppcmds) ->
  (constr_expr -> std_ppcmds) ->
  (tolerability -> raw_tactic_expr -> std_ppcmds) ->
  (constr_expr -> std_ppcmds) ->
  (Libnames.reference -> std_ppcmds) -> rlevel generic_argument ->
    std_ppcmds

val pr_raw_extend:
  (constr_expr -> std_ppcmds) -> (constr_expr -> std_ppcmds) ->
  (tolerability -> raw_tactic_expr -> std_ppcmds) ->
  (constr_expr -> std_ppcmds) -> int ->
    string -> raw_generic_argument list -> std_ppcmds

val pr_glob_extend:
  (rawconstr_and_expr -> std_ppcmds) -> (rawconstr_and_expr -> std_ppcmds) ->
  (tolerability -> glob_tactic_expr -> std_ppcmds) ->
  (rawconstr_pattern_and_expr -> std_ppcmds) -> int ->
    string -> glob_generic_argument list -> std_ppcmds

val pr_extend :
  (Term.constr -> std_ppcmds) -> (Term.constr -> std_ppcmds) ->
  (tolerability -> glob_tactic_expr -> std_ppcmds) ->
  (constr_pattern -> std_ppcmds) -> int ->
    string -> typed_generic_argument list -> std_ppcmds

val pr_ltac_constant : Nametab.ltac_constant -> std_ppcmds

val pr_raw_tactic : env -> raw_tactic_expr -> std_ppcmds

val pr_raw_tactic_level : env -> tolerability -> raw_tactic_expr -> std_ppcmds

val pr_glob_tactic : env -> glob_tactic_expr -> std_ppcmds

val pr_tactic : env -> Proof_type.tactic_expr -> std_ppcmds

val pr_hintbases : string list option -> std_ppcmds

val pr_auto_using : ('constr -> std_ppcmds) -> 'constr list -> std_ppcmds

val pr_bindings :
  ('constr -> std_ppcmds) ->
  ('constr -> std_ppcmds) -> 'constr bindings -> std_ppcmds

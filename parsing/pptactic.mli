(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Genarg
open Tacexpr
open Pretyping
open Proof_type
open Topconstr

(* if the boolean is false then the extension applies only to old syntax *)
val declare_extra_genarg_pprule : 
  bool ->
  ('a raw_abstract_argument_type * ('a -> std_ppcmds)) ->
  ('b closed_abstract_argument_type * ('b -> std_ppcmds)) -> unit 

(* idem *)
val declare_extra_tactic_pprule : 
  bool -> string ->
    (raw_generic_argument list ->
      string * Egrammar.grammar_tactic_production list)
    -> (closed_generic_argument list ->
      string * Egrammar.grammar_tactic_production list)
      -> unit 

val pr_match_pattern : pattern_expr match_pattern -> std_ppcmds

val pr_match_rule : bool -> (raw_tactic_expr -> std_ppcmds) ->
  (pattern_expr,raw_tactic_expr) match_rule -> std_ppcmds

val pr_raw_tactic : raw_tactic_expr -> std_ppcmds

val pr_tactic : Proof_type.tactic_expr -> std_ppcmds

val pr_rawgen:
  (constr_expr -> std_ppcmds) ->
  (raw_tactic_expr -> std_ppcmds) ->
    (constr_expr, raw_tactic_expr) generic_argument ->
      std_ppcmds
val pr_raw_extend:
  (constr_expr -> std_ppcmds) ->
  (raw_tactic_expr -> std_ppcmds) -> string ->
    (constr_expr, raw_tactic_expr) generic_argument list ->
      std_ppcmds
val pr_extend :
  (raw_tactic_expr -> std_ppcmds) -> string ->
    (Term.constr, raw_tactic_expr) generic_argument list ->
      std_ppcmds

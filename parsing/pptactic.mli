(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Genarg
open Tacexpr
open Pretyping
open Proof_type
open Topconstr
open Rawterm

val pr_or_var : ('a -> std_ppcmds) -> 'a or_var -> std_ppcmds
val pr_or_metaid : ('a -> std_ppcmds) -> 'a or_metaid -> std_ppcmds
val pr_and_short_name : ('a -> std_ppcmds) -> 'a and_short_name -> std_ppcmds
val pr_located : ('a -> std_ppcmds) -> 'a Util.located -> std_ppcmds

type 'a raw_extra_genarg_printer =
    (constr_expr -> std_ppcmds) -> (raw_tactic_expr -> std_ppcmds) ->
      'a -> std_ppcmds

type 'a glob_extra_genarg_printer =
    (rawconstr_and_expr -> std_ppcmds) -> (glob_tactic_expr -> std_ppcmds) ->
      'a -> std_ppcmds

type 'a extra_genarg_printer =
    (Term.constr -> std_ppcmds) -> (glob_tactic_expr -> std_ppcmds) ->
      'a -> std_ppcmds

  (* if the boolean is false then the extension applies only to old syntax *)
val declare_extra_genarg_pprule : 
  bool ->
  ('c raw_abstract_argument_type * 'c raw_extra_genarg_printer) ->
  ('a glob_abstract_argument_type * 'a glob_extra_genarg_printer) ->
  ('b closed_abstract_argument_type * 'b extra_genarg_printer) -> unit

type grammar_terminals = string option list

  (* if the boolean is false then the extension applies only to old syntax *)
val declare_extra_tactic_pprule : bool -> string -> 
  argument_type list * (string * grammar_terminals) -> unit

val pr_match_pattern : ('a -> std_ppcmds) -> 'a match_pattern -> std_ppcmds

val pr_match_rule : bool -> ('a -> std_ppcmds) -> ('b -> std_ppcmds) ->
  ('a,'b) match_rule -> std_ppcmds

val pr_glob_tactic : glob_tactic_expr -> std_ppcmds

val pr_tactic : Proof_type.tactic_expr -> std_ppcmds

val pr_glob_generic:
  (rawconstr_and_expr -> std_ppcmds) -> 
  (rawconstr_and_expr -> std_ppcmds) -> 
  (glob_tactic_expr -> std_ppcmds) ->
    glob_generic_argument -> std_ppcmds

val pr_raw_generic : 
  (constr_expr -> std_ppcmds) ->
  (constr_expr -> std_ppcmds) ->
  (raw_tactic_expr -> std_ppcmds) ->
  (Libnames.reference -> std_ppcmds) ->
    (constr_expr, raw_tactic_expr) generic_argument ->
      std_ppcmds

val pr_raw_extend:
  (constr_expr -> std_ppcmds) -> (constr_expr -> std_ppcmds) ->
  (raw_tactic_expr -> std_ppcmds) -> string ->
    raw_generic_argument list -> std_ppcmds

val pr_glob_extend:
  (rawconstr_and_expr -> std_ppcmds) -> (rawconstr_and_expr -> std_ppcmds) ->
  (glob_tactic_expr -> std_ppcmds) -> string ->
    glob_generic_argument list -> std_ppcmds

val pr_extend :
  (Term.constr -> std_ppcmds) -> (Term.constr -> std_ppcmds) ->
  (glob_tactic_expr -> std_ppcmds) -> string -> closed_generic_argument list -> std_ppcmds

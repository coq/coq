(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Names
open Libnames
open Term
open Sign
open Environ
open Rawterm
open Pattern
open Nametab
open Termops
(*i*)

(* These are the entry points for printing terms, context, tac, ... *)
(*
val gentacpr  : Tacexpr.raw_tactic_expr -> std_ppcmds
*)

val prterm_env      : env -> constr -> std_ppcmds
val prterm_env_at_top : env -> constr -> std_ppcmds
val prterm          : constr -> std_ppcmds
val prtype_env      : env -> types -> std_ppcmds
val prtype          : types -> std_ppcmds
val prjudge_env     :
  env -> Environ.unsafe_judgment -> std_ppcmds * std_ppcmds
val prjudge         : Environ.unsafe_judgment -> std_ppcmds * std_ppcmds

val pr_rawterm       : Rawterm.rawconstr -> std_ppcmds
val pr_cases_pattern : Rawterm.cases_pattern -> std_ppcmds

val pr_constant     : env -> constant -> std_ppcmds
val pr_existential  : env -> existential -> std_ppcmds
val pr_constructor  : env -> constructor -> std_ppcmds
val pr_inductive    : env -> inductive -> std_ppcmds
val pr_global       : global_reference -> std_ppcmds
val pr_ref_label    : constr_label -> std_ppcmds
val pr_pattern      : constr_pattern -> std_ppcmds
val pr_pattern_env  : env -> names_context -> constr_pattern -> std_ppcmds

val pr_ne_context_of : std_ppcmds -> env -> std_ppcmds

val pr_var_decl     : env -> named_declaration -> std_ppcmds
val pr_rel_decl     : env -> rel_declaration -> std_ppcmds

val pr_named_context_of : env -> std_ppcmds
val pr_rel_context  : env -> rel_context -> std_ppcmds
val pr_context_of   : env -> std_ppcmds

val emacs_str       : string -> string


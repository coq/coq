
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Sign
open Rawterm
open Pattern
(*i*)

(* These are the entry points for printing terms, context, tac, ... *)
val gentacpr  : Coqast.t -> std_ppcmds

val prterm_env      : 'a assumptions -> constr -> std_ppcmds
val prterm_env_at_top : 'a assumptions -> constr -> std_ppcmds
val prterm          : constr -> std_ppcmds
val prtype_env      : 'a assumptions -> typed_type -> std_ppcmds
val prtype          : typed_type -> std_ppcmds

val pr_rawterm       : Rawterm.rawconstr -> std_ppcmds
val pr_cases_pattern : Rawterm.cases_pattern -> std_ppcmds

val pr_constant     : 'a assumptions -> constant -> std_ppcmds
val pr_existential  : 'a assumptions -> existential -> std_ppcmds
val pr_constructor  : 'a assumptions -> constructor -> std_ppcmds
val pr_inductive    : 'a assumptions -> inductive -> std_ppcmds
val pr_ref_label    : constr_label -> std_ppcmds
val pr_pattern      : constr_pattern -> std_ppcmds
val pr_pattern_env  : 'a assumptions -> constr_pattern -> std_ppcmds

val pr_ne_env       : std_ppcmds -> path_kind -> context -> std_ppcmds

val pr_sign         : var_context -> std_ppcmds
val pr_env_opt      : context -> std_ppcmds

val emacs_str       : string -> string

(* For compatibility *)
val term0           : 'a assumptions -> constr -> std_ppcmds

val fprterm_env     : 'a assumptions -> constr -> std_ppcmds
val fprterm         : constr -> std_ppcmds
val fprtype_env     : 'a assumptions -> typed_type -> std_ppcmds
val fprtype         : typed_type -> std_ppcmds

(* For compatibility *)
val fterm0          : 'a assumptions -> constr -> std_ppcmds

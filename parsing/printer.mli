
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Sign
(*i*)

(* These are the entry points for printing terms, context, tac, ... *)
val gencompr  : path_kind -> Coqast.t -> std_ppcmds
val gentermpr : path_kind -> 'a assumptions -> constr -> std_ppcmds
val gentacpr  : Coqast.t -> std_ppcmds

val prterm_env      : 'a assumptions -> constr -> std_ppcmds
val prterm_env_at_top : 'a assumptions -> constr -> std_ppcmds
val prterm          : constr -> std_ppcmds
val prtype_env      : 'a assumptions -> typed_type -> std_ppcmds
val prtype          : typed_type -> std_ppcmds
val fprterm_env     : 'a assumptions -> constr -> std_ppcmds
val fprterm         : constr -> std_ppcmds
val fprtype_env     : 'a assumptions -> typed_type -> std_ppcmds
val fprtype         : typed_type -> std_ppcmds

val prrawterm       : Rawterm.rawconstr -> std_ppcmds
val prpattern       : Rawterm.pattern -> std_ppcmds

val pr_constant     : constant -> std_ppcmds
val pr_existential  : existential -> std_ppcmds
val pr_constructor  : constructor -> std_ppcmds
val pr_inductive    : inductive -> std_ppcmds

val pr_ne_env       : std_ppcmds -> path_kind -> context -> std_ppcmds

val pr_sign         : var_context -> std_ppcmds
val pr_env_opt      : context -> std_ppcmds

val emacs_str       : string -> string

(* For compatibility *)
val fterm0          : 'a assumptions -> constr -> std_ppcmds
val term0           : 'a assumptions -> constr -> std_ppcmds


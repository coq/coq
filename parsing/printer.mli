
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Sign
(*i*)

val gencompr  : path_kind -> Coqast.t -> std_ppcmds
val gentermpr : path_kind -> 'a assumptions -> constr -> std_ppcmds
val gentacpr  : Coqast.t -> std_ppcmds

val prterm          : constr -> std_ppcmds
val prtype_env      : 'a assumptions -> typed_type -> std_ppcmds
val prtype          : typed_type -> std_ppcmds
val fprterm         : constr -> std_ppcmds
val fprtype_env     : 'a assumptions -> typed_type -> std_ppcmds
val fprtype         : typed_type -> std_ppcmds
val fterm0          : 'a assumptions -> constr -> std_ppcmds
val term0           : 'a assumptions -> constr -> std_ppcmds
val term0_at_top    : 'a assumptions -> constr -> std_ppcmds

val pr_sign         : var_context -> std_ppcmds
val pr_env_opt      : context -> std_ppcmds

val print_arguments : bool ref
val print_casts     : bool ref
val print_emacs     : bool ref
val with_implicits  : ('a -> 'b) -> 'a -> 'b

val emacs_str       : string -> string


(* $Id$ *)

open Pp
open Names
open Term
open Sign
open Environ

val pr_id : identifier -> std_ppcmds
val pr_sp : section_path -> std_ppcmds

val gen_pr_term : path_kind -> 'a unsafe_env -> constr -> std_ppcmds
val pr_term : constr -> std_ppcmds
val pr_ne_env : std_ppcmds -> path_kind -> environment -> std_ppcmds


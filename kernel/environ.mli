
(* $Id$ *)

open Names
open Term
open Constant
open Inductive

type 'a unsafe_env

val push_var : identifier * constr -> 'a unsafe_env -> 'a unsafe_env
val push_rel : name * constr -> 'a unsafe_env -> 'a unsafe_env

val add_constant : constant -> 'a unsafe_env -> 'a unsafe_env
val add_mind : mind -> 'a unsafe_env -> 'a unsafe_env


val lookup_var : identifier -> 'a unsafe_env -> constr
val loopup_rel : int -> 'a unsafe_env -> name * constr
val lookup_constant : section_path -> 'a unsafe_env -> constant

val const_abst_opt_value : 'a unsafe_env -> constr -> constr option

val mindsp_nparams : 'a unsafe_env -> section_path -> int



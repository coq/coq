
(* $Id$ *)

open Names
open Term
open Constant
open Inductive

type unsafe_env

val push_var : identifier * constr -> unsafe_env -> unsafe_env
val push_rel : name * constr -> unsafe_env -> unsafe_env

val add_constant : constant -> unsafe_env -> unsafe_env
val add_mind : mind -> unsafe_env -> unsafe_env


val lookup_var : identifier -> unsafe_env -> constr
val loopup_rel : int -> unsafe_env -> name * constr


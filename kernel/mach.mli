
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Univ
open Environ
open Machops
(*i*)

(*s Machine without information. *)

val fexecute_type : 'a unsafe_env -> constr -> typed_type
val fexecute : 'a unsafe_env -> constr -> unsafe_judgment

val execute_rec_type : 'a unsafe_env -> constr -> typed_type
val execute_rec : 'a unsafe_env -> constr -> unsafe_judgment

val type_of : 'a unsafe_env -> constr -> constr
val type_of_type : 'a unsafe_env -> constr -> constr

val type_of_rel : 'a unsafe_env -> constr -> constr

val unsafe_type_of : 'a unsafe_env -> constr -> constr

val fexemeta_type : 'a unsafe_env -> constr -> typed_type
val fexemeta : 'a unsafe_env -> constr -> unsafe_judgment

val core_fmachine_type : bool -> 'a unsafe_env -> constr -> typed_type
val core_fmachine : bool -> 'a unsafe_env -> constr -> unsafe_judgment


(*s Machine with information. *)

val infexemeta : 
  'a unsafe_env -> constr -> unsafe_judgment * information * universes

val infexecute_type : 
  'a unsafe_env -> constr -> typed_type * information * universes

val infexecute : 
  'a unsafe_env -> constr -> unsafe_judgment * information * universes

val inf_env_of_env : 'a unsafe_env -> 'a unsafe_env

val core_infmachine : 'a unsafe_env -> constr -> information

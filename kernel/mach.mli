
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Univ
open Environ
open Machops
(*i*)

(*s Machines without information. *)

val safe_machine : 'a unsafe_env -> constr -> unsafe_judgment * universes
val safe_machine_type : 'a unsafe_env -> constr -> typed_type

val fix_machine : 'a unsafe_env -> constr -> unsafe_judgment * universes
val fix_machine_type : 'a unsafe_env -> constr -> typed_type

val unsafe_machine : 'a unsafe_env -> constr -> unsafe_judgment * universes
val unsafe_machine_type : 'a unsafe_env -> constr -> typed_type

val type_of : 'a unsafe_env -> constr -> constr

val type_of_type : 'a unsafe_env -> constr -> constr

val unsafe_type_of : 'a unsafe_env -> constr -> constr


(*s Machine with information. *)

type information = Logic | Inf of unsafe_judgment

(*i
val infexemeta : 
  'a unsafe_env -> constr -> unsafe_judgment * information * universes

val infexecute_type : 
  'a unsafe_env -> constr -> typed_type * information * universes

val infexecute : 
  'a unsafe_env -> constr -> unsafe_judgment * information * universes

val inf_env_of_env : 'a unsafe_env -> 'a unsafe_env

val core_infmachine : 'a unsafe_env -> constr -> information
i*)

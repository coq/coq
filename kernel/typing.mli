
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Univ
open Sign
open Constant
open Inductive
open Environ
open Typeops
(*i*)

(*s Safe environments. Since we are now able to type terms, we can define an
  abstract type of safe environments, where objects are typed before being
  added. Internally, the datatype is still [unsafe_env]. We re-export the
  functions of [Environ] for the new type [environment]. *)

type environment

val empty_environment : environment

val universes : environment -> universes
val context : environment -> context

val push_var : identifier * constr -> environment -> environment
val push_rel : name * constr -> environment -> environment
val add_constant : 
  section_path -> constant_entry -> environment -> environment
val add_parameter :
  section_path -> constr -> environment -> environment
val add_mind : 
  section_path -> mutual_inductive_entry -> environment -> environment
val add_constraints : constraints -> environment -> environment

val lookup_var : identifier -> environment -> name * typed_type
val lookup_rel : int -> environment -> name * typed_type
val lookup_constant : section_path -> environment -> constant_body
val lookup_mind : section_path -> environment -> mutual_inductive_body
val lookup_mind_specif : constr -> environment -> mind_specif

val export : environment -> string -> compiled_env
val import : compiled_env -> environment -> environment

val unsafe_env_of_env : environment -> unsafe_env

(*s Typing without information. *)

type judgment

val j_val : judgment -> constr
val j_type : judgment -> constr
val j_kind : judgment -> constr

val safe_machine : environment -> constr -> judgment * constraints
val safe_machine_type : environment -> constr -> typed_type

val fix_machine : environment -> constr -> judgment * constraints
val fix_machine_type : environment -> constr -> typed_type

val unsafe_machine : environment -> constr -> judgment * constraints
val unsafe_machine_type : environment -> constr -> typed_type

val type_of : environment -> constr -> constr

val type_of_type : environment -> constr -> constr

val unsafe_type_of : environment -> constr -> constr


(*s Typing with information (extraction). *)

type information = Logic | Inf of judgment



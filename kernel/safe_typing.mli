
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Univ
open Sign
open Declarations
open Inductive
open Environ
open Typeops
(*i*)

(*s Safe environments. Since we are now able to type terms, we can define an
  abstract type of safe environments, where objects are typed before being
  added. Internally, the datatype is still [env]. We re-export the
  functions of [Environ] for the new type [environment]. *)

type safe_environment

val empty_environment : safe_environment

val universes : safe_environment -> universes
val context : safe_environment -> context
val var_context : safe_environment -> var_context

val push_var_decl : identifier * constr -> safe_environment -> safe_environment
val push_var_def : identifier * constr -> safe_environment -> safe_environment
(*i
val push_rel_decl : name * constr -> safe_environment -> safe_environment
val push_rel_def : name * constr -> safe_environment -> safe_environment
i*)

val add_constant : 
  section_path -> constant_entry -> safe_environment -> safe_environment
val add_lazy_constant : 
  section_path -> (unit -> constr) -> constr -> safe_environment 
    -> safe_environment
val add_parameter :
  section_path -> constr -> safe_environment -> safe_environment
val add_mind : 
  section_path -> mutual_inductive_entry -> safe_environment 
    -> safe_environment
val add_constraints : constraints -> safe_environment -> safe_environment

val pop_vars : identifier list -> safe_environment -> safe_environment

val lookup_var : identifier -> safe_environment -> constr option * typed_type
(*i
val lookup_rel : int -> safe_environment -> name * typed_type
i*)
val lookup_constant : section_path -> safe_environment -> constant_body
val lookup_mind : section_path -> safe_environment -> mutual_inductive_body
val lookup_mind_specif : inductive -> safe_environment -> inductive_instance

val export : safe_environment -> string -> compiled_env
val import : compiled_env -> safe_environment -> safe_environment

val env_of_safe_env : safe_environment -> env


(*s Typing judgments without modifying the global safe env - used in minicoq *)

type judgment

val j_val : judgment -> constr
val j_type : judgment -> constr

val safe_infer : safe_environment -> constr -> judgment * constraints

(*i For debug
val fix_machine : safe_environment -> constr -> judgment * constraints
val fix_machine_type : safe_environment -> constr -> typed_type * constraints

val unsafe_infer : safe_environment -> constr -> judgment * constraints
val unsafe_infer_type : safe_environment -> constr -> typed_type * constraints

val type_of : safe_environment -> constr -> constr

val type_of_type : safe_environment -> constr -> constr
val unsafe_type_of : safe_environment -> constr -> constr
i*)



(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Sign
open Constant
open Inductive
open Environ
open Safe_typing
(*i*)

(* This module defines the global environment of Coq. 
   The functions below are exactly the same as the ones in [Typing],
   operating on that global environment. *)

val env : unit -> environment
val unsafe_env : unit -> unsafe_env

val universes : unit -> universes
val context : unit -> context
val var_context : unit -> var_context

val push_var : identifier * constr -> unit
val push_rel : name * constr -> unit
val add_constant : section_path -> constant_entry -> unit
val add_parameter : section_path -> constr -> unit
val add_mind : section_path -> mutual_inductive_entry -> unit
val add_constraints : constraints -> unit

val lookup_var : identifier -> name * typed_type
val lookup_rel : int -> name * typed_type
val lookup_constant : section_path -> constant_body
val lookup_mind : section_path -> mutual_inductive_body
val lookup_mind_specif : constr -> mind_specif

val export : string -> compiled_env
val import : compiled_env -> unit

(*s Some functions of [Environ] instanciated on the global environment. *)

val id_of_global : sorts oper -> identifier

(*s Re-exported functions of [Inductive], composed with 
    [lookup_mind_specif]. *)

val mind_is_recursive : constr -> bool
val mind_nconstr : constr -> int
val mind_nparams : constr -> int
val mind_arity : constr -> constr

val mind_lc_without_abstractions : constr -> constr array



(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Sign
open Constant
open Inductive
open Environ
open Typing
(*i*)

(* This module defines the global environment of Coq. 
   The functions below are exactly the same as the ones in [Typing],
   operating on that global environment. *)

val env : unit -> environment

val universes : unit -> universes
val context : unit -> context

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

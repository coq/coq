(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Identifier
open Names
open Univ
open Term
open Sign
open Declarations
open Mod_declarations
open Inductive
open Environ
open Safe_env
(*i*)

(* This module defines the global environment of Coq. 
   The functions below are exactly the same as the ones in [Safe_env],
   operating on that global environment. *)

val safe_env : unit -> safe_environment
val env : unit -> env

val universes : unit -> universes
(*val context : unit -> context*)
val named_context : unit -> named_context

val push_named_assum : identifier * constr -> unit
val push_named_def : identifier * constr -> unit

val add_constant : label -> constant_entry -> constant_path
val add_mind : mutual_inductive_entry -> mutual_inductive_path
val add_module : label -> module_entry -> module_path
val add_modtype : label -> module_type_entry -> long_name
(*val add_constraints : constraints -> unit *)

(*val pop_named_decls : identifier list -> unit*)

val lookup_named : identifier -> constr option * types
val lookup_constant : long_name -> constant_body
val lookup_mind : long_name -> mutual_inductive_body
val lookup_mind_specif : inductive -> inductive_instance

val lookup_module : module_path -> module_body
val lookup_modtype : long_name -> module_type_body

val begin_module : 
  label -> (mod_bound_id * module_type_entry) list 
    -> module_type_entry option -> unit
val end_module : label -> module_path

val begin_modtype : 
  label -> (mod_bound_id * module_type_entry) list -> unit
val end_modtype : label -> long_name

val current_modpath : unit -> module_path
val current_msid : unit -> mod_str_id

val set_opaque : long_name -> unit
val set_transparent : long_name -> unit

val export : dir_path -> mod_str_id * compiled_module
val import : compiled_module -> Digest.t -> module_path

(*s Some functions of [Environ] instanciated on the global environment. *)

(*val sp_of_global : global_reference -> section_path

(*s This is for printing purpose *)
val qualid_of_global : global_reference -> Nametab.qualid
val string_of_global : global_reference -> string
*)

(*s Function to get an environment from the constants part of the global
    environment and a given context. *)

val env_of_context : named_context -> env

(*s Re-exported functions of [Inductive], composed with 
    [lookup_mind_specif]. *)

val mind_is_recursive : inductive -> bool
val mind_nconstr : inductive -> int
val mind_nparams : inductive -> int
val mind_nf_lc : inductive -> constr array


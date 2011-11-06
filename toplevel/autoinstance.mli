(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id:$ *)

(*i*)
open Term
open Libnames
open Typeclasses
open Names
open Evd
open Sign
(*i*)

(*s Automatic detection of (some) record instances *)

(* What to do if we find an instance. Passed are : the reference
 * representing the record/class (definition or constructor) *)
type instance_decl_function = global_reference -> rel_context -> constr list -> unit

(* [search_declaration gr] Search in the library if the (new)
 * declaration gr can form an instance of a registered record/class *)
val search_declaration : global_reference -> unit

(* [search_record declf gr evm] Search the library for instances of
   the (new) record/class declaration [gr], and register them using
   [declf]. [evm] is the signature of the record (to avoid recomputing
   it) *)
val search_record : instance_decl_function -> global_reference -> evar_map -> unit

(* Instance declaration for both scenarios *)
val declare_record_instance : instance_decl_function
val declare_class_instance : instance_decl_function

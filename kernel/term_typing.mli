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
open Term
open Univ
open Declarations
open Mod_declarations
open Inductive
open Environ
open Typeops
(*i*)

(*s Safe environments. Since we are now able to type terms, we can
  define an abstract type of safe environments, where objects are
  typed before being added. Internally, the datatype is still [env].
  We re-export the functions of [Environ] for the new type
  [safe_environment]. 

  We also add [open_structure] and [close_section], [close_module]
  to provide functionnality for sections and interactive modules *)

val translate_constant : env -> constant_entry -> constant_body

val translate_mind : 
  env -> mutual_inductive_entry -> mutual_inductive_body


val infer : env -> constr -> unsafe_judgment * constraints

val infer_type : env -> types -> unsafe_type_judgment * constraints


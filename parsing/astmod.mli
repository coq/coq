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
open Evd
open Environ
open Mod_declarations
(*i*)

(* Module expressions and module types are interpreted relatively to 
eventual functor or funsig arguments. *)

val interp_modexpr       : 
  'a evar_map -> env -> 
    (identifier list * Coqast.t) list -> Coqast.t option -> 
      (mod_bound_id * module_type_entry) list * module_expr option

val interp_modtype        : 
  'a evar_map -> env -> (identifier list * Coqast.t) list -> Coqast.t -> 
    (mod_bound_id * module_type_entry) list * module_type_entry

val interp_modbinders    : 
  'a evar_map -> env -> (identifier list * Coqast.t) list -> 
    (mod_bound_id * module_type_entry) list


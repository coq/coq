(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Declarations
open Environ
open Entries
open Evd
(*i*)

(* Module expressions and module types are interpreted relatively to 
   eventual functor or funsig arguments. *)

val interp_module_decl : evar_map -> env -> 
  (identifier list * Coqast.t) list -> 
  Coqast.t option ->
  Coqast.t option
    ->
      (identifier * (mod_bound_id * module_type_entry)) list * 
      module_type_entry option *
      module_expr option


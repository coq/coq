(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Names
open Declarations
open Environ
open Libnames
open Miniml
open Mlutil

val add_structure : module_path -> module_structure_body -> env -> env

val add_functor : mod_bound_id -> module_type_body -> env -> env

val print_one_decl :
  ml_structure -> module_path -> ml_decl -> unit

val print_structure_to_file : 
  (string * string) option -> extraction_params -> ml_structure -> unit



(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Declarations
open Environ
open Entries
(*i*)


val translate_modtype : env -> module_type_entry -> module_type_body

val translate_module : env -> module_entry -> module_body

val add_modtype_constraints : env -> module_type_body -> env

val add_module_constraints : env -> module_body -> env


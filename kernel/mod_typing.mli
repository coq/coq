(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Declarations
open Environ
open Entries
(*i*)


val translate_modtype : env -> module_type_entry -> module_type_body

val translate_module : env -> module_entry -> module_body

val translate_mexpr : env -> module_expr -> module_expr_body * module_type_body

val add_modtype_constraints : env -> module_type_body -> env

val add_module_constraints : env -> module_body -> env


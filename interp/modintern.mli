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
open Util
open Libnames
open Names
open Topconstr
(*i*)

(* Module expressions and module types are interpreted relatively to 
   eventual functor or funsig arguments. *)

val interp_modtype : env -> module_type_ast -> module_struct_entry

val interp_modexpr : env -> module_ast -> module_struct_entry

val lookup_module : qualid located -> module_path

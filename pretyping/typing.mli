(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Environ
open Evd
(*i*)

(* This module provides the typing machine with existential variables
   (but without universes). *)

(* Typecheck a term and return its type *)
val type_of : env -> evar_map -> constr -> types
(* Typecheck a type and return its sort *)
val sort_of : env -> evar_map -> types -> sorts
(* Typecheck a term has a given type (assuming the type is OK *)
val check   : env -> evar_map -> constr -> types -> unit

(* The same but with metas... *)
val mtype_of : env -> evar_defs -> constr -> types
val msort_of : env -> evar_defs -> types -> sorts
val mcheck   : env -> evar_defs -> constr -> types -> unit
val meta_type : evar_defs -> metavariable -> types

(* unused typing function... *)
val mtype_of_type : env -> evar_defs -> types -> types

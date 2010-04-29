(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Term
open Environ
open Evd

(** This module provides the typing machine with existential variables
   (but without universes). *)

(** Typecheck a term and return its type *)
val type_of : env -> evar_map -> constr -> types

(** Typecheck a type and return its sort *)
val sort_of : env -> evar_map -> types -> sorts

(** Typecheck a term has a given type (assuming the type is OK) *)
val check   : env -> evar_map -> constr -> types -> unit

(** Returns the instantiated type of a metavariable *)
val meta_type : evar_map -> metavariable -> types

(** Solve existential variables using typing *)
val solve_evars : env -> evar_map -> constr -> constr

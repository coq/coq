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

val unsafe_machine : env -> evar_map -> constr -> unsafe_judgment

val type_of : env -> evar_map -> constr -> constr

val execute_type : env -> evar_map -> constr -> types

val execute_rec_type : env -> evar_map -> constr -> types


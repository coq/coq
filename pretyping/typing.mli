(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Term
open Environ
open Evd
(*i*)

(* This module provides the typing machine with existential variables
   (but without universes). *)

val unsafe_machine : env -> 'a evar_map -> constr -> unsafe_judgment

val type_of : env -> 'a evar_map -> constr -> constr

val execute_type : env -> 'a evar_map -> constr -> types

val execute_rec_type : env -> 'a evar_map -> constr -> types


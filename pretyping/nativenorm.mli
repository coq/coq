(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Term
open Environ
open Evd
open Nativelambda

(** This module implements normalization by evaluation to OCaml code *)

val evars_of_evar_map : evar_map -> evars

val native_norm : env -> evars -> constr -> types -> constr

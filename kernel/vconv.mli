(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Environ
open Reduction

(**********************************************************************
  s conversion functions *)
val use_vm : unit -> bool
val set_use_vm : bool -> unit
val vconv : conv_pb -> types conversion_function

val val_of_constr : env -> constr -> values


(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Names
open Term
open Environ
open Reduction
(*i*)

(***********************************************************************)
(*s conversion functions *)
val use_vm : unit -> bool
val set_use_vm : bool -> unit
val vconv : conv_pb -> types conversion_function

val val_of_constr : env -> constr -> values


(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Constr
open Environ
open Reduction

(**********************************************************************
  s conversion functions *)
val vm_conv : conv_pb -> types kernel_conversion_function

(** A conversion function parametrized by a universe comparator. Used outside of
    the kernel. *)
val vm_conv_gen : conv_pb -> (types, 'a) generic_conversion_function

(** Precompute a VM value from a constr *)
val val_of_constr : env -> constr -> Vmvalues.values

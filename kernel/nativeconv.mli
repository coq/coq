(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Constr
open Reduction
open Nativelambda

(** This module implements the conversion test by compiling to OCaml code *)

val native_conv : conv_pb -> evars -> types kernel_conversion_function

(** A conversion function parametrized by a universe comparator. Used outside of
    the kernel. *)
val native_conv_gen : conv_pb -> evars -> (types, 'a) generic_conversion_function

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Reduction

(**********************************************************************
  s conversion functions *)
val vm_conv : conv_pb -> types kernel_conversion_function

(** A conversion function parametrized by a universe comparator. Used outside of
    the kernel. *)
val vm_conv_gen : conv_pb -> (types, 'a) generic_conversion_function

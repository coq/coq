(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vmvalues
open Environ

type lval
type lambda = lval Genlambda.lambda

val get_lval : lval -> structured_values
val as_value : int -> lambda array -> lval option

val lambda_of_constr : env -> Genlambda.evars -> Constr.t -> lambda

(** Dump the VM lambda code after compilation (for debugging purposes) *)
val dump_lambda : bool ref

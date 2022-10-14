(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Vmvalues
open Environ

type lambda = structured_values Genlambda.lambda

exception TooLargeInductive of Pp.t

val lambda_of_constr : optimize:bool -> env -> Genlambda.evars -> Constr.t -> lambda

val get_alias : env -> Constant.t -> Constant.t

(** Dump the VM lambda code after compilation (for debugging purposes) *)
val dump_lambda : bool ref

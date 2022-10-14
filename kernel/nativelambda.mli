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
open Constr
open Environ
open Genlambda

(** This file defines the lambda code generation phase of the native compiler *)
type prefix = string

type lambda = Nativevalues.t Genlambda.lambda

val decompose_Llam : lambda -> Name.t Context.binder_annot array * lambda
val decompose_Llam_Llet : lambda -> (Name.t Context.binder_annot * lambda option) array * lambda

val is_lazy : constr -> bool

val get_mind_prefix : env -> MutInd.t -> string
val get_const_prefix : env -> Constant.t -> string

val get_alias : env -> pconstant -> pconstant

val lambda_of_constr : env -> evars -> Constr.constr -> lambda

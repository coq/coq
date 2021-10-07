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
open Environ
open Constr

val rename_arguments : bool -> GlobRef.t -> Name.t list -> unit

(** [Not_found] is raised if no names are defined for [r] *)
val arguments_names : GlobRef.t -> Name.t list

val rename_type : types -> GlobRef.t -> types

val rename_type_of_constant : env -> pconstant -> types
val rename_type_of_inductive : env -> pinductive -> types
val rename_type_of_constructor : env -> pconstructor -> types
val rename_typing : env -> constr -> unsafe_judgment

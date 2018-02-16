(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Environ
open Constr

val rename_arguments : bool -> global_reference -> Name.t list -> unit

(** [Not_found] is raised if no names are defined for [r] *)
val arguments_names : global_reference -> Name.t list

val rename_type_of_constant : env -> pconstant -> types
val rename_type_of_inductive : env -> pinductive -> types
val rename_type_of_constructor : env -> pconstructor -> types
val rename_typing : env -> constr -> unsafe_judgment

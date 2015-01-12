(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Decl_kinds

(** Operations about types defined in [Decl_kinds] *)

val logical_kind_of_goal_kind : goal_object_kind -> logical_kind
val string_of_theorem_kind : theorem_kind -> string
val string_of_definition_kind : definition_kind -> string

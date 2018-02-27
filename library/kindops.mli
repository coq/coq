(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Decl_kinds

(** Operations about types defined in [Decl_kinds] *)

val logical_kind_of_goal_kind : goal_object_kind -> logical_kind
val string_of_theorem_kind : theorem_kind -> string
val string_of_definition_object_kind : definition_object_kind -> string

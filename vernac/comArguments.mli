(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val vernac_arguments
  : section_local:bool
  -> Libnames.qualid Constrexpr.or_by_notation
  -> Vernacexpr.vernac_argument_status list
  -> (Names.Name.t * Impargs.implicit_kind) list list
  -> Vernacexpr.arguments_modifier list
  -> unit

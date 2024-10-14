(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val vernac_arguments
  : section_local:bool
  -> Libnames.qualid Constrexpr.or_by_notation
  -> Vernacexpr.vernac_argument_status list
  -> (Names.Name.t * Glob_term.binding_kind) list list
  -> Vernacexpr.arguments_modifier list
  -> unit

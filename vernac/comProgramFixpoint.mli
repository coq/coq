(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacexpr

(** Special Fixpoint handling when command is activated. *)
val do_fixpoint :
     pm:Declare.OblState.t
  -> scope:Locality.definition_scope
  -> poly:bool
  -> ?typing_flags:Declarations.typing_flags
  -> ?using:Vernacexpr.section_subset_expr
  -> fixpoint_expr list
  -> Declare.OblState.t

val do_cofixpoint :
     pm:Declare.OblState.t
  -> scope:Locality.definition_scope
  -> poly:bool
  -> ?using:Vernacexpr.section_subset_expr
  -> cofixpoint_expr list
  -> Declare.OblState.t

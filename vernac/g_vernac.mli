(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val query_command : (Goal_select.t option -> Vernacexpr.vernac_expr) Pcoq.Entry.t
(** G_ltac defines the versions of Check etc with a goal selector. *)

val parse_compat_version : string -> Flags.compat_version
(** Used for the command line -compat *)

val section_subset_expr : Vernacexpr.section_subset_expr Pcoq.Entry.t
(** Called by Proof_using *)

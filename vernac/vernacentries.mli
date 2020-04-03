(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Vernac Translation into the Vernac DSL *)
val translate_vernac
  : atts:Attributes.vernac_flags
  -> Vernacexpr.vernac_expr
  -> Vernacextend.typed_vernac

(** Vernacular require command *)
val vernac_require :
  Libnames.qualid option -> bool option -> Libnames.qualid list -> unit

(** Miscellaneous stuff *)
val command_focus : unit Proof.focus_kind

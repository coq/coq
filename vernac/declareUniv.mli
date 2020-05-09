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

(* object_kind , id *)
exception AlreadyDeclared of (string option * Id.t)

(** Global universe contexts, names and constraints *)
val declare_univ_binders : GlobRef.t -> UnivNames.universe_binders -> unit

val do_universe : poly:bool -> lident list -> unit
val do_constraint : poly:bool -> Glob_term.glob_constraint list -> unit

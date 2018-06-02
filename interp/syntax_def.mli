(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Notation_term

(** Syntactic definitions. *)

type syndef_interpretation = (Id.t * subscopes) list * notation_constr

val declare_syntactic_definition : bool -> Id.t ->
  Flags.compat_version option -> syndef_interpretation -> unit

val search_syntactic_definition : ?loc:Loc.t -> KerName.t -> syndef_interpretation

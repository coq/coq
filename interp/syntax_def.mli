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
open Notation_term

(** Syntactic definitions. *)

type syndef_interpretation = (Id.t * subscopes) list * notation_constr

val declare_syntactic_definition : local:bool -> Deprecation.t option -> Id.t ->
  onlyparsing:bool -> syndef_interpretation -> unit

val search_syntactic_definition : ?loc:Loc.t -> KerName.t -> syndef_interpretation

val search_filtered_syntactic_definition : ?loc:Loc.t ->
  (syndef_interpretation -> 'a option) -> KerName.t -> 'a option

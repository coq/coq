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
open Globnames

(** Abbreviations. *)

val declare_abbreviation : local:bool -> ?also_in_cases_pattern:bool -> Deprecation.t option -> Id.t ->
  onlyparsing:bool -> interpretation -> unit

val search_abbreviation : ?loc:Loc.t -> abbreviation -> interpretation

val search_filtered_abbreviation : ?loc:Loc.t ->
  (interpretation -> 'a option) -> abbreviation -> 'a option

val import_abbreviation : int -> Libnames.full_path -> abbreviation -> unit

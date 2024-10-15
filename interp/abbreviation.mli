(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Notation_term
open Notationextern
open Globnames

(** Abbreviations. *)

val declare_abbreviation : local:bool -> Globnames.extended_global_reference UserWarn.with_qf option -> Id.t ->
  onlyparsing:bool -> interpretation -> unit

val search_abbreviation : abbreviation -> interpretation

val search_filtered_abbreviation :
  (interpretation -> 'a option) -> abbreviation -> 'a option

val import_abbreviation : int -> Libnames.full_path -> KerName.t -> unit

(** Activate (if on:true) or deactivate (if on:false) an abbreviation assumed to exist *)
val toggle_abbreviation : on:bool -> use:notation_use -> abbreviation -> unit

(** Activate (if on:true) or deactivate (if on:false) all abbreviations satisfying a criterion *)
val toggle_abbreviations : on:bool -> use:notation_use -> (Libnames.full_path -> interpretation -> bool) -> unit

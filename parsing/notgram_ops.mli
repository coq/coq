(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Merge with metasyntax? *)
open Constrexpr
open Notation_gram

val level_eq : level -> level -> bool

(** {6 Declare and test the level of a (possibly uninterpreted) notation } *)

val declare_notation_level : ?onlyprint:bool -> notation -> level -> unit
val level_of_notation : ?onlyprint:bool -> notation -> level (** raise [Not_found] if no level or not respecting onlyprint *)

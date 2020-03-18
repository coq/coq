(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Merge with metasyntax? *)
open Constrexpr
open Notation_gram

val level_eq : level -> level -> bool
val entry_relative_level_eq : entry_relative_level -> entry_relative_level -> bool

(** {6 Declare and test the level of a (possibly uninterpreted) notation } *)

val declare_notation_level : notation -> notation_grammar option -> level -> unit
val level_of_notation : notation -> notation_grammar option * level
  (** raise [Not_found] if not declared *)

(** Returns notations with defined parsing/printing rules *)
val get_defined_notations : unit -> notation list

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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

val declare_notation_level : notation -> onlyprint:bool -> notation_grammar -> level -> unit
val level_of_notation : notation -> bool (* = onlyprint *) * notation_grammar * level
  (** raise [Not_found] if not declared *)

(** Returns notations with defined parsing/printing rules *)
val get_defined_notations : unit -> notation list

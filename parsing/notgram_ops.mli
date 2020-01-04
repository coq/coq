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

val notation_signature_eq : notation_signature -> notation_signature -> bool

(** {6 Declare and test the level of a (possibly uninterpreted) notation } *)

val declare_notation_signature : ?onlyprint:bool -> notation -> notation_signature -> unit
val signature_of_notation : ?onlyprint:bool -> notation -> notation_signature (** raise [Not_found] if no level or not respecting onlyprint *)

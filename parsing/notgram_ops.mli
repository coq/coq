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

(** {6 Declare the parsing rules and entries of a (possibly uninterpreted) notation } *)

val declare_notation_grammar : notation -> notation_grammar -> unit
val grammar_of_notation : notation -> notation_grammar
  (** raise [Not_found] if not declared *)

val declare_notation_subentries : notation -> Extend.constr_entry_key list -> unit
val subentries_of_notation : notation -> Extend.constr_entry_key list

(** Returns notations with defined parsing/printing rules *)
val get_defined_notations : unit -> notation list

(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

type entry_types = Extend.constr_entry_key list

val declare_notation_grammar : notation -> notation_grammar -> unit
val grammar_of_notation : notation -> notation_grammar
  (** raise [Not_found] if not declared *)

val declare_notation_non_terminals : notation -> entry_types -> unit
val non_terminals_of_notation : notation -> entry_types

(** Prefixes inherit parsing levels, which may differ from printing levels. *)
val declare_notation_prefixes : notation -> Notationextern.level -> Extend.constr_entry_key list -> unit

(** Return a parsing notation with the longest common prefix, its levels and
    argument entries, and the number of shared nonterminals, if any. *)
val longest_common_prefix : notation -> (notation * Notationextern.level * Extend.constr_entry_key list * int) option

(** Returns notations with defined parsing/printing rules *)
val get_defined_notations : unit -> notation list

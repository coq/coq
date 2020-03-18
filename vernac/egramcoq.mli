(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Mapping of grammar productions to camlp5 actions *)

(** This is the part specific to Coq-level Notation and Tactic Notation.
    For the ML-level tactic and vernac extensions, see Egramml. *)

(** {5 Adding notations} *)

val extend_constr_grammar : Notation_gram.one_notation_grammar -> unit
(** Add a term notation rule to the parsing system. *)

val create_custom_entry : local:bool -> string -> unit

val exists_custom_entry : string -> bool

val locality_of_custom_entry : string -> bool

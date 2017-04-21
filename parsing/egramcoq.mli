(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Mapping of grammar productions to camlp4 actions *)

(** This is the part specific to Coq-level Notation and Tactic Notation.
    For the ML-level tactic and vernac extensions, see Egramml. *)

(** {5 Adding notations} *)

val extend_constr_grammar : Notation.level -> Notation_term.notation_grammar -> unit
(** Add a term notation rule to the parsing system. *)

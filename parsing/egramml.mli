(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Mapping of grammar productions to camlp4 actions. *)

(** This is the part specific to ML-level tactic and vernac extensions.
    For the Coq-level Notation and Tactic Notation, see Egramcoq. *)

type grammar_prod_item =
  | GramTerminal of string
  | GramNonTerminal of Pp.loc * Genarg.argument_type *
      Pcoq.prod_entry_key * Names.identifier option

val extend_tactic_grammar :
  string -> grammar_prod_item list list -> unit

val extend_vernac_command_grammar :
  string -> Vernacexpr.vernac_expr Pcoq.Gram.entry option ->
    grammar_prod_item list list -> unit

val get_extend_vernac_grammars :
  unit -> (string * grammar_prod_item list list) list

(** Utility function reused in Egramcoq : *)

val make_rule :
  (Pp.loc -> (Names.identifier * Tacexpr.raw_generic_argument) list -> 'b) ->
  grammar_prod_item list -> Pcoq.Gram.symbol list * Pcoq.Gram.action

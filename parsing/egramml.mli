(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Mapping of grammar productions to camlp4 actions. *)

(** This is the part specific to vernac extensions.
    For the Coq-level Notation and Tactic Notation, see Egramcoq. *)

type grammar_prod_item =
  | GramTerminal of string
  | GramNonTerminal of Loc.t * Genarg.argument_type *
      Pcoq.prod_entry_key * Names.Id.t option

val extend_vernac_command_grammar :
  Vernacexpr.extend_name -> Vernacexpr.vernac_expr Pcoq.Gram.entry option ->
    grammar_prod_item list -> unit

val get_extend_vernac_rule : Vernacexpr.extend_name -> grammar_prod_item list

(** Utility function reused in Egramcoq : *)

val make_rule :
  (Loc.t -> (Names.Id.t * Genarg.raw_generic_argument) list -> 'b) ->
  grammar_prod_item list -> Pcoq.Gram.symbol list * Pcoq.Gram.action

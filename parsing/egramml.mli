(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr

(** Mapping of grammar productions to camlp4 actions. *)

(** This is the part specific to vernac extensions.
    For the Coq-level Notation and Tactic Notation, see Egramcoq. *)

type 's grammar_prod_item =
  | GramTerminal of string
  | GramNonTerminal : ('a Genarg.raw_abstract_argument_type option *
      ('s, 'a) Extend.symbol) Loc.located -> 's grammar_prod_item

val extend_vernac_command_grammar :
  Vernacexpr.extend_name -> vernac_expr Pcoq.Gram.entry option ->
    vernac_expr grammar_prod_item list -> unit

val get_extend_vernac_rule : Vernacexpr.extend_name -> vernac_expr grammar_prod_item list

(** Utility function reused in Egramcoq : *)

val make_rule :
  (Loc.t -> Genarg.raw_generic_argument list -> 'a) ->
  'a grammar_prod_item list -> 'a Extend.production_rule

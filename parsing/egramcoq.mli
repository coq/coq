(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat
open Pp
open Names
open Constrexpr
open Notation_term
open Pcoq
open Extend
open Vernacexpr
open Ppextend
open Genarg
open Egramml

(** Mapping of grammar productions to camlp4 actions *)

(** This is the part specific to Coq-level Notation and Tactic Notation.
    For the ML-level tactic and vernac extensions, see Egramml. *)

(** For constr notations *)

type grammar_constr_prod_item =
  | GramConstrTerminal of Tok.t
  | GramConstrNonTerminal of constr_prod_entry_key * identifier option
  | GramConstrListMark of int * bool
    (* tells action rule to make a list of the n previous parsed items;
       concat with last parsed list if true *)

type notation_grammar = {
  notgram_level : int;
  notgram_assoc : gram_assoc option;
  notgram_notation : notation;
  notgram_prods : grammar_constr_prod_item list list
}

type tactic_grammar = {
  tacgram_key : string;
  tacgram_level : int;
  tacgram_prods : grammar_prod_item list;
  tacgram_tactic : dir_path * Tacexpr.glob_tactic_expr;
}

(** Adding notations *)

type all_grammar_command =
  | Notation of
	 (precedence * tolerability list)
	  * notation_var_internalization_type list
	   (** not needed for defining grammar, hosted by egrammar for
	       transmission to interp_aconstr (via recover_notation_grammar) *)
	  * notation_grammar
  | TacticGrammar of tactic_grammar

val extend_grammar : all_grammar_command -> unit

(** For a declared grammar, returns the rule + the ordered entry types
    of variables in the rule (for use in the interpretation) *)
val recover_notation_grammar :
  notation -> (precedence * tolerability list) ->
  notation_var_internalization_type list * notation_grammar

val with_grammar_rule_protection : ('a -> 'b) -> 'a -> 'b

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constrexpr
open Notation_term
open Pcoq
open Extend
open Genarg
open Egramml

(** Mapping of grammar productions to camlp4 actions *)

(** This is the part specific to Coq-level Notation and Tactic Notation.
    For the ML-level tactic and vernac extensions, see Egramml. *)

(** For constr notations *)

type grammar_constr_prod_item =
  | GramConstrTerminal of Tok.t
  | GramConstrNonTerminal of constr_prod_entry_key * Id.t option
  | GramConstrListMark of int * bool
    (* tells action rule to make a list of the n previous parsed items;
       concat with last parsed list if true *)

type notation_grammar = {
  notgram_level : int;
  notgram_assoc : gram_assoc option;
  notgram_notation : notation;
  notgram_prods : grammar_constr_prod_item list list;
  notgram_typs : notation_var_internalization_type list;
}

(** {5 Extending the parser with Summary-synchronized commands} *)

type 'a grammar_command
(** Type of synchronized parsing extensions. The ['a] type should be
    marshallable. *)

val create_grammar_command : string -> ('a -> int) -> 'a grammar_command
(** Create a new grammar-modifying command with the given name. The function
    should modify the parser state and return the number of grammar extensions
    performed. *)

val extend_grammar : 'a grammar_command -> 'a -> unit
(** Extend the grammar of Coq with the given data. *)

(** {5 Adding notations} *)

val extend_constr_grammar : Notation.level -> notation_grammar -> unit
(** Add a term notation rule to the parsing system. *)

val recover_constr_grammar : notation -> Notation.level -> notation_grammar
(** For a declared grammar, returns the rule + the ordered entry types
    of variables in the rule (for use in the interpretation) *)

val with_grammar_rule_protection : ('a -> 'b) -> 'a -> 'b

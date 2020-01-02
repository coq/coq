(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Extend
open Constrexpr

(** Dealing with precedences *)

type notation_signature =
  notation_entry * entry_level * entry_relative_level list * constr_entry_key list
  (* first argument is InCustomEntry s for custom entries *)

type grammar_constr_prod_item =
  | GramConstrTerminal of string Tok.p
  | GramConstrNonTerminal of Extend.constr_prod_entry_key * Id.t option
  | GramConstrListMark of int * bool * int
    (* tells action rule to make a list of the n previous parsed items;
       concat with last parsed list when true; additionally release
       the p last items as if they were parsed autonomously *)

(** Grammar rules for a notation *)

type one_notation_grammar = {
  notgram_signature : notation_signature;
  notgram_assoc : Gramlib.Gramext.g_assoc option;
  notgram_notation : Constrexpr.notation;
  notgram_prods : grammar_constr_prod_item list list;
}

type notation_grammar = {
  notgram_onlyprinting : bool;
  notgram_rules : one_notation_grammar list
}

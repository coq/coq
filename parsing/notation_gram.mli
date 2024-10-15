(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

type grammar_constr_prod_item =
  | GramConstrTerminal of bool (* true = in keyword position *) * string
  | GramConstrNonTerminal of Extend.constr_prod_entry_key * Id.t option
  | GramConstrListMark of int * bool * int
    (* tells action rule to make a list of the n previous parsed items;
       concat with last parsed list when true; additionally release
       the p last items as if they were parsed autonomously *)

(** Grammar rules for a notation *)

type one_notation_grammar = {
  notgram_level : Notationextern.level;
  notgram_assoc : Gramlib.Gramext.g_assoc option;
  notgram_notation : Constrexpr.notation;
  notgram_prods : grammar_constr_prod_item list list;
  notgram_typs : Extend.constr_entry_key list;
}

type notation_grammar = one_notation_grammar list

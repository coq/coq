(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

type tactic_grammar = {
  tacgram_level : int;
  tacgram_prods : grammar_prod_item list;
}

(** {5 Adding notations} *)

val extend_constr_grammar : Notation.level -> notation_grammar -> unit
(** Add a term notation rule to the parsing system. *)

val extend_tactic_grammar : KerName.t -> tactic_grammar -> unit
(** Add a tactic notation rule to the parsing system. This produces a TacAlias
    tactic with the provided kernel name. *)

val extend_ml_tactic_grammar : Tacexpr.ml_tactic_name -> grammar_prod_item list list -> unit
(** Add a ML tactic notation rule to the parsing system. This produces a
    TacML tactic with the provided string as name. *)

val recover_constr_grammar : notation -> Notation.level -> notation_grammar
(** For a declared grammar, returns the rule + the ordered entry types
    of variables in the rule (for use in the interpretation) *)

val with_grammar_rule_protection : ('a -> 'b) -> 'a -> 'b

(** {5 Adding tactic quotations} *)

val create_ltac_quotation : string -> ('grm Loc.located -> 'raw) ->
  ('raw, 'glb, 'top) genarg_type -> 'grm Gram.entry -> unit
(** [create_ltac_quotation name f wit e] adds a quotation rule to Ltac, that is,
    Ltac grammar now accepts arguments of the form ["name" ":" <e>], and
    generates a generic argument using [f] on the entry parsed by [e]. *)

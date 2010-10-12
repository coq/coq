(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat
open Util
open Names
open Topconstr
open Pcoq
open Extend
open Vernacexpr
open Ppextend
open Rawterm
open Genarg
open Mod_subst

(** Mapping of grammar productions to camlp4 actions
    Used for Coq-level Notation and Tactic Notation,
    and for ML-level tactic and vernac extensions
 *)

(** For constr notations *)

type grammar_constr_prod_item =
  | GramConstrTerminal of Tok.t
  | GramConstrNonTerminal of constr_prod_entry_key * identifier option
  | GramConstrListMark of int * bool
    (* tells action rule to make a list of the n previous parsed items; 
       concat with last parsed list if true *)

type notation_grammar =
    int * gram_assoc option * notation * grammar_constr_prod_item list list

(** For tactic and vernac notations *)

type grammar_prod_item =
  | GramTerminal of string
  | GramNonTerminal of loc * argument_type *
      prod_entry_key * identifier option

(** Adding notations *)

type all_grammar_command =
  | Notation of
	 (precedence * tolerability list)
	  * notation_var_internalization_type list
	   (** not needed for defining grammar, hosted by egrammar for
	       transmission to interp_aconstr (via recover_notation_grammar) *)
	  * notation_grammar
  | TacticGrammar of
      (string * int * grammar_prod_item list *
         (dir_path * Tacexpr.glob_tactic_expr))

val extend_grammar : all_grammar_command -> unit

val extend_tactic_grammar :
  string -> grammar_prod_item list list -> unit

val extend_vernac_command_grammar :
  string -> vernac_expr Gram.entry option -> grammar_prod_item list list -> unit

val get_extend_vernac_grammars :
 unit -> (string * grammar_prod_item list list) list

(** For a declared grammar, returns the rule + the ordered entry types
    of variables in the rule (for use in the interpretation) *)
val recover_notation_grammar :
  notation -> (precedence * tolerability list) ->
  notation_var_internalization_type list * notation_grammar

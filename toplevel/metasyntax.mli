(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Libnames
open Ppextend
open Extend
open Tacexpr
open Vernacexpr
open Symbols
open Topconstr
(*i*)

(* Adding grammar and pretty-printing objects in the environment *)

val add_syntax_obj : string -> raw_syntax_entry list -> unit

val add_grammar_obj : string -> raw_grammar_entry list -> unit
val add_token_obj : string -> unit
val add_tactic_grammar :
  (string * (string * grammar_production list) * raw_tactic_expr) list -> unit

val add_infix :
  grammar_associativity -> precedence -> string -> reference
    -> scope_name option -> unit
val add_distfix :
  grammar_associativity -> precedence -> string -> reference
    -> scope_name option -> unit
val add_delimiters : scope_name -> delimiters -> unit

val add_notation : string -> constr_expr
    -> syntax_modifier list -> scope_name option -> unit

val add_syntax_extension : string -> syntax_modifier list -> unit

val print_grammar : string -> string -> unit


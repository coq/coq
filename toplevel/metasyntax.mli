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
open Extend
open Tacexpr
open Vernacexpr
open Symbols
(*i*)

(* Adding grammar and pretty-printing objects in the environment *)

val add_syntax_obj : string -> syntax_entry_ast list -> unit

val add_grammar_obj : string -> grammar_entry_ast list -> unit
val add_token_obj : string -> unit
val add_tactic_grammar :
  (string * (string * grammar_production list) * raw_tactic_expr) list -> unit

val add_infix :
  Gramext.g_assoc option -> precedence -> string -> qualid located
    -> scope_name option -> unit
val add_distfix :
  Gramext.g_assoc option -> precedence -> string -> Coqast.t 
    -> scope_name option -> unit
val add_delimiters : scope_name -> delimiters -> unit

val add_notation : 
  Gramext.g_assoc option -> precedence -> string -> Coqast.t
    -> (string * precedence) list -> scope_name option -> unit

val print_grammar : string -> string -> unit


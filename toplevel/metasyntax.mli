(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Extend
open Vernacexpr
(*i*)

(* Adding grammar and pretty-printing objects in the environment *)

val add_syntax_obj : string -> syntax_entry_ast list -> unit

val add_grammar_obj : string -> grammar_entry_ast list -> unit
val add_token_obj : string -> unit
val add_tactic_grammar :  (string * (string * grammar_production list) * Tacexpr.raw_tactic_expr) list -> unit

val add_infix :
  Gramext.g_assoc option -> int -> string -> Libnames.qualid Util.located -> unit
val add_distfix :
  Gramext.g_assoc option -> int -> string -> Coqast.t -> unit

val print_grammar : string -> string -> unit

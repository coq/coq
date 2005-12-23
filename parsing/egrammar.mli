(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Topconstr
open Ast
open Coqast
open Vernacexpr
open Ppextend
open Extend
open Rawterm
open Mod_subst
(*i*)

type notation_grammar = 
    int * Gramext.g_assoc option * notation * prod_item list

type all_grammar_command =
  | Notation of (precedence * tolerability list) * notation_grammar
  | Grammar of grammar_command
  | TacticGrammar of
      (string * int * grammar_production list * 
        (Names.dir_path * Tacexpr.glob_tactic_expr))

val extend_grammar : all_grammar_command -> unit

(* Add grammar rules for tactics *)
type grammar_tactic_production =
  | TacTerm of string
  | TacNonTerm of loc * (Token.t Gramext.g_symbol * Genarg.argument_type) * string option

val extend_tactic_grammar :
  string -> grammar_tactic_production list list -> unit

val extend_vernac_command_grammar :
  string -> grammar_tactic_production list list -> unit

val get_extend_tactic_grammars :
 unit -> (string * grammar_tactic_production list list) list
val get_extend_vernac_grammars :
 unit -> (string * grammar_tactic_production list list) list
val reset_extend_grammars_v8 : unit -> unit

val interp_entry_name : int -> string -> string -> 
  entry_type * Token.t Gramext.g_symbol

val recover_notation_grammar :
  notation -> (precedence * tolerability list) -> notation_grammar

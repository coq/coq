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

val add_infix : locality_flag -> (string * syntax_modifier list) ->
  reference -> (string * syntax_modifier list) option ->
    scope_name option -> unit
val add_distfix : locality_flag ->
  grammar_associativity -> precedence -> string -> reference
    -> scope_name option -> unit
val translate_distfix : grammar_associativity -> string -> reference ->
  Gramext.g_assoc * string * constr_expr

val add_delimiters : scope_name -> string -> unit
val add_class_scope : scope_name -> Classops.cl_typ -> unit

val add_notation : locality_flag -> constr_expr
  -> (string * syntax_modifier list) option
  -> (string * syntax_modifier list) option
      -> scope_name option -> unit

val add_notation_interpretation : string -> Constrintern.implicits_env
  -> constr_expr -> scope_name option -> unit

val add_syntax_extension : locality_flag
  -> (string * syntax_modifier list) option
  -> (string * syntax_modifier list) option -> unit

val print_grammar : string -> string -> unit

val merge_modifiers : Gramext.g_assoc option -> int option -> 
  syntax_modifier list -> syntax_modifier list

val interp_infix_modifiers : syntax_modifier list ->
  Gramext.g_assoc option * precedence option * bool * string located option

val standardise_locatable_notation : string -> string

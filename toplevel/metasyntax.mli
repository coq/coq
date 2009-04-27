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
open Notation
open Topconstr
(*i*)

val add_token_obj : string -> unit

(* Adding a tactic notation in the environment *)

val add_tactic_notation : 
  int * grammar_tactic_prod_item_expr list * raw_tactic_expr -> unit

(* Adding a (constr) notation in the environment*)

val add_infix : locality_flag -> (string * syntax_modifier list) ->
  reference -> scope_name option -> unit

val add_notation : locality_flag -> constr_expr ->
  (string * syntax_modifier list) -> scope_name option -> unit

(* Declaring delimiter keys and default scopes *)

val add_delimiters : scope_name -> string -> unit
val add_class_scope : scope_name -> Classops.cl_typ -> unit

(* Add only the interpretation of a notation that already has pa/pp rules *)

val add_notation_interpretation : string -> Constrintern.implicits_env ->
  constr_expr -> scope_name option -> unit

(* Add only the parsing/printing rule of a notation *)

val add_syntax_extension : 
  locality_flag -> (string * syntax_modifier list) -> unit

(* Print the Camlp4 state of a grammar *)

val print_grammar : string -> unit

(* Removes quotes in a notation *)

val standardize_locatable_notation : string -> string

(* Evaluate whether a notation is not printable *)

val is_not_printable : aconstr -> bool

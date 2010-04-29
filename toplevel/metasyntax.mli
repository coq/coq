(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Util
open Names
open Libnames
open Ppextend
open Extend
open Tacexpr
open Vernacexpr
open Notation
open Topconstr

val add_token_obj : string -> unit

(** Adding a tactic notation in the environment *)

val add_tactic_notation :
  int * grammar_tactic_prod_item_expr list * raw_tactic_expr -> unit

(** Adding a (constr) notation in the environment*)

val add_infix : locality_flag -> (lstring * syntax_modifier list) ->
  constr_expr -> scope_name option -> unit

val add_notation : locality_flag -> constr_expr ->
  (lstring * syntax_modifier list) -> scope_name option -> unit

(** Declaring delimiter keys and default scopes *)

val add_delimiters : scope_name -> string -> unit
val add_class_scope : scope_name -> Classops.cl_typ -> unit

(** Add only the interpretation of a notation that already has pa/pp rules *)

val add_notation_interpretation :
  (lstring * constr_expr * scope_name option) -> unit

(** Add a notation interpretation for supporting the "where" clause *)

val set_notation_for_interpretation : Constrintern.full_internalization_env ->
  (lstring * constr_expr * scope_name option) -> unit

(** Add only the parsing/printing rule of a notation *)

val add_syntax_extension :
  locality_flag -> (lstring * syntax_modifier list) -> unit

(** Add a syntactic definition (as in "Notation f := ...") *)

val add_syntactic_definition : identifier -> identifier list * constr_expr ->
  bool -> bool -> unit

(** Print the Camlp4 state of a grammar *)

val print_grammar : string -> unit

val check_infix_modifiers : syntax_modifier list -> unit

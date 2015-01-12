(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Tacexpr
open Vernacexpr
open Notation
open Constrexpr
open Notation_term

val add_token_obj : string -> unit

(** Adding a tactic notation in the environment *)

val add_tactic_notation :
  locality_flag * int * grammar_tactic_prod_item_expr list * raw_tactic_expr ->
    unit

type atomic_entry = string * Genarg.glob_generic_argument list option

val add_ml_tactic_notation : ml_tactic_name ->
  Egramml.grammar_prod_item list list -> atomic_entry list -> unit

(** Adding a (constr) notation in the environment*)

val add_infix : locality_flag -> (lstring * syntax_modifier list) ->
  constr_expr -> scope_name option -> unit

val add_notation : locality_flag -> constr_expr ->
  (lstring * syntax_modifier list) -> scope_name option -> unit

val add_notation_extra_printing_rule : string -> string -> string -> unit

(** Declaring delimiter keys and default scopes *)

val add_delimiters : scope_name -> string -> unit
val add_class_scope : scope_name -> scope_class list -> unit

(** Add only the interpretation of a notation that already has pa/pp rules *)

val add_notation_interpretation :
  (lstring * constr_expr * scope_name option) -> unit

(** Add a notation interpretation for supporting the "where" clause *)

val set_notation_for_interpretation : Constrintern.internalization_env ->
  (lstring * constr_expr * scope_name option) -> unit

(** Add only the parsing/printing rule of a notation *)

val add_syntax_extension :
  locality_flag -> (lstring * syntax_modifier list) -> unit

(** Add a syntactic definition (as in "Notation f := ...") *)

val add_syntactic_definition : Id.t -> Id.t list * constr_expr ->
  bool -> Flags.compat_version option -> unit

(** Print the Camlp4 state of a grammar *)

val pr_grammar : string -> Pp.std_ppcmds

val check_infix_modifiers : syntax_modifier list -> unit

val with_syntax_protection : ('a -> 'b) -> 'a -> 'b

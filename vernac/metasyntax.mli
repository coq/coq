(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Vernacexpr
open Notation
open Constrexpr
open Notation_term
open Environ

val add_token_obj : string -> unit

(** Adding a (constr) notation in the environment*)

val add_infix : local:bool -> Deprecation.t option -> env -> (lstring * syntax_modifier list) ->
  constr_expr -> scope_name option -> unit

val add_notation : local:bool -> Deprecation.t option -> env -> constr_expr ->
  (lstring * syntax_modifier list) -> scope_name option -> unit

val add_notation_extra_printing_rule : string -> string -> string -> unit

(** Declaring scopes, delimiter keys and default scopes *)

val declare_scope : locality_flag -> scope_name -> unit
val add_delimiters : locality_flag -> scope_name -> string -> unit
val remove_delimiters : locality_flag -> scope_name -> unit
val add_class_scope : locality_flag -> scope_name -> scope_class list -> unit

(** Add only the interpretation of a notation that already has pa/pp rules *)

val add_notation_interpretation :
  env -> (lstring * constr_expr * scope_name option) -> unit

(** Add a notation interpretation for supporting the "where" clause *)

val set_notation_for_interpretation : env -> Constrintern.internalization_env ->
  (lstring * constr_expr * scope_name option) -> unit

(** Add only the parsing/printing rule of a notation *)

val add_syntax_extension :
  local:bool -> (lstring * syntax_modifier list) -> unit

(** Add a syntactic definition (as in "Notation f := ...") *)

val add_syntactic_definition : local:bool -> Deprecation.t option -> env ->
  Id.t -> Id.t list * constr_expr -> Flags.compat_version option -> unit

(** Print the Camlp5 state of a grammar *)

val pr_grammar : string -> Pp.t
val pr_custom_grammar : string -> Pp.t

val check_infix_modifiers : syntax_modifier list -> unit

val with_syntax_protection : ('a -> 'b) -> 'a -> 'b

val declare_custom_entry : locality_flag -> string -> unit

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Vernacexpr
open Notation
open Constrexpr
open Notation_term

val add_token_obj : string -> unit

(** Adding a (constr) notation in the environment*)

val add_infix : locality_flag -> (lstring * syntax_modifier list) ->
  constr_expr -> scope_name option -> unit

val add_notation : locality_flag -> constr_expr ->
  (lstring * syntax_modifier list) -> scope_name option -> unit

val add_notation_extra_printing_rule : string -> string -> string -> unit

(** Declaring delimiter keys and default scopes *)

val add_delimiters : scope_name -> string -> unit
val remove_delimiters : scope_name -> unit
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

type any_entry = AnyEntry : 'a Pcoq.Gram.entry -> any_entry

val register_grammar : string -> any_entry list -> unit

val check_infix_modifiers : syntax_modifier list -> unit

val with_syntax_protection : ('a -> 'b) -> 'a -> 'b

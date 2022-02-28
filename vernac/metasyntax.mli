(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

(** Declare syntax rules for a notation *)
val add_notation_syntax : local:bool -> infix:bool -> Deprecation.t option -> constr_expr ->
  (lstring * syntax_modifier CAst.t list) -> unit

(** Declare interpretation for a notation *)
val add_notation_interp : local:bool -> infix:bool -> Deprecation.t option -> env -> constr_expr ->
  (lstring * syntax_modifier CAst.t list) -> scope_name option -> unit

(** Declare a (constr) notation. This function is the composition of
    [add_notation_syntax] and [add_notation_interp]. *)
val add_notation : local:bool -> infix:bool -> Deprecation.t option -> env -> constr_expr ->
  (lstring * syntax_modifier CAst.t list) -> scope_name option -> unit

val add_notation_extra_printing_rule : string -> string -> string -> unit

(** Declaring scopes, delimiter keys and default scopes *)

val declare_scope : locality_flag -> scope_name -> unit
val add_delimiters : locality_flag -> scope_name -> string -> unit
val remove_delimiters : locality_flag -> scope_name -> unit
val add_class_scope : locality_flag -> scope_name -> scope_class list -> unit

(** Add a notation interpretation associated to a "where" clause (already has pa/pp rules) *)

type where_decl_notation

val prepare_where_notation :
  decl_notation -> where_decl_notation
  (** Interpret the modifiers of a where-notation *)

val add_notation_interpretation :
  local:bool -> env -> where_decl_notation -> unit
  (** Declare the interpretation of the where-notation *)

val set_notation_for_interpretation :
  env -> Constrintern.internalization_env -> where_decl_notation -> unit
  (** Set the interpretation of the where-notation for interpreting a mutual block *)

(** Add only the parsing/printing rule of a notation *)

val add_reserved_notation :
  local:bool -> infix:bool -> (lstring * syntax_modifier CAst.t list) -> unit

(** Add a syntactic definition (as in "Notation f := ...") *)

val add_abbreviation : local:bool -> Deprecation.t option -> env ->
  Id.t -> Id.t list * constr_expr -> syntax_modifier CAst.t list -> unit

(** Print the Camlp5 state of a grammar *)

val pr_grammar : string -> Pp.t
val pr_custom_grammar : string -> Pp.t

val with_syntax_protection : ('a -> 'b) -> 'a -> 'b

val declare_custom_entry : locality_flag -> string -> unit

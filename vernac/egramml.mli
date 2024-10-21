(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacexpr

(** Mapping of grammar productions to camlp5 actions. *)

(** This is the part specific to vernac extensions.
    For the Rocq-level Notation and Tactic Notation, see Egramrocq. *)

type 's grammar_prod_item =
  | GramTerminal of string
  | GramNonTerminal : ('a Genarg.raw_abstract_argument_type *
      ('s, _, 'a) Procq.Symbol.t) Loc.located -> 's grammar_prod_item

val declare_vernac_command_grammar :
  allow_override:bool -> extend_name -> vernac_expr Procq.Entry.t option ->
    vernac_expr grammar_prod_item list -> unit

val extend_vernac_command_grammar : undoable:bool -> extend_name -> unit

val grammar_extend
  : ?plugin_uid:(string * string)
  -> 'a Procq.Entry.t
  -> 'a Procq.extend_statement
  -> unit

val get_extend_vernac_rule : extend_name -> vernac_expr grammar_prod_item list

val proj_symbol : ('a, 'b, 'c) Extend.ty_user_symbol -> ('a, 'b, 'c) Genarg.genarg_type

(** Utility function reused in Egramrocq : *)

val make_rule :
  (Loc.t -> Genarg.raw_generic_argument list -> 'a) ->
  'a grammar_prod_item list -> 'a Procq.Production.t

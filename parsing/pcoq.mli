(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Util
open Names
open Rawterm
open Ast
open Genarg
open Topconstr
open Tacexpr
open Vernacexpr
open Libnames
open Extend

(* The lexer and parser of Coq. *)

val lexer : Token.lexer

module Gram : Grammar.S with type te = Token.t

type grammar_object
type typed_entry

val type_of_typed_entry : typed_entry -> Extend.entry_type
val object_of_typed_entry : typed_entry -> grammar_object Gram.Entry.e
val weaken_entry : 'a Gram.Entry.e -> grammar_object Gram.Entry.e

val get_constr_entry :
  bool -> constr_entry -> grammar_object Gram.Entry.e * int option * bool

val symbol_of_production : Gramext.g_assoc option -> constr_entry ->
  bool -> constr_production_entry -> Token.t Gramext.g_symbol

val grammar_extend :
  'a Gram.Entry.e -> Gramext.position option ->
    (string option * Gramext.g_assoc option *
     (Token.t Gramext.g_symbol list * Gramext.g_action) list) list
    -> unit

val remove_grammars : int -> unit

val camlp4_verbosity : bool -> ('a -> unit) -> 'a -> unit

(* Parse a string *)

val parse_string : 'a Gram.Entry.e -> string -> 'a
val eoi_entry : 'a Gram.Entry.e -> 'a Gram.Entry.e
val map_entry : ('a -> 'b) -> 'a Gram.Entry.e -> 'b Gram.Entry.e

(* Entry types *)

(* Table of Coq's grammar entries *)

type gram_universe

val create_univ_if_new : string -> string * gram_universe
val get_univ : string -> string * gram_universe
val get_entry : string * gram_universe -> string -> typed_entry

val entry_type : string * gram_universe -> string -> entry_type option

val get_entry_type : string * string -> entry_type
val create_entry_if_new :
  string * gram_universe -> string -> entry_type -> unit
val create_entry :
  string * gram_universe -> string -> entry_type -> typed_entry
val force_entry_type :
  string * gram_universe -> string -> entry_type -> typed_entry

val create_constr_entry :
  string * gram_universe -> string -> constr_expr Gram.Entry.e
val create_generic_entry : string -> ('a, constr_expr,raw_tactic_expr) abstract_argument_type -> 'a Gram.Entry.e
val get_generic_entry : string -> grammar_object Gram.Entry.e
val get_generic_entry_type : string * gram_universe -> string -> Genarg.argument_type

type parser_type =
  | ConstrParser
  | CasesPatternParser

val entry_type_of_parser : parser_type -> entry_type option
val parser_type_from_name : string -> parser_type

(* Quotations in ast parser *)
val define_ast_quotation : bool -> string -> (Coqast.t Gram.Entry.e) -> unit
val set_globalizer : (constr_expr -> Coqast.t) -> unit

(* The default parser for actions in grammar rules *)

val default_action_parser : dynamic_grammar Gram.Entry.e
val set_default_action_parser : parser_type -> unit

(* The main entry: reads an optional vernac command *)

val main_entry : (loc * vernac_expr) option Gram.Entry.e

(* Initial state of the grammar *)

module Prim :
  sig
    open Util
    open Names
    open Libnames
    val preident : string Gram.Entry.e
    val ident : identifier Gram.Entry.e
    val name : name located Gram.Entry.e
    val identref : identifier located Gram.Entry.e
    val base_ident : identifier Gram.Entry.e
    val natural : int Gram.Entry.e
    val bigint : Bignat.bigint Gram.Entry.e
    val integer : int Gram.Entry.e
    val string : string Gram.Entry.e
    val qualid : qualid located Gram.Entry.e
    val reference : reference Gram.Entry.e
    val dirpath : dir_path Gram.Entry.e
    val ne_string : string Gram.Entry.e
    val hyp : identifier Gram.Entry.e
    (* v7 only entries *)
    val astpat: typed_ast Gram.Entry.e
    val ast : Coqast.t Gram.Entry.e
    val astlist : Coqast.t list Gram.Entry.e
    val ast_eoi : Coqast.t Gram.Entry.e
    val var : identifier Gram.Entry.e
  end

module Constr :
  sig
    val constr : constr_expr Gram.Entry.e
    val constr_eoi : constr_expr Gram.Entry.e
    val lconstr : constr_expr Gram.Entry.e
    val binder_constr : constr_expr Gram.Entry.e
    val operconstr : constr_expr Gram.Entry.e
    val ident : identifier Gram.Entry.e
    val global : reference Gram.Entry.e
    val sort : rawsort Gram.Entry.e
    val pattern : cases_pattern_expr Gram.Entry.e
    val annot : constr_expr Gram.Entry.e
    val constr_pattern : constr_expr Gram.Entry.e
    val lconstr_pattern : constr_expr Gram.Entry.e
    val binder : (name located list * constr_expr) Gram.Entry.e
    val binder_let : local_binder Gram.Entry.e
  end

module Module : 
  sig
    val module_expr : module_ast Gram.Entry.e
    val module_type : module_type_ast Gram.Entry.e
  end

module Tactic :
  sig
    open Rawterm
    val castedopenconstr : constr_expr Gram.Entry.e
    val constr_with_bindings : constr_expr with_bindings Gram.Entry.e
    val bindings : constr_expr bindings Gram.Entry.e
    val constrarg : (constr_expr,reference) may_eval Gram.Entry.e
    val quantified_hypothesis : quantified_hypothesis Gram.Entry.e
    val int_or_var : int or_var Gram.Entry.e
    val red_expr : raw_red_expr Gram.Entry.e
    val simple_tactic : raw_atomic_tactic_expr Gram.Entry.e
    val simple_intropattern : Genarg.intro_pattern_expr Gram.Entry.e
    val tactic_arg : raw_tactic_arg Gram.Entry.e
    val tactic : raw_tactic_expr Gram.Entry.e
    val tactic_eoi : raw_tactic_expr Gram.Entry.e
  end

module Vernac_ :
  sig
    open Decl_kinds
    val gallina : vernac_expr Gram.Entry.e
    val gallina_ext : vernac_expr Gram.Entry.e
    val command : vernac_expr Gram.Entry.e
    val syntax : vernac_expr Gram.Entry.e
    val vernac : vernac_expr Gram.Entry.e
    val vernac_eoi : vernac_expr Gram.Entry.e
  end

val reset_all_grammars : unit -> unit

(* Registering/resetting the level of an entry *)

val find_position : 
  bool -> bool -> Gramext.g_assoc option -> int option ->
    Gramext.position option * Gramext.g_assoc option * string option

val remove_levels : int -> unit 

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Names
open Tacexpr
open Ast
open Genarg
open Tacexpr
open Vernacexpr

(* The lexer and parser of Coq. *)

val lexer : Token.lexer

module Gram : Grammar.S with type te = Token.t

type grammar_object
type typed_entry

val type_of_typed_entry : typed_entry -> entry_type
val object_of_typed_entry : typed_entry -> grammar_object Gram.Entry.e

val grammar_extend :
  typed_entry -> Gramext.position option ->
    (string option * Gramext.g_assoc option *
     (Token.t Gramext.g_symbol list * Gramext.g_action) list) list
    -> unit

val remove_grammars : int -> unit

(* Parse a string *)

val parse_string : 'a Gram.Entry.e -> string -> 'a
val eoi_entry : 'a Gram.Entry.e -> 'a Gram.Entry.e
val map_entry : ('a -> 'b) -> 'a Gram.Entry.e -> 'b Gram.Entry.e

(*
val slam_ast : Coqast.loc -> Coqast.t -> Coqast.t -> Coqast.t
val abstract_binders_ast :
  Coqast.loc -> string -> Coqast.t -> Coqast.t -> Coqast.t
*)

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
  string * gram_universe -> string -> Coqast.t Gram.Entry.e
val create_generic_entry : string -> ('a, constr_ast,raw_tactic_expr) abstract_argument_type -> 'a Gram.Entry.e
val get_generic_entry : string -> grammar_object Gram.Entry.e
val get_generic_entry_type : string * gram_universe -> string -> Genarg.argument_type

type parser_type =
  | AstListParser
  | AstParser
  | ConstrParser
  | TacticParser
  | VernacParser

val entry_type_from_name : string -> entry_type
val entry_type_of_parser : parser_type -> entry_type option
val parser_type_from_name : string -> parser_type

(* Quotations *)
val define_quotation : bool -> string -> (Coqast.t Gram.Entry.e) -> unit
val set_globalizer : (typed_ast -> typed_ast) -> unit

(* The default parser for actions in grammar rules *)

val default_action_parser : typed_ast Gram.Entry.e
val set_default_action_parser : parser_type -> unit

(* The main entry: reads an optional vernac command *)

val main_entry : (Coqast.loc * vernac_expr) option Gram.Entry.e

(* Initial state of the grammar *)

module Prim :
  sig
    open Util
    open Names
    open Nametab
    val preident : string Gram.Entry.e
    val ident : identifier Gram.Entry.e
    val rawident : identifier located Gram.Entry.e
    val natural : int Gram.Entry.e
    val integer : int Gram.Entry.e
    val string : string Gram.Entry.e
    val qualid : qualid located Gram.Entry.e
    val reference : reference_expr Gram.Entry.e
    val dirpath : dir_path Gram.Entry.e
    val astpat: typed_ast Gram.Entry.e
    val ast : Coqast.t Gram.Entry.e
    val astlist : Coqast.t list Gram.Entry.e
    val ast_eoi : Coqast.t Gram.Entry.e
    val astact : Coqast.t Gram.Entry.e
    val metaident : Coqast.t Gram.Entry.e
    val numarg : Coqast.t Gram.Entry.e
    val var : Coqast.t Gram.Entry.e
  end

module Constr :
  sig
    val constr : Coqast.t Gram.Entry.e
    val constr0 : Coqast.t Gram.Entry.e
    val constr1 : Coqast.t Gram.Entry.e
    val constr2 : Coqast.t Gram.Entry.e
    val constr3 : Coqast.t Gram.Entry.e
    val lassoc_constr4 : Coqast.t Gram.Entry.e
    val constr5 : Coqast.t Gram.Entry.e
    val constr6 : Coqast.t Gram.Entry.e
    val constr7 : Coqast.t Gram.Entry.e
    val constr8 : Coqast.t Gram.Entry.e
    val constr9 : Coqast.t Gram.Entry.e
    val constr91 : Coqast.t Gram.Entry.e
    val constr10 : Coqast.t Gram.Entry.e
    val constr_eoi : constr_ast Gram.Entry.e
    val lconstr : Coqast.t Gram.Entry.e
    val ident : Coqast.t Gram.Entry.e
    val qualid : Coqast.t Gram.Entry.e
    val global : Coqast.t Gram.Entry.e
    val ne_ident_comma_list : Coqast.t list Gram.Entry.e
    val ne_constr_list : Coqast.t list Gram.Entry.e
    val sort : Coqast.t Gram.Entry.e
    val pattern : Coqast.t Gram.Entry.e
    val constr_pattern : Coqast.t Gram.Entry.e
    val ne_binders_list : Coqast.t list Gram.Entry.e
  end

module Tactic :
  sig
    open Rawterm
    val castedopenconstr : constr_ast Gram.Entry.e
    val constr_with_bindings : constr_ast with_bindings Gram.Entry.e
    val constrarg : constr_ast may_eval Gram.Entry.e
    val quantified_hypothesis : quantified_hypothesis Gram.Entry.e
    val int_or_var : int or_var Gram.Entry.e
    val red_expr : raw_red_expr Gram.Entry.e
    val simple_tactic : raw_atomic_tactic_expr Gram.Entry.e
    val tactic_arg : raw_tactic_arg Gram.Entry.e
    val tactic : raw_tactic_expr Gram.Entry.e
    val tactic_eoi : raw_tactic_expr Gram.Entry.e
  end

module Vernac_ :
  sig
    open Util
    open Nametab
    val thm_token : theorem_kind Gram.Entry.e
    val class_rawexpr : class_rawexpr Gram.Entry.e
    val gallina : vernac_expr Gram.Entry.e
    val gallina_ext : vernac_expr Gram.Entry.e
    val command : vernac_expr Gram.Entry.e
    val syntax : vernac_expr Gram.Entry.e
    val vernac : vernac_expr Gram.Entry.e
    val vernac_eoi : vernac_expr Gram.Entry.e
(*
    val reduce : Coqast.t list Gram.Entry.e
*)
  end

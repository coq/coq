(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(* The lexer and parser of Coq. *)

val lexer : Token.lexer

module Gram : Grammar.S

type typed_entry =
  | Ast of Coqast.t Gram.Entry.e
  | ListAst of Coqast.t list Gram.Entry.e

val grammar_extend :
  typed_entry -> Gramext.position option ->
    (string option * Gramext.g_assoc option *
     (Gramext.g_symbol list * Gramext.g_action) list) list
    -> unit

val remove_grammars : int -> unit

(* Parse a string *)

val parse_string : 'a Gram.Entry.e -> string -> 'a
val eoi_entry : 'a Gram.Entry.e -> 'a Gram.Entry.e
val map_entry : ('a -> 'b) -> 'a Gram.Entry.e -> 'b Gram.Entry.e

val slam_ast : Coqast.loc -> Coqast.t -> Coqast.t -> Coqast.t
val abstract_binders_ast :
  Coqast.loc -> string -> Coqast.t -> Coqast.t -> Coqast.t

(* Entry types *)

type entry_type = ETast | ETastl

val entry_type : Coqast.t -> entry_type
val type_of_entry : typed_entry -> entry_type

(* Table of Coq's grammar entries *)

type gram_universe

val get_univ : string -> string * gram_universe
val get_entry :  string * gram_universe -> string -> typed_entry

val create_entry : string * gram_universe -> string -> entry_type ->
  typed_entry
val force_entry_type : string * gram_universe -> string ->
  entry_type -> typed_entry

(* Quotations *)

val define_quotation : bool -> string -> (Coqast.t Gram.Entry.e) -> unit
val update_constr_parser : Coqast.t Gram.Entry.e -> unit
val update_tactic_parser : Coqast.t Gram.Entry.e -> unit
val update_vernac_parser : Coqast.t Gram.Entry.e -> unit

(* The default parser for actions in grammar rules *)

val default_action_parser : Coqast.t Gram.Entry.e
val set_default_action_parser : Coqast.t Gram.Entry.e -> unit
val set_default_action_parser_by_name : string -> unit

(* The main entry: reads an optional vernac command *)

val main_entry : Coqast.t option Gram.Entry.e

(* Initial state of the grammar *)

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
    val constr_eoi : Coqast.t Gram.Entry.e
    val lconstr : Coqast.t Gram.Entry.e
    val ident : Coqast.t Gram.Entry.e
    val qualid : Coqast.t list Gram.Entry.e
    val global : Coqast.t Gram.Entry.e
    val ne_ident_comma_list : Coqast.t list Gram.Entry.e
    val ne_constr_list : Coqast.t list Gram.Entry.e
    val sort : Coqast.t Gram.Entry.e
    val pattern : Coqast.t Gram.Entry.e
    val ne_binders_list : Coqast.t list Gram.Entry.e
  end

module Module : 
  sig
    val identarg : Coqast.t Gram.Entry.e
    val qualidarg : Coqast.t list Gram.Entry.e
    val ne_binders_list : Coqast.t list Gram.Entry.e
    val module_expr : Coqast.t Gram.Entry.e
    val module_type : Coqast.t Gram.Entry.e
  end

module Tactic :
  sig
    val autoargs : Coqast.t list Gram.Entry.e
    val binding_list : Coqast.t Gram.Entry.e
    val castedopenconstrarg : Coqast.t Gram.Entry.e
    val castedconstrarg : Coqast.t Gram.Entry.e
    val clausearg : Coqast.t Gram.Entry.e
    val cofixdecl : Coqast.t list Gram.Entry.e
    val com_binding_list : Coqast.t list Gram.Entry.e
    val constrarg : Coqast.t Gram.Entry.e
    val constrarg_binding_list : Coqast.t list Gram.Entry.e
    val constrarg_list : Coqast.t list Gram.Entry.e
    val fixdecl : Coqast.t list Gram.Entry.e
    val ident_or_numarg : Coqast.t Gram.Entry.e
    val ident_or_constrarg : Coqast.t Gram.Entry.e
    val identarg : Coqast.t Gram.Entry.e
    val hypident : Coqast.t Gram.Entry.e
    val idmeta_arg : Coqast.t Gram.Entry.e
    val idmetahyp : Coqast.t Gram.Entry.e
    val qualidarg : Coqast.t Gram.Entry.e
    val qualidconstarg : Coqast.t Gram.Entry.e
    val input_fun : Coqast.t Gram.Entry.e
    val intropattern : Coqast.t Gram.Entry.e
    val lconstrarg : Coqast.t Gram.Entry.e
    val lconstrarg_binding_list : Coqast.t list Gram.Entry.e
    val let_clause : Coqast.t Gram.Entry.e
    val letcut_clause : Coqast.t Gram.Entry.e
    val match_context_rule : Coqast.t Gram.Entry.e
    val match_hyps : Coqast.t Gram.Entry.e
    val match_pattern : Coqast.t Gram.Entry.e
    val match_context_list : Coqast.t list Gram.Entry.e
    val match_rule : Coqast.t Gram.Entry.e
    val match_list : Coqast.t list Gram.Entry.e
    val ne_identarg_list : Coqast.t list Gram.Entry.e
    val ne_hyp_list : Coqast.t list Gram.Entry.e
    val ne_idmetahyp_list : Coqast.t list Gram.Entry.e
    val ne_qualidarg_list : Coqast.t list Gram.Entry.e
    val ne_qualidconstarg_list : Coqast.t list Gram.Entry.e
    val ne_intropattern : Coqast.t Gram.Entry.e
    val ne_pattern_list : Coqast.t list Gram.Entry.e
    val clause_pattern : Coqast.t Gram.Entry.e
    val ne_unfold_occ_list : Coqast.t list Gram.Entry.e
    val numarg : Coqast.t Gram.Entry.e
    val numarg_binding_list : Coqast.t list Gram.Entry.e
    val one_intropattern : Coqast.t Gram.Entry.e
    val pattern_occ : Coqast.t Gram.Entry.e
    val pattern_occ_hyp : Coqast.t Gram.Entry.e
    val pure_numarg : Coqast.t Gram.Entry.e
    val rec_clause : Coqast.t Gram.Entry.e
    val red_flag : Coqast.t Gram.Entry.e
    val red_tactic : Coqast.t Gram.Entry.e
    val simple_binding : Coqast.t Gram.Entry.e
    val simple_binding_list : Coqast.t list Gram.Entry.e
    val simple_intropattern : Coqast.t Gram.Entry.e
    val simple_tactic : Coqast.t Gram.Entry.e
    val tactic : Coqast.t Gram.Entry.e
    val tactic_arg : Coqast.t Gram.Entry.e
    val tactic_atom0 : Coqast.t Gram.Entry.e
    val tactic_atom : Coqast.t Gram.Entry.e
    val tactic_eoi : Coqast.t Gram.Entry.e
    val tactic_expr : Coqast.t Gram.Entry.e
    val tactic_expr_par : Coqast.t Gram.Entry.e
    val unfold_occ : Coqast.t Gram.Entry.e
    val with_binding_list : Coqast.t Gram.Entry.e
  end

module Vernac_ :
  sig
    val identarg : Coqast.t Gram.Entry.e
    val ne_identarg_list : Coqast.t list Gram.Entry.e
    val qualidarg : Coqast.t Gram.Entry.e
    val qualidconstarg : Coqast.t Gram.Entry.e
    val commentarg : Coqast.t Gram.Entry.e
    val commentarg_list : Coqast.t list Gram.Entry.e
    val ne_qualidarg_list : Coqast.t list Gram.Entry.e
    val numarg : Coqast.t Gram.Entry.e
    val numarg_list : Coqast.t list Gram.Entry.e
    val ne_numarg_list : Coqast.t list Gram.Entry.e
    val stringarg : Coqast.t Gram.Entry.e
    val ne_stringarg_list : Coqast.t list Gram.Entry.e
    val constrarg : Coqast.t Gram.Entry.e
    val ne_constrarg_list : Coqast.t list Gram.Entry.e
    val tacarg : Coqast.t Gram.Entry.e
    val sortarg : Coqast.t Gram.Entry.e
    val theorem_body : Coqast.t Gram.Entry.e
    val thm_tok : Coqast.t Gram.Entry.e

    val gallina : Coqast.t Gram.Entry.e
    val gallina_ext : Coqast.t Gram.Entry.e
    val command : Coqast.t Gram.Entry.e
    val syntax : Coqast.t Gram.Entry.e
    val vernac : Coqast.t Gram.Entry.e
    val vernac_eoi : Coqast.t Gram.Entry.e
  end

module Prim :
  sig
    val ast : Coqast.t Gram.Entry.e
    val ast_eoi : Coqast.t Gram.Entry.e
    val astact : Coqast.t Gram.Entry.e
    val astpat: Coqast.t Gram.Entry.e
    val entry_type : Coqast.t Gram.Entry.e
    val grammar_entry : Coqast.t Gram.Entry.e
    val grammar_entry_eoi : Coqast.t Gram.Entry.e
    val ident : Coqast.t Gram.Entry.e
    val metaident : Coqast.t Gram.Entry.e
    val number : Coqast.t Gram.Entry.e
    val path : Coqast.t Gram.Entry.e
    val string : Coqast.t Gram.Entry.e
    val syntax_entry : Coqast.t Gram.Entry.e
    val syntax_entry_eoi : Coqast.t Gram.Entry.e
    val var : Coqast.t Gram.Entry.e
  end

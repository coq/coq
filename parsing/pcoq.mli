
(* $Id$ *)

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
    val ne_ident_comma_list : Coqast.t list Gram.Entry.e
    val ne_constr_list : Coqast.t list Gram.Entry.e

    val pattern : Coqast.t Gram.Entry.e

(*
    val binder : Coqast.t Gram.Entry.e

    val abstraction_tail : Coqast.t Gram.Entry.e
    val cofixbinder : Coqast.t Gram.Entry.e
    val cofixbinders : Coqast.t list Gram.Entry.e
    val fixbinder : Coqast.t Gram.Entry.e
    val fixbinders : Coqast.t list Gram.Entry.e

    val ne_binder_list : Coqast.t list Gram.Entry.e

    val ne_pattern_list : Coqast.t list Gram.Entry.e
    val pattern_list : Coqast.t list Gram.Entry.e
    val simple_pattern : Coqast.t Gram.Entry.e
*)
  end

module Tactic :
  sig
    val autoarg_adding : Coqast.t Gram.Entry.e
    val autoarg_depth : Coqast.t Gram.Entry.e
    val autoarg_destructing : Coqast.t Gram.Entry.e
    val autoarg_excluding : Coqast.t Gram.Entry.e
    val autoarg_usingTDB : Coqast.t Gram.Entry.e
    val binding_list : Coqast.t Gram.Entry.e
    val clausearg : Coqast.t Gram.Entry.e
    val cofixdecl : Coqast.t list Gram.Entry.e
    val com_binding_list : Coqast.t list Gram.Entry.e
    val comarg : Coqast.t Gram.Entry.e
    val comarg_binding_list : Coqast.t list Gram.Entry.e
    val comarg_list : Coqast.t list Gram.Entry.e
    val fixdecl : Coqast.t list Gram.Entry.e
    val identarg : Coqast.t Gram.Entry.e
    val intropattern : Coqast.t Gram.Entry.e
    val lcomarg : Coqast.t Gram.Entry.e
    val lcomarg_binding_list : Coqast.t list Gram.Entry.e
    val ne_identarg_list : Coqast.t list Gram.Entry.e
    val ne_intropattern : Coqast.t Gram.Entry.e
    val ne_num_list : Coqast.t list Gram.Entry.e
    val ne_pattern_list : Coqast.t list Gram.Entry.e
    val ne_pattern_hyp_list : Coqast.t list Gram.Entry.e
    val ne_unfold_occ_list : Coqast.t list Gram.Entry.e
    val numarg : Coqast.t Gram.Entry.e
    val numarg_binding_list : Coqast.t list Gram.Entry.e
    val one_intropattern : Coqast.t Gram.Entry.e
    val pattern_occ : Coqast.t Gram.Entry.e
    val pattern_occ_hyp : Coqast.t Gram.Entry.e
    val red_flag : Coqast.t Gram.Entry.e
    val red_tactic : Coqast.t Gram.Entry.e
    val simple_binding : Coqast.t Gram.Entry.e
    val simple_binding_list : Coqast.t list Gram.Entry.e
    val simple_intropattern : Coqast.t Gram.Entry.e
    val simple_tactic : Coqast.t Gram.Entry.e
    val tactic : Coqast.t Gram.Entry.e
    val tactic_com : Coqast.t Gram.Entry.e
    val tactic_com_list : Coqast.t Gram.Entry.e
    val tactic_com_tail : Coqast.t Gram.Entry.e
    val tactic_eoi : Coqast.t Gram.Entry.e
    val unfold_occ : Coqast.t Gram.Entry.e
    val with_binding_list : Coqast.t Gram.Entry.e
  end

module Vernac :
  sig
    val binder : Coqast.t Gram.Entry.e
    val block : Coqast.t list Gram.Entry.e
    val block_old_style : Coqast.t list Gram.Entry.e
    val check_tok : Coqast.t Gram.Entry.e
    val comarg : Coqast.t Gram.Entry.e
    val def_tok : Coqast.t Gram.Entry.e
    val definition_tail : Coqast.t Gram.Entry.e
    val dep : Coqast.t Gram.Entry.e
    val destruct_location : Coqast.t Gram.Entry.e
    val destruct_location : Coqast.t Gram.Entry.e
    val extracoindblock : Coqast.t list Gram.Entry.e
    val extraindblock : Coqast.t list Gram.Entry.e
    val field : Coqast.t Gram.Entry.e
    val fields : Coqast.t Gram.Entry.e
    val finite_tok : Coqast.t Gram.Entry.e
    val hyp_tok : Coqast.t Gram.Entry.e
    val hyps_tok : Coqast.t Gram.Entry.e
    val idcom : Coqast.t Gram.Entry.e
    val identarg : Coqast.t Gram.Entry.e
    val import_tok : Coqast.t Gram.Entry.e
    val indpar : Coqast.t Gram.Entry.e
    val lcomarg : Coqast.t Gram.Entry.e
    val lidcom : Coqast.t Gram.Entry.e
    val orient:Coqast.t Gram.Entry.e;; 
    val lvernac : Coqast.t list Gram.Entry.e
    val meta_binding : Coqast.t Gram.Entry.e
    val meta_binding_list : Coqast.t list Gram.Entry.e
    val ne_binder_list : Coqast.t list Gram.Entry.e
    val ne_comarg_list : Coqast.t list Gram.Entry.e
    val ne_identarg_comma_list : Coqast.t list Gram.Entry.e
    val ne_identarg_list : Coqast.t list Gram.Entry.e
    val ne_lidcom : Coqast.t list Gram.Entry.e
    val ne_numarg_list : Coqast.t list Gram.Entry.e
    val ne_stringarg_list : Coqast.t list Gram.Entry.e
    val nefields : Coqast.t list Gram.Entry.e
    val numarg : Coqast.t Gram.Entry.e
    val numarg_list : Coqast.t list Gram.Entry.e
    val onecorec : Coqast.t Gram.Entry.e
    val oneind : Coqast.t Gram.Entry.e
    val oneind_old_style : Coqast.t Gram.Entry.e
    val onerec : Coqast.t Gram.Entry.e
    val onescheme : Coqast.t Gram.Entry.e
    val opt_identarg_list : Coqast.t list Gram.Entry.e
    val option_value : Coqast.t Gram.Entry.e
    val param_tok : Coqast.t Gram.Entry.e
    val params_tok : Coqast.t Gram.Entry.e
    val rec_constr : Coqast.t Gram.Entry.e
    val record_tok : Coqast.t Gram.Entry.e
    val sortdef : Coqast.t Gram.Entry.e
    val specif_tok : Coqast.t Gram.Entry.e
    val specifcorec : Coqast.t list Gram.Entry.e
    val specifrec : Coqast.t list Gram.Entry.e
    val specifscheme : Coqast.t list Gram.Entry.e
    val stringarg : Coqast.t Gram.Entry.e
    val tacarg : Coqast.t Gram.Entry.e
    val theorem_body : Coqast.t Gram.Entry.e
    val theorem_body_line : Coqast.t Gram.Entry.e
    val theorem_body_line_list : Coqast.t list Gram.Entry.e
    val thm_tok : Coqast.t Gram.Entry.e
    val varg_ne_stringarg_list : Coqast.t Gram.Entry.e
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
    val number : Coqast.t Gram.Entry.e
    val path : Coqast.t Gram.Entry.e
    val string : Coqast.t Gram.Entry.e
    val syntax_entry : Coqast.t Gram.Entry.e
    val syntax_entry_eoi : Coqast.t Gram.Entry.e
    val var : Coqast.t Gram.Entry.e
  end

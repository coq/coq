(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Util
open Names
open Ast
open Coqast
open Ppextend
open Topconstr
open Genarg
(*i*)

type entry_type = argument_type

type production_position =
  | BorderProd of bool * Gramext.g_assoc option  (* true=left; false=right *)
  | InternalProd

type 'pos constr_entry_key =
  | ETIdent | ETReference
  | ETConstr of (int * 'pos)
  | ETPattern
  | ETOther of string * string

type constr_production_entry = production_position constr_entry_key
type constr_entry = unit constr_entry_key

type nonterm_prod =
  | ProdList0 of nonterm_prod
  | ProdList1 of nonterm_prod
  | ProdOpt of nonterm_prod
  | ProdPrimitive of constr_production_entry

type prod_item =
  | Term of Token.pattern
  | NonTerm of
      nonterm_prod * (Names.identifier * constr_production_entry) option

type grammar_rule = {
  gr_name : string; 
  gr_production : prod_item list; 
  gr_action : aconstr }

type grammar_entry = { 
  ge_name : string;
  gl_assoc : Gramext.g_assoc option;
  gl_rules : grammar_rule list }

type grammar_command = { 
  gc_univ : string; 
  gc_entries : grammar_entry list }

type grammar_associativity = Gramext.g_assoc option

(* Globalisation and type-checking of Grammar actions *)
type entry_context = identifier list
val to_act_check_vars : entry_context -> grammar_action -> aconstr
val set_ast_to_rawconstr : (entry_context -> constr_expr -> aconstr) -> unit

type syntax_modifier =
  | SetItemLevel of string list * int
  | SetLevel of int
  | SetAssoc of Gramext.g_assoc
  | SetEntryType of string * constr_entry
  | SetOnlyParsing

type nonterm =
  | NtShort of string
  | NtQual of string * string
type grammar_production =
  | VTerm of string
  | VNonTerm of loc * nonterm * Names.identifier option
type raw_grammar_rule = string * grammar_production list * grammar_action
type raw_grammar_entry = string * grammar_associativity * raw_grammar_rule list

val terminal : string -> string * string

val rename_command_entry : string -> string

val explicitize_entry : string -> string -> constr_entry

val subst_grammar_command : 
  Names.substitution -> grammar_command -> grammar_command

(* unparsing objects *)

type 'pat unparsing_hunk = 
  | PH of 'pat * string option * parenRelation
  | RO of string
  | UNP_BOX of ppbox * 'pat unparsing_hunk list
  | UNP_BRK of int * int
  | UNP_TBRK of int * int
  | UNP_TAB
  | UNP_FNL
  | UNP_SYMBOLIC of string * string * 'pat unparsing_hunk

(*val subst_unparsing_hunk : 
  Names.substitution -> (Names.substitution -> 'pat -> 'pat) -> 
  'pat unparsing_hunk -> 'pat unparsing_hunk
*)

(* Checks if the precedence of the parent printer (None means the
   highest precedence), and the child's one, follow the given
   relation. *)

val tolerable_prec : tolerability option -> precedence -> bool

type 'pat syntax_entry = {
  syn_id : string;
  syn_prec: precedence;
  syn_astpat : 'pat;
  syn_hunks : 'pat unparsing_hunk list }

val subst_syntax_entry : 
  (Names.substitution -> 'pat -> 'pat) -> 
  Names.substitution -> 'pat syntax_entry -> 'pat syntax_entry


type 'pat syntax_command = { 
  sc_univ : string; 
  sc_entries : 'pat syntax_entry list }

val subst_syntax_command : 
  (Names.substitution -> 'pat -> 'pat) -> 
  Names.substitution -> 'pat syntax_command -> 'pat syntax_command

type syntax_rule = string * Coqast.t * Coqast.t unparsing_hunk list
type raw_syntax_entry = precedence * syntax_rule list

val interp_grammar_command :
  string -> (string * string -> unit) -> 
      raw_grammar_entry list -> grammar_command

val interp_syntax_entry :
  string -> raw_syntax_entry list -> Ast.astpat syntax_command

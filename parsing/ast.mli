(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Util
open Names
open Libnames
open Coqast
open Topconstr
open Genarg
(*i*)

(* Abstract syntax trees. *)

val loc : Coqast.t -> loc

(* ast constructors with dummy location *)
val ope : string * Coqast.t list -> Coqast.t
val slam : identifier option * Coqast.t -> Coqast.t
val nvar : identifier -> Coqast.t
val ide : string -> Coqast.t
val num : int -> Coqast.t
val string : string -> Coqast.t
val path : kernel_name -> Coqast.t
val dynamic : Dyn.t -> Coqast.t

val set_loc : loc -> Coqast.t -> Coqast.t

val path_section : loc -> kernel_name -> Coqast.t
val section_path : kernel_name -> kernel_name

(* ast destructors *)
val num_of_ast : Coqast.t -> int
val id_of_ast : Coqast.t -> string
val nvar_of_ast : Coqast.t -> identifier
val meta_of_ast : Coqast.t -> string

(* patterns of ast *)
type astpat =
  | Pquote of t
  | Pmeta of string * tok_kind
  | Pnode of string * patlist
  | Pslam of identifier option * astpat
  | Pmeta_slam of string * astpat

and patlist =
  | Pcons of astpat * patlist
  | Plmeta of string
  | Pnil

and tok_kind = Tnum | Tid | Tstr | Tpath | Tvar | Tany | Tlist

type pat =
  | AstListPat of patlist
  | PureAstPat of astpat

(* semantic actions of grammar rules *)
type act =
  | Act of constr_expr
  | ActCase of act * (pat * act) list
  | ActCaseList of act * (pat * act) list

(* values associated to variables *)
type typed_ast =
  | AstListNode of Coqast.t list
  | PureAstNode of Coqast.t

type ast_action_type = ETast | ETastl

type dynamic_grammar =
  | ConstrNode of constr_expr
  | CasesPatternNode of cases_pattern_expr

type grammar_action =
  | SimpleAction of loc * dynamic_grammar
  | CaseAction of
      loc * grammar_action * ast_action_type * (t list * grammar_action) list

type env = (string * typed_ast) list

val coerce_to_id : constr_expr -> identifier located

val coerce_global_to_id : reference -> identifier
val coerce_reference_to_id : reference -> identifier

exception No_match of string

val isMeta : string -> bool

val print_ast : Coqast.t -> std_ppcmds
val print_astl : Coqast.t list -> std_ppcmds
val print_astpat : astpat -> std_ppcmds
val print_astlpat : patlist -> std_ppcmds

(* Meta-syntax operations: matching and substitution *)

type entry_env = (string * ast_action_type) list

val grammar_type_error : loc * string -> 'a
 
(* Converting and checking free meta-variables *)

(* For old ast printer *)
val pat_sub : loc -> env -> astpat -> Coqast.t
val val_of_ast : entry_env -> Coqast.t -> astpat
val alpha_eq : Coqast.t * Coqast.t -> bool
val alpha_eq_val : typed_ast * typed_ast -> bool
val occur_var_ast : identifier -> Coqast.t -> bool
val find_all_matches : ('a -> astpat) -> env -> t -> 'a list -> ('a * env) list
val first_matchl : ('a -> patlist) -> env -> Coqast.t list -> 'a list ->
  ('a * env) option
val to_pat : entry_env -> Coqast.t -> (astpat * entry_env)

(* Object substitution in modules *)
val subst_astpat : Names.substitution -> astpat -> astpat

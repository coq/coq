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
open Names
open Libnames
open Coqast
open Genarg
(*i*)

(* Abstract syntax trees. *)

val dummy_loc : Coqast.loc
val loc : Coqast.t -> Coqast.loc
(*
val vernac_loc : Coqast.vernac_ast -> Coqast.loc
*)

(* ast constructors with dummy location *)
val ope : string * Coqast.t list -> Coqast.t
val slam : identifier option * Coqast.t -> Coqast.t
val nvar : identifier -> Coqast.t
val ide : string -> Coqast.t
val num : int -> Coqast.t
val string : string -> Coqast.t
val path : kernel_name -> Coqast.t
val dynamic : Dyn.t -> Coqast.t

val set_loc : Coqast.loc -> Coqast.t -> Coqast.t

val path_section : Coqast.loc -> kernel_name -> Coqast.t
val section_path : kernel_name -> kernel_name

(* ast destructors *)
val num_of_ast : Coqast.t -> int
val id_of_ast : Coqast.t -> string
val nvar_of_ast : Coqast.t -> identifier
val meta_of_ast : Coqast.t -> string

(* ast processing datatypes *)

type entry_type =
  | PureAstType
  | IntAstType
  | IdentAstType
  | AstListType
  | TacticAtomAstType
  | ThmTokenAstType
  | DynamicAstType
  | ReferenceAstType
  | GenAstType of Genarg.argument_type

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
  | Act of pat
  | ActCase of act * (pat * act) list
  | ActCaseList of act * (pat * act) list

(* values associated to variables *)
type typed_ast =
  | AstListNode of Coqast.t list
  | PureAstNode of Coqast.t

type ast_action_type = ETast | ETastl

type grammar_action =
  | SimpleAction of loc * typed_ast
  | CaseAction of
      loc * grammar_action * ast_action_type * (t list * grammar_action) list

type env = (string * typed_ast) list

val coerce_to_var : Coqast.t -> Coqast.t 

val coerce_to_id : Coqast.t -> identifier

val coerce_qualid_to_id : qualid Util.located -> identifier

val coerce_reference_to_id : Tacexpr.reference_expr -> identifier

val abstract_binders_ast :
  Coqast.loc -> string -> Coqast.t -> Coqast.t -> Coqast.t

val mkCastC : Coqast.t * Coqast.t -> Coqast.t
val mkLambdaC : identifier * Coqast.t * Coqast.t -> Coqast.t
val mkLetInC : identifier * Coqast.t * Coqast.t -> Coqast.t
val mkProdC : identifier * Coqast.t * Coqast.t -> Coqast.t

exception No_match of string

val isMeta : string -> bool

val print_ast : Coqast.t -> std_ppcmds
val print_astl : Coqast.t list -> std_ppcmds
val print_astpat : astpat -> std_ppcmds
val print_astlpat : patlist -> std_ppcmds

(* Meta-syntax operations: matching and substitution *)

type entry_env = (string * ast_action_type) list

val grammar_type_error : Coqast.loc * string -> 'a
 
(* Converting and checking free meta-variables *)
val pat_sub : Coqast.loc -> env -> astpat -> Coqast.t
val val_of_ast : entry_env -> Coqast.t -> astpat
val vall_of_astl : entry_env -> Coqast.t list -> patlist

val pat_of_ast : entry_env -> Coqast.t -> astpat * entry_env

val alpha_eq : Coqast.t * Coqast.t -> bool
val alpha_eq_val : typed_ast * typed_ast -> bool

val occur_var_ast : identifier -> Coqast.t -> bool
val replace_vars_ast : (identifier * identifier) list -> Coqast.t -> Coqast.t

val bind_env : env -> string -> typed_ast -> env
val ast_match : env -> astpat -> Coqast.t -> env
val astl_match : env -> patlist -> Coqast.t list -> env
val first_match : ('a -> astpat) -> env -> t -> 'a list -> ('a * env) option
val first_matchl : ('a -> patlist) -> env -> Coqast.t list -> 'a list ->
  ('a * env) option

val to_pat : entry_env -> Coqast.t -> (astpat * entry_env)

val eval_act : Coqast.loc -> env -> act -> typed_ast
val to_act_check_vars : entry_env -> ast_action_type -> grammar_action -> act

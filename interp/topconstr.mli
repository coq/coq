(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Names
open Libnames
open Glob_term
open Term
open Mod_subst
open Misctypes
open Decl_kinds
open Constrexpr
open Notation_term

(** Topconstr *)

val oldfashion_patterns : bool ref

(** Utilities on constr_expr                                           *)

val replace_vars_constr_expr :
  (identifier * identifier) list -> constr_expr -> constr_expr

val free_vars_of_constr_expr : constr_expr -> Idset.t
val occur_var_constr_expr : identifier -> constr_expr -> bool

(** Specific function for interning "in indtype" syntax of "match" *)
val ids_of_cases_indtype : cases_pattern_expr -> identifier list

val split_at_annot : local_binder list -> identifier located option -> local_binder list * local_binder list

(** Used in typeclasses *)

val fold_constr_expr_with_binders : (identifier -> 'a -> 'a) ->
   ('a -> 'b -> constr_expr -> 'b) -> 'a -> 'b -> constr_expr -> 'b

(** Used in correctness and interface; absence of var capture not guaranteed 
   in pattern-matching clauses and in binders of the form [x,y:T(x)] *)

val map_constr_expr_with_binders :
  (identifier -> 'a -> 'a) -> ('a -> constr_expr -> constr_expr) ->
      'a -> constr_expr -> constr_expr

val ntn_loc :
  loc -> constr_notation_substitution -> string -> (int * int) list
val patntn_loc :
  loc -> cases_pattern_notation_substitution -> string -> (int * int) list

(** For cases pattern parsing errors *)

val error_invalid_pattern_notation : Pp.loc -> 'a

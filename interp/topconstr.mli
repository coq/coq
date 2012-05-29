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

val constr_loc : constr_expr -> loc

val cases_pattern_expr_loc : cases_pattern_expr -> loc

val local_binders_loc : local_binder list -> loc

val replace_vars_constr_expr :
  (identifier * identifier) list -> constr_expr -> constr_expr

val free_vars_of_constr_expr : constr_expr -> Idset.t
val occur_var_constr_expr : identifier -> constr_expr -> bool

val default_binder_kind : binder_kind

(** Specific function for interning "in indtype" syntax of "match" *)
val ids_of_cases_indtype : cases_pattern_expr -> identifier list

val mkIdentC : identifier -> constr_expr
val mkRefC : reference -> constr_expr
val mkAppC : constr_expr * constr_expr list -> constr_expr
val mkCastC : constr_expr * constr_expr cast_type -> constr_expr
val mkLambdaC : name located list * binder_kind * constr_expr * constr_expr -> constr_expr
val mkLetInC : name located * constr_expr * constr_expr -> constr_expr
val mkProdC : name located list * binder_kind * constr_expr * constr_expr -> constr_expr

val coerce_reference_to_id : reference -> identifier
val coerce_to_id : constr_expr -> identifier located
val coerce_to_name : constr_expr -> name located

val split_at_annot : local_binder list -> identifier located option -> local_binder list * local_binder list

val abstract_constr_expr : constr_expr -> local_binder list -> constr_expr
val prod_constr_expr : constr_expr -> local_binder list -> constr_expr

(** Same as [abstract_constr_expr] and [prod_constr_expr], with location *)
val mkCLambdaN : loc -> local_binder list -> constr_expr -> constr_expr
val mkCProdN : loc -> local_binder list -> constr_expr -> constr_expr

(** For binders parsing *)

(** With let binders *)
val names_of_local_binders : local_binder list -> name located list

(** Does not take let binders into account *)
val names_of_local_assums : local_binder list -> name located list

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

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Constrexpr

(** Topconstr *)

val asymmetric_patterns : bool ref

(** Utilities on constr_expr *)

val replace_vars_constr_expr :
  Id.t Id.Map.t -> constr_expr -> constr_expr

val free_vars_of_constr_expr : constr_expr -> Id.Set.t
val occur_var_constr_expr : Id.t -> constr_expr -> bool

(** Specific function for interning "in indtype" syntax of "match" *)
val ids_of_cases_indtype : cases_pattern_expr -> Id.Set.t

val split_at_annot : local_binder_expr list -> Id.t located option -> local_binder_expr list * local_binder_expr list

(** Used in typeclasses *)

val fold_constr_expr_with_binders : (Id.t -> 'a -> 'a) ->
   ('a -> 'b -> constr_expr -> 'b) -> 'a -> 'b -> constr_expr -> 'b

(** Used in correctness and interface; absence of var capture not guaranteed 
   in pattern-matching clauses and in binders of the form [x,y:T(x)] *)

val map_constr_expr_with_binders :
  (Id.t -> 'a -> 'a) -> ('a -> constr_expr -> constr_expr) ->
      'a -> constr_expr -> constr_expr

val ntn_loc :
  Loc.t -> constr_notation_substitution -> string -> (int * int) list
val patntn_loc :
  Loc.t -> cases_pattern_notation_substitution -> string -> (int * int) list

(** For cases pattern parsing errors *)

val error_invalid_pattern_notation : ?loc:Loc.t -> unit -> 'a

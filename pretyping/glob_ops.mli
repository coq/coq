(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Glob_term

(** Equalities *)

val cases_pattern_eq : 'a cases_pattern_g -> 'a cases_pattern_g -> bool

val cast_type_eq : ('a -> 'a -> bool) ->
  'a Misctypes.cast_type -> 'a Misctypes.cast_type -> bool

val glob_constr_eq : 'a glob_constr_g -> 'a glob_constr_g -> bool

(** Operations on [glob_constr] *)

val cases_pattern_loc : 'a cases_pattern_g -> Loc.t option

val cases_predicate_names : 'a tomatch_tuples_g -> Name.t list

(** Apply one argument to a glob_constr *)
val mkGApp : ?loc:Loc.t -> 'a glob_constr_g -> 'a glob_constr_g -> 'a glob_constr_g

val map_glob_constr :
  (glob_constr -> glob_constr) -> glob_constr -> glob_constr

(** Ensure traversal from left to right *)
val map_glob_constr_left_to_right :
  (glob_constr -> glob_constr) -> glob_constr -> glob_constr

val warn_variable_collision : ?loc:Loc.t -> Id.t -> unit

val mk_glob_constr_eq : (glob_constr -> glob_constr -> bool) ->
  glob_constr -> glob_constr -> bool

val fold_glob_constr : ('a -> glob_constr -> 'a) -> 'a -> glob_constr -> 'a
val fold_glob_constr_with_binders : (Id.t -> 'a -> 'a) -> ('a -> 'b -> glob_constr -> 'b) -> 'a -> 'b -> glob_constr -> 'b
val iter_glob_constr : (glob_constr -> unit) -> glob_constr -> unit
val occur_glob_constr : Id.t -> 'a glob_constr_g -> bool
val free_glob_vars : 'a glob_constr_g -> Id.Set.t
val bound_glob_vars : glob_constr -> Id.Set.t
(* Obsolete *)
val loc_of_glob_constr : 'a glob_constr_g -> Loc.t option
val glob_visible_short_qualid : 'a glob_constr_g -> Id.Set.t

(* Renaming free variables using a renaming map; fails with
   [UnsoundRenaming] if applying the renaming would introduce
   collision, as in, e.g., renaming [P x y] using substitution [(x,y)];
   inner alpha-conversion done only for forall, fun, let but
   not for cases and fix *)

exception UnsoundRenaming
val rename_var : (Id.t * Id.t) list -> Id.t -> Id.t
val rename_glob_vars : (Id.t * Id.t) list -> 'a glob_constr_g -> 'a glob_constr_g

(** [map_pattern_binders f m c] applies [f] to all the binding names
    in a pattern-matching expression ({!Glob_term.GCases}) represented
    here by its relevant components [m] and [c]. It is used to
    interpret Ltac-bound names both in pretyping and printing of
    terms. *)
val map_pattern_binders : (Name.t -> Name.t) ->
  tomatch_tuples -> cases_clauses -> (tomatch_tuples*cases_clauses)

(** [map_pattern f m c] applies [f] to the return predicate and the
    right-hand side of a pattern-matching expression
    ({!Glob_term.GCases}) represented here by its relevant components
    [m] and [c]. *)
val map_pattern : (glob_constr -> glob_constr) ->
  tomatch_tuples -> cases_clauses -> (tomatch_tuples*cases_clauses)

(** Conversion from glob_constr to cases pattern, if possible

    Take the current alias as parameter,
    @raise Not_found if translation is impossible *)
val cases_pattern_of_glob_constr : Name.t -> glob_constr -> cases_pattern

val glob_constr_of_closed_cases_pattern : 'a cases_pattern_g -> Name.t * 'a glob_constr_g

val add_patterns_for_params_remove_local_defs : constructor -> 'a cases_pattern_g list -> 'a cases_pattern_g list

val ltac_interp_name : Ltac_pretype.ltac_var_map -> Name.t -> Name.t
val empty_lvar : Ltac_pretype.ltac_var_map

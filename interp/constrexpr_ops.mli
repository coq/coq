(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Libnames
open Constrexpr

(** Constrexpr_ops: utilities on [constr_expr] *)

val expr_Type_sort : sort_expr
val expr_SProp_sort : sort_expr
val expr_Prop_sort : sort_expr
val expr_Set_sort : sort_expr

(** {6 Equalities on [constr_expr] related types} *)

val sort_name_expr_eq : sort_name_expr -> sort_name_expr -> bool
val univ_level_expr_eq : univ_level_expr -> univ_level_expr -> bool
val sort_expr_eq : sort_expr -> sort_expr -> bool
val relevance_info_expr_eq : relevance_info_expr -> relevance_info_expr -> bool

val explicitation_eq : explicitation -> explicitation -> bool
(** Equality on [explicitation]. *)

val constr_expr_eq_gen : (constr_expr -> constr_expr -> bool) -> constr_expr -> constr_expr -> bool

val constr_expr_eq : constr_expr -> constr_expr -> bool
(** Equality on [constr_expr]. This is a syntactical one, which is oblivious to
    some parsing details, including locations. *)

val local_binder_eq : local_binder_expr -> local_binder_expr -> bool
(** Equality on [local_binder_expr]. Same properties as [constr_expr_eq]. *)

val binder_kind_eq : binder_kind -> binder_kind -> bool
(** Equality on [binder_kind] *)

(** {6 Retrieving locations} *)

val constr_loc : constr_expr -> Loc.t option
val cases_pattern_expr_loc : cases_pattern_expr -> Loc.t option
val local_binders_loc : local_binder_expr list -> Loc.t option

(** {6 Constructors} *)

(** {7 Term constructors} *)

(** Basic form of the corresponding constructors *)

val mkIdentC : Id.t -> constr_expr
val mkRefC : qualid -> constr_expr
val mkCastC : constr_expr * Constr.cast_kind option * constr_expr -> constr_expr
val mkLambdaC : lname list * binder_kind * constr_expr * constr_expr -> constr_expr
val mkLetInC : lname * constr_expr * constr_expr option * constr_expr -> constr_expr
val mkProdC : lname list * binder_kind * constr_expr * constr_expr -> constr_expr

val mkAppC : constr_expr * constr_expr list -> constr_expr
(** Basic form of application, collapsing nested applications *)

(** Optimized constructors: does not add a constructor for an empty binder list *)

val mkLambdaCN : ?loc:Loc.t -> local_binder_expr list -> constr_expr -> constr_expr
val mkProdCN : ?loc:Loc.t -> local_binder_expr list -> constr_expr -> constr_expr

(** Aliases for the corresponding constructors; generally [mkLambdaCN] and
    [mkProdCN] should be preferred *)

val mkCLambdaN : ?loc:Loc.t -> local_binder_expr list -> constr_expr -> constr_expr
val mkCProdN : ?loc:Loc.t -> local_binder_expr list -> constr_expr -> constr_expr

(** {7 Pattern constructors} *)

(** Interpretation of a list of patterns as a disjunctive pattern (optimized) *)
val mkCPatOr : ?loc:Loc.t -> cases_pattern_expr list -> cases_pattern_expr

val mkAppPattern : ?loc:Loc.t -> cases_pattern_expr -> cases_pattern_expr list -> cases_pattern_expr
(** Apply a list of pattern arguments to a pattern *)

(** {6 Destructors}*)

val coerce_reference_to_id : qualid -> Id.t
(** FIXME: nothing to do here *)

val coerce_to_id : constr_expr -> lident
(** Destruct terms of the form [CRef (Ident _)]. *)

val coerce_to_name : constr_expr -> lname
(** Destruct terms of the form [CRef (Ident _)] or [CHole _]. *)

val coerce_to_cases_pattern_expr : constr_expr -> cases_pattern_expr

(** {6 Binder manipulation} *)

val default_binder_kind : binder_kind

val names_of_local_binders : local_binder_expr list -> lname list
(** Retrieve a list of binding names from a list of binders. *)

val names_of_local_assums : local_binder_expr list -> lname list
(** Same as [names_of_local_binder_exprs], but does not take the [let] bindings into
    account. *)

(** {6 Folds and maps} *)

(** Used in typeclasses *)
val fold_constr_expr_with_binders : (Id.t -> 'a -> 'a) ->
   ('a -> 'b -> constr_expr -> 'b) -> 'a -> 'b -> constr_expr -> 'b

(** Used in correctness and interface; absence of var capture not guaranteed
   in pattern-matching clauses and in binders of the form [x,y:T(x)] *)

val map_constr_expr_with_binders :
  (Id.t -> 'a -> 'a) -> ('a -> constr_expr -> constr_expr) ->
      'a -> constr_expr -> constr_expr

(** {6 Miscellaneous}*)

val replace_vars_constr_expr :
  Id.t Id.Map.t -> constr_expr -> constr_expr

val free_vars_of_constr_expr : constr_expr -> Id.Set.t
val occur_var_constr_expr : Id.t -> constr_expr -> bool

(** Return all (non-qualified) names treating binders as names *)
val names_of_constr_expr : constr_expr -> Id.Set.t

val ntn_loc : ?loc:Loc.t -> constr_notation_substitution -> notation -> (int * int) list
val patntn_loc : ?loc:Loc.t -> cases_pattern_notation_substitution -> notation -> (int * int) list

val isCSort : constr_expr -> bool

(** For cases pattern parsing errors *)
val error_invalid_pattern_notation : ?loc:Loc.t -> unit -> 'a

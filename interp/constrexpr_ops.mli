(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Libnames
open Constrexpr

(** Constrexpr_ops: utilities on [constr_expr] *)

(** {6 Equalities on [constr_expr] related types} *)

val explicitation_eq : explicitation -> explicitation -> bool
(** Equality on [explicitation]. *)

val constr_expr_eq : constr_expr -> constr_expr -> bool
(** Equality on [constr_expr]. This is a syntactical one, which is oblivious to
    some parsing details, including locations. *)

val local_binder_eq : local_binder_expr -> local_binder_expr -> bool
(** Equality on [local_binder_expr]. Same properties as [constr_expr_eq]. *)

val binding_kind_eq : Decl_kinds.binding_kind -> Decl_kinds.binding_kind -> bool
(** Equality on [binding_kind] *)

val binder_kind_eq : binder_kind -> binder_kind -> bool
(** Equality on [binder_kind] *)

(** {6 Retrieving locations} *)

val constr_loc : constr_expr -> Loc.t option
val cases_pattern_expr_loc : cases_pattern_expr -> Loc.t option
val local_binders_loc : local_binder_expr list -> Loc.t option

(** {6 Constructors}*)

val mkIdentC : Id.t -> constr_expr
val mkRefC : qualid -> constr_expr
val mkAppC : constr_expr * constr_expr list -> constr_expr
val mkCastC : constr_expr * constr_expr Glob_term.cast_type -> constr_expr
val mkLambdaC : lname list * binder_kind * constr_expr * constr_expr -> constr_expr
val mkLetInC : lname * constr_expr * constr_expr option * constr_expr -> constr_expr
val mkProdC : lname list * binder_kind * constr_expr * constr_expr -> constr_expr

val mkCLambdaN : ?loc:Loc.t -> local_binder_expr list -> constr_expr -> constr_expr
(** Same as [abstract_constr_expr], with location *)

val mkCProdN : ?loc:Loc.t -> local_binder_expr list -> constr_expr -> constr_expr
(** Same as [prod_constr_expr], with location *)

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

val replace_vars_constr_expr :
  Id.t Id.Map.t -> constr_expr -> constr_expr

(** Specific function for interning "in indtype" syntax of "match" *)
val ids_of_cases_indtype : cases_pattern_expr -> Id.Set.t

val free_vars_of_constr_expr : constr_expr -> Id.Set.t
val occur_var_constr_expr : Id.t -> constr_expr -> bool

val split_at_annot : local_binder_expr list -> lident option -> local_binder_expr list * local_binder_expr list

val ntn_loc : ?loc:Loc.t -> constr_notation_substitution -> notation -> (int * int) list
val patntn_loc : ?loc:Loc.t -> cases_pattern_notation_substitution -> notation -> (int * int) list

(** For cases pattern parsing errors *)
val error_invalid_pattern_notation : ?loc:Loc.t -> unit -> 'a

(** Placeholder for global option, should be moved to a parameter *)
val asymmetric_patterns : bool ref

(** Local universe and constraint declarations. *)
val interp_univ_decl : Environ.env -> universe_decl_expr ->
                       Evd.evar_map * UState.universe_decl

val interp_univ_decl_opt : Environ.env -> universe_decl_expr option ->
                       Evd.evar_map * UState.universe_decl

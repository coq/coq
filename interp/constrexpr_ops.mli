(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Libnames
open Misctypes
open Constrexpr

(** Constrexpr_ops: utilities on [constr_expr] *)

(** {6 Equalities on [constr_expr] related types} *)

val explicitation_eq : explicitation -> explicitation -> bool
(** Equality on [explicitation]. *)

val constr_expr_eq : constr_expr -> constr_expr -> bool
(** Equality on [constr_expr]. This is a syntactical one, which is oblivious to
    some parsing details, including locations. *)

val local_binder_eq : local_binder -> local_binder -> bool
(** Equality on [local_binder]. Same properties as [constr_expr_eq]. *)

val binding_kind_eq : Decl_kinds.binding_kind -> Decl_kinds.binding_kind -> bool
(** Equality on [binding_kind] *)

val binder_kind_eq : binder_kind -> binder_kind -> bool
(** Equality on [binder_kind] *)

(** {6 Retrieving locations} *)

val constr_loc : constr_expr -> Loc.t
val cases_pattern_expr_loc : cases_pattern_expr -> Loc.t
val raw_cases_pattern_expr_loc : raw_cases_pattern_expr -> Loc.t
val local_binders_loc : local_binder list -> Loc.t

(** {6 Constructors}*)

val mkIdentC : Id.t -> constr_expr
val mkRefC : reference -> constr_expr
val mkAppC : constr_expr * constr_expr list -> constr_expr
val mkCastC : constr_expr * constr_expr cast_type -> constr_expr
val mkLambdaC : Name.t located list * binder_kind * constr_expr * constr_expr -> constr_expr
val mkLetInC : Name.t located * constr_expr * constr_expr -> constr_expr
val mkProdC : Name.t located list * binder_kind * constr_expr * constr_expr -> constr_expr

val abstract_constr_expr : constr_expr -> local_binder list -> constr_expr
val prod_constr_expr : constr_expr -> local_binder list -> constr_expr

val mkCLambdaN : Loc.t -> local_binder list -> constr_expr -> constr_expr
(** Same as [abstract_constr_expr], with location *)

val mkCProdN : Loc.t -> local_binder list -> constr_expr -> constr_expr
(** Same as [prod_constr_expr], with location *)

(** {6 Destructors}*)

val coerce_reference_to_id : reference -> Id.t
(** FIXME: nothing to do here *)

val coerce_to_id : constr_expr -> Id.t located
(** Destruct terms of the form [CRef (Ident _)]. *)

val coerce_to_name : constr_expr -> Name.t located
(** Destruct terms of the form [CRef (Ident _)] or [CHole _]. *)

(** {6 Binder manipulation} *)

val default_binder_kind : binder_kind

val names_of_local_binders : local_binder list -> Name.t located list
(** Retrieve a list of binding names from a list of binders. *)

val names_of_local_assums : local_binder list -> Name.t located list
(** Same as [names_of_local_binders], but does not take the [let] bindings into
    account. *)

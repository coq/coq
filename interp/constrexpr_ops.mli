(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Pp
open Names
open Libnames
open Misctypes
open Term
open Mod_subst
open Constrexpr

(** Constrexpr_ops: utilities on [constr_expr] *)

val constr_loc : constr_expr -> Loc.t

val cases_pattern_expr_loc : cases_pattern_expr -> Loc.t
val raw_cases_pattern_expr_loc : raw_cases_pattern_expr -> Loc.t

val local_binders_loc : local_binder list -> Loc.t

val binding_kind_eq : Decl_kinds.binding_kind -> Decl_kinds.binding_kind -> bool

val binder_kind_eq : binder_kind -> binder_kind -> bool

val default_binder_kind : binder_kind

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

val abstract_constr_expr : constr_expr -> local_binder list -> constr_expr
val prod_constr_expr : constr_expr -> local_binder list -> constr_expr

(** Same as [abstract_constr_expr] and [prod_constr_expr], with location *)
val mkCLambdaN : Loc.t -> local_binder list -> constr_expr -> constr_expr
val mkCProdN : Loc.t -> local_binder list -> constr_expr -> constr_expr

(** For binders parsing *)

(** With let binders *)
val names_of_local_assums : local_binder list -> name located list

(** Does not take let binders into account *)
val names_of_local_binders : local_binder list -> name located list

val raw_cases_pattern_expr_of_glob_constr : (Globnames.global_reference -> unit)
  -> Glob_term.glob_constr -> raw_cases_pattern_expr

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
open Entries
open Libnames
open Vernacexpr
open Constrexpr
open Decl_kinds

(** {6 Inductive and coinductive types} *)

(** Entry points for the vernacular commands Inductive and CoInductive *)

type uniform_inductive_flag =
  | UniformParameters
  | NonUniformParameters

val do_mutual_inductive :
  (one_inductive_expr * decl_notation list) list -> cumulative_inductive_flag ->
  polymorphic -> private_flag -> uniform:uniform_inductive_flag ->
  Declarations.recursivity_kind -> unit

(************************************************************************)
(** Internal API  *)
(************************************************************************)

(** Exported for Record and Funind *)

(** Registering a mutual inductive definition together with its
   associated schemes *)

type one_inductive_impls =
  Impargs.manual_implicits (** for inds *)*
  Impargs.manual_implicits list (** for constrs *)

val declare_mutual_inductive_with_eliminations :
  mutual_inductive_entry -> UnivNames.universe_binders -> one_inductive_impls list ->
  MutInd.t

(** Exported for Funind *)

(** Extracting the semantical components out of the raw syntax of mutual
   inductive declarations *)

type structured_one_inductive_expr = {
  ind_name : Id.t;
  ind_univs : universe_decl_expr option;
  ind_arity : constr_expr;
  ind_lc : (Id.t * constr_expr) list
}

type structured_inductive_expr =
  local_binder_expr list * structured_one_inductive_expr list

val extract_mutual_inductive_declaration_components :
  (one_inductive_expr * decl_notation list) list ->
    structured_inductive_expr * (*coercions:*) qualid list * decl_notation list

(** Typing mutual inductive definitions *)

val interp_mutual_inductive :
  structured_inductive_expr -> decl_notation list -> cumulative_inductive_flag ->
  polymorphic -> private_flag -> Declarations.recursivity_kind ->
  mutual_inductive_entry * UnivNames.universe_binders * one_inductive_impls list

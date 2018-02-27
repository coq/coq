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
open Glob_term
open Constrexpr
open Libnames
open Globnames

val declare_generalizable : Vernacexpr.locality_flag -> Misctypes.lident list option -> unit

val ids_of_list : Id.t list -> Id.Set.t
val destClassApp : constr_expr -> (reference * constr_expr list * instance_expr option) CAst.t
val destClassAppExpl : constr_expr -> (reference * (constr_expr * explicitation CAst.t option) list * instance_expr option) CAst.t

(** Fragile, should be used only for construction a set of identifiers to avoid *)

val free_vars_of_constr_expr : constr_expr -> ?bound:Id.Set.t ->
  Id.t list -> Id.t list

val free_vars_of_binders :
  ?bound:Id.Set.t -> Id.t list -> local_binder_expr list -> Id.Set.t * Id.t list

(** Returns the generalizable free ids in left-to-right
   order with the location of their first occurrence *)

val generalizable_vars_of_glob_constr : ?bound:Id.Set.t -> ?allowed:Id.Set.t ->
  glob_constr -> Misctypes.lident list

val make_fresh : Id.Set.t -> Environ.env -> Id.t -> Id.t

val implicits_of_glob_constr : ?with_products:bool -> Glob_term.glob_constr -> Impargs.manual_implicits

val combine_params_freevar :
  Id.Set.t -> global_reference option * Context.Rel.Declaration.t ->
  Constrexpr.constr_expr * Id.Set.t

val implicit_application : Id.Set.t -> ?allow_partial:bool ->
  (Id.Set.t -> global_reference option * Context.Rel.Declaration.t ->
    Constrexpr.constr_expr * Id.Set.t) ->
  constr_expr -> constr_expr * Id.Set.t

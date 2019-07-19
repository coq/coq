(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Vernacexpr

(** {6 Fixpoints and cofixpoints} *)

(** Entry points for the vernacular commands Fixpoint and CoFixpoint *)

val do_fixpoint_interactive :
  scope:DeclareDef.locality -> poly:bool -> fixpoint_expr list -> Lemmas.t

val do_fixpoint :
  scope:DeclareDef.locality -> poly:bool -> fixpoint_expr list -> unit

val do_cofixpoint_interactive :
  scope:DeclareDef.locality -> poly:bool -> cofixpoint_expr list -> Lemmas.t

val do_cofixpoint :
  scope:DeclareDef.locality -> poly:bool -> cofixpoint_expr list -> unit

(************************************************************************)
(** Internal API  *)
(************************************************************************)

(** Typing global fixpoints and cofixpoint_expr *)

val adjust_rec_order
  :  structonly:bool
  -> Constrexpr.local_binder_expr list
  -> Constrexpr.recursion_order_expr option
  -> lident option

(** Exported for Program *)
val interp_recursive :
  (* Misc arguments *)
  program_mode:bool -> cofix:bool ->
  (* Notations of the fixpoint / should that be folded in the previous argument? *)
  lident option fix_expr_gen list ->
  (* env / signature / univs / evar_map *)
  (Environ.env * EConstr.named_context * UState.universe_decl * Evd.evar_map) *
  (* names / defs / types *)
  (Id.t list * Sorts.relevance list * EConstr.constr option list * EConstr.types list) *
  (* ctx per mutual def / implicits / struct annotations *)
  (EConstr.rel_context * Impargs.manual_implicits * int option) list

(** Exported for Funind *)

type recursive_preentry = Id.t list * Sorts.relevance list * constr option list * types list

val interp_fixpoint
  :  cofix:bool
  -> lident option fix_expr_gen list
  -> recursive_preentry * UState.universe_decl * UState.t *
     (EConstr.rel_context * Impargs.manual_implicits * int option) list

(** Very private function, do not use *)
val compute_possible_guardness_evidences :
  ('a, 'b) Context.Rel.pt * 'c * int option -> int list

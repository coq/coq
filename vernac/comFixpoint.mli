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
open Constrexpr
open Vernacexpr

(** {6 Fixpoints and cofixpoints} *)

(** Entry points for the vernacular commands Fixpoint and CoFixpoint *)

val do_fixpoint_interactive :
  scope:DeclareDef.locality -> poly:bool -> (fixpoint_expr * decl_notation list) list -> Lemmas.t

val do_fixpoint :
  scope:DeclareDef.locality -> poly:bool -> (fixpoint_expr * decl_notation list) list -> unit

val do_cofixpoint_interactive :
  scope:DeclareDef.locality -> poly:bool -> (cofixpoint_expr * decl_notation list) list -> Lemmas.t

val do_cofixpoint :
  scope:DeclareDef.locality -> poly:bool -> (cofixpoint_expr * decl_notation list) list -> unit

(************************************************************************)
(** Internal API  *)
(************************************************************************)

type structured_fixpoint_expr = {
  fix_name : Id.t;
  fix_univs : Constrexpr.universe_decl_expr option;
  fix_annot : lident option;
  fix_binders : local_binder_expr list;
  fix_body : constr_expr option;
  fix_type : constr_expr
}

(** Typing global fixpoints and cofixpoint_expr *)

(** Exported for Program *)
val interp_recursive :
  (* Misc arguments *)
  program_mode:bool -> cofix:bool ->
  (* Notations of the fixpoint / should that be folded in the previous argument? *)
  structured_fixpoint_expr list -> decl_notation list ->

  (* env / signature / univs / evar_map *)
  (Environ.env * EConstr.named_context * UState.universe_decl * Evd.evar_map) *
  (* names / defs / types *)
  (Id.t list * Sorts.relevance list * EConstr.constr option list * EConstr.types list) *
  (* ctx per mutual def / implicits / struct annotations *)
  (EConstr.rel_context * Impargs.manual_implicits * int option) list

(** Exported for Funind *)

(** Extracting the semantical components out of the raw syntax of
   (co)fixpoints declarations *)

val extract_fixpoint_components : structonly:bool ->
  (fixpoint_expr * decl_notation list) list ->
    structured_fixpoint_expr list * decl_notation list

val extract_cofixpoint_components :
  (cofixpoint_expr * decl_notation list) list ->
    structured_fixpoint_expr list * decl_notation list

type recursive_preentry =
  Id.t list * Sorts.relevance list * constr option list * types list

val interp_fixpoint :
  cofix:bool ->
  structured_fixpoint_expr list -> decl_notation list ->
  recursive_preentry * UState.universe_decl * UState.t *
  (EConstr.rel_context * Impargs.manual_implicits * int option) list

(** Very private function, do not use *)
val compute_possible_guardness_evidences :
  ('a, 'b) Context.Rel.pt * 'c * int option -> int list

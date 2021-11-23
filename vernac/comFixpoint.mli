(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Vernacexpr

(** {6 Fixpoints and cofixpoints} *)

(** Entry points for the vernacular commands Fixpoint and CoFixpoint *)

val do_fixpoint_interactive
  : scope:Locality.definition_scope
  -> poly:bool
  -> ?typing_flags:Declarations.typing_flags
  -> fixpoint_expr list
  -> Declare.Proof.t

val do_fixpoint
   : ?scope:Locality.definition_scope
  -> poly:bool
  -> ?typing_flags:Declarations.typing_flags
  -> ?using:Vernacexpr.section_subset_expr
  -> fixpoint_expr list
  -> unit

val do_cofixpoint_interactive :
  scope:Locality.definition_scope -> poly:bool -> cofixpoint_expr list -> Declare.Proof.t

val do_cofixpoint
  : scope:Locality.definition_scope
  -> poly:bool
  -> ?using:Vernacexpr.section_subset_expr
  -> cofixpoint_expr list
  -> unit

(************************************************************************)
(** Internal API  *)
(************************************************************************)

(** Typing global fixpoints and cofixpoint_expr *)

val adjust_rec_order
  :  structonly:bool
  -> Constrexpr.local_binder_expr list
  -> Constrexpr.recursion_order_expr option
  -> lident option

(** names / relevance / defs / types *)
type ('constr, 'types) recursive_preentry = Id.t list * Sorts.relevance list * 'constr option list * 'types list

(** Exported for Program *)
val interp_recursive :
  Environ.env ->
  (* Misc arguments *)
  program_mode:bool -> cofix:bool ->
  (* Notations of the fixpoint / should that be folded in the previous argument? *)
  lident option fix_expr_gen list ->
  (* env / signature / univs / evar_map *)
  (Environ.env * EConstr.named_context * UState.universe_decl * Evd.evar_map) *
  (* names / defs / types *)
  (EConstr.t, EConstr.types) recursive_preentry *
  (* ctx per mutual def / implicits / struct annotations *)
  (EConstr.rel_context * Impargs.manual_implicits * int option) list

(** Exported for Funind *)

val interp_fixpoint
  :  ?check_recursivity:bool
  -> ?typing_flags:Declarations.typing_flags
  -> cofix:bool
  -> lident option fix_expr_gen list
  -> (Constr.t, Constr.types) recursive_preentry *
     UState.universe_decl * UState.t *
     (EConstr.rel_context * Impargs.manual_implicits * int option) list

(** Very private function, do not use *)
val compute_possible_guardness_evidences :
  ('a, 'b) Context.Rel.pt * 'c * int option -> int list

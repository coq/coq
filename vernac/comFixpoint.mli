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

val do_mutually_recursive
  : ?scope:Locality.definition_scope
  -> ?clearbody:bool
  -> poly:bool
  -> ?typing_flags:Declarations.typing_flags
  -> ?user_warns:UserWarn.t
  -> ?using:Vernacexpr.section_subset_expr
  -> recursives_expr
  -> Declare.Proof.t option

(************************************************************************)
(** Internal API  *)
(************************************************************************)

(** names / relevance / defs / types *)
type ('constr, 'types, 'r) recursive_preentry = Id.t list * 'r list * 'constr option list * 'types list

(** Exported for Program *)
val interp_recursive_evars :
  Environ.env ->
  (* Misc arguments *)
  program_mode:bool ->
  (* Notations of the fixpoint / should that be folded in the previous argument? *)
  bool * recursion_order_expr ->
  recursive_expr_gen list ->
  (* env / signature / univs / evar_map *)
  (Environ.env * EConstr.named_context * UState.universe_decl * Evd.evar_map) *
  (* names / defs / types *)
  (EConstr.t, EConstr.types, EConstr.ERelevance.t) recursive_preentry *
  (* ctx per mutual def / implicits / struct annotations *)
  (EConstr.rel_context * Impargs.manual_implicits) list * Decls.definition_object_kind * Pretyping.possible_guard

(** Exported for Funind *)

val interp_recursive
  :  ?check_recursivity:bool
  -> ?typing_flags:Declarations.typing_flags
  -> bool * Vernacexpr.recursion_order_expr
  -> recursive_expr_gen list
  -> Decls.definition_object_kind * Pretyping.possible_guard *
     ((Constr.t, Constr.types, Sorts.relevance) recursive_preentry *
      UState.universe_decl * UState.t *
      (EConstr.rel_context * Impargs.manual_implicits) list)

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
  :  ?pm:Declare.OblState.t
  -> ?scope:Locality.definition_scope
  -> ?clearbody:bool
  -> poly:bool
  -> ?typing_flags:Declarations.typing_flags
  -> ?user_warns:UserWarn.t
  -> ?using:Vernacexpr.section_subset_expr
  -> recursives_expr
  -> Declare.OblState.t option * Declare.Proof.t option

(************************************************************************)
(** Internal API  *)
(************************************************************************)

(** names / relevance / defs / types / contexts / implicit args / struct annotations / universe decl *)
type ('constr, 'types, 'r) recursive_preentry =
  (Id.t list * 'r list * 'constr option list * 'types list * EConstr.rel_context list * Impargs.manual_implicits list) *
  Decls.definition_object_kind * Pretyping.possible_guard * UState.universe_decl

(** Exported for Funind *)

val interp_fixpoint_short
  :  Constrexpr.fixpoint_order_expr option list
  -> recursive_expr_gen list
  -> Constr.types list * UState.t

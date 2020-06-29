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
open Constrexpr

(** {6 Parameters/Assumptions} *)

val do_assumptions
  :  program_mode:bool
  -> poly:bool
  -> scope:Locality.locality
  -> kind:Decls.assumption_object_kind
  -> Declaremods.inline
  -> (ident_decl list * constr_expr) with_coercion list
  -> unit

val declare_variable
  : coercion_flag
  -> kind:Decls.assumption_object_kind
  -> Constr.types
  -> Impargs.manual_implicits
  -> Glob_term.binding_kind
  -> variable CAst.t
  -> unit

val declare_axiom
  : coercion_flag
  -> poly:bool
  -> local:Locality.import_status
  -> kind:Decls.assumption_object_kind
  -> Constr.types
  -> Entries.universes_entry * UnivNames.universe_binders
  -> Impargs.manual_implicits
  -> Declaremods.inline
  -> variable CAst.t
  -> GlobRef.t * Univ.Instance.t

(** Context command *)

val context
  :  poly:bool
  -> local_binder_expr list
  -> unit

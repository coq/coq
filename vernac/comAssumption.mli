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
open Vernacexpr
open Constrexpr
open Decl_kinds

(** {6 Parameters/Assumptions} *)

val do_assumptions
  :  program_mode:bool
  -> poly:bool
  -> scope:DeclareDef.locality
  -> kind:assumption_object_kind
  -> Declaremods.inline
  -> (ident_decl list * constr_expr) with_coercion list
  -> bool

(** returns [false] if the assumption is neither local to a section,
    nor in a module type and meant to be instantiated. *)
val declare_assumption
  : coercion_flag
  -> poly:bool
  -> scope:DeclareDef.locality
  -> kind:assumption_object_kind
  -> Constr.types
  -> Entries.universes_entry
  -> UnivNames.universe_binders
  -> Impargs.manual_implicits
  -> bool (** implicit *)
  -> Declaremods.inline
  -> variable CAst.t
  -> GlobRef.t * Univ.Instance.t * bool

(** Context command *)

(** returns [false] if, for lack of section, it declares an assumption
    (unless in a module type). *)
val context
  :  poly:bool
  -> local_binder_expr list
  -> bool

val do_primitive : lident -> CPrimitives.op_or_type -> constr_expr option -> unit

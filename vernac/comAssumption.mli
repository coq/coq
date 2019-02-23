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
open Constr
open Entries
open Vernacexpr
open Constrexpr
open Decl_kinds

(** {6 Parameters/Assumptions} *)

val do_assumptions
  :  pstate:Proof_global.t option
  -> program_mode:bool
  -> locality * polymorphic * assumption_object_kind
  -> Declaremods.inline
  -> (ident_decl list * constr_expr) with_coercion list
  -> bool

(************************************************************************)
(** Internal API  *)
(************************************************************************)

(** Exported for Classes *)

(** returns [false] if the assumption is neither local to a section,
    nor in a module type and meant to be instantiated. *)
val declare_assumption
  :  pstate:Proof_global.t option
  -> coercion_flag
  -> assumption_kind
  -> types in_universes_entry
  -> UnivNames.universe_binders
  -> Impargs.manual_implicits
  -> bool (** implicit *)
  -> Declaremods.inline
  -> variable CAst.t
  -> GlobRef.t * Univ.Instance.t * bool

val do_primitive : lident -> CPrimitives.op_or_type -> constr_expr option -> unit

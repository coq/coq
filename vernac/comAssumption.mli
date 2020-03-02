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

(** {6 Parameters/Assumptions} *)

val do_assumptions
  :  program_mode:bool
  -> poly:bool
  -> scope:DeclareDef.locality
  -> kind:Decls.assumption_object_kind
  -> Declaremods.inline
  -> (ident_decl list * constr_expr) with_coercion list
  -> unit

(* variables cannot be universe polymorphic, but can mention, in the type,
   polymorphic universes, hence the ~poly argument *)
val declare_variable
  : coercion_flag
  -> poly:bool
  -> kind:Decls.assumption_object_kind
  -> Constr.types
  -> Univ.ContextSet.t
  -> Impargs.manual_implicits
  -> Glob_term.binding_kind
  -> variable CAst.t
  -> GlobRef.t * Univ.Instance.t

val declare_axiom
  : coercion_flag
  -> poly:bool
  -> local:Declare.import_status
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

(** Deprecated *)
val declare_assumption
  : coercion_flag
  -> poly:bool
  -> scope:DeclareDef.locality
  -> kind:Decls.assumption_object_kind
  -> Constr.types
  -> Entries.universes_entry
  -> UnivNames.universe_binders
  -> Impargs.manual_implicits
  -> Glob_term.binding_kind
  -> Declaremods.inline
  -> variable CAst.t
  -> GlobRef.t * Univ.Instance.t
[@@ocaml.deprecated "Use declare_variable or declare_axiom instead."]

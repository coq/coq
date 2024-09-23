(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** Also used by [Declare] for constants, [DeclareInd] for inductives, etc.
    Containts [object_kind , id]. *)
exception AlreadyDeclared of (string option * Id.t)

(** Internally used to declare names of universes from monomorphic
   constants/inductives. Noop on polymorphic references. *)
val declare_univ_binders : GlobRef.t -> UState.named_universes_entry -> unit

(** Internally used to name universes associated with no particular constant in a section. *)
val name_mono_section_univs : Univ.Level.Set.t -> unit

(** Command [Universes]. *)
val do_universe : poly:bool -> lident list -> unit

(** Command [Constraint]. *)
val do_constraint : poly:bool -> Constrexpr.univ_constraint_expr list -> unit

val add_constraint_source : GlobRef.t -> Univ.ContextSet.t -> unit

val constraint_sources : unit -> (GlobRef.t * Univ.Constraints.t) list
(** Returns constraints associated to globrefs, newest first. *)

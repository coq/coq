(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

val pr_with_global_universes : Level.t -> Pp.t
val qualid_of_level : Level.t -> Libnames.qualid

(** Global universe information outside the kernel, to handle
    polymorphic universes in sections that have to be discharged. *)
val add_global_universe : Level.t -> Decl_kinds.polymorphic -> unit

(** Is [lvl]  a global polymorphic universe? (ie section polymorphic universe) *)
val is_polymorphic : Level.t -> bool

(** Local universe name <-> level mapping *)

type universe_binders = Univ.Level.t Names.Id.Map.t

val empty_binders : universe_binders

val register_universe_binders : Names.GlobRef.t -> universe_binders -> unit
val universe_binders_of_global : Names.GlobRef.t -> universe_binders

type univ_name_list = Names.lname list

(** [universe_binders_with_opt_names ref u l]

    If [l] is [Some univs] return the universe binders naming the levels of [u] by [univs] (skipping Anonymous).
    May error if the lengths mismatch.

    Otherwise return [universe_binders_of_global ref]. *)
val universe_binders_with_opt_names : Names.GlobRef.t ->
  Univ.Level.t list -> univ_name_list option -> universe_binders

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

val pr_with_global_universes : Level.t -> Pp.t
val qualid_of_level : Level.t -> Libnames.qualid option

(** Local universe name <-> level mapping *)

type universe_binders = Univ.Level.t Names.Id.Map.t

val empty_binders : universe_binders

val compute_instance_binders : Instance.t -> universe_binders -> Names.Name.t array

type univ_name_list = Names.lname list

(** [universe_binders_with_opt_names ref l]

    If [l] is [Some univs] return the universe binders naming the bound levels
    of [ref] by [univs] (skipping Anonymous). May error if the lengths mismatch.

    Otherwise return the bound universe names registered for [ref]. *)
val universe_binders_with_opt_names : AUContext.t ->
  univ_name_list option -> universe_binders

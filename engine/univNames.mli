(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

type univ_name_list = Names.lname list

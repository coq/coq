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
open Univ
open Sorts

(** Local universe name <-> level mapping *)

type universe_binders = QVar.t Id.Map.t * Level.t Id.Map.t

type rev_binders = Id.t QVar.Map.t * Id.t Level.Map.t

val empty_binders : universe_binders

val empty_rev_binders : rev_binders

type univ_name_list = Names.lname list

type full_name_list = lname list * lname list

val pr_level_with_global_universes : ?binders:universe_binders -> Level.t -> Pp.t
val qualid_of_level : universe_binders -> Level.t -> Libnames.qualid option

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
open Univ


let qualid_of_level ctx l =
  match Level.name l with
  | Some qid  ->
    (try Some (Nametab.shortest_qualid_of_universe ctx qid)
     with Not_found -> None)
  | None -> None

let pr_with_global_universes ctx l =
  match qualid_of_level ctx l with
  | Some qid  -> Libnames.pr_qualid qid
  | None -> Level.pr l

(** Global universe information outside the kernel, to handle
    polymorphic universe names in sections that have to be discharged. *)

(** Local universe names of polymorphic references *)

type universe_binders = Level.t Names.Id.Map.t

let empty_binders = Id.Map.empty

type univ_name_list = Names.lname list

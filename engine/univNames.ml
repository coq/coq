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

type universe_binders = QVar.t Id.Map.t * Level.t Id.Map.t

type rev_binders = Id.t QVar.Map.t * Id.t Level.Map.t

let empty_binders = Id.Map.empty, Id.Map.empty

let empty_rev_binders = QVar.Map.empty, Level.Map.empty

type univ_name_list = {
  qualities : lname list;
  ext_ql : bool;
  univlevels : lname list;
  ext_ul : bool;
}

let qualid_of_level (_,ctx) l =
  match Level.name l with
  | Some qid  ->
    (try Some (Nametab.shortest_qualid_of_universe ctx qid)
     with Not_found -> None)
  | None -> None

let pr_level_with_global_universes ?(binders=empty_binders) l =
  match qualid_of_level binders l with
  | Some qid  -> Libnames.pr_qualid qid
  | None -> Level.raw_pr l

let qualid_of_quality (ctx,_) q =
  try Some (Nametab.Quality.shortest_qualid_gen (fun id -> Id.Map.mem id ctx) q)
  with Not_found -> None

let pr_quality_with_global_universes ?(binders=empty_binders) q =
  match qualid_of_quality binders q with
  | Some qid  -> Libnames.pr_qualid qid
  | None -> Sorts.Quality.raw_pr q

let quality_printer binders = {
  Sorts.Quality.prvar = (fun q -> pr_quality_with_global_universes ~binders (QVar q));
  prglobal = (fun q -> pr_quality_with_global_universes ~binders (QGlobal q));
}

let sort_printer binders = {
  Sorts.prq = quality_printer binders;
  pru = (fun u -> pr_level_with_global_universes ~binders u);
}

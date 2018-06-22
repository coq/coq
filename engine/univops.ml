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
open Constr

let universes_of_constr c =
  let rec aux s c =
    match kind c with
    | Const (c, u) ->
          LSet.fold LSet.add (Instance.levels u) s
    | Ind ((mind,_), u) | Construct (((mind,_),_), u) ->
          LSet.fold LSet.add (Instance.levels u) s
    | Sort u when not (Sorts.is_small u) ->
      let u = Sorts.univ_of_sort u in
      LSet.fold LSet.add (Universe.levels u) s
    | _ -> Constr.fold aux s c
  in aux LSet.empty c

let restrict_universe_context (univs, csts) keep =
  let removed = LSet.diff univs keep in
  if LSet.is_empty removed then univs, csts
  else
  let allunivs = Constraint.fold (fun (u,_,v) all -> LSet.add u (LSet.add v all)) csts univs in
  let g = UGraph.empty_universes in
  let g = LSet.fold UGraph.add_universe_unconstrained allunivs g in
  let g = UGraph.merge_constraints csts g in
  let allkept = LSet.diff allunivs removed in
  let csts = UGraph.constraints_for ~kept:allkept g in
  (LSet.inter univs keep, csts)

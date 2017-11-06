(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Constr
open Univ

let universes_of_constr c =
  let rec aux s c = 
    match kind c with
    | Const (_, u) | Ind (_, u) | Construct (_, u) ->
      LSet.fold LSet.add (Instance.levels u) s
    | Sort u when not (Sorts.is_small u) -> 
      let u = Term.univ_of_sort u in
      LSet.fold LSet.add (Universe.levels u) s
    | _ -> Constr.fold aux s c
  in aux LSet.empty c

let restrict_universe_context (univs,csts) s =
  (* Universes that are not necessary to typecheck the term.
     E.g. univs introduced by tactics and not used in the proof term. *)
  let diff = LSet.diff univs s in
  let rec aux diff candid univs ness = 
    let (diff', candid', univs', ness') = 
      Constraint.fold
	(fun (l, d, r as c) (diff, candid, univs, csts) ->
	  if not (LSet.mem l diff) then
	    (LSet.remove r diff, candid, univs, Constraint.add c csts)
	  else if not (LSet.mem r diff) then
	    (LSet.remove l diff, candid, univs, Constraint.add c csts)
	  else (diff, Constraint.add c candid, univs, csts))
	candid (diff, Constraint.empty, univs, ness)
    in
      if ness' == ness then (LSet.diff univs diff', ness)
      else aux diff' candid' univs' ness'
  in aux diff csts univs Constraint.empty

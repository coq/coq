(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Univ
open Declarations

let universes_of_constr c =
  let rec aux s c = 
    match kind_of_term c with
    | Const (_, u) | Ind (_, u) | Construct (_, u) ->
      LSet.fold LSet.add (Instance.levels u) s
    | Sort u when not (Sorts.is_small u) -> 
      let u = univ_of_sort u in
      LSet.fold LSet.add (Universe.levels u) s
    | _ -> fold_constr aux s c
  in aux LSet.empty c

let universes_of_inductive mind =
  if mind.mind_polymorphic then
  begin
    let u = Univ.UContext.instance (Univ.UInfoInd.univ_context mind.mind_universes) in
    let univ_of_one_ind oind = 
      let arity_univs =
        Context.Rel.fold_outside
          (fun decl unvs ->
             Univ.LSet.union
              (Context.Rel.Declaration.fold_constr
                 (fun cnstr unvs ->
                    let cnstr = Vars.subst_instance_constr u cnstr in
                    Univ.LSet.union
                      (universes_of_constr cnstr) unvs)
              decl Univ.LSet.empty) unvs)
        oind.mind_arity_ctxt ~init:Univ.LSet.empty
      in
      Array.fold_left (fun unvs cns ->
          let cns = Vars.subst_instance_constr u cns in
          Univ.LSet.union (universes_of_constr cns) unvs) arity_univs 
       oind.mind_nf_lc
    in
    let univs = Array.fold_left (fun unvs pk -> Univ.LSet.union (univ_of_one_ind pk) unvs) Univ.LSet.empty mind.mind_packets in
    let mindcnt = Univ.UContext.constraints (Univ.instantiate_univ_context (Univ.UInfoInd.univ_context mind.mind_universes)) in
    let univs = Univ.LSet.union univs (Univ.universes_of_constraints mindcnt) in
    univs
  end
  else LSet.empty

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

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Univ
open Constr

let universes_of_constr env c =
  let open Declarations in
  let rec aux s c = 
    match kind c with
    | Const (c, u) ->
      begin match (Environ.lookup_constant c env).const_universes with
        | Polymorphic_const _ ->
          LSet.fold LSet.add (Instance.levels u) s
        | Monomorphic_const (univs, _) ->
          LSet.union s univs
      end
    | Ind ((mind,_), u) | Construct (((mind,_),_), u) ->
      begin match (Environ.lookup_mind mind env).mind_universes with
        | Cumulative_ind _ | Polymorphic_ind _ ->
          LSet.fold LSet.add (Instance.levels u) s
        | Monomorphic_ind (univs,_) ->
          LSet.union s univs
      end
    | Sort u when not (Sorts.is_small u) ->
      let u = Sorts.univ_of_sort u in
      LSet.fold LSet.add (Universe.levels u) s
    | _ -> Constr.fold aux s c
  in aux LSet.empty c

type graphnode = {
  mutable up : constraint_type LMap.t;
  mutable visited : bool
}

let merge_types d d0 =
  match d, d0 with
  | _, Lt | Lt, _ -> Lt
  | Le, _ | _, Le -> Le
  | Eq, Eq -> Eq

let merge_up d b up =
  let find = try Some (LMap.find b up) with Not_found -> None in
  match find with
  | Some d0 ->
    let d = merge_types d d0 in
    if d == d0 then up else LMap.add b d up
  | None -> LMap.add b d up

let add_up a d b graph =
  let node, graph =
    try LMap.find a graph, graph
    with Not_found ->
      let node = { up = LMap.empty; visited = false } in
      node, LMap.add a node graph
  in
  node.up <- merge_up d b node.up;
  graph

(* for each node transitive close until you find a non removable, discard the rest *)
let transitive_close removable graph =
  let rec do_node a node =
    if not node.visited
    then
      let keepup =
        LMap.fold (fun b d keepup ->
            if not (LSet.mem b removable)
            then merge_up d b keepup
            else
              begin
                match LMap.find b graph with
                | bnode ->
                  do_node b bnode;
                  LMap.fold (fun k d' keepup ->
                    merge_up (merge_types d d') k keepup)
                    bnode.up keepup
                | exception Not_found -> keepup
              end
          )
          node.up LMap.empty
      in
      node.up <- keepup;
      node.visited <- true
  in
  LMap.iter do_node graph

let restrict_universe_context (univs,csts) keep =
  let removable = LSet.diff univs keep in
  let (csts, rem) =
    Constraint.fold (fun (a,d,b as cst) (csts, rem) ->
        if LSet.mem a removable || LSet.mem b removable
        then (csts, add_up a d b rem)
        else (Constraint.add cst csts, rem))
      csts (Constraint.empty, LMap.empty)
  in
  transitive_close removable rem;
  let csts =
    LMap.fold (fun a node csts ->
        if LSet.mem a removable
        then csts
        else
          LMap.fold (fun b d csts -> Constraint.add (a,d,b) csts)
            node.up csts)
      rem csts
  in
  (LSet.inter univs keep, csts)

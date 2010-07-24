(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

type ('a,'b) t = Node of 'b Gset.t * ('a, ('a,'b) t) Gmap.t

let empty = Node (Gset.empty, Gmap.empty)

let map (Node (_,m)) lbl = Gmap.find lbl m

let xtract (Node (hereset,_)) = Gset.elements hereset

let dom (Node (_,m)) = Gmap.dom m

let in_dom (Node (_,m)) lbl = Gmap.mem lbl m

let is_empty_node (Node(a,b)) = (Gset.elements a = []) & (Gmap.to_list b = [])

let assure_arc m lbl =
  if Gmap.mem lbl m then
    m
  else
    Gmap.add lbl (Node (Gset.empty,Gmap.empty)) m

let cleanse_arcs (Node (hereset,m)) =
  let l = Gmap.rng m in
  Node(hereset, if List.for_all is_empty_node l then Gmap.empty else m)

let rec at_path f (Node (hereset,m)) = function
  | [] ->
      cleanse_arcs (Node(f hereset,m))
  | h::t ->
      let m = assure_arc m h in
      cleanse_arcs (Node(hereset,
                         Gmap.add h (at_path f (Gmap.find h m) t) m))

let add tm (path,v) =
  at_path (fun hereset -> Gset.add v hereset) tm path

let rmv tm (path,v) =
  at_path (fun hereset -> Gset.remove v hereset) tm path

let app f tlm =
  let rec apprec pfx (Node(hereset,m)) =
    let path = List.rev pfx in
    Gset.iter (fun v -> f(path,v)) hereset;
    Gmap.iter (fun l tm -> apprec (l::pfx) tm) m
  in
  apprec [] tlm

let to_list tlm =
  let rec torec pfx (Node(hereset,m)) =
    let path = List.rev pfx in
    List.flatten((List.map (fun v -> (path,v)) (Gset.elements hereset))::
		 (List.map (fun (l,tm) -> torec (l::pfx) tm) (Gmap.to_list m)))
  in
  torec [] tlm

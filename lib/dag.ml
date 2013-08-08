(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type S = sig

  type cluster_id
  val string_of_cluster_id : cluster_id -> string

  type node
  type ('edge,'info) t
  
  val empty : ('e,'i) t

  val add_edge : ('e,'i) t -> node -> 'e -> node -> ('e,'i) t
  val from_node : ('e,'i) t -> node -> (node * 'e) list
  val mem : ('e,'i) t -> node -> bool

  val iter : ('e,'i) t -> 
    (node -> cluster_id option -> 'i option ->
      (node * 'e) list -> unit) -> unit

  val create_cluster : ('e,'i) t -> node list -> ('e,'i) t
  val cluster_of : ('e,'i) t -> node -> cluster_id option

  val get_info : ('e,'i) t -> node -> 'i option
  val set_info : ('e,'i) t -> node -> 'i -> ('e,'i) t
  val clear_info : ('e,'i) t -> node -> ('e,'i) t

end

module Make(OT : Map.OrderedType) = struct

type node = OT.t
type cluster_id = int
let string_of_cluster_id = string_of_int

module NodeMap = Map.Make(OT)
module NodeSet = Set.Make(OT)

type ('edge,'info) t = {
  graph : (node * 'edge) list NodeMap.t;
  clusters : cluster_id NodeMap.t;
  infos : 'info NodeMap.t;
}

let empty = {
  graph = NodeMap.empty;
  clusters = NodeMap.empty;
  infos = NodeMap.empty;
}

let mem { graph } id = NodeMap.mem id graph

let add_edge dag from trans dest = { dag with
  graph =
    let extra = [dest, trans] in
    try NodeMap.add from (extra @ NodeMap.find from dag.graph) dag.graph
    with Not_found -> NodeMap.add from extra dag.graph }

let from_node { graph } id = NodeMap.find id graph 

let clid = ref 1
let create_cluster dag l=
  incr clid;
  { dag with clusters =
     List.fold_right (fun x clusters ->
       NodeMap.add x !clid clusters) l dag.clusters }

let cluster_of dag id =
  try Some (NodeMap.find id dag.clusters)
  with Not_found -> None

let get_info dag id =
  try Some (NodeMap.find id dag.infos)
  with Not_found -> None

let set_info dag id info = { dag with infos = NodeMap.add id info dag.infos }

let clear_info dag id = { dag with infos = NodeMap.remove id dag.infos }

let iter dag f =
  NodeMap.iter (fun k v -> f k (cluster_of dag k) (get_info dag k) v) dag.graph

end


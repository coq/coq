(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type S = sig

  module Cluster :
  sig
    type 'd t
    val equal : 'd t -> 'd t -> bool
    val compare : 'd t -> 'd t -> int
    val to_string : 'd t -> string
    val data : 'd t -> 'd
  end

  type node
  module NodeSet : Set.S with type elt = node

  type ('edge,'info,'cdata) t

  val empty : ('e,'i,'d) t

  val add_edge : ('e,'i,'d) t -> node -> 'e -> node -> ('e,'i,'d) t
  val from_node : ('e,'i,'d) t -> node -> (node * 'e) list
  val mem : ('e,'i,'d) t -> node -> bool
  val del_edge : ('e,'i,'d) t -> node -> node -> ('e,'i,'d) t
  val del_nodes : ('e,'i,'d) t -> NodeSet.t  -> ('e,'i,'d) t
  val all_nodes : ('e,'i,'d) t -> NodeSet.t

  val iter : ('e,'i,'d) t ->
    (node -> 'd Cluster.t option -> 'i option ->
      (node * 'e) list -> unit) -> unit

  val create_cluster : ('e,'i,'d) t -> node list -> 'd -> ('e,'i,'d) t
  val cluster_of : ('e,'i,'d) t -> node -> 'd Cluster.t option
  val del_cluster : ('e,'i,'d) t -> 'd Cluster.t -> ('e,'i,'d) t

  val get_info : ('e,'i,'d) t -> node -> 'i option
  val set_info : ('e,'i,'d) t -> node -> 'i -> ('e,'i,'d) t
  val clear_info : ('e,'i,'d) t -> node -> ('e,'i,'d) t

end

module Make(OT : Map.OrderedType) = struct

module Cluster =
struct
  type 'd t = 'd * int
  let equal (_,i1) (_,i2) = Int.equal i1 i2
  let compare (_,i1) (_,i2) = Int.compare i1 i2
  let to_string (_,i) = string_of_int i
  let data (d,_) = d
end

type node = OT.t

module NodeMap = CMap.Make(OT)
module NodeSet = Set.Make(OT)

type ('edge,'info,'data) t = {
  graph : (node * 'edge) list NodeMap.t;
  clusters : 'data Cluster.t NodeMap.t;
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
    try NodeMap.modify from (fun _ arcs -> (dest, trans) :: arcs) dag.graph
    with Not_found -> NodeMap.add from [dest, trans] dag.graph }

let from_node { graph } id = NodeMap.find id graph

let del_edge dag id tgt = { dag with
  graph =
    try
      let modify _ arcs =
        let filter (d, _) = OT.compare d tgt <> 0 in
        List.filter filter arcs
      in
      NodeMap.modify id modify dag.graph
    with Not_found -> dag.graph }

let del_nodes dag s = {
  infos = NodeMap.filter (fun n _ -> not(NodeSet.mem n s)) dag.infos;
  clusters = NodeMap.filter (fun n _ -> not(NodeSet.mem n s)) dag.clusters;
  graph = NodeMap.filter (fun n l ->
      let drop = NodeSet.mem n s in
      if not drop then
        assert(List.for_all (fun (n',_) -> not(NodeSet.mem n' s)) l);
      not drop)
    dag.graph }

let clid = ref 1
let create_cluster dag l data =
  incr clid;
  { dag with clusters =
     List.fold_right (fun x clusters ->
       NodeMap.add x (data, !clid) clusters) l dag.clusters }

let cluster_of dag id =
  try Some (NodeMap.find id dag.clusters)
  with Not_found -> None

let del_cluster dag c =
  { dag with clusters =
     NodeMap.filter (fun _ c' -> not (Cluster.equal c' c)) dag.clusters }

let get_info dag id =
  try Some (NodeMap.find id dag.infos)
  with Not_found -> None

let set_info dag id info = { dag with infos = NodeMap.add id info dag.infos }

let clear_info dag id = { dag with infos = NodeMap.remove id dag.infos }

let iter dag f =
  NodeMap.iter (fun k v -> f k (cluster_of dag k) (get_info dag k) v) dag.graph

let all_nodes dag = NodeMap.domain dag.graph

end


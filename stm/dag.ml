(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type S = sig

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

  val get_info : ('e,'i,'d) t -> node -> 'i option
  val set_info : ('e,'i,'d) t -> node -> 'i -> ('e,'i,'d) t
  val clear_info : ('e,'i,'d) t -> node -> ('e,'i,'d) t

  module Property :
  sig
    type 'd t
    val equal : 'd t -> 'd t -> bool
    val compare : 'd t -> 'd t -> int
    val to_string : 'd t -> string
    val data : 'd t -> 'd
    val having_it : 'd t -> NodeSet.t
  end

  val create_property : ('e,'i,'d) t -> node list -> 'd -> ('e,'i,'d) t
  val property_of : ('e,'i,'d) t -> node -> 'd Property.t list
  val del_property : ('e,'i,'d) t -> 'd Property.t -> ('e,'i,'d) t

  val iter : ('e,'i,'d) t ->
    (node -> 'd Property.t list -> 'i option ->
      (node * 'e) list -> unit) -> unit

end

module Make(OT : Map.OrderedType) = struct

module NodeSet = Set.Make(OT)

module Property =
struct
  type 'd t = { data : 'd; uid : int; having_it : NodeSet.t }
  let equal { uid = i1 } { uid = i2 } = Int.equal i1 i2
  let compare { uid = i1 } { uid = i2 } = Int.compare i1 i2
  let to_string { uid = i } = string_of_int i
  let data { data = d } = d
  let having_it { having_it } = having_it
end

type node = OT.t

module NodeMap = CMap.Make(OT)

type ('edge,'info,'data) t = {
  graph : (node * 'edge) list NodeMap.t;
  properties : 'data Property.t list NodeMap.t;
  infos : 'info NodeMap.t;
}

let empty = {
  graph = NodeMap.empty;
  properties = NodeMap.empty;
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
  properties = NodeMap.filter (fun n _ -> not(NodeSet.mem n s)) dag.properties;
  graph = NodeMap.filter (fun n l ->
      let drop = NodeSet.mem n s in
      if not drop then
        assert(List.for_all (fun (n',_) -> not(NodeSet.mem n' s)) l);
      not drop)
    dag.graph }

let map_add_list k v m =
  try
    let l = NodeMap.find k m in
    NodeMap.add k (v::l) m
  with Not_found -> NodeMap.add k [v] m

let clid = ref 1
let create_property dag l data =
  incr clid;
  let having_it = List.fold_right NodeSet.add l NodeSet.empty in
  let property = { Property.data; uid = !clid; having_it } in
  { dag with properties =
     List.fold_right (fun x ps -> map_add_list x property ps) l dag.properties }

let property_of dag id =
  try NodeMap.find id dag.properties
  with Not_found -> []

let del_property dag c =
  { dag with properties =
     NodeMap.filter (fun _ cl -> cl <> [])
       (NodeMap.map (fun cl ->
          List.filter (fun c' ->
            not (Property.equal c' c)) cl)
          dag.properties) }

let get_info dag id =
  try Some (NodeMap.find id dag.infos)
  with Not_found -> None

let set_info dag id info = { dag with infos = NodeMap.add id info dag.infos }

let clear_info dag id = { dag with infos = NodeMap.remove id dag.infos }

let iter dag f =
  NodeMap.iter (fun k v -> f k (property_of dag k) (get_info dag k) v) dag.graph

let all_nodes dag = NodeMap.domain dag.graph

end


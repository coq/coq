(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type S = sig

  (* A cluster is just a set of nodes.  This set holds some data.
     Stm uses this to group nodes contribution to the same proofs and
     that can be evaluated asynchronously *)
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

module Make(OT : Map.OrderedType) : S with type node = OT.t


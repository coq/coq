(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type S = sig

  module Cluster :
  sig
    type t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val to_string : t -> string
  end

  type node
  type ('edge,'info) t

  val empty : ('e,'i) t

  val add_edge : ('e,'i) t -> node -> 'e -> node -> ('e,'i) t
  (* raise Not_found if the node is not there *)
  val from_node : ('e,'i) t -> node -> (node * 'e) list
  val mem : ('e,'i) t -> node -> bool

  val iter : ('e,'i) t -> 
    (node -> Cluster.t option -> 'i option ->
      (node * 'e) list -> unit) -> unit

  val create_cluster : ('e,'i) t -> node list -> ('e,'i) t
  val cluster_of : ('e,'i) t -> node -> Cluster.t option

  val get_info : ('e,'i) t -> node -> 'i option
  val set_info : ('e,'i) t -> node -> 'i -> ('e,'i) t
  val clear_info : ('e,'i) t -> node -> ('e,'i) t

end

module Make(OT : Map.OrderedType) : S with type node = OT.t


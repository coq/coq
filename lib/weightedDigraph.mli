module type COMPARABLE = sig
  type t
  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool
end

module Make : functor(V: COMPARABLE) -> sig
  type t
  type vertex = V.t

  module E : sig
    type t = vertex * int * vertex
    val compare : t -> t -> int
  end

  type edge = E.t
  val nb_vertex : t -> int
  val mem_vertex : t -> vertex -> bool
  val mem_edge_e : t -> edge -> bool
  val create : ?size:int -> unit -> t
  val copy : t -> t
  val add_edge_e : t -> edge -> unit
  val remove_vertex : t -> vertex -> unit
  val find_all_edges : t -> vertex -> vertex -> edge list
  val fold_edges_e : (edge -> 'a -> 'a) -> t -> 'a -> 'a
  val iter_edges_e : (edge -> unit) -> t -> unit
  val succ : t -> vertex -> vertex list
  val pred : t -> vertex -> vertex list
  val bellman_ford : t -> edge list
end

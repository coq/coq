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

  (* A property applies to a set of nodes and holds some data.
     Stm uses this feature to group nodes contributing to the same proofs and
     to structure proofs in boxes limiting the scope of errors *)
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

module Make(OT : Map.OrderedType) : S
with type node = OT.t
and type NodeSet.t = Set.Make(OT).t
and type NodeSet.elt = OT.t


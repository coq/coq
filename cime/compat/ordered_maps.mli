(***************************************************************************

Maps over ordered sets, polymorphic keys, with in place modification
of values

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

module type OrderedMap =
  sig
    type 'a key
    type ('a,'b) t
    val empty: ('a,'b) t
    val add: 'a key -> 'b -> ('a,'b) t -> ('a,'b) t
    val find: 'a key -> ('a,'b) t -> 'b
    val remove: 'a key -> ('a,'b) t -> ('a,'b) t
    val mem:  'a key -> ('a,'b) t -> bool    
    val iter: ('a key -> 'b -> unit) -> ('a,'b) t -> unit
    val map: ('b -> 'c) -> ('a,'b) t -> ('a,'c) t
    val mapi: ('a key -> 'b -> 'c) -> ('a,'b) t -> ('a,'c) t
    val fold: ('a key -> 'b -> 'c -> 'c) -> ('a,'b) t -> 'c -> 'c
    val max: ('a,'b) t -> 'a key * 'b
    val min: ('a,'b) t -> 'a key * 'b
    val elements_increasing_order: ('a,'b) t -> ('a key * 'b) list
    val find_one : ('a key -> 'b -> bool) -> ('a,'b) t -> 'b
    val find_key : ('a key -> 'b -> bool) -> ('a,'b) t -> 'a key
    val size : ('a,'b) t -> int
  end

module Make(Ord: Ordered_types.OrderedType) : 
  OrderedMap with type 'a key=Ord.t;;

module MakePoly(Ord: Ordered_types.OrderedPolyType) : 
  OrderedMap with type 'a key='a Ord.t;;




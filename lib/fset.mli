module Make : functor (X : Set.OrderedType) ->
sig
  type elt = X.t
  type  t

val empty :  t
val is_empty :  t -> bool
val mem : elt ->  t -> bool
val add : elt ->  t ->  t
val singleton : elt ->  t
val remove : elt -> t -> t
val union : t -> t -> t
val inter : t -> t -> t
val diff : t -> t -> t
val compare : t -> t -> int
val equal : t -> t -> bool
val subset : t -> t -> bool
val iter : ( elt -> unit) -> t -> unit
val fold : (elt -> 'b -> 'b) -> t -> 'b -> 'b
val cardinal : t -> int
val elements : t -> elt list
val min_elt : t -> elt
val max_elt : t -> elt
val choose : t -> elt
end


module Make : functor (X : Map.OrderedType) ->
sig
  type key = X.t
  type 'a t

val empty : 'a t
val is_empty : 'a t -> bool
val add : key -> 'a -> 'a t -> 'a t
val find : key -> 'a t -> 'a
val remove : key -> 'a t -> 'a t
val mem :  key -> 'a t -> bool
val iter : (key -> 'a -> unit) -> 'a t -> unit
val map : ('a -> 'b) -> 'a t -> 'b t
val fold : (key -> 'a -> 'c -> 'c) -> 'a t -> 'c -> 'c

(* Additions with respect to ocaml standard library. *)

val dom : 'a t -> key list
val rng : 'a t -> 'a list
val to_list : 'a t -> (key * 'a) list
end
 


(* $Id$ *)

(* Maps from ['a] to lists of ['b]. *)

type ('a,'b) t

val empty : ('a,'b) t
val mem :  'a -> ('a,'b) t -> bool
val iter : ('a -> 'b list -> unit) -> ('a,'b) t -> unit
val map : ('b list -> 'c list) -> ('a,'b) t -> ('a,'c) t
val fold : ('a -> 'b list -> 'c -> 'c) -> ('a,'b) t -> 'c -> 'c

val add : 'a -> 'b -> ('a,'b) t -> ('a,'b) t
val find : 'a -> ('a,'b) t -> 'b list
val remove : 'a -> 'b -> ('a,'b) t -> ('a,'b) t

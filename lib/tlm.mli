
(* $Id$ *)

type ('a,'b) t

val create : unit -> ('a,'b) t

(* Work on labels, not on paths *)

val map : ('a,'b) t -> 'a -> ('a,'b) t
val xtract : ('a,'b) t -> 'b list
val dom : ('a,'b) t -> 'a list
val in_dom : ('a,'b) t -> 'a -> bool

(* Work on paths, not labels *)

val add : ('a,'b) t -> 'a list * 'b -> ('a,'b) t
val rmv : ('a,'b) t -> ('a list * 'b) -> ('a,'b) t

val app : (('a list * 'c) -> unit) -> ('a,'c) t -> unit
val to_list : ('a,'b) t -> ('a list * 'b) list



open Hcons

type 'a t
    
val empty : 'a t

val is_empty : 'a t -> bool

val mem : 'a hash_consed -> 'a t -> bool
      
val add : 'a hash_consed -> 'a t -> 'a t
      
val singleton : 'a hash_consed -> 'a t

val remove : 'a hash_consed -> 'a t -> 'a t

val union : 'a t -> 'a t -> 'a t

val subset : 'a t -> 'a t -> bool

val inter : 'a t -> 'a t -> 'a t

val diff : 'a t -> 'a t -> 'a t

val equal : 'a t -> 'a t -> bool

(*

  [equalq t1 t2] checks equality of [t1] and [t2], using physical equality
  over elements.

*)

val equalq : 'a t -> 'a t -> bool

val compare : 'a t -> 'a t -> int

val elements : 'a t -> 'a hash_consed list
      
val choose : 'a t -> 'a  hash_consed

val elt : 'a t -> 'a  hash_consed

val cardinal : 'a t -> int

val iter : ('a hash_consed -> unit) -> 'a t -> unit

val fold : ('a hash_consed -> 'b -> 'b) -> 'a t -> 'b -> 'b

(*

  [case e f1 f2] computes [f1()] if [e] is empty, and [f2 h t] if [e]
  is not empty where [h] is some element of [e] and [t] is [e-h].

*)

val case : 'a t -> (unit -> 'b) -> ('a hash_consed -> 'a t -> 'b) -> 'b

(*

  [case1 f0 f1 f e] computes [f0()] if [e] is empty, [f1 x] if [e] has
  one element [x], and [f ()] otherwise.

*)

val case1 : 
  (unit -> 'b) -> ('a hash_consed -> 'b) -> (unit -> 'b) -> 'a t -> 'b

val for_all : ('a hash_consed -> bool) -> 'a t -> bool

val exists : ('a hash_consed -> bool) -> 'a t -> bool

val filter : ('a hash_consed -> bool) -> 'a t -> 'a t

val partition : ('a hash_consed -> bool) -> 'a t -> 'a t * 'a t


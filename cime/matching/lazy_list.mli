type 'a frozen = Freeze of (unit -> 'a) | Val of 'a
and 'a llist = Nil | Cons of 'a cell
and 'a cell = { head : 'a; mutable tail : 'a llist frozen; } 
val hdl : 'a llist -> 'a
val mapl : ('a -> 'b) -> 'a llist -> 'b llist
val map : ('a -> 'b) -> 'a list -> 'b llist
val map2_without_repetition : ('a -> 'b * 'b) -> 'a list -> 'b llist
val lazy_append : 'a llist -> 'a llist frozen -> 'a llist

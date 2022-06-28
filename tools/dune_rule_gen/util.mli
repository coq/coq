(* Utilities missing from stdlib *)

val list_concat_map : ('a -> 'b list) -> 'a list -> 'b list
val pmap : ('a -> 'b option) -> 'a list -> 'b list

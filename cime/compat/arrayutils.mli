(***************************************************************************

  Various basic functions on arrays : interface

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

val index : 'a -> 'a array -> int

val find : ('a -> bool) -> 'a array -> int

val filter : ('a -> bool) -> 'a array -> 'a list

val fold_lefti : ('a -> int -> 'b -> 'a) -> 'a -> 'b array -> 'a

val fold_righti : (int -> 'a -> 'b -> 'b) -> 'a array -> 'b -> 'b

val filter_indices : ('a -> bool) -> 'a array -> int list


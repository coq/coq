(***************************************************************************

Balanced trees with two data info (one key, one data)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


type ('key,'data) node_info =
    {
      key : 'key;
      data : 'data;
      height : int;
      left : ('key,'data) t;
      right : ('key,'data) t
    }	
    
and ('key,'data) t =
    Empty
  | Node of ('key,'data) node_info
      

val empty : ('key, 'data) t

val height : ('key, 'data) t -> int

val create : 
  ('key, 'data) t -> 'key -> 'data -> ('key, 'data) t -> ('key, 'data) t

val bal : 
  ('key, 'data) t -> 'key -> 'data -> ('key, 'data) t -> ('key, 'data) t

val merge : ('key, 'data) t -> ('key, 'data) t -> ('key, 'data) t

val iter : ('key -> 'data -> 'a) -> ('key, 'data) t -> unit

val map : ('data1 -> 'data2) -> ('key, 'data1) t -> ('key, 'data2) t

val mapi : ('key -> 'data1 -> 'data2) -> ('key, 'data1) t -> ('key, 'data2) t

val fold : ('key -> 'data -> 'a -> 'a) -> ('key, 'data) t -> 'a -> 'a

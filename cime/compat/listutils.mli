(***************************************************************************

  Various basic functions on lists : interface

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


(*

  This module provides some basic functions on lists, mainly functions
  that used to exist in earlier version of CAML, but do not exist
  anymore.

  Advice: the functions that operate on lists as if they were sets
  should not be used anymore, the module Set should be used instead.

*)

val power : 'a list -> int -> 'a list
 
val intersect : 'a list -> 'a list -> 'a list
val add : 'a -> 'a list -> 'a list
val union : 'a list -> 'a list -> 'a list
val index : 'a -> 'a list -> int
val except : 'a -> 'a list -> 'a list
val remove : 'a -> ('a * 'b) list -> ('a * 'b) list
val flat_map : ('a -> 'b list) -> 'a list -> 'b list
val subtract : 'a list -> 'a list -> 'a list
val do_list_combine : ('a * 'b -> 'c) -> 'a list * 'b list -> unit
val map_filter : ('a -> 'b) -> ('a -> bool) -> 'a list -> 'b list
val map_with_exception : exn -> ('a -> 'b) -> 'a list -> 'b list
val split : string -> string list;;
val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
val flat_mapi : (int -> 'a -> 'b list) -> 'a list -> 'b list



(*

  [fold_right_env f env [l1;..;lk]] is equivalent to
  \begin{verbatim}

  let env1,e1 = f env l1 in
  let env2,e2 = f env1 l2 in
  ...
  let envk,ek = f env{k-1} lk in
  envk,[e1;..,ek]
  \end{verbatim}
*)
  
val fold_right_env :
  ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> ('a * 'c list)
;;

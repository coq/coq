(***************************************************************************

Maps over ordered sets, polymorphic

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Ordered_types;;


module type OrderedMap =
  sig
    type 'a key
    type ('a,'b) t
    val empty: ('a,'b) t
    val add: 'a key -> 'b -> ('a,'b) t -> ('a,'b) t
    val find: 'a key -> ('a,'b) t -> 'b
    val remove: 'a key -> ('a,'b) t -> ('a,'b) t
    val mem:  'a key -> ('a,'b) t -> bool    
    val iter: ('a key -> 'b -> unit) -> ('a,'b) t -> unit
    val map: ('b -> 'c) -> ('a,'b) t -> ('a,'c) t
    val mapi: ('a key -> 'b -> 'c) -> ('a,'b) t -> ('a,'c) t
    val fold: ('a key -> 'b -> 'c -> 'c) -> ('a,'b) t -> 'c -> 'c
    val max: ('a,'b) t -> 'a key * 'b
    val min: ('a,'b) t -> 'a key * 'b
    val elements_increasing_order: ('a,'b) t -> ('a key * 'b) list
    val find_one : ('a key -> 'b -> bool) -> ('a,'b) t -> 'b
    val find_key : ('a key -> 'b -> bool) -> ('a,'b) t -> 'a key
    val size : ('a,'b) t -> int
  end
;;


open Balanced_trees2;;

module MakePoly(Ord: OrderedPolyType) = 
  struct

    type 'a key = 'a Ord.t

    type ('a,'b) t = ('a key,'b) Balanced_trees2.t;;

    let empty = Empty;;

    let rec add x data = function
        Empty ->
          Node
	    {
	      key = x;
	      data = data;
	      height = 1;
	      left = Empty;
	      right = Empty
	    } 
      | Node(i) ->
          let c = Ord.compare x i.key in
          if c = 0 
	  then
            Node
	      {
	        key = x;
	        data = data;
	        height = i.height;
	        left = i.left;
	        right = i.right
	      }
          else 
	    if c < 0 
	    then
              bal (add x data i.left) i.key i.data i.right
            else
              bal i.left i.key i.data (add x data i.right)

    let rec find x = function
        Empty ->
          raise Not_found
      | Node(i) ->
          let c = Ord.compare x i.key in
          if c = 0 then i.data
          else find x (if c < 0 then i.left else i.right)

    let rec remove x = function
        Empty ->
          Empty
      | Node(i) ->
          let c = Ord.compare x i.key in
          if c = 0 then
            merge i.left i.right
          else if c < 0 then
            bal (remove x i.left) i.key i.data i.right
          else
            bal i.left i.key i.data (remove x i.right)

    let rec mem x = function
        Empty -> false
      | Node(i) ->
          let c = Ord.compare x i.key in
          if c = 0 then true
          else mem x (if c < 0 then i.left else i.right)

    let iter = Balanced_trees2.iter

    let map = Balanced_trees2.map

    let mapi = Balanced_trees2.mapi

    let fold = Balanced_trees2.fold

    let rec max = function
      	Empty -> raise Not_found
      | Node(i) ->
	  if i.right=Empty
	  then i.key,i.data
	  else max i.right
	
    let rec min = function
      	Empty -> raise Not_found
      | Node(i) ->
	  if i.left=Empty
	  then i.key,i.data
	  else min i.left
	
    let rec elements_increasing_order_aux accu =  function
	Empty -> accu
      |	Node(i) ->
	  elements_increasing_order_aux 
	    ((i.key,i.data)::(elements_increasing_order_aux accu i.right)) 
	    i.left

    let rec elements_increasing_order t = 
	elements_increasing_order_aux [] t
  
    let rec elements_decreasing_order_aux accu =  function
	Empty -> accu
      |	Node(i) ->
	  elements_decreasing_order_aux 
	    ((i.key,i.data)::(elements_decreasing_order_aux accu i.left)) 
	    i.right

    let rec elements_decreasing_order t = 
	elements_decreasing_order_aux [] t
  
    let rec find_one p = function
	Empty -> raise Not_found
      | Node(i) ->          
	  if p i.key i.data 
	  then i.data
          else 
	    try find_one p i.left with Not_found -> find_one p i.right
	  
    let rec find_key p = function
	Empty -> raise Not_found
      | Node(i) ->          
	  if p i.key i.data 
	  then i.key
          else 
	    try find_key p i.left with Not_found -> find_key p i.right

    let rec size t = 
      match t with
	| Empty -> 0
	| Node(i) -> 1 + (size i.left) + (size i.right)
end

module Make(Ord: OrderedType) = 
  MakePoly(struct
	     type 'a t = Ord.t
	     let compare = Ord.compare
	   end);;



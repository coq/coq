(***************************************************************************

Sets over ordered sets. Same as the standard set module of ocaml, but
polymorphic and allow extraction of min and max

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

module type OrderedSet =
  sig
    type 'a elt
    type 'a t
    val empty: 'a t
    val is_empty: 'a t -> bool
    val mem: 'a elt -> 'a t -> bool
    val add: 'a elt -> 'a t -> 'a t
    val singleton: 'a elt -> 'a t
    val remove: 'a elt -> 'a t -> 'a t
    val union: 'a t -> 'a t -> 'a t
    val inter: 'a t -> 'a t -> 'a t
    val diff: 'a t -> 'a t -> 'a t
    val compare: 'a t -> 'a t -> int
    val equal: 'a t -> 'a t -> bool
    val subset: 'a t -> 'a t -> bool
    val iter: ('a elt -> unit) -> 'a t -> unit
    val fold: ('a elt -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val filter : ('a elt -> bool) -> 'a t -> 'a t
    val cardinal: 'a t -> int
    val elements: 'a t -> 'a elt list
    val choose: 'a t -> 'a elt
    val min_elt: 'a t -> 'a elt
    val find : ('a elt -> bool) -> 'a t -> 'a elt
    val exists : ('a elt -> bool) -> 'a t -> bool
  end
;;

open Balanced_trees;;

module MakePoly(Ord: Ordered_types.OrderedPolyType) =
struct
  type 'a elt = 'a Ord.t
		  
  (* Sets are represented by balanced binary trees (the heights of the 
     children differ by at most 2 *)
		  
  type 'a t = ('a elt) Balanced_trees.t
		
  (* Implementation of the set operations *)
		
  let empty = Empty
		
  let is_empty = function Empty -> true | _ -> false

  let rec mem x = function
      Empty -> false
    | Node(l, v, r, _) ->
        let c = Ord.compare x v in
        if c = 0 then true else
          if c < 0 then mem x l else mem x r
	    
  let rec add x = function
      Empty -> Node(Empty, x, Empty, 1)
    | Node(l, v, r, _) as t ->
        let c = Ord.compare x v in
        if c = 0 then t else
          if c < 0 then bal (add x l) v r else bal l v (add x r)
	
  let singleton x = Node(Empty, x, Empty, 1)

  let rec remove x = function
      Empty -> Empty
    | Node(l, v, r, _) ->
        let c = Ord.compare x v in
        if c = 0 then merge l r else
          if c < 0 then bal (remove x l) v r else bal l v (remove x r)
	    
(* Splitting *)

  let rec split x = function
      Empty ->
	(Empty, None, Empty)
    | Node(l, v, r, _) ->
	let c = Ord.compare x v in
	if c = 0 then (l, Some v, r)
	else if c < 0 then
          let (ll, vl, rl) = split x l in (ll, vl, join rl v r)
	else
          let (lr, vr, rr) = split x r in (join l v lr, vr, rr)


  let rec union s1 s2 =
    match (s1, s2) with
        (Empty, t2) -> t2
      | (t1, Empty) -> t1
      | (Node(l1, v1, r1, _), t2) ->
          let (l2, _, r2) = split v1 t2 in
          join (union l1 l2) v1 (union r1 r2)
	    
  let rec inter s1 s2 =
    match (s1, s2) with
        (Empty, t2) -> Empty
      | (t1, Empty) -> Empty
      | (Node(l1, v1, r1, _), t2) ->
          match split v1 t2 with
              (l2, None, r2) ->
		concat (inter l1 l2) (inter r1 r2)
            | (l2, Some _, r2) ->
		join (inter l1 l2) v1 (inter r1 r2)
		  
  let rec diff s1 s2 =
    match (s1, s2) with
        (Empty, t2) -> Empty
      | (t1, Empty) -> t1
      | (Node(l1, v1, r1, _), t2) ->
          match split v1 t2 with
              (l2, None, r2) ->
		join (diff l1 l2) v1 (diff r1 r2)
            | (l2, Some _, r2) ->
		concat (diff l1 l2) (diff r1 r2)
		  
  let rec compare_aux l1 l2 =
    match (l1, l2) with
        ([], []) -> 0
      | ([], _)  -> -1
      | (_, []) -> 1
      | (Empty :: t1, Empty :: t2) ->
          compare_aux t1 t2
      | (Node(Empty, v1, r1, _) :: t1, Node(Empty, v2, r2, _) :: t2) ->
          let c = Ord.compare v1 v2 in
          if c <> 0 then c else compare_aux (r1::t1) (r2::t2)
      | (Node(l1, v1, r1, _) :: t1, t2) ->
          compare_aux (l1 :: Node(Empty, v1, r1, 0) :: t1) t2
      | (t1, Node(l2, v2, r2, _) :: t2) ->
          compare_aux t1 (l2 :: Node(Empty, v2, r2, 0) :: t2)
	    
  let compare s1 s2 =
    compare_aux [s1] [s2]
      
  let equal s1 s2 =
    compare s1 s2 = 0
		      
  let rec subset s1 s2 =
    match (s1, s2) with
        Empty, _ ->
          true
      | _, Empty ->
          false
      | Node (l1, v1, r1, _), (Node (l2, v2, r2, _) as t2) ->
          let c = Ord.compare v1 v2 in
          if c = 0 then
            subset l1 l2 && subset r1 r2
          else if c < 0 then
            subset (Node (l1, v1, Empty, 0)) l2 && subset r1 t2
          else
            subset (Node (Empty, v1, r1, 0)) r2 && subset l1 t2
	      
  let rec iter f = function
      Empty -> ()
    | Node(l, v, r, _) -> iter f l; f v; iter f r
	
  let rec fold f s accu =
    match s with
        Empty -> accu
      | Node(l, v, r, _) -> fold f l (f v (fold f r accu))
	    
  let filter p s = 
      let rec filt accu = function
        | Empty -> accu
        | Node(l, v, r, _) ->
            filt (filt (if p v then add v accu else accu) l) r in
      filt Empty s
      
  let rec cardinal = function
      Empty -> 0
    | Node(l, v, r, _) -> cardinal l + 1 + cardinal r
	  
  let rec elements_aux accu = function
      Empty -> accu
    | Node(l, v, r, _) -> elements_aux (v :: elements_aux accu r) l
	  
  let elements s =
    elements_aux [] s
      
  let rec choose = function
      Empty -> raise Not_found
    | Node(Empty, v, r, _) -> v
    | Node(l, v, r, _) -> choose l

  let rec min_elt = function
      Empty -> raise Not_found
    | Node(Empty, v, r, _) -> v
    | Node(l, v, r, _) -> min_elt l

  let rec find p = function
      Empty -> raise Not_found
    | Node (l,v,r,_) ->
	if p v
	then v
	else 
	  try find p l
	  with Not_found -> find p r

  let rec exists p = function
      Empty -> false
    | Node (l,v,r,_) -> p v || exists p l || exists p r
end
  

module Make(Ord: Ordered_types.OrderedType) =
  MakePoly (
    struct
      type 'a t = Ord.t
      let compare = Ord.compare
    end);;


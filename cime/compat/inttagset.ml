(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



module type IntTagSetModule =
sig
  type 'a elt 

  type 'a t
    
  val empty : 'a t

  val is_empty : 'a t -> bool

  val mem : 'a elt -> 'a t -> bool
      
  val add : 'a elt -> 'a t -> 'a t
      
  val singleton : 'a elt -> 'a t

  val remove : 'a elt -> 'a t -> 'a t

  val union : 'a t -> 'a t -> 'a t

  val subset : 'a t -> 'a t -> bool

  val inter : 'a t -> 'a t -> 'a t

  val diff : 'a t -> 'a t -> 'a t

  val equal : 'a t -> 'a t -> bool

  val compare : 'a t -> 'a t -> int

  val elements : 'a t -> 'a elt list
      
  val choose : 'a t -> 'a elt

  val cardinal : 'a t -> int

  val iter : ('a elt -> unit) -> 'a t -> unit

  val fold : ('a elt -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val for_all : ('a elt -> bool) -> 'a t -> bool

  val exists : ('a elt -> bool) -> 'a t -> bool

  val filter : ('a elt -> bool) -> 'a t -> 'a t

  val partition : ('a elt -> bool) -> 'a t -> 'a t * 'a t

(*
  val cases : 'a t -> (unit -> 'b) -> ('a elt -> 'a t -> 'b) -> 'b
*)
end


module MakePoly(O : sig type 'a t val tag : 'a t -> int end) =
struct
  
  type 'a elt = 'a O.t
		  
  type 'a t =
    | Empty
    | Leaf of 'a elt
    | Branch of int * int * 'a t * 'a t
	
  let empty = Empty
		
  let is_empty = function Empty -> true | _ -> false

  let singleton k = Leaf k

  let zero_bit k m = (k land m) = 0

  let rec tag_mem k = function
    | Empty -> false
    | Leaf j -> k = O.tag j
    | Branch (_, m, l, r) -> tag_mem k (if zero_bit k m then l else r)

  let mem e s = tag_mem (O.tag e) s

  let lowest_bit x = x land (-x)
		       
  let branching_bit p0 p1 = lowest_bit (p0 lxor p1)

  let mask p m = p land (m-1)

  let join p0 t0 p1 t1 =
    let m = branching_bit p0 p1 in
    if zero_bit p0 m 
    then Branch(mask p0 m, m, t0, t1)
    else Branch(mask p0 m, m, t1, t0)

  let match_prefix k p m = (mask k m) = p

  let rec ins e e_tag t = 
    match t with
      | Empty -> Leaf e
      | Leaf j ->
	  let j_tag = O.tag j in
	  if j_tag = e_tag then t else join e_tag (Leaf e) j_tag t
      | Branch(p,m,t0,t1) ->
	  if match_prefix e_tag p m 
	  then
	    if zero_bit e_tag m 
	    then Branch(p, m, ins e e_tag t0, t1)
	    else Branch(p, m, t0, ins e e_tag t1)
	  else
	    join e_tag (Leaf e) p t
	    
  let add e t = ins e (O.tag e) t
      
  let branch p m t0 t1 = 
    if t0=Empty 
    then t1
    else 
      if t1=Empty 
      then t0
      else Branch(p,m,t0,t1)

  let rec rmv e_tag t = 
    match t with
      | Empty -> Empty
      | Leaf j -> if e_tag = O.tag j then Empty else t
      | Branch (p,m,t0,t1) -> 
	  if match_prefix e_tag p m 
	  then
	    if zero_bit e_tag m 
	    then branch p m (rmv e_tag t0) t1
	    else branch p m t0 (rmv e_tag t1)
	  else
	    t

  let remove e t = rmv (O.tag e) t

  let rec merge s t = 
    match (s,t) with 
      | Empty, t  -> t
      | t, Empty  -> t
      | Leaf k, t -> add k t
      | t, Leaf k -> add k t
      | Branch(p,m,s0,s1), Branch(q,n,t0,t1) ->
	  if m = n && match_prefix q p m 
	  then
	    (* The trees have the same prefix. Merge the subtrees. *)
	    Branch(p, m, merge s0 t0, merge s1 t1)
	  else 
	    if m < n && match_prefix q p m 
	    then
	      (* [q] contains [p]. Merge [t] with a subtree of [s]. *)
	      if zero_bit q m 
	      then Branch(p, m, merge s0 t, s1)
              else Branch(p, m, s0, merge s1 t)
	    else 
	      if m > n && match_prefix p q n 
	      then
		(* [p] contains [q]. Merge [s] with a subtree of [t]. *)
		if zero_bit p n 
		then Branch(q, n, merge s t0, t1)
		else Branch(q, n, t0, merge s t1)
	      else
		(* The prefixes disagree. *)
		join p s q t
		  
  let union s t = merge s t

  let rec subset s1 s2 = 
    match (s1,s2) with
      | Empty, _ -> true
      | _, Empty -> false
      | Leaf k1, _ -> mem k1 s2
      | Branch _, Leaf _ -> false
      | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
	  if m1 = m2 
	  then
	    p1 = p2 && subset l1 l2 && subset r1 r2
	  else 
	    if m1 > m2 
	    then
	      (match_prefix p1 p2 m2) && 
	      (if zero_bit p1 m2 then subset l1 l2 && subset r1 l2
	       else subset l1 r2 && subset r1 r2)
	    else
	      false

  let rec inter s1 s2 = 
    match (s1,s2) with
      | Empty, _ -> Empty
      | _, Empty -> Empty
      | Leaf k1, _ -> if mem k1 s2 then s1 else Empty
      | _, Leaf k2 -> if mem k2 s1 then s2 else Empty
      | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
	  if m1 = m2 
	  then
	    if p1 = p2 
	    then merge (inter l1 l2) (inter r1 r2) 
	    else Empty
	  else 
	    if m1 < m2 
	    then
	      if match_prefix p2 p1 m1 
	      then inter (if zero_bit p2 m1 then l1 else r1) s2
	      else Empty
	    else 
	      if match_prefix p1 p2 m2 
	      then inter s1 (if zero_bit p1 m2 then l2 else r2)
	      else Empty

  let rec diff s1 s2 = 
    match (s1,s2) with
      | Empty, _ -> Empty
      | _, Empty -> s1
      | Leaf k1, _ -> if mem k1 s2 then Empty else s1
      | _, Leaf k2 -> remove k2 s1
      | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
	  if m1 = m2 
	  then
	    if p1 = p2 
	    then merge (diff l1 l2) (diff r1 r2) 
	    else s1
	  else 
	    if m1 < m2 
	    then
	      if match_prefix p2 p1 m1 
	      then
		if zero_bit p2 m1 
		then merge (diff l1 s2) r1 
		else merge l1 (diff r1 s2)
	      else
		s1
	    else 
	      if match_prefix p1 p2 m2 
	      then
		if zero_bit p1 m2 then diff s1 l2 else diff s1 r2
	      else
		s1

  let rec cardinal = function
    | Empty -> 0
    | Leaf _ -> 1
    | Branch (_,_,t0,t1) -> cardinal t0 + cardinal t1

  let rec iter f = function
    | Empty -> ()
    | Leaf k -> f k
    | Branch (_,_,t0,t1) -> iter f t0; iter f t1
      
  let rec fold f s accu = 
    match s with
      | Empty -> accu
      | Leaf k -> f k accu
      | Branch (_,_,t0,t1) -> fold f t0 (fold f t1 accu)

  let rec for_all p = function
    | Empty -> true
    | Leaf k -> p k
    | Branch (_,_,t0,t1) -> for_all p t0 && for_all p t1

  let rec exists p = function
    | Empty -> false
    | Leaf k -> p k
    | Branch (_,_,t0,t1) -> exists p t0 || exists p t1

  let filter p s = 
    let rec filt acc = function
      | Empty -> acc
      | Leaf k -> if p k then add k acc else acc
      | Branch (_,_,t0,t1) -> filt (filt acc t0) t1
    in
    filt Empty s
      
  let partition p s =
    let rec part (t,f as acc) = function
      | Empty -> acc
      | Leaf k -> if p k then (add k t, f) else (t, add k f)
      | Branch (_,_,t0,t1) -> part (part acc t0) t1
    in
    part (Empty, Empty) s
      
  let rec choose = function
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_, _,t0,_) -> choose t0

  let elements s =
    let rec elements_aux acc = function
      | Empty -> acc
      | Leaf k -> k :: acc
      | Branch (_,_,l,r) -> elements_aux (elements_aux acc l) r
    in
    elements_aux [] s
      
  let equal = (=)
		
  let compare = compare

(*i
  let cases s a f = 
    match s with
      | Empty -> a ()
      | _ ->
	  let t = choose s in
	  let r = remove t s in
	  f t r
i*)
end


module Make(O : sig type t val tag : t -> int end) =
  MakePoly(struct type 'a t = O.t let tag = O.tag end)

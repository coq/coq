(***************************************************************************

This module allows to define orderings on finite sets.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Orderings_generalities

exception Incompatible

module type Finite_ordering =
sig
  type elt
  type t
  val identity_ordering : t
  val compare : t -> elt Orderings_generalities.ordering
  val add_equiv : t -> elt -> elt -> t
  val add_greater : t -> elt -> elt -> t
end

module Make(M : Map.OrderedType) = struct

  type elt = M.t

  module MapM = Map.Make(M)
  
  type t = (comparison_result MapM.t) MapM.t

let get t x y =
  if M.compare x y = 0
  then Equivalent
  else
    try
      let m = MapM.find x t in
      MapM.find y m
    with Not_found -> Uncomparable

let set t x y v =
  let m = 
    try
      MapM.find x t 
    with Not_found -> MapM.empty
  in 
  let m = MapM.add y v m in
  MapM.add x m t

let compare = get

let add_equiv t x y =
      match get t x y with
	  Uncomparable ->
	    let t = set t x y Equivalent in
	    let t = set t y x Equivalent in
	    let t =
	      MapM.fold
		(fun x1 m t ->
		   MapM.fold
		     (fun y1 v t -> 
			let c1 = get t x1 x
			and c2 = get t y y1
			in
			if c1 = Equivalent & c2 = Equivalent
			then
			  match get t x1 y1 with
			      Uncomparable ->
				let t = set t x1 y1 Equivalent in
				set t y1 x1 Equivalent
			    | Equivalent -> t
			    | _ -> raise Incompatible
			else 
			  if is_greater_or_equal c1 & is_greater_or_equal c2
			  then 
			    if is_less_or_equal (get t x1 y1)
			    then raise Incompatible
			    else
			      let t = set t x1 y1 Greater_than in
			      set t y1 x1 Less_than
			  else 
			    if is_less_or_equal c1 & is_less_or_equal c2
			    then 
			      if is_greater_or_equal (get t x1 y1)
			      then raise Incompatible
			      else
				let t = set t x1 y1 Less_than in
				set t y1 x1 Greater_than
			    else t)
		     t
		     t)
		t
		t
	    in
	    t
	| Equivalent -> t
	| _ -> raise Incompatible

let add_greater t x y =
      if is_less_or_equal (get t x y)
      then
	raise Incompatible
     else
	let t = set t x y Greater_than in
	let t = set t y x Less_than in
	let t =
	  MapM.fold
	    (fun x1 m t ->
	       MapM.fold
		 (fun y1 v t -> 
		    if is_greater_or_equal (get t x1 x) 
		      & is_greater_or_equal (get t y y1) 
		    then
		      if is_less_or_equal (get t x1 y1)
		      then raise Incompatible
		      else
			let t = set t x1 y1 Greater_than in
			set t y1 x1 Less_than
		    else t)
		 t
		 t)
	    t
	    t
      in
      t

let identity_ordering = MapM.empty

type 'a precedence =
    One of 'a
  | Gt of 'a * 'a precedence
  | Lt of 'a * 'a precedence
  | Eq of 'a * 'a precedence

let first p = 
  match p with
      One(x) -> x
    | Gt(x,_) -> x
    | Lt(x,_) -> x
    | Eq(x,_) -> x

let rec add_list order prec = 
  match prec with
      Gt(x,y) -> 
	add_greater order x (first y);
	add_list order y
    | Lt(x,y) -> 
	add_greater order (first y) x;
	add_list order y
    | Eq(x,y) -> 
	add_equiv order x (first y);
	add_list order y
    | _ -> ()

let rec map_prec f p =
  match p with
    | One(x) -> One(f x)
    | Gt(x,l) -> Gt(f x,map_prec f l)
    | Lt(x,l) -> Lt(f x,map_prec f l)
    | Eq(x,l) -> Eq(f x,map_prec f l)

end

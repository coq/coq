(***************************************************************************

This module provides functions to compute superpositions and unification 
over a string rewriting system.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(*

Obsolete header:

$Id: 

***************************************************************************)



(* Computes the solutions of [l1 w1 = w2 l2] with [w1] and [w2] not empty 
and returns (r1 w1),(r2 w2) *)

exception Not_a_strict_prefix

let superpose (l1,r1) (l2,r2) =
  let rec is_strict_prefix a b = 
    match a,b with
      | (a1::ar),(b1::br) -> 
	  if (a1=b1) then 
	    (is_strict_prefix ar br) 
	  else raise Not_a_strict_prefix
      | [],[] -> raise Not_a_strict_prefix
      | [],(_::_ as br) -> br
      | _::_,[] -> raise Not_a_strict_prefix
  in
  let rec superpose_rec acc_l l  = 
    match l with 
	[] -> []
      | (x::s) -> 
	  let next_superposition = superpose_rec (x::acc_l) s in
	    try 
	      let w2 = is_strict_prefix l l2 in
	      let w1 = List.rev acc_l in
		(r1@w2,w1@r2)::next_superposition
	    with 
		Not_a_strict_prefix -> next_superposition
  in
      match l1,l2 with 
	  [],_ -> []
	| _,[] -> []
	| _ -> superpose_rec [] l1


(* Idem superpose but returns [w1,w2] *)
let superpose_internal l1 l2 =
  let rec is_strict_prefix a b = 
    match a,b with
      | (a1::ar),(b1::br) -> 
	  if (a1=b1) then 
	    (is_strict_prefix ar br) 
	  else raise Not_a_strict_prefix
      | [],[] -> raise Not_a_strict_prefix
      | [],(_::_ as br) -> br
      | _::_,[] -> raise Not_a_strict_prefix
  in
  let rec superpose_rec acc_l l  = 
    match l with 
	[] -> []
      | (x::s) -> 
	  let next_superposition = superpose_rec (x::acc_l) s in
	    try 
	      let w2 = is_strict_prefix l l2 in
	      let w1 = List.rev acc_l in
		(w2,w1)::next_superposition
	    with 
		Not_a_strict_prefix -> next_superposition
  in
      match l1,l2 with 
	  [],_ -> []
	| _,[] -> []
	| _ -> superpose_rec [] l1


exception Not_a_prefix

(* if $\exists$ x <> epsilon tq w1 x = w2 or w1 = w2 x returns [x] *)
let rec is_prefix w1 w2 = 
  match w1,w2 with
    | a1::r1,a2::r2 -> 
	if a1 = a2 then is_prefix r1 r2 else raise Not_a_prefix
    | [],[] -> []
    | [] , l -> l (* suffix for w1 *)
    | l,[] -> raise Not_a_prefix (* ([],l) suffix for w2 *)


let unify u v =
  let  superposition_unif_1 u v = 
	  (List.map 
	     (function w1,w2-> ([],w1),(w2,[])) 
	     (superpose_internal u v))
  in
  let  superposition_unif_2 u v = 
	  (List.map 
	     (function w1,w2-> (w2,[]),([],w1)) 
	     (superpose_internal u v))
  in
  let rec embed u v = match v with
    | [] -> if u = [] then [[],[]] else []
    | x::r -> 
	try 
	  ([],(is_prefix u v ))::
	  (List.map (function a,b -> x::a,b) (embed u r))
	with 
	    Not_a_prefix -> List.map (function a,b -> x::a,b) (embed u r)
			    
  in (superposition_unif_1 u v)@(superposition_unif_2 v u)@
     (List.map (function ps -> ps,([],[])) (embed u v))@
      List.map (function ps -> ([],[]),ps) (embed v u)


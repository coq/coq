(***************************************************************************

Innermost strategies

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Gen_terms;;
open Substitution;;
open Variables;;


(*


Attempt of a more efficient innermost normalization

we use an auxiliary function 

[substitute_and_innermost_normalize : 
  (term -> term * substitution) -> substitution -> term ]

[(substitute_and_innermost_normalize red sigma t)] returns the
innermost normal form of [(t sigma)] for the reduction relation [red]
where we assume that [sigma] is already in normal form

for a term [t], [(red t)] must return a pair [(u,tau)] such that [t]
rewrites to [(u tau)] at root, or raise [Irreducible] if [t] is in
normal form

*)

exception Unnormalized;;

let decrease_bound b =
  if !b >= 0 then decr b;
  if !b = 0 then raise Unnormalized
;;

let rec substitute_and_innermost_normalize sign bound red sigma t = 

  let rec normalize_at_top f t =
    let (t'',sigma') = red t in
    decrease_bound bound;
    let sigma'' = 
      Variables.VarMap.map
	(fun t ->
	   try
	     if Gen_terms.root_symbol t = f 
	     then normalize_at_top f t
	     else t
	   with Not_found -> t)
	sigma' 
    in
    substitute_and_innermost_normalize sign bound red sigma'' t''
  in
  match t with
    | (Var x) as v -> 
	begin
	  try 
	    VarMap.find x sigma	            	
      	  with Not_found -> v
	end
    | Term (f,l) -> 
	let l'= 
	  List.map 
	    (substitute_and_innermost_normalize sign bound red sigma) l 
	in
	let t' = head_flatten sign f l'
	in
	try 
	  normalize_at_top f t'
	with Not_found -> t'
;;




(*

  [(innermost_normalize red t)] returns the innermost normal
form of [t] w.r.t to the reduction relation [red].

  [red] is a function which, given a term [t], returns a pair
  [(u,sigma)] such that [t] rewrites to [u sigma], or raises
  [Irreducible] if [t] is irreducible.

  The substitution will be applied during the normalization process.

*)


let innermost_normalize sign red t = 
  substitute_and_innermost_normalize sign (ref 0) red VarMap.empty t
;;

exception Irreducible;;

let force_innermost_normalize sign red t = 
  let x = ref 0 in
  let t = substitute_and_innermost_normalize sign x red VarMap.empty t in
  if !x = 0 then raise Irreducible else t
;;

 

(* [safe_innermost_normalize n red t] does the same but where [n] is a
bound for the number of rewrite steps to apply. If this bound is
reached, then this function raises the exception [Unnormalized u]
where [u] is the reduct of [t] obtained so far *)

let safe_innermost_normalize sign b red t = 
  substitute_and_innermost_normalize sign (ref b) red VarMap.empty t
;;

let safe_force_innermost_normalize sign b red t = 
  let x = ref b in
  let t = substitute_and_innermost_normalize sign x red VarMap.empty t in
  if !x = b then raise Irreducible else t
;;





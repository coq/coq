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

let rec substitute_and_innermost_normalize sign vars bound red sigma t = 
  let _ = 
    begin
      Format.printf "DEBUT normalisation de ";
      Gen_terms.print_term sign vars t;
      Format.printf "\n"
    end in
    match t with

    	(Var x) as v -> 
	  begin
	    try 
	      VarMap.find x sigma	            	
      	    with Not_found -> v
	  end
	  
      | Term (f,l) -> 
	  let l'= 
	    List.map (substitute_and_innermost_normalize sign vars bound red sigma) l 
	  in
	  let t' = Term(f,l') 
	  in
	    try 
	      let (t'',sigma') = red t' in
          	decrease_bound bound;
		substitute_and_innermost_normalize sign vars bound red sigma' t''

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


let innermost_normalize sign vars red t = 
  substitute_and_innermost_normalize sign vars (ref 0) red VarMap.empty t
;;

exception Irreducible;;

let force_innermost_normalize sign vars red t = 
  let x = ref 0 in
  let s = substitute_and_innermost_normalize sign vars x red VarMap.empty t in
  if !x = 0 then raise Irreducible else s
;;

 

(* [safe_innermost_normalize n red t] does the same but where [n] is a
bound for the number of rewrite steps to apply. If this bound is
reached, then this function raises the exception [Unnormalized u]
where [u] is the reduct of [t] obtained so far *)

let safe_innermost_normalize sign vars b red t = 
  substitute_and_innermost_normalize sign vars (ref b) red VarMap.empty t
;;

let safe_force_innermost_normalize sign vars b red t = 
  let x = ref b in
  let t = substitute_and_innermost_normalize sign vars x red VarMap.empty t in
  if !x = b then raise Irreducible else t
;;





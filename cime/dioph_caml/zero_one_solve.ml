(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Comparaison
open Orderings_generalities

let scalar_product l v1 v2 =
  let r = ref 0 in
  let _ = 
    for i = 0 to l do
      r := !r + (v1.(i) * v2.(i))
    done in
    !r

let is_a_solution_for_the_line (a,b) l v =
  let av = scalar_product l a v
  and bv = scalar_product l b v in
    ((av = 0) & (bv = 0)) or ((av > 0) & (bv > 0))

let is_a_solution system l v =
  try
    let _ = 
      Array.iter 
	(function eq -> 
	   if not(is_a_solution_for_the_line eq l v)
	   then raise Exit)
	system in
      true
  with Exit -> false

exception No_zero
exception Found of int

let index_of_first_zero l v =
  try
    for i = 0 to l do
      if v.(i) = 0
      then raise (Found i)
    done;
    raise No_zero
  with Found i -> i

let computes_next_vector l v =
  let z = index_of_first_zero l v in
    for i = 0 to pred z do
      v.(i) <- 0
    done;
    v.(z) <- 1
 

let is_sum n v1 v2 s =
  try
    let _ =
      for i = 0 to n do
	let v1_plus_v2_i = v1.(i) + v2.(i) in
	  if (v1_plus_v2_i = 0 & s.(i) > 0) or
	    (v1_plus_v2_i > 0 & s.(i) = 0)
	  then raise Exit
      done in
      true
  with Exit -> false

let rec add_solution n system sol = function
      [] -> [sol]
  | s::l as ll ->
      match comparaison sol s with
	  Greater_than -> 
	    begin
	      let d = Array.create (succ n) 0 in
		try
		  let _ = 
		    while true do
		      computes_next_vector n d;
		      if is_sum n d s sol
		      then 
			if (is_a_solution system n d) & (d <> sol)
			then raise Exit
		    done in
		    []
		with 
		    No_zero -> s::(add_solution n system sol l)
		  | Exit -> ll
	    end
	| Less_than ->
	    begin
	      let d = Array.create (succ n) 0 in
		try
		  let _ = 
		    while true do
		      computes_next_vector n d;
		      if is_sum n d sol s
		      then 
			if (is_a_solution system n d) & (d <> s)
			then raise Exit
		    done in
		    []
		with 
		    No_zero -> s::(add_solution n system sol l)
		  | Exit -> add_solution n system sol l
	    end
	| Equivalent -> ll
	| _ -> s::(add_solution n system sol l)

let solve system =
  let n = pred (Array.length (fst system.(0))) in
  let current_vector = Array.make (succ n) 0 
  and current_solutions = ref [] in
    try
      while true do
	computes_next_vector n current_vector;
	if is_a_solution system n current_vector
	then 
	  let sol = Array.copy current_vector in
	    current_solutions := add_solution n system sol !current_solutions
      done;
      [||]
    with No_zero -> Array.of_list !current_solutions


	



(***************************************************************************

  This module provides some functions in order to translate back a
  solved arithmetic problem into a solved unification problem modulo
  an AC-like theory.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Bit_field
open Hullot_bin_trees
open Variables
open Gen_terms
open Theory
open Problems
open Controle

(*

  Computation of the interesting subsets of the set of Diophantine
  solutions. First case : less than 32 solutions.

*)

(*

  [pcache v], where [v] is a bi-dimensional matrix of integers,
  returns a vector of integers which encode vectors of bits, such that
  each 1 corresponds to a non-zero integer of the transposed entry,
  each 0 to a 0, in order to access directly to the column associated
  with a variable.

*)

let pcache v = 
  let nb_sol = Array.length v 
  and nb_var = Array.length v.(0) in
  let cache = Array.create nb_var 0 in
    for i=0 to (pred nb_var) do
      for j=0 to (pred nb_sol) do
        if v.(j).(i) > 0
        then cache.(i) <- cache.(i) + (1 lsl j)
      done
    done;
    cache

(* 

  [(psmall_enough from_var to_var vect_sols_cache node)] checks
  whether the subset of Diophantine solutions encoded by [node] is
  small enough, that is does not instanciate the variables whose index
  is between [from_var] and [to_var] (by another term than a
  variable).

*)

let psmall_enough from_var to_var vect_sols_cache node = 
  try 
    for i= from_var to (pred to_var) do
      let p = node land vect_sols_cache.(i) in
        if (p land (pred p)) <> 0
        then raise Exit (* not small enough for the ith constant *)
    done;
    true
  with Exit -> false


(*
  
  [(pgreat_enough from_var to_var nb_digit vect_sols_cache node)]
  whether the subset of Diophantine solutions encoded by [node] is
  great enough, that is does not instanciate the variables whose index
  is between [from_var] and [to_var] by the zero of the theory.

*)

let pgreat_enough from_var to_var vect_sols_cache node = 
  try
    for i = from_var to (pred to_var) do
      let p = node land vect_sols_cache.(i) in
        if p = 0
        then raise Exit (* not great enough for the ith variable or constant *)
    done;
    true
  with Exit -> false 


(*

  Computation of the interesting subsets of the set of Diophantine
  solutions. Second case : more than 32 solutions.

*)

(*
  
  [gcache] is the same as [pcache] except that it returns a vector of
  bit_fields.

*)

let gcache v = 
  let nb_sol = Array.length v 
  and nb_var = Array.length v.(0) in
  let res = Array.create nb_var (Large_bit_field.all_zero nb_sol) 
  and c = Array.create nb_sol 0 in
    for i = 0 to pred nb_var do
      for j=0 to pred nb_sol do
        if v.(j).(i) > 0
        then c.(j) <- 1
        else c.(j) <- 0
      done;
      res.(i) <- Large_bit_field.vect_of_bits_to_bit_field c
    done;
    res

(*

 [gsmall_enough] is the same as [psmall_enough] except that it last
  argument is a vector of bit_fields and not a vector of integers.

*)

let gsmall_enough from_var to_var vect_sols_cache node = 
  try 
    for i = from_var to pred to_var do
      let p = Large_bit_field.bit_and node vect_sols_cache.(i) in
        if not (Large_bit_field.atmost_one_one p)
        then raise Exit (* not small enough for the ith constant *)
    done;
    true
  with Exit -> false


(*

 [ggreat_enough] is the same as [pgreat_enough] except that it last
  argument is a vector of bit_fields and not a vector of integers.

*)

let ggreat_enough from_var to_var vect_sols_cache node = 
  try 
    for i = from_var to (pred to_var) do
      let p = Large_bit_field.bit_and node vect_sols_cache.(i) in
        if Large_bit_field.is_zero p
        then raise Exit (* not great enough for the ith variable or constant *)
    done;
    true
  with Exit -> false 


(*

  Buildind the solutions over the terms.

*)

let rec cons_n n x l =
  if n <= 0
  then l
  else cons_n (pred n) x (x::l)

let linear_combination unif_k th non_zero_vars map_var_int vect_sols 
  vect_new_var char_vect =

  let plus = additive_symbol_of_theory th
  and nb_sols = Array.length vect_sols in
  let nb_occ_new_var = Array.create nb_sols None in

  let build_value_of_var ix x =
    let _ =
      for i = 0 to pred nb_sols do
	nb_occ_new_var.(i) <- 
	if char_vect.(i) = 0 
	then None 
	else Some (vect_sols.(i).(ix),vect_new_var.(i))
      done in

    let list_of_args =
      Array.fold_left
	(fun partial_list_of_args nb_occ_new_vari ->
	   match nb_occ_new_vari with
	       None -> partial_list_of_args
	     | Some (n,var) ->
		 if n>=0
		 then cons_n n var partial_list_of_args
		 else
		   let minus = minus_symbol_of_theory th in
		   let minus_var = Term (minus,[var]) in
		     cons_n (abs n) minus_var partial_list_of_args)
	[] nb_occ_new_var in

      match List.length list_of_args with 
	  0 -> 
	    begin
	      match unif_k with
		  PLAIN -> Term (unit_symbol_of_theory th,[])
		| _ ->
		    if VarSet.mem x non_zero_vars
		    then raise No_solution
		    else Term (unit_symbol_of_theory th,[])
	    end
	|  1 -> List.hd list_of_args 
	|  _ -> Term (plus,list_of_args) in
    
    VarMap.fold
      (fun x ix partial_list_of_eqs ->
	 let value_of_x = build_value_of_var ix x in
	   (Var x, value_of_x) :: partial_list_of_eqs)
      map_var_int []
      
  

(*

  [(sum_of_columns matrix) returns an array containing the sum of 
  the columns of the argument [matrix].

*)

let sum_of_columns matrix =
  let nb_lines = Array.length matrix
  and nb_columns = Array.length matrix.(0) in
  let sum = Array.create nb_columns 0 in
    for i = 0 to pred nb_lines do
      for j = 0 to pred nb_columns do
	sum.(j) <- sum.(j) + matrix.(i).(j)
      done
    done;
    sum

(*

  [(associated_var_with_sol sum_of_sols map_var_int v_type sol)] returns
  \begin{itemize}
  \item [Some c] when the value of the solution [sol] is equal to 1
  for the component corresponding to the marked variable [c] (when
  there are several such marked variables, the function returns the
  first one encountered).
  \item [Some x] when the value of the solution [sol] is equal to 1
  for the component corresponding to the variable [x], and there is no
  other such variable.
  \item [None] otherwise.
  \end{itemize}

*)

exception Found of int

let associated_var_with_sol sum_of_sols array_of_vars v_type sol = 
  try 
    for i = v_type.(0) to (pred (Array.length sol)) do
      if sol.(i) = 1
      then raise (Found i)
    done;
    for i = 0 to pred v_type.(0) do
      if ((sol.(i) = 1) && (sum_of_sols.(i) = 1)) 
      then raise (Found i)
    done;
    None
  with Found i -> 
    let var_of_index_i = array_of_vars.(i) in
      Some var_of_index_i


(*

  [(associated_marked_var_with_sol sum_of_sols map_var_int v_type sol)] 
  returns
  \begin{itemize}
  \item [Some c] when the value of the solution [sol] is equal to 1
  for the component corresponding to the marked variable [c] (when
  there are several such marked variables, the function returns the
  first one encountered).
  \item [None] otherwise.
  \end{itemize}

*)

let associated_marked_var_with_sol array_of_vars v_type sol = 
  try 
    for i = v_type.(0) to (pred (Array.length sol)) do
      if sol.(i) = 1
      then raise (Found i)
    done;
    None
  with Found i -> 
    let var_of_index_i = array_of_vars.(i) in
      Some var_of_index_i

	
(*

  [(builds_a_cycle elem_pb vect_var sol)] checks whether the solution [sol]
  makes a cycle of size 2, thanks to [elem_pb.edges].

*)

let builds_a_cycle elem_pb map_var_int sol = 
  List.exists 
    (function (x,y) -> 
       try 
	 ((sol.(VarMap.find x map_var_int) = 1) && 
          (sol.(VarMap.find y map_var_int) = 1))
       with Not_found -> false)
    elem_pb.edges

    
(* 

   [(clean_solutions elem_pb map_var_int vect_sols)] cleans the set of
   Diophantine solutions, removing those which create a cycle of size 2.

*)

let clean_solutions elem_pb map_var_int vect_sols = 
  Array.of_list
    (Arrayutils.filter
       (function sol -> not (builds_a_cycle elem_pb map_var_int sol))
       vect_sols)


(*
  classer_elem pe_edge vect_var vect_cst (v0,v1) sol range la 
  solution sol dans (v0,v1) ou 
  v0 contient les solutions qui valent 0 sur toutes les constantes 
  v1 les solutions qui valent 1 sur au moins une constante. 
*)

let classify_a_sol elem_pb array_of_vars map_var_int v_type (v0,v1 as v) sol = 
  match associated_marked_var_with_sol array_of_vars v_type sol with
      None -> Array.append v0 [|sol|], v1
    | _ -> 
	if builds_a_cycle elem_pb map_var_int sol
	then v
	else v0, Array.append v1 [|sol|]
	  
(*

  [(classify elem_pb map_var_int v_type vect_sols)] returns a pair
  [(vect_homogeneous_sols,vect_heterogeneous_sols)] where
  \begin{itemize} 
  \item [vect_homogeneous_sols] contains the solutions from the array
  [vect_sols] which are equal to 0 over the marked variables,
  \item [vect_heterogeneous_sols] contains the other solutions of
  [vect_sols]
  \end{itemize} 

  Remark : The solutions of [vect_sols] creating a cycle of size 2 are
  removed in [sorted_vect_sols].

*)

let classify elem_pb array_of_vars map_var_int v_type vect_sols =
  Array.fold_left 
    (classify_a_sol elem_pb array_of_vars map_var_int v_type) 
    ([||],[||]) vect_sols 

(*
(*
  rearranger v0v1 reconstruit un vecteur de vecteurs
  solutions, ou les vecteurs-solutions qui valent 0 sur toutes 
  les composantes correspondant a des variables instanciees sont 
  en tete
*)
let rearranger (v0,v1) = Array.append v0 v1

*)


let generate_vect_char_cst nb_var nb_true_var vect_sols_cst =
  let nb_sols_cst = Array.length vect_sols_cst in
    if nb_sols_cst = 0
    then []
    else 
      if nb_sols_cst < 32
      then 
	begin
	  let cache_vect_sols_cst = pcache vect_sols_cst in
	  let test_ag = pgreat_enough nb_true_var nb_var cache_vect_sols_cst
	  and test_ap = 
	    psmall_enough nb_true_var nb_var cache_vect_sols_cst in
	  List.rev_map 
	    (Small_bit_field.bit_field_to_vect_of_bits nb_sols_cst)
            (Small_binary_tree.arbre_binaire nb_sols_cst test_ag test_ap)
	end
      else 
	begin
	  let cache_vect_sols_cst = gcache vect_sols_cst in
	  let test_ag = ggreat_enough nb_true_var nb_var cache_vect_sols_cst
	  and test_ap = 
	    gsmall_enough nb_true_var nb_var cache_vect_sols_cst in 
	    List.rev_map 
	      (Large_bit_field.bit_field_to_vect_of_bits nb_sols_cst)
              (Large_binary_tree.arbre_binaire nb_sols_cst test_ag test_ap)
	end
	




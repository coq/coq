(***************************************************************************

  This module provides a function for solving an elementary
  unification problem modulo an associative and commutative
  symbol. This function should only be called on a problem which is
  quasi-solved, that is all the equations are of the form 
  [variable = term] and the {\bf Merge} rule can apply.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(*

Obsolete header:

  Remark : the general solver for an elementary unification problem
  modulo ACU is provided in the module [Unif_acu] by the function
  [solve].

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Orderings_generalities
open Variables
open Gen_terms
open Theory
open Problems
open Unif_to_arith
open Arith_to_unif

module IntSet = 
  Set.Make
    (struct 
       type t = int
       let compare = (-)
     end)
       
let compare_projected_sols map_var_int sol1 sol2 =
  try
    VarMap.fold
      (fun x i cmp ->
	 if sol1.(i) = sol2.(i)
	 then cmp
	 else 
	   if sol1.(i) < sol2.(i)
	   then 
	     begin
	       match cmp with 
		   Equivalent
		 | Less_than
		 | Less_or_equivalent -> Less_than
		 | _ -> raise Exit
	     end
	   else 
	     begin
	       match cmp with
		   Equivalent
		 | Greater_than
		 | Greater_or_equivalent -> Greater_than
		 | _ -> raise Exit
	     end)
      map_var_int Equivalent
  with 
      Exit -> Uncomparable

let is_min cmp i vect =
  let vi = vect.(i) in
    try
      let _ = 
	Array.iteri
	  (fun j vj ->
	     if i <> j
	     then 
	       begin
		 match cmp vi vj with
		     Greater_than
		   | Greater_or_equivalent -> raise Exit
		   | Equivalent -> 
		       if i > j
		       then raise Exit
		   | _ -> ()
	       end)
	  vect in
	true
    with
	Exit -> false

let is_equivalent cmp v vect =
  try
    let _ = 
      Array.iter
	(function v' ->
	   match cmp v v' with
	       Equivalent -> raise Exit
	     | _ -> ())
	vect in
      false
  with Exit -> true


let select_min_sols_h map_var_int vect_sols_h =
  Arrayutils.fold_lefti
    (fun partial_min_sols_h i sol ->
       if is_min (compare_projected_sols map_var_int) i vect_sols_h 
       then Array.append [|sol|] partial_min_sols_h
       else partial_min_sols_h)
    [||] vect_sols_h

let select_min_sols_cst map_var_int vect_sols_h vect_sols_cst = 
  Array.fold_left
    (fun partial_min_sols_cst sol ->
       if is_equivalent (compare_projected_sols map_var_int) sol vect_sols_h 
       then partial_min_sols_cst
       else Array.append partial_min_sols_cst [|sol|])
    [||] vect_sols_cst

let solve unif_k first_variables elem_pb =
  let (map_var_int,array_of_vars,v_type,matrix) = unif_to_arith elem_pb in
    if (Array.length matrix) = 0
    then [[]]
    else 
      let nb_var = v_type.(pred (Array.length v_type))
      and nb_true_var = v_type.(0) in
      let unsorted_vect_sols = 
	begin
	  let vect_non_zero_sols = 
	    clean_solutions elem_pb map_var_int
              (Solve.dioph_solve v_type matrix) in
            if ((Array.length vect_non_zero_sols) = 0 & (unif_k = PLAIN))
            then [|Array.create nb_var 0|]
            else vect_non_zero_sols
	end in
      let nb_sols = Array.length unsorted_vect_sols in
        if nb_sols = 0
        then []
	else (* projection over the variables occurring at the beginning *)
	  let map_var_int' =
	    VarMap.fold
	      (fun x i partial_map ->
		 if VarSet.mem x first_variables
		 then VarMap.add x i partial_map
		 else partial_map)
	      map_var_int VarMap.empty in
	  let _ =
	    let indices_to_keep =
	      VarMap.fold
		(fun _ i partial_indices -> IntSet.add i partial_indices)
		map_var_int' IntSet.empty in
	      Array.iter
		(function sol ->
		   for i = 0 to pred nb_var do
		     if not (IntSet.mem i indices_to_keep)
		     then sol.(i) <- 0
		   done)
		unsorted_vect_sols in
	    
	  let vect_sols_h, vect_sols_cst = 
	    classify elem_pb array_of_vars map_var_int 
	      v_type unsorted_vect_sols in
	  let vect_sols_h' = select_min_sols_h map_var_int' vect_sols_h
	  and vect_sols_cst' = 
	    select_min_sols_cst map_var_int' vect_sols_h vect_sols_cst in


	  let vect_sols' = Array.append vect_sols_h' vect_sols_cst' in
	  let sum_of_sols' = sum_of_columns vect_sols' in
          let vect_new_var = 
	    Array.map 
              (function sol -> 
		 let ass_var_sol = 
		   associated_var_with_sol 
		     sum_of_sols' array_of_vars v_type sol in
		   match ass_var_sol with
		       Some var -> Var var
		     | None -> Var (fresh_var_for_unif ()))
              vect_sols' in 
	  let map_var_non_unit_int = 
	    Unif_acu.filter_non_unit_vars first_variables nb_true_var 
	      map_var_int' in
          let list_vect_char = 
	    Unif_acu.generate_vect_char unif_k nb_var nb_true_var 
	      map_var_non_unit_int vect_sols_h' vect_sols_cst' in
            List.map 
	      (linear_combination unif_k elem_pb.elem_th first_variables
		 map_var_int' vect_sols' vect_new_var) 
	      list_vect_char






(***************************************************************************

  Unification modulo an associative and commutative symbol with a unit.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Bit_field
open Variables
open Gen_terms
open Theory
open Problems
open Unif_to_arith
open Arith_to_unif

(*===================================================================

         L'unification AC et l'unification AC1 ne doivent etre
         appelees que sur des problemes purs, certaines variables
         pouvant etre instanciees par ailleurs dans d'autres 
         theories et jouant de ce fait un role similaire a 
         des constantes. Si le probleme de depart n'est pas 
         pur, on aura un echec. 

===================================================================*)


(*===================================================================

                       Unification ACU

====================================================================*)

let great_enough_var map_var_non_unit_int vect_sols_cache node =
  try
    let _ = 
      VarMap.iter 
	(fun _ i ->
	   let p = Large_bit_field.bit_and node vect_sols_cache.(i) in
	     if Large_bit_field.is_zero p
             then raise Exit 
	       (* not great enough for the ith variable or constant *)
	)
	map_var_non_unit_int in
      true
  with Exit -> false


(*
 engendrer_vect_car v0v1 vect_var vect_cst engendre 
 la liste des vecteurs caracterisques de presence des solutions 
 qui sont pertinents pour l'unification AC1
*)

let generate_vect_char unif_k nb_var nb_true_var map_var_non_unit_int 
  vect_sols_h vect_sols_cst =
 
  let all_1 = Array.create (Array.length vect_sols_h) 1 in
  let vect_char_cst =
    if Array.length vect_sols_cst = 0
    then 
      if nb_true_var = nb_var
      then [[||]]
      else []
    else generate_vect_char_cst nb_var nb_true_var vect_sols_cst in
   
    if unif_k = PLAIN
    then 
      List.map 
	(function v -> Array.append all_1 v) 
	vect_char_cst
    else
      let vect_sols_cache = 
	gcache (Array.append vect_sols_h vect_sols_cst) in
      let test_ag_var = 
	great_enough_var map_var_non_unit_int vect_sols_cache in
	List.fold_left
	  (fun partial_vect_char v ->
	     let v' = Array.append all_1 v in
	       if test_ag_var (Large_bit_field.vect_of_bits_to_bit_field v')
	       then v' :: partial_vect_char
	       else partial_vect_char)
	  [] vect_char_cst
	  


let filter_non_unit_vars non_unit_vars n map_var_int = 
  VarMap.fold
    (fun x i partial_map -> 
       if (i < n) & (VarSet.mem x non_unit_vars)
       then VarMap.add x i partial_map
       else partial_map)
    map_var_int
    VarMap.empty

let solve unif_k non_unit_variables elem_pb =
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
	else 
	  let vect_sols_h, vect_sols_cst = 
	    classify elem_pb array_of_vars map_var_int 
	      v_type unsorted_vect_sols in
	  let vect_sols = Array.append vect_sols_h vect_sols_cst in
	  let sum_of_sols = sum_of_columns vect_sols in
          let vect_new_var = 
	    Array.map 
              (function sol -> 
		 let ass_var_sol = 
		   associated_var_with_sol 
		     sum_of_sols array_of_vars v_type sol in
		   match ass_var_sol with
		       Some var -> Var var
		     | None -> Var (fresh_var_for_unif ()))
              vect_sols in 
	  let map_var_non_unit_int = 
	    filter_non_unit_vars non_unit_variables nb_true_var map_var_int in
          let list_vect_char = 
	    generate_vect_char unif_k nb_var nb_true_var map_var_non_unit_int 
	      vect_sols_h vect_sols_cst in
            List.map 
	      (linear_combination unif_k elem_pb.elem_th non_unit_variables 
		 map_var_int vect_sols vect_new_var) 
	      list_vect_char



let exists_vect_char nb_var nb_true_var map_var_non_unit_int 
  vect_sols_h vect_sols_cst = 
  let nb_sols_cst = Array.length vect_sols_cst 
  and nb_sols_h = Array.length vect_sols_h in
  let vect_sols_cache = gcache (Array.append vect_sols_h vect_sols_cst) in
  let test_ag_var = great_enough_var map_var_non_unit_int vect_sols_cache in
  let vect_car_cst = generate_vect_char_cst nb_var nb_true_var vect_sols_cst in
  let all_1 = Array.make nb_sols_h 1 in
    if nb_true_var = nb_var
    then test_ag_var (Large_bit_field.vect_of_bits_to_bit_field all_1)
    else List.exists 
      (function v -> 
	 let v'= Array.append all_1 v in
           test_ag_var (Large_bit_field.vect_of_bits_to_bit_field v'))
      vect_car_cst



let is_ac_unifiable non_unit_variables elem_pb =
  let (map_var_int,array_of_vars,v_type,matrix) = unif_to_arith elem_pb in
    if ((Array.length matrix) = 0)
    then true
    else 
      let unsorted_vect_sols = clean_solutions elem_pb map_var_int
			(Solve.dioph_solve v_type matrix) in
      let nb_sols = Array.length unsorted_vect_sols in
	if nb_sols = 0
	then false
	else 
	  let nb_var = v_type.(pred (Array.length v_type))
	  and nb_true_var = v_type.(0) in
	  let map_var_non_unit_int = 
	    filter_non_unit_vars non_unit_variables nb_true_var map_var_int in
	  let vect_sols_h, vect_sols_cst = 
	    classify elem_pb array_of_vars map_var_int v_type 
	      unsorted_vect_sols in
	    exists_vect_char nb_var nb_true_var map_var_non_unit_int 
	      vect_sols_h vect_sols_cst




(***************************************************************************

  Unification modulo an associative and commutative symbol.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Unif_to_arith
open Bit_field
open Hullot_bin_trees
open Arith_to_unif
open Problems

(*===================================================================

         L'unification AC ne doit etre appelee que sur des problemes
      	 purs, certaines variables pouvant etre instanciees par
      	 ailleurs dans d'autres theories et jouant de ce fait un role
      	 similaire a des constantes. Si le probleme de depart n'est
      	 pas pur, on aura un echec.

===================================================================*)

let solve unif_k non_zero_variables elem_pb = 
  let (map_var_int,array_of_vars,v_type,matrix) = unif_to_arith elem_pb in
    if (Array.length matrix) = 0
    then [[]]
    else 
      let nb_var = v_type.(pred (Array.length v_type))
      and nb_true_var = v_type.(0) in
      let vect_sols = 
	clean_solutions elem_pb map_var_int 
	  (Solve.dioph_solve v_type matrix) in 
      let nb_sols = Array.length vect_sols in
        if nb_sols = 0
        then []
        else 
	  begin
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
            let list_vect_car = 
              if nb_sols < 32
              then 
		let vect_sols_cache = pcache vect_sols in
	        let test_ag = pgreat_enough 0 nb_var vect_sols_cache
	        and test_ap = 
		  psmall_enough nb_true_var nb_var vect_sols_cache in
		  List.rev_map
		    (Small_bit_field.bit_field_to_vect_of_bits nb_sols)
                    (Small_binary_tree.arbre_binaire nb_sols test_ag test_ap)
              else 
		let vect_sols_cache = gcache vect_sols in
	        let test_ag = ggreat_enough 0 nb_var vect_sols_cache
	        and test_ap = 
		  gsmall_enough nb_true_var nb_var vect_sols_cache in
		  List.rev_map
		    (Large_bit_field.bit_field_to_vect_of_bits nb_sols)
                    (Large_binary_tree.arbre_binaire nb_sols test_ag test_ap)
		in 
		  List.rev_map 
		    (linear_combination unif_k elem_pb.elem_th
		       non_zero_variables map_var_int vect_sols vect_new_var) 
		    list_vect_car
                    
          end



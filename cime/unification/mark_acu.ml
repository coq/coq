(***************************************************************************

  This module provides a function for solving an elementary
  unification problem modulo an associative and commutative
  symbol. This function should only be called on a problem which is
  solved except that the marked variables may be instanciated.

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

open Variables
open Gen_terms
open Theory
open Problems
open Controle


let equation_to_process elem_pb = 
  List.find
    (function
	 (Var x, Term _) ->
	   VarMap.mem x elem_pb.marked_variables
       | _ -> false)
    elem_pb.equations

let inst_all_vars_but_one y var_to_uninstanciate non_unit_vars set_of_vars 
  elem_pb =
  let one = Term (unit_symbol_of_theory elem_pb.elem_th, []) in
  let new_equations = 
    List.map 
      (function 
	   (Var _ , Var _ as eq) -> eq
	 | ((Var x as vx),Term (f,l)) -> 
             begin
               let l'= 
		 List.filter
		   (function
			Var z -> (z = y) or (not (VarSet.mem z set_of_vars))
		      | _ -> true)
		   l in
		 match l' with
                     [] -> 
		       if VarSet.mem x non_unit_vars
		       then raise No_solution
		       else (vx, one)
                   | [v] -> (vx,v)
                   | _     -> 
		       if x = var_to_uninstanciate
                       then raise No_solution
                       else (vx,Term (f,l'))
             end
	 | _ -> assert false)
      elem_pb.equations in

    VarSet.fold 
      (fun x list_of_eqs ->
	 if x <> y
	 then (Var x, one) :: list_of_eqs
	 else list_of_eqs)
      set_of_vars new_equations


(*

  [(solve unif_k non_unit_variables elem_pb)] should be called only
  when the status of [elem_pb] is [Marked]. [non_unit_variables] is a
  set of variables which cannot be instanciated by the unit of the ACU
  theory. [(solve unif_k non_unit_variables elem_pb)] returns a list
  of solutions, each solution being given by a list of equations.

*)

let solve unif_k (* sign vars *) first_variables elem_pb =
(*
  let _ = 
  begin
    Printf.printf "--------------------------------------------\n";
    Printf.printf "Selected elementary problem \n";
    print_elem_pb sign vars elem_pb;
    Printf.printf "--------------------------------------------\n"
  end in
*)
  try 
    begin
      match equation_to_process elem_pb with
	  (Var x,t) ->
	    begin
	      let non_unit_vars =
		match unif_k with
		    PLAIN -> 
		      VarMap.fold
			(fun x _ set -> VarSet.add x set) 
			elem_pb.marked_variables VarSet.empty
		  | _ -> 
		      VarMap.fold
			(fun x _ set -> VarSet.add x set) 
			elem_pb.marked_variables first_variables 
	      and vars_of_t =  set_of_variables t in
	      let non_unit_vars_of_t = 
		VarSet.inter vars_of_t non_unit_vars in
		match VarSet.cardinal non_unit_vars_of_t with
		    0 -> 
		      VarSet.fold 
			(fun y partial_solutions -> 
			   try
			     let sol_y = 
			       inst_all_vars_but_one y x non_unit_vars
				 vars_of_t elem_pb in
			       sol_y :: partial_solutions
			   with No_solution -> partial_solutions)
			vars_of_t []
		  | 1 -> 
		      begin
			let y = VarSet.choose non_unit_vars_of_t in
			  try 
			    [inst_all_vars_but_one y x non_unit_vars 
			       vars_of_t elem_pb]
			  with 
			      No_solution -> []
		      end
		  | _ -> []
	    end
	| _ -> assert false
    end
  with 
      Not_found -> raise Not_appliable








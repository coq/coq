(***************************************************************************

  This module provides a function which gives some constraints in
  order to break an occur-check cycle in a quasi-solved problem.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Theory
open Problems
open Oc
open Mark
open Controle

let rec value_of_var x = function
    [] -> raise Not_found
  | (Var y,t)::l -> if x = y then t else value_of_var x l
  | (t,Var y)::l -> if x = y then t else value_of_var x l
  | _::l -> value_of_var x l


let key_of_elem_pb_where_var_instanciated pb x = 
  UnifElemThMap.find_key
    (fun _ elem_pb -> 
       List.exists 
	 (function 
	      (Var y), _ -> x = y
	    | _, (Var y) -> x = y
	    | _, _ -> false)
	 elem_pb.equations)
    pb.elem_pbs 


(*

  [(rec_cycle only_reg_th pb x list_of_pbs list_of_vars)]
  builds the disjunction of problems obtained from the problem [pb] by
  applying the rule
  \[
  P \longrightarrow 
     (P \wedge Mark_{E_i}(y)) \vee 
     (P \wedge Mark_{E_i}(z) \wedge Edge_{E_i}(z,y))
  \]
  whenever $y = t[z]$ is an equation of the elementary problem $P_i$
  which belongs to a mixed cycle w. r. t. the variables of the list
  [list_of_vars] (which are a partial cycle in the occur-check graph.

  Remark : 
  When the elementary theory $E_i$ is equal to Empty, C or AC, neither
  $(P \wedge Mark_{E_i}(y))$ nor $(P \wedge Mark_{E_i}(z) \wedge
  Edge_{E_i}(z,y))$ have solutions.

  When $E_i$ is equal to ACU, $(P \wedge Mark_{E_i}(z) \wedge
  Edge_{E_i}(z,y))$ has no solution.

  Hence whenever there are only Empty, C, AC and ACU as elementary
  theories in the original problem, the only solution is to collapse
  the cycle. In this case the booleen [only_reg_th] has to
  be equal to [true] at the first call.


*)

let next_var_in_the_cycle first_var cycle_remaining = 
  match cycle_remaining with
      [] -> first_var
    | z :: _ -> z




let add_a_mark_and_an_edge (y,z as edge) mark_to_set key_of_elem_pb pb =
  let new_elem_pbs = 
    UnifElemThMap.mapi
      (fun key elem_pb -> 
	 if key = key_of_elem_pb
	 then 
	   let new_marked_variables = 
	     VarMap.add y mark_to_set elem_pb.marked_variables 
	   and new_edges = edge::elem_pb.edges in
	     {
	       key = elem_pb.key;
	       status = Unsolved;
	       size = elem_pb.size;
	       elem_th = elem_pb.elem_th;
	       inst_variables = elem_pb.inst_variables;
	       marked_variables = new_marked_variables;
	       edges = new_edges;
	       equations = elem_pb.equations
	     }
	 else elem_pb)
      pb.elem_pbs in
    {
      pb with
      global_status = Unsolved;
      elem_pbs = new_elem_pbs;
      solved_part = []
    }


let rec break_cycle only_reg_th pb x list_of_pbs = function
    [] -> list_of_pbs

  | y::lvar -> 
      let z = next_var_in_the_cycle x lvar in
      let unif_elem_th_i = 
	key_of_elem_pb_where_var_instanciated pb z in
      let elem_th_i = elem_theory_from_unif_elem_theory unif_elem_th_i in
         
	match elem_th_i with
	    Empty _ | C _ | AC _ -> 
	      if only_reg_th
              then raise No_solution
              else break_cycle only_reg_th pb x list_of_pbs lvar
		
	  | ACU _ -> 
	      let new_pb = add_a_mark z Erasable unif_elem_th_i pb in
		if only_reg_th
		then break_cycle only_reg_th pb x [new_pb] lvar
		else break_cycle only_reg_th pb x (new_pb::list_of_pbs) lvar

	   | _ ->     
	       if only_reg_th
               then failwith "Cycle.rec_cycle"
               else 
		 let new_pb = add_a_mark z Erasable unif_elem_th_i pb 
		 and new_pb' = 
		   add_a_mark_and_an_edge (y,z) Erasable unif_elem_th_i pb in
                   break_cycle only_reg_th pb x 
		     (new_pb::new_pb'::list_of_pbs) lvar



let cycle sign (*i vars i*) pb =
  match pb.global_status with 
      Solved -> raise Not_appliable
    | _ ->
	let list_of_equations = 
	  UnifElemThMap.fold
	    (fun _ elem_pb partial_list_of_equations ->
	       elem_pb.equations @ partial_list_of_equations)
	    pb.elem_pbs [] in
	  
	  match occur_check_without_var_var sign (*i vars i*) list_of_equations with
	      No_cycle list_of_vars ->
		let solved_form = 
		  instanciate_when_no_cycle list_of_vars list_of_equations in
		let instanciated_list_of_eqs_var_var = 
		  VarMap.fold 
		    (fun v1 v2 partially_inst_eqs_var_var ->
		       let value_of_v2 = 
			 try List.assoc (Var v2) solved_form 
			 with Not_found -> Var v2 in
			 (Var v1, value_of_v2) :: partially_inst_eqs_var_var)
		    pb.var_var [] in
		let new_pb = 
		  {
		    pb with
		    global_status = Solved;
		    var_var = VarMap.empty;
		    elem_pbs = UnifElemThMap.empty;
		    solved_part = 
		     instanciated_list_of_eqs_var_var @ solved_form
		  } in
		  
		  [new_pb]
		  
	    | Cycle list_of_vars ->
		let only_reg_th = 
		  try
		    let _ = 
		      UnifElemThMap.find_one
			(fun _ elem_pb -> 
			   match elem_pb.elem_th with
			       Empty _ -> false
			     | C _ -> false
			     | AC _ -> false
			     | ACU _ -> false
			     | _ -> true) 
			pb.elem_pbs in 
		      false
		  with Not_found -> true
		      
		and first_var_of_cycle = List.hd list_of_vars in
		  break_cycle only_reg_th pb first_var_of_cycle [] list_of_vars
         

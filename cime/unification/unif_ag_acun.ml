(***************************************************************************

  Unification modulo AG, the Abelian Groups theory and modulo ACUN, a
  theory with a unit and an associative, commutative and nilpotent
  symbol of order $n$.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Theory
open Problems
open Unif_to_arith
open I_solve
open I_solve_modulo
open Arith_to_unif
open Unif_acu
open Controle

(*
open Aux;;
open Symbols;;
open Terms;;
open I_solve;;
open I_solve_modulo;;
open Theorie;;
open Type_de_donnees;;
open Var;;
open Unif_to_arith;;
open Arith_to_unif;;
open Unif_acu;;
*)


(*===================================================================

         L'unification modulo AG ou modulo ACUN ne doit etre
         appelee que sur des problemes purs, certaines variables
         pouvant etre instanciees par ailleurs dans d'autres 
         theories et jouant de ce fait un role similaire a 
         des constantes. Si le probleme de depart n'est pas 
         pur, on aura un echec. 

===================================================================*)


(*

  Unification modulo AG and ACUN: solving the equations.

*)

let solve_equations unif_k non_zero_variables elem_pb = 
  let (map_var_int,array_of_vars,v_type,matrix) = unif_to_arith elem_pb in
    if (Array.length matrix) = 0
    then [[]]
    else
      let nb_var = v_type.(pred (Array.length v_type))
      and edges = 
	List.map 
	  (function (x,y) -> 
	     (VarMap.find x map_var_int,VarMap.find y map_var_int))
	  elem_pb.edges in 
      let integer_sols = 
	begin
	  match elem_pb.elem_th with 
              AG _ -> i_solve v_type matrix edges 
            | ACUN (_,_,n) -> i_solve_modulo n v_type matrix edges
            | _ -> assert false
	end in

        match integer_sols with 
	    Without_identifications (sols_h,sols_p) -> 
	      let vect_sols = Array.append sols_h sols_p in
	      let nb_sols = Array.length vect_sols in
		if nb_sols = 0
		then []
		else 
		  let vect_char = Array.make nb_sols 1 in
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
		    [(linear_combination unif_k elem_pb.elem_th
		       non_zero_variables map_var_int vect_sols vect_new_var
		       vect_char)]

	  | With_identifications (sols_h,sols_p) -> 
	      let nb_true_var = v_type.(0) in
	      let vect_sols = Array.append sols_h sols_p in 
	      let nb_sols = Array.length vect_sols in
		if nb_sols = 0
		then []
		else 
		  let all_1 = Array.make (Array.length sols_h) 1 
		  and list_vect_char_cst = 
		    generate_vect_char_cst nb_var nb_true_var sols_p in
		  let list_vect_char =
		    List.map 
		      (function v -> Array.append all_1 v) list_vect_char_cst
		  and sum_of_sols = sum_of_columns vect_sols in 
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
		    List.map
		      (linear_combination unif_k elem_pb.elem_th 
			 non_zero_variables map_var_int vect_sols vect_new_var)
		      list_vect_char
		      
	  | No_sol -> raise No_solution


(*

  Processing of the [edges] constraints of a unification problem modulo
  AG/ACUN. This is done by the "constants elimination" technique. It
  is assumed that the problem, that is [list_of_equations] is of the form 
  \[
  x_1 = t_1 \wedge x_2 = t_2 \wedge \ldots \wedge x_n = t_n, 
  \]
  where the $x_i$s are pairwise distinct, and do not occur in the $t_j$s.

  Reminder: if [(x,y)] occur in the [edges] part of a problem, the
  variable [x] should be marked, that is, cannot be instanciated in the
  current theory (hence is considered as a constant) and [x] should not
  occur in the value of [y].

*)

(*

  [(clean_edges list_of_equations edges)] returns the edges
  corresponding to a constraint which is {\em not} fulfilled by the
  [list_of_equations].

*)


let clean_edges list_of_equations edges =
  List.filter
    (function (x,y) -> 
       try
	 let t = List.assoc (Var y) list_of_equations in
	   VarSet.mem x (set_of_variables t)
       with Not_found -> false)
    edges



(*

  [(expandable_variables marks list_of_equations)] returns the
  variables occurring in the right hand sides of the equations of
  [list_of_equations] which are not marked in [marks]. These variables
  can be instanciated further in order to make a constant disappear
  from the value of another variable. For example, if one wants to
  make $a$ disappear from the value $x+a+b$ modulo AG, this is done by
  instanciating $x$ by $-(a) + x'$, and $x+a+b$ becomes $-(a)+x'+a+b
  =_{AG} x'+b$.


*)

let expandable_variables marks list_of_equations =
  let variables_of_right_hand_sides =
    List.fold_left
      (fun partial_set (_,t) ->
	 VarSet.union partial_set (set_of_variables t))
      VarSet.empty list_of_equations in

    VarSet.filter
      (function x -> not (VarMap.mem x marks))
      variables_of_right_hand_sides


let constants_to_eliminate edges =
  List.fold_left
    (fun partial_set_of_csts (x,_) ->
       VarSet.add x partial_set_of_csts)
    VarSet.empty edges
  
let rec project zero m x map_exp_var_int new_var_mat = function
    Var z as v -> 
      if z = x 
      then v
      else 
	begin
          try 
	    let i = VarMap.find z map_exp_var_int in
              new_var_mat.(i).(m)
          with Not_found  -> zero
	end
  | Term (f,l) -> 
      Term (f, List.map (project zero m x map_exp_var_int new_var_mat) l)

let eliminate_cst unif_k non_zero_variables elem_pb list_of_equations =
  let edges = clean_edges list_of_equations elem_pb.edges in
  let expandable_vars =
    expandable_variables elem_pb.marked_variables list_of_equations
  and csts = constants_to_eliminate edges in
    
  let (nb_exp_vars,map_exp_var_int) =
    VarSet.fold
      (fun x (current_index,partial_map) ->
	 (succ current_index, VarMap.add x current_index partial_map))
      expandable_vars (0,VarMap.empty) 
  and (nb_csts,map_cst_int) =
    VarSet.fold
      (fun x (current_index,partial_map) ->
	 (succ current_index, VarMap.add x current_index partial_map))
      csts (0,VarMap.empty) in

    
  let new_var_mat =
    let first_new_var = Var (fresh_var_for_unif ()) in
      Array.create_matrix nb_exp_vars (succ nb_csts) first_new_var in
  let _ = 
    for m=1 to nb_csts do
      new_var_mat.(0).(m) <- Var (fresh_var_for_unif ())
    done
  and _ =
    for j=1 to (pred nb_exp_vars) do
      for m=0 to nb_csts do
        new_var_mat.(j).(m) <- Var (fresh_var_for_unif ())
      done
    done in 

    let plus = additive_symbol_of_theory elem_pb.elem_th 
    and zero = Term (unit_symbol_of_theory elem_pb.elem_th, []) in
    let list_of_exp_eqs =
      VarMap.fold 
	(fun xi i partial_list_of_exp_eqs ->
	   let ti = Term (plus, Array.to_list new_var_mat.(i)) in
	     (Var xi, ti) :: partial_list_of_exp_eqs)
	map_exp_var_int [] 

    and list_of_elim_eqs =
      List.map
        (function (x,y) -> 
	   let t = List.assoc (Var y) list_of_equations
           and m = VarMap.find x map_cst_int in
             (zero, (project zero m x map_exp_var_int new_var_mat t)))
        edges in
	
      let list_of_additional_eqs = list_of_exp_eqs @ list_of_elim_eqs in
	match list_of_additional_eqs with
	    [] -> [list_of_equations]
	  | _ -> 
	      let new_elem_pb = 
		{
		  key = elem_pb.key;
		  status = Unsolved;
		  size = None;
		  elem_th = elem_pb.elem_th;
		  inst_variables = elem_pb.inst_variables;
		  marked_variables = elem_pb.marked_variables;
		  edges = elem_pb.edges;
		  equations = list_of_equations @ list_of_additional_eqs
		} in
		solve_equations unif_k non_zero_variables new_elem_pb


let solve unif_k non_zero_variables elem_pb =  
  if (unif_k = PLAIN) or (is_ac_unifiable non_zero_variables elem_pb)
  then 
    let res1 = solve_equations unif_k non_zero_variables elem_pb in
      if elem_pb.edges = []
      then res1
      else 
	List.fold_left
	  (fun partial_list_of_solutions list_of_equations ->
	     let sols = 
	       eliminate_cst unif_k non_zero_variables elem_pb 
		 list_of_equations in
	       sols @ partial_list_of_solutions)
	  [] res1
  else []





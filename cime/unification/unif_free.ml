(***************************************************************************

  Unification in the free theory.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Problems
open Oc
open Controle

type 'symbol pure_elem_pb =
    {
      map_of_var_var : (unit, var_id) VarMap.t;
      scanned_equations : ('symbol term * 'symbol term) list;
      other_equations : ('symbol term * 'symbol term) list
    }

(*===================================================================

  Deletion of trivial equations.

====================================================================*)

let delete pb = 
  match pb.other_equations with
      (s,t) :: list_of_equations ->
	if s = t
	then 
	  {
	    map_of_var_var = pb.map_of_var_var;
	    scanned_equations = pb.scanned_equations;
	    other_equations = list_of_equations
	  }
	else raise Not_appliable
    | _ -> raise Not_appliable
	  
(*===================================================================

  Clash and decomposition for free symbols.

====================================================================*)

let clash_dec pb =
  match pb.other_equations with
      (Term (f,l), Term (g,k)) :: list_of_equations ->
	 if f = g
	 then 
	   try
	     let new_equations = (List.combine l k) @ list_of_equations in
	       {
		 map_of_var_var = pb.map_of_var_var;
		 scanned_equations = pb.scanned_equations;
		 other_equations = new_equations
	       }
	   with Invalid_argument "List.combine" -> raise No_solution
	 else raise No_solution
      | _ -> raise Not_appliable


(*===================================================================

  Coalesce (Replacement of a variable by a variable).

====================================================================*)

let representative x map_of_var_var = 
  try
    VarMap.find x map_of_var_var
  with 
      Not_found -> x


let coalesce pb = 
  match pb.other_equations with
      (Var x,Var y):: list_of_equations -> 
	if x = y 
	then 
	  {
	    map_of_var_var = pb.map_of_var_var;
	    scanned_equations = pb.scanned_equations;
	    other_equations = list_of_equations
	  }
	else 
	  let (var,rep) = 
	    let x' = representative x pb.map_of_var_var
	    and y' = representative y pb.map_of_var_var in
	      if (VarOrd.compare x' y') > 0
	      then (x',y')
	      else (y',x') in
	    let new_map_of_var_var = 
	      VarMap.add var rep 
		(VarMap.map 
		   (function r -> if r = var then rep else r) 
		   pb.map_of_var_var)
	    and reverted_new_list_of_equations = 
	      List.fold_left
		(fun partial_list_of_equations e ->
		   let e' = replace_a_var_by_a_var_in_an_eq var rep e in
		     e' :: partial_list_of_equations)
		(List.map 
		   (replace_a_var_by_a_var_in_an_eq var rep) 
		   pb.scanned_equations) 
		list_of_equations in
	      {
		map_of_var_var = new_map_of_var_var;
		scanned_equations = [];
		other_equations = List.rev reverted_new_list_of_equations
	      }
	    
    | _ -> raise Not_appliable


(*===================================================================

  Merge for two equations with the same variable left-hand side.

====================================================================*)

let rec find_a_value_of_var x = function
    (Var y, (Term _ as t)) :: list_of_equations ->
      if x = y
      then t 
      else find_a_value_of_var x list_of_equations
  | (Term _ as t, Var y) :: list_of_equations ->
      if x = y
      then t
      else find_a_value_of_var x list_of_equations
  | _ :: list_of_equations -> find_a_value_of_var x list_of_equations
  | [] -> raise Not_found


let remove_an_equation_in_a_list (s,t as s_t) list_of_equations =
  let t_s = (t,s) in
    List.filter
      (function eq -> (eq <> s_t) & (eq <> t_s))
      list_of_equations

let merge sign pb =
  match pb.other_equations with
      eq :: list_of_equations ->
	let x, var_x, s =
	  match eq with
	      Var x' as var_x' , (Term _ as s') -> x', var_x', s'
	    | Term _ as s', (Var x' as var_x') -> x', var_x', s'
	    | _, _-> raise Not_appliable in
	  begin 
	    try 
	      let t = find_a_value_of_var x list_of_equations in
      		if  s = t
		then 
		  {
		    map_of_var_var = pb.map_of_var_var;
		    scanned_equations = pb.scanned_equations;
		    other_equations = list_of_equations
		  }
		else 
		  let v = if (size sign s) < (size sign t) then s else t in
		    {
		      map_of_var_var = pb.map_of_var_var;
		      scanned_equations = pb.scanned_equations;
		      other_equations =  
		       (s,t) :: (var_x,v) :: (remove_an_equation_in_a_list 
						(var_x,t) list_of_equations)
		    }
	    with Not_found -> 
	      try 
		let t = find_a_value_of_var x pb.scanned_equations in
      		  if  s = t
		  then 
		    {
		      map_of_var_var = pb.map_of_var_var;
		      scanned_equations = pb.scanned_equations;
		      other_equations = list_of_equations
		    }
		  else 
		    let v = if (size sign s) < (size sign t) then s else t in
		      {
			map_of_var_var = pb.map_of_var_var;
			scanned_equations = 
			 remove_an_equation_in_a_list 
			   (var_x, t) pb.scanned_equations;
			other_equations =  
			 (s,t) :: (var_x, v) :: list_of_equations
		      }
	      with Not_found -> raise Not_appliable
	  end
 
    | [] -> raise Not_appliable 


(*===================================================================

                             Controle

====================================================================*)

let rec repeat rule pb = 
  match pb.other_equations with
      [] -> pb.map_of_var_var, pb.scanned_equations
    | eq::list_of_equations -> 
	let pb' = 
	  try 
      	    rule pb
	  with 
	      Not_appliable ->
		{
		  map_of_var_var = pb.map_of_var_var;
		  scanned_equations = eq :: pb.scanned_equations;
		  other_equations = list_of_equations
		} in
	  repeat rule pb'

(*===================================================================

  [solve_without_marks sign list_of_equations] computes a unifier
  for [list_of_equations] modulo the empty equational theory.

====================================================================*)

let solve_without_marks sign (*i vars i*) list_of_equations =
(*
  let _ =
    begin
      Printf.printf "La liste des equations a resoudre\n";
      List.iter
	(fun (s,t) ->
	   print_term sign vars s;
	   Format.print_flush ();
	   Printf.printf " = ";
	   print_term sign vars t;
	   Format.print_flush ();
	   Printf.printf "\n")
	list_of_equations
    end in
*)
  let map_of_var_var, quasi_solved_form = 
    repeat
      (orelse (orelse (orelse delete clash_dec) coalesce) (merge sign))
      {
	map_of_var_var = VarMap.empty;
	scanned_equations = [];
	other_equations = list_of_equations
      } in
(*
  let _ =
    begin
      Printf.printf "La forme quasi-resolue avant OC\n";
      VarMap.iter
	(fun x y ->
	   print_term sign vars (Var x);
	   Format.print_flush ();
	   Printf.printf " = ";
	   print_term sign vars (Var y);
	   Format.print_flush ();
	   Printf.printf "\n")
	map_of_var_var;
      List.iter
	(function (s,t) ->
	   print_term sign vars s;
	   Format.print_flush ();
	   Printf.printf " = ";
	   print_term sign vars t;
	   Format.print_flush ();
	   Printf.printf "\n")
	quasi_solved_form
    end in
*)
  occur_check sign (*i vars i*) map_of_var_var quasi_solved_form
       

(*

  [solve sign elem_pb] computes a unifier for [elem_pb] modulo the
  empty equational theory, that is, solves the equations of the
  problem and checks that the constraints of marks are satisfied.

*)

let solve sign (*i vars i*) elem_pb =
  let solved_form = solve_without_marks sign (*i vars i*) elem_pb.equations in
  let _ = 
    List.iter 
      (function 
	   (Var x, Term _) ->
	     if VarMap.mem x elem_pb.marked_variables
	     then raise No_solution
	 | (Term _, Var x) ->
	     if VarMap.mem x elem_pb.marked_variables
	     then raise No_solution
	 | _ -> ())
      solved_form in
    [solved_form]










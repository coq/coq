(***************************************************************************

  Unification modulo a commutative symbol.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Problems
open Oc
open Controle

(*

  Important remark: all the terms occurring in the arguments of the
  functions defined in this module are assumed to be pure, that is
  built only with variables and [+], a fixed commutative symbol.

*)

(*===================================================================

  Deletion of trivial equations

====================================================================*)

let delete pb = [Unif_free.delete pb]

(*===================================================================

  Syntactic decomposition for equations between two terms headed by
  the commutative symbol. By assumption, the terms are pure, hence
  there cannot be a clash.

====================================================================*)

let decompose_equations = function
    (Term (_,[s1;s2]), Term (_,[t1;t2]))::list_of_equations ->
      if s1 = t1
      then 
	if s2 = t2 
        then [list_of_equations]           (* s1 = t1 and s2 = t2 *)
        else [(s2,t2)::list_of_equations]  (* s1 = t1 and s2 <> t2 *)
      else 
	if s1 = t2
        then 
	  if s2 = t1 
          then [list_of_equations]          (* s1 = t2 and s2 = t1 *)
          else [(s2,t1)::list_of_equations] (* s1 = t2 and s2 <> t1 *)
        else 
	  if s2 = t1
          then [(s1,t2)::list_of_equations] (* s1 <> t1,t2 and s2 = t1 *)
          else 
	    if s2 = t2
            then [(s1,t1)::list_of_equations] (* s1 <> t1,t2 and s2 = t2 *)
            else 
	      [(s1,t1)::(s2,t2)::list_of_equations; (* s1 <> t1,t2 and *)
	       (s2,t1)::(s1,t2)::list_of_equations] (* s2 <> t1,t2 *)

 | _ -> raise Not_appliable


let decompose pb = 
  List.map
    (function list_of_dec_equations ->
       {
	 Unif_free.map_of_var_var = pb.Unif_free.map_of_var_var;
	 Unif_free.scanned_equations = pb.Unif_free.scanned_equations;
	 Unif_free.other_equations = list_of_dec_equations
       }
    )
       (decompose_equations pb.Unif_free.other_equations)

(*===================================================================

  Coalesce (Replacement of a variable by a variable).

====================================================================*)

let coalesce pb = [Unif_free.coalesce pb]

(*===================================================================

  Merge for two equations with the same variable left-hand side.

====================================================================*)

let merge sign pb = [Unif_free.merge sign pb]

(*===================================================================

                             Controle

====================================================================*)

  
let rec repeat rule = function
    [] -> []
  | pb :: list_of_pbs -> 
      match pb.Unif_free.other_equations with
	  [] -> 
	    (pb.Unif_free.map_of_var_var, pb.Unif_free.scanned_equations) :: 
	    (repeat rule list_of_pbs)
	| eq::list_of_equations ->
	    try 
      	      let list_of_pbs' = rule pb in
		repeat rule (list_of_pbs' @ list_of_pbs)
	    with 
		Not_appliable ->
		  let pb' =
		    {
		      Unif_free.map_of_var_var = pb.Unif_free.map_of_var_var;
		      Unif_free.scanned_equations = 
		       eq :: pb.Unif_free.scanned_equations;
		      Unif_free.other_equations = list_of_equations
		    } in
		    repeat rule (pb' :: list_of_pbs)
	      | No_solution ->
		  repeat rule list_of_pbs

(*===================================================================

  [solve_without_marks sign list_of_equations] computes a unifier
  for [list_of_equations] modulo the commutativity.

====================================================================*)

let solve_without_marks sign (*i vars i*) list_of_equations =
  let list_of_quasi_solved_forms = 
    repeat
      (orelse (orelse (orelse delete decompose) coalesce) (merge sign))
      [
	{
	  Unif_free.map_of_var_var = VarMap.empty;
	  Unif_free.scanned_equations = [];
	  Unif_free.other_equations = list_of_equations
	} 
      ] in

    List.fold_left 
      (fun result (map_of_var_var, quasi_solved_form) ->
	 try
	   let solved_form = 
	     occur_check sign (*i vars i*) map_of_var_var quasi_solved_form in
	     solved_form :: result
	 with No_solution -> result)
      [] list_of_quasi_solved_forms


(*

  [solve sign elem_pb] computes a unifier for [elem_pb] modulo the
  commutativity, that is, solves the equations of the problem and
  checks that the constraints of marks are satisfied.

*)

let solve sign (*i vars i*) elem_pb =
  let list_of_solved_forms = 
    solve_without_marks sign (*i vars i*) elem_pb.equations 
  in
  List.fold_left
      (fun result solved_form ->
	 try
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
	     solved_form :: result
	 with No_solution -> result)
      [] list_of_solved_forms



	   





(***************************************************************************

This module provides a function which implements the E-Resolution,
that is solves an elementary (pure) problem according to its theory.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Theory
open Problems
open Oc
open Controle

(*===================================================================

                      General E-Resolution

====================================================================*)

exception No_unsolved_elem_pb

let size_eq sigma (s,t) = 
  (Gen_terms.size sigma s) + (Gen_terms.size sigma t)


let size_of_an_elem_pb sigma elem_pb = 
  let rec rec_size current_max_size = function
      [] -> current_max_size
    | eq::list_of_eqs ->
	let n = size_eq sigma eq in
	  if n > current_max_size
	  then rec_size n list_of_eqs
	  else rec_size current_max_size list_of_eqs in
    rec_size 0 elem_pb.equations


let select_an_elem_pb_with_unitary_unif pb = 
  UnifElemThMap.find_one
    (fun _ elem_pb -> 
       if elem_pb.status = Solved
       then false
       else 
	 match elem_pb.elem_th with
	     AC _ 
	   | ACU _ 
	   | ACI _  -> false
	   | _ -> true
    )
    pb.elem_pbs

let recompute_sizes_of_elem_pbs pb = 
  let new_elem_pbs = 
    UnifElemThMap.map
      (function elem_pb ->
	 if elem_pb.status = Solved
	 then elem_pb
	 else 
	   match elem_pb.size with
	       Some _ -> elem_pb
	     | None ->
		 {
		   elem_pb with
		   size = Some (size_of_an_elem_pb pb.sign elem_pb)
		 }) 
      pb.elem_pbs in

    {
      pb with 
	elem_pbs = new_elem_pbs
    }


let select_the_smallest_unsolved_elem_pb pb =
  let pb' = recompute_sizes_of_elem_pbs pb in

  let first_unsolved_elem_pb = 
    UnifElemThMap.find_one 
      (fun _ elem_pb -> elem_pb.status <> Solved) pb'.elem_pbs in
  let first_size = 
    match first_unsolved_elem_pb.size with 
	Some n -> n
      | None -> failwith "select_the_smallest_unsolved_elem_pb" in

  let (_,selected_elem_pb) = 
    UnifElemThMap.fold 
      (fun _ elem_pb (current_size,currently_selected_elem_pb as selection) ->
	 if elem_pb.status = Solved
	 then selection
	 else 
	   match elem_pb.size with
	       Some n -> 
		 if n < current_size
		 then (n,elem_pb)
		 else selection
	     | None -> failwith "select_the_smallest_unsolved_elem_pb")
      pb'.elem_pbs (first_size, first_unsolved_elem_pb) in

    selected_elem_pb
      


let select_an_elem_pb_with_a_cycle sign (*i vars i*)  pb = 
  UnifElemThMap.find_one
    (fun _ elem_pb -> 
       match elem_pb.elem_th with
	   Empty _ 
	 | C _ 
	 | AC _ -> false
	 | _ ->
	     begin
	       match occur_check_without_var_var 
		 sign (*i vars i*) elem_pb.equations with
		   Cycle _ -> true
		 | No_cycle _ -> false
	     end)
    pb.elem_pbs


let select_an_unsolved_elem_pb sign (*i vars i*) pb = 
   try 
     select_an_elem_pb_with_unitary_unif pb
   with 
       Not_found -> 
	 begin 
	   try 
	     select_the_smallest_unsolved_elem_pb pb
	   with Not_found ->
             begin 
               try 
		 select_an_elem_pb_with_a_cycle sign (*i vars i*) pb
               with 
		   Not_found ->
		     raise No_unsolved_elem_pb
	     end
	 end


let unif_elem unif_k sign (*i vars i*) non_zero_vars elem_pb = 
  match elem_pb.elem_th with
      Empty _  -> 
	(try Unif_free.solve sign (*i vars i*) elem_pb with No_solution -> [])
    | C _ -> Unif_commutative.solve sign (*i vars i*) elem_pb
    | AC _ -> Unif_ac.solve unif_k non_zero_vars elem_pb
    | ACU _ -> Unif_acu.solve unif_k non_zero_vars elem_pb
    | ACI _ -> Unif_aci.solve unif_k non_zero_vars elem_pb
    | ACUN _ 
    | AG _ -> Unif_ag_acun.solve unif_k non_zero_vars elem_pb
    | BR _ -> Unif_bool.solve sign elem_pb
	
      
let general_E_resolution sign (*i vars i*) pb =
(*
  let _ = 
    begin
      Printf.printf "\n\n\n\n\n\ngeneral_E_resolution is called with\n";
      print_problem sign vars pb
    end in
*)
  try 
    let elem_pb = select_an_unsolved_elem_pb sign (*i vars i*) pb in
(*
    let _ =
      begin
	Printf.printf "--------------------------------------------\n";
	Printf.printf "Selected elementary problem \n";
	print_elem_pb sign vars elem_pb;
	Printf.printf "--------------------------------------------\n"
      end in
*)
    let solved_elem_pbs = 
      match elem_pb.elem_th with
	  ACU _ ->
	    begin
	      match elem_pb.status with
		  Unsolved -> 
		    Unif_acu.solve pb.unif_kind pb.first_vars elem_pb  
		| Marked -> 
		    Mark_acu.solve pb.unif_kind pb.first_vars elem_pb
		| Merged -> 
		    Merge_acu.solve pb.unif_kind pb.first_vars elem_pb
		| Solved -> assert false
	    end
	| _ -> 	   
	    begin
	      match elem_pb.status with
		  Unsolved  
		| Marked   
		| Merged -> 
		    unif_elem 
		      pb.unif_kind pb.sign (*i vars i*) pb.first_vars elem_pb
		| Solved -> assert false
	    end in
      
(*
    let _ = 
      begin
	List.iter 
	  (function solved_elem_pb ->
	  Printf.printf "~~~~~~~~~~~~~~~~~~~~~~~~~~\n";
	  Printf.printf "solved form\n";
	  List.iter
	    (function (s,t) ->
	       Gen_terms.print_term sign vars s;
	       Format.print_flush ();
	       Printf.printf " = ";
	       Gen_terms.print_term sign vars t;
	       Format.print_flush ();
	       Printf.printf "\n")
	    solved_elem_pb;
	  Printf.printf "~~~~~~~~~~~~~~~~~~~~~~~~~~\n")
	  solved_elem_pbs
      end in
*)
    let res = 
      insert_solved_elem_pbs 
	sign (*i vars i*) pb elem_pb.key solved_elem_pbs 
    in
(*
    let _ =
      begin
	Printf.printf "The problem after solving inserting the elem sols\n";
	List.iter (print_problem sign vars) res
      end in
*)
      res
      

  with No_unsolved_elem_pb -> raise Not_appliable




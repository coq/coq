(***************************************************************************

  This module provides the function [mark] which adds some constraints
  on a unification problem in order to solve the clashes between the 
  elementary unification theories.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Signatures
open Variables
open Gen_terms
open Theory
open Problems
open Controle


(*
  detecte_pour_mark pb x retourne (x,n1,l1,l2) ou n1 est la longueur de l1,
  l1 est une liste de couples [(th,f)] tels que 
  - the est une theorie reguliere collapse-free, ici Empty, C, AC
  - il existe une equation [x = Term(f,_)] dans le sous-probleme 
    associe a [th]
  l2 correspond au meme type de liste pour les autres theories.
*)

let instanciations_of_var pb x = 
  UnifElemThMap.fold
    (fun key_of_elem_pb elem_pb (perm_th_inst,list_of_other_inst as res) ->
       if elem_pb.status = Marked 
       then raise Not_appliable 
       else 
	 try
	   let t = VarMap.find x elem_pb.inst_variables in
	     match elem_pb.elem_th with
		 Empty _ ->
		   begin
		     match perm_th_inst with
			 None ->
			   begin
			     match t with
				 Term (f,_) ->
				   let f_to_th = 
				     Empty (Some f) in
				     (Some f_to_th, list_of_other_inst)
			       | _ -> assert false
			   end
		       | Some _ -> raise No_solution
		   end
	       | C _ 
	       | AC _ ->
		   begin
		     match perm_th_inst with
			 None -> (Some elem_pb.elem_th, list_of_other_inst)
		       | Some _ -> raise No_solution
		   end
	       | _ -> (perm_th_inst, key_of_elem_pb :: list_of_other_inst)
	 with 
	     Not_found -> res)
    pb.elem_pbs (None,[])
	 

let rec detect_first_theories_clash pb = function
    x :: list_of_variables ->
(*
      let _ = 
	begin
	  Format.print_string "mark is called";
	  Format.print_newline();
	  Format.print_flush()
	end in
*)      
      let (perm_th_inst_for_x, list_of_other_inst_for_x as res) = 
	instanciations_of_var pb x in
	begin
	  match perm_th_inst_for_x with
	      None -> 
		if (List.length list_of_other_inst_for_x) <= 1
		then detect_first_theories_clash pb list_of_variables
		else (x,res)
	    | Some _ ->
		if list_of_other_inst_for_x = []
		then detect_first_theories_clash pb list_of_variables
		else (x,res)
	end
  | [] -> raise Not_appliable



let add_a_mark var_to_be_marked mark_to_set key_of_elem_pb pb = 
  let new_elem_pbs = 
    UnifElemThMap.mapi
      (fun key elem_pb -> 
	 if key = key_of_elem_pb
	 then 
	   let new_status =
	     match elem_pb.status with
		 Solved ->
		   if VarMap.mem var_to_be_marked elem_pb.inst_variables
		   then Marked
		   else Solved
	       | s -> s
	   and new_marked_variables = 
	     VarMap.add var_to_be_marked mark_to_set 
	       elem_pb.marked_variables in
	     {
	       elem_pb with
	       status = new_status;
	       marked_variables = new_marked_variables;
	     }
	 else elem_pb)
      pb.elem_pbs in
    {
      pb with
      global_status = Unsolved;
      elem_pbs = new_elem_pbs;
      solved_part = []
    }  

(*
  Mark_aux effectue Mark avec la variable a marquer (+ autres
  informations) donnee en argument no 1. 
*)

let set_marks pb = function
    (x,((Some elem_th),list_of_keys_of_elem_pbs)) ->
       let mark_to_be_set = Permanent elem_th in
       let new_pb = 
	 List.fold_left 
	   (fun pb' key_of_elem_pb -> 
	      add_a_mark x mark_to_be_set key_of_elem_pb pb')
	   pb list_of_keys_of_elem_pbs in
	 [new_pb]

    | (x,(None,list_of_keys_elem_pbs)) ->
	List.map
	  (function key ->
	     List.fold_left 
	       (fun pb' key' ->
		  if key' <> key
		  then 
		    add_a_mark x Erasable key' pb'
		  else pb')
	       pb list_of_keys_elem_pbs)
	  list_of_keys_elem_pbs



	
(* 

   [(mark pb)] applies the {\bf Mark} rule on the unification problem
   [pb] and returns
   \begin{itemize}
   \item either the exception [Not_appliable]
   \item either the exception [No_solution
   \item or a list of marked unification problems.
   \end{itemize}

*)

let mark pb = 
  let list_of_instanciated_vars = 
    UnifElemThMap.fold
      (fun _ elem_pb list_of_vars -> 
	 VarMap.fold 
	   (fun inst_var _ current_list_of_vars -> 
	      if List.mem inst_var current_list_of_vars 
	      then current_list_of_vars 
	      else inst_var :: current_list_of_vars)
	   elem_pb.inst_variables list_of_vars)
      pb.elem_pbs [] in

  let first_theories_clash = 
    detect_first_theories_clash pb list_of_instanciated_vars in
    
    set_marks pb first_theories_clash





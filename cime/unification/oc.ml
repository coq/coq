(***************************************************************************

This module provides a generalized occur-check based on the topological sort.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


(*

  Topological Sort

*)

type cycle_in_a_graph = 
    Graphe_cycle of int list
  | No_graphe_cycle of int list
         
let nodes_without_predecessor vect_pred =
  Arrayutils.filter_indices
    (function nb_pred_i -> nb_pred_i = 0)
    vect_pred

let nodes_without_successor vect_succ = 
  Arrayutils.filter_indices
    (function nb_succ_i -> nb_succ_i = 0)
    vect_succ

(*

  [(find_a_node_in_a_cycle vect_succ)] has to be called only once all
  nodes without successor have been removed in the graph and [vect_succ]
  is up-to-date with this removal.

*)

let find_a_node_in_a_cycle vect_succ = 
  try
    Arrayutils.find (function nb_succ_i -> nb_succ_i > 0) vect_succ
  with 
      Not_found -> failwith "Oc.find_a_node_in_a_cycle"

(*

  [(next_node_in_cycle nb_nodes incidence_matrix vect_succ node)]
  returns a successor of the node [node] in the graph described by the
  [incidence_matrix], and both [node] and its successor are in a
  cycle.

  This function has has to be called only once all nodes without
  successor have been removed in the graph and [vect_succ] is
  up-to-date with this removal.

*)

exception Found of int

let next_node_in_cycle nb_nodes incidence_matrix vect_succ node =
  try
    for j = 0 to nb_nodes do
      if (vect_succ.(j) > 0) & (incidence_matrix.(node).(j) = 1)
      then raise (Found j)
    done;
    failwith "Oc.next_node_in_cycle"
  with Found next -> next


(* 

   [(add_a_node_to_a_partial_cycle nb_nodes incidence_matrix vect_succ
    partial_cycle)] adds a node to [partial_cycle], a part of a
   cycle which is already built.

  This function has has to be called only once all nodes without
  successor have been removed in the graph and [vect_succ] is
  up-to-date with this removal.

*)

let rec add_a_node_to_a_partial_cycle nb_nodes incidence_matrix vect_succ 
  partial_cycle =
  let last_node = List.hd partial_cycle
  and rest_of_partial_cycle = List.tl partial_cycle in
  if 
    List.exists 
      (function u -> (incidence_matrix.(last_node).(u) = 1)) 
      rest_of_partial_cycle 
  then (* the partial cycle is actually a cycle *)
    Graphe_cycle partial_cycle 
  else 
    let z = next_node_in_cycle nb_nodes incidence_matrix vect_succ last_node in
      add_a_node_to_a_partial_cycle nb_nodes incidence_matrix vect_succ (z::partial_cycle)



let remove_a_node_in_vect_succ nb_nodes incidence_matrix vect_succ ix = 
  for j=0 to nb_nodes do
    if (incidence_matrix.(j).(ix) = 1) 
    then vect_succ.(j) <- pred vect_succ.(j) 
  done;
  vect_succ.(ix) <- -1

let remove_a_node_in_vect_pred nb_nodes incidence_matrix vect_pred ix = 
  for j=0 to nb_nodes do
    if (incidence_matrix.(ix).(j) = 1) 
    then vect_pred.(j) <- pred vect_pred.(j) 
  done;
  vect_pred.(ix) <- -1

(* 

   [(find_a_cycle nb_nodes incidence_matrix vect_succ)] finds a cycle
   in the graph described by the [incidence_matrix]. 


  This function has has to be called only once all nodes without
  predecessor have been recursively removed in the graph and
  [vect_succ] is up-to-date with this removal.

*)

let rec find_a_cycle nb_nodes incidence_matrix vect_succ 
  list_of_nodes_without_successors =

  let _ = 
    List.iter 
      (function node ->
	 remove_a_node_in_vect_succ nb_nodes incidence_matrix vect_succ node)
      list_of_nodes_without_successors in

  let new_list_of_nodes_without_successors = 
    nodes_without_successor vect_succ in
    
    match new_list_of_nodes_without_successors with
	[] -> 
	  let v = find_a_node_in_a_cycle vect_succ in
	    add_a_node_to_a_partial_cycle nb_nodes incidence_matrix 
	      vect_succ [v]  
      | _ -> 
	  find_a_cycle nb_nodes incidence_matrix vect_succ 
	    new_list_of_nodes_without_successors



(*

  [(topological_sort nb_nodes mat vect_pred vect_succ n sorted_nodes
  list_of_nodes_without_predecessors)] 
  \begin{itemize} 
  \item when there is no cycle in the graph described by the incidence
  matrix [mat], returns [No_graphe_cycle list_of_nodes] where
  [list_of_nodes] provides a total ordering over the nodes, compatible
  with the partial ordering induced by the graph.
  \item when there is a cycle in the graph described by [mat], returns
  [Graphe_cycle partial_list_of_nodes] where [partial_list_of_nodes]
  is a cycle in the graph.
  \end{itemize}

*)

let rec topological_sort nb_nodes mat vect_pred vect_succ n 
  sorted_nodes list_of_nodes_without_predecessors =

  if n = 0 (* success, all variables have been popped *)
  then No_graphe_cycle sorted_nodes
  else 
    begin
      match list_of_nodes_without_predecessors with

	  [] -> 
	    let new_list_of_nodes_without_predecessors = 
	      nodes_without_predecessor vect_pred in
              if new_list_of_nodes_without_predecessors = []
              then (* there is a cycle *)
		find_a_cycle nb_nodes mat vect_succ 
		  (nodes_without_successor vect_succ)
              else 
		topological_sort nb_nodes mat vect_pred vect_succ n 
		  sorted_nodes new_list_of_nodes_without_predecessors

	| node::list_of_nodes -> 
	    if n = succ (List.length list_of_nodes)
            then (* success *)
	      No_graphe_cycle 
		(list_of_nodes_without_predecessors @ sorted_nodes)
            else 
	      let _ = remove_a_node_in_vect_pred nb_nodes mat vect_pred node 
	      and _ = remove_a_node_in_vect_succ nb_nodes mat vect_succ node in
		topological_sort nb_nodes mat vect_pred vect_succ
		  (pred n) (node::sorted_nodes) list_of_nodes
    end



(*

  Generalized Occur-check using the topological sort
  
*)

open Variables
open Gen_terms
open Substitution
open Controle

type cycle = 
     Cycle of (var_id list)
  |  No_cycle of (var_id list)


(*

  Computation of the list of variables of a list of equations

*)

let set_of_vars_of_an_equation (s,t) = 
  VarSet.union (set_of_variables s) (set_of_variables t)


let set_of_vars_of_a_list_of_equations list_of_equations = 
  List.fold_left 
    (fun set_of_vars equation -> 
       VarSet.union set_of_vars (set_of_vars_of_an_equation equation))
    VarSet.empty 
    list_of_equations

let list_of_vars_of_list_of_equations list_of_equations = 
  let set_of_vars = set_of_vars_of_a_list_of_equations list_of_equations in
    VarSet.elements set_of_vars

(*

  Computation of (the incidence matrix of) the graph generated by 
  a list of equations.

*)


(*
  mise_a_jour_mat_et_vect_x ix vect_var mat vect_pred vect_succ t 
  met a jour la matrice des successeurs pour la variable x d'indice ix 
  dans vect_var, le vecteur du nombre de successeurs de x et le vecteur 
  du nombre de predecesseurs des variables de t, lorsque l'on rencontre 
  une equation x = t.
*)

let rec update_mat_and_vect ix map_of_var_indices (m,vp,vs as arg) = function
    Var z -> 
      let iz = VarMap.find z map_of_var_indices in
	if m.(ix).(iz) = 0
        then 
	  begin 
	    m.(ix).(iz) <- 1;
	    vp.(iz) <- succ vp.(iz);
	    vs.(ix) <- succ vs.(ix)
          end

  | Term (_,l) -> 
      List.iter (update_mat_and_vect ix map_of_var_indices arg) l

(* 


   [(mat_and_vect nb_var map_of_var_indices list_of_equations)] builds
  the triple [(mat,vect_pred,vect_succ)] such that
   \begin{itemize}
   \item [mat] is the incidence matrix of the occur-check graph
  generated the [list_of_equations], that is [mat.(ix).(iy) = 1] if
  and only if the iy-th variable occurs in the value of the ix-th
  variable,
   \item [vect_pred] contains the number of predecessors in the graph,
   \item [vect_succ] contains the number of successors in the graph.
   \end{itemize}

*)

let mat_and_vect nb_var map_of_var_indices list_of_equations = 
  let mat = Array.create_matrix nb_var nb_var 0 
  and vect_pred = Array.create nb_var 0 
  and vect_succ = Array.create nb_var 0 in

  let m_vp_vc = (mat,vect_pred,vect_succ) in

  let _ = 
    List.iter 
      (function equation -> 
	 match equation with
	     Var x, (Term _ as t) -> 
	       let ix = VarMap.find x map_of_var_indices in
		 update_mat_and_vect ix map_of_var_indices m_vp_vc t
		   
	   | Term _ as t, Var x -> 
	       let ix = VarMap.find x map_of_var_indices in
		 update_mat_and_vect ix map_of_var_indices m_vp_vc t
		   
	   |  _, _ -> ())
      
      list_of_equations in

    m_vp_vc
      
 
(*

  The occur-check functions.
  
*)


(*

  [(occur_check_without_var_var list_of_equations)] check that there 
  is no cycle in the occurrence graph generated by the 
  [list_of_equations], that is returns
  \begin{itemize}
  \item [No_cycle list_of_vars] when there is no cycle in the graph;
  in this case, the (total) ordering of the variables in the
  [list_of_vars] is compatible with the (partial) ordering induced by
  the graph,
  \item [Cycle list_of_vars] when there is a cycle in the graph going
  through the nodes [list_of_vars].
  \end{itemize}

  It is assumed that [list_of_equations] does not contains any equation 
  between variables.

*)

let occur_check_without_var_var sign (*i vars i*) list_of_equations = 
  let list_of_vars = list_of_vars_of_list_of_equations list_of_equations in
  let nb_var = List.length list_of_vars in
  let nb_nodes = pred nb_var in
  let (_, map_of_var_indices) = 
    List.fold_left
      (fun (i,partial_map) x -> (succ i, VarMap.add x i partial_map))
      (0, VarMap.empty) 
      list_of_vars in

  let (mat,vect_pred,vect_succ) = 
    mat_and_vect nb_var map_of_var_indices list_of_equations in

    match topological_sort nb_nodes mat vect_pred vect_succ nb_var [] [] with
	
	No_graphe_cycle list_of_indices ->
	  No_cycle (List.map (List.nth list_of_vars) list_of_indices)
	    
      | Graphe_cycle list_of_indices ->
	  Cycle (List.map (List.nth list_of_vars) list_of_indices)


let rec eq_for_value_of_var x = function
    (Var y, _ as eq) :: list_of_equations ->
      if x = y
      then Some eq
      else eq_for_value_of_var x list_of_equations
  | (t, (Var y as v)) :: list_of_equations ->
      if x = y
      then Some (v,t)
      else eq_for_value_of_var x list_of_equations
  | _ :: list_of_equations -> eq_for_value_of_var x list_of_equations
  | [] -> None


(* 

   A call to [(instanciate_when_no_cycle list_of_vars list_of_equations)] 
   assumes that
  \begin{itemize}
  \item there is no cycle in the occur-check graph generated by the
  [list_of_equations],
  \item and that [list_of_vars] provides a total ordering compatible
  with the occur-check graph.
  \end{itemize}
  This function takes [list_of_equations] as a DAG-solved form, in
  particular all the equations are of the form [variable = term], and
  it returns an equivalent solved form.

*)

let instanciate_when_no_cycle list_of_vars list_of_equations = 

  let rec sort_equations sorted_equations = function
      [] -> sorted_equations
    | (x::lv) ->
	match eq_for_value_of_var x list_of_equations with
	    Some eq -> sort_equations (sorted_equations @ [eq]) lv
	  | None -> sort_equations sorted_equations lv
 
  and instanciate res = function
      [] -> res
 
   | (Var x as v, t as eq) :: list_of_eqs -> 
	let x_mapsto_t = VarMap.add x t (VarMap.empty) in
	let instanciated_list_of_eqs = 
          List.map 
	    (function 
		 (Var _ as var,s) -> 
		   (var, Substitution.apply_term s x_mapsto_t)
	       | _ -> assert false)
	    list_of_eqs in
	  instanciate (eq::res) instanciated_list_of_eqs 

   | _ -> assert false in
	  

    instanciate [] (sort_equations [] list_of_vars)


(*

  A call to [(occur_check list_of_eqs_var_var list_of_equations)]
  assumes that 
  \begin{itemize}
  \item [list_of_eqs_var_var] contains only equations between variables, 
  \item [list_of_equations] contains only equations between a variable 
  and a non-variable term,
  \item and the {\bf Coalesce} rule does not apply on the union of
  these two sets of equations.
  \end{itemize}

  It returns either a failure when there is a cycle in the occur-check
  graph or a list of equations which is a solved form for the union of
  [list_of_eqs_var_var] and [list_of_equations].

*)

let occur_check sign (*i vars i*) list_of_eqs_var_var list_of_equations =
  match occur_check_without_var_var sign (*i vars i*) list_of_equations with
      Cycle _ -> raise No_solution

    | No_cycle list_of_vars ->
	let solved_form = 
	  instanciate_when_no_cycle list_of_vars list_of_equations in
	let instanciated_list_of_eqs_var_var = 
	  VarMap.fold 
	    (fun v1 v2 partially_inst_eqs_var_var ->
	       let value_of_v2 = 
		 let var_v2 = Var v2 in
		   try List.assoc var_v2 solved_form 
		   with Not_found -> var_v2 in
		 (Var v1, value_of_v2) :: partially_inst_eqs_var_var)
	    list_of_eqs_var_var [] in

	  instanciated_list_of_eqs_var_var @ solved_form


(***************************************************************************

  This module provides some functions in order to translate a
  unification problem modulo an AC-like theory into an arithmetic
  problem.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Theory
open Problems

(*
   tri_par_theorie m [x1;x2;...;xi;...] regroupe les xi
   suivant leur theorie d'instanciation : le resultat est
   une liste de couples 
  (theorie, liste de ces variables instanciees dans cette theorie)
   avec les conventions suivantes :
   - le premier element de la liste comprend les variables 
     qui ne sont pas instanciees dans une autre theorie,
   - le deuxieme element comporte les variables qui sont
     marquees parce qu'instanciees dans une theorie non
     reguliere et collapse-free (ie ACU, AG, BR, ...)
   - les elements suivants comportent triees suivant leur theorie
     d'instanciation les variables marquees parce qu'instanciees 
     dans une theorie reguliere collapse-free, ou l'instanciation 
     est irreversible.     
*)

module OrderedMarkTheory =
  struct 
    type 'symbol t = 'symbol mark
    let compare m1 m2 = 
      match m1 with
	  No_mark ->
	    begin
	      match m2 with
		  No_mark -> 0
		| _ -> -1
	    end
	| Erasable ->
	    begin
	      match m2 with
		  No_mark -> 1
		| Erasable -> 0
		| Permanent _ -> -1
	    end
	| Permanent th1 ->
	    begin
	      match m2 with
		  No_mark -> 2
		| Erasable -> 1
		| Permanent th2 -> OrderedElemTheory.compare th1 th2
	    end
  end

module MarkTheoryMap = Ordered_maps.MakePoly (OrderedMarkTheory)


let add_a_var_to_a_sorted_map elem_pb var sorted_map =
  let mark_of_var = 
    try 
      VarMap.find var elem_pb.marked_variables
    with 
	Not_found -> No_mark in
    try 
      let same_mark_as_var = MarkTheoryMap.find mark_of_var sorted_map in
	MarkTheoryMap.add mark_of_var (var::same_mark_as_var) sorted_map
    with 
	Not_found -> MarkTheoryMap.add mark_of_var [var] sorted_map
  
let sort_vars_by_mark elem_pb set_of_vars =
  VarSet.fold (add_a_var_to_a_sorted_map elem_pb) 
    set_of_vars MarkTheoryMap.empty 


let number_and_list_of_sorted_vars elem_pb = 
  let set_of_vars = 
    List.fold_left
      (fun set (s,t) -> 
	 let s_vars = set_of_variables s
	 and t_vars = set_of_variables t in
	   VarSet.union s_vars (VarSet.union t_vars set))
      VarSet.empty elem_pb.equations in

  let sorted_vars = sort_vars_by_mark elem_pb set_of_vars in
  
  let ((n0,l0),(n1,l1),(ln,lv)) = 
    MarkTheoryMap.fold 
      (fun mark_th list_of_vars 
	 (no_mark,erasable,(lnb,lvrs as others)) ->
	   let n = List.length list_of_vars in
	     match mark_th with
		 No_mark -> ((n,list_of_vars),erasable,others)
	       | Erasable -> (no_mark,(n,list_of_vars),others)
	       | _ -> (no_mark,erasable,(n::lnb,(list_of_vars @ lvrs)))
      )
      sorted_vars ((0,[]),(0,[]),([],[])) in
    (n0 :: n1 :: ln, l0 @ l1 @ lv)

(*
  accumulation [|v0;v1;...;vn|] retourne [|v0;v0+v1;...;v0+v1+...+vn|].
*)

let accumulation v = 
  let v'= Array.copy v in
    for i=1 to (pred (Array.length v)) do
      v'.(i) <- v.(i) + v'.(pred i)
    done;
    v'


    
(*
  int_trivial teste si un vecteur representant les coefficients
  d'une equation a coefficients entiers code une equation triviale
*)

let is_trivial v = 
  try 
    for i=0 to (pred (Array.length v)) do
      if (v.(i) <> 0)
      then raise Exit
    done;
    true
  with Exit -> false


(*===================================================================

              Transformation d'une equation entre termes
                  en une equation sur les entiers

====================================================================*)

(*

   Les equations doivent etre de la forme 
   x1 + ... + xn = y1 + ... + ym
   ou les xi,yj sont egaux 
   soit a une variable, 
   soit a 0, 
   soit a -(v) ou v est une variable.

*)

let rec add_term th map_var_int eq_as_int_vect = function
    Var x -> 
      let index_of_x = VarMap.find x map_var_int in
	eq_as_int_vect.(index_of_x) <- succ eq_as_int_vect.(index_of_x)

  | Term (f,l) -> 
      if f = additive_symbol_of_theory th
      then List.iter (add_term th map_var_int eq_as_int_vect) l
      else 
	if f <> unit_symbol_of_theory th
	then 
	  if f = minus_symbol_of_theory th
	  then substract_term th map_var_int eq_as_int_vect (List.hd l)
	  else assert false

and substract_term th map_var_int eq_as_int_vect = function
    Var x -> 
      let index_of_x = VarMap.find x map_var_int in
	eq_as_int_vect.(index_of_x) <- pred eq_as_int_vect.(index_of_x)

  | Term (f,l) -> 
      if f = additive_symbol_of_theory th
      then List.iter (substract_term th map_var_int eq_as_int_vect) l
      else 
	if f <> unit_symbol_of_theory th
	then 
	  if f = minus_symbol_of_theory th
	  then add_term th map_var_int eq_as_int_vect (List.hd l)
	  else assert false



let eq_to_int_vect th nb_var map_var_int (s,t) =
  let eq = Array.create nb_var 0 in
  let _ = add_term th map_var_int eq s in
  let _ = substract_term th map_var_int eq t in
    eq

let unif_to_arith_without_matrix elem_pb =
  let (list_n,list_var) = number_and_list_of_sorted_vars elem_pb in
  let v_type = accumulation (Array.of_list list_n)
  and map_var_int = 
    let index = ref (-1) in
      List.fold_left
	(fun partial_map var ->
	   let _ = index := succ !index in
	     VarMap.add var !index partial_map)
	VarMap.empty
	list_var in
   (map_var_int,(Array.of_list list_var),v_type) 



let unif_to_arith elem_pb = 
  let (list_n,list_var) = number_and_list_of_sorted_vars elem_pb in
  let v_type = accumulation (Array.of_list list_n)
  and nb_var = List.length list_var 
  and map_var_int = 
    let index = ref (-1) in
      List.fold_left
	(fun partial_map var ->
	   let _ = index := succ !index in
	     VarMap.add var !index partial_map)
	VarMap.empty
	list_var in
  let vect_eq_int = 
    List.fold_left
      (fun res eq -> 
         let eq_as_int_vect = 
	   eq_to_int_vect elem_pb.elem_th nb_var map_var_int eq in
           if is_trivial eq_as_int_vect
           then res
           else Array.append res [|eq_as_int_vect|]) 
      [||] elem_pb.equations in
    (map_var_int,(Array.of_list list_var),v_type,vect_eq_int)
    


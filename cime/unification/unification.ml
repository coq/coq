(***************************************************************************

Unification modulo some predefined theories

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Variables
open Gen_terms
open Theory
open E_res
open Cycle
open Mark
open Eqe
open Controle

(*

  [set_of_unifiers S E term1 term2] returns a complete set of unifiers
  of [term1] and [term2] modulo the equational theory [E], where [S]
  is the signature over which [term1] and [term2] are built. [E] may
  be any combination of some elementary theories among
  \begin{itemize}
  \item the free theory
  \item C 
  \item AC
  \item ACU
  \item ACI
  \item AG
  \item ACUN
  \item BR
  \end{itemize}
  provided that they are pairwise signature-disjoint.
*)

let verbose = ref 0

let set_of_solutions unif_k s (*i vars i*) find_th t1 t2 = 
  try
    let starting_pb = Problems.init unif_k s find_th t1 t2 in
    let disj_of_solved_forms = 
      repeat
	(orelse (orelse (general_E_resolution s (*i vars i*)) mark) (cycle s (*i varsi*) )) 
	starting_pb in
    let disj_of_cleaned_solved_forms =
      List.map existential_quantifiers_elimination disj_of_solved_forms in
      
      List.map
	(function cleaned_solved_form ->
	   List.fold_left
	     (fun partial_substitution eq ->
		match eq with
		    Var x, t -> VarMap.add x t partial_substitution
		  | _, _ -> assert false)
	     VarMap.empty cleaned_solved_form)
	disj_of_cleaned_solved_forms

  with No_solution -> []

let plain_set_of_solutions sigma th (*i vars i*) t1 t2 =
  let find_th f = 
    let th_of_f = 
      try 
	TheorySet.find
	  (function
	     | ACU(g,u) -> f=g or f=u
	     | ACI(g) -> f=g
	     | ACUN(g,u,_) -> f=g or f=u
	     | AG(p,u,m) -> f=p or f=u or f=m
	     | BR(g,h,i,j) -> f=g or f=h or f=i or f=j
	     | _ -> assert false)
	  th
      with 
	  Not_found ->
	    if sigma#is_ac f
	    then AC(f)
	    else 
	      if sigma#is_commutative f
	      then C(f)
	      else Empty (None) in

      (None,th_of_f) in
  
    set_of_solutions PLAIN sigma (*i vars i*) find_th t1 t2

let display_plain_set_of_solutions sigma th vars t1 t2 =
  let sols = 
    plain_set_of_solutions 
      (sigma :> 'symbol Signatures.signature) th (*i vars i*) t1 t2 in
    Format.print_int (List.length sols);
    Format.print_string " solution(s)";
    Format.print_newline();
    if !verbose > 1
    then 
      begin
	let n = ref 1 in
	  List.iter 
	    (fun sol ->
	       Format.print_string "-----";
	       Format.print_int !n;
	       n := succ !n;
	       Format.print_string "-----";
	       Format.print_newline();
	       Format.print_flush ();
	       if sol = Variables.VarMap.empty
	       then 
		 begin
		   Format.print_string "{}";
		   Format.print_newline()
		 end
	       else Substitution.print sigma vars sol;
	       Format.print_flush ())
	    sols;
	  Format.print_string "-----------";
	  Format.print_newline();
	  Format.print_flush ()
      end


let has_a_solution s th t1 t2 = assert false

let free_unification sigma (*i vars i*) t1 t2 =
  let sol = Unif_free.solve_without_marks sigma (*i vars i*) [t1,t2] in
    List.fold_left
      (fun partial_substitution eq ->
	 match eq with
	     Var x, t -> VarMap.add x t partial_substitution
	   | t, Var x -> VarMap.add x t partial_substitution
	   | _,_ -> assert false)
      VarMap.empty sol

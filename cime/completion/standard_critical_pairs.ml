(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Positions
open Gen_terms
open Rewrite_rules
open Controle
open Unification

let head_critical_pair sign (*i vars i*) rule1 rule2 =
  let lhs1 = leftify_term rule1.lhs
  and lhs2 = rightify_term rule2.lhs in
    try
      let sigma = free_unification sign (*i vars i*) lhs1 lhs2 in
	(Substitution.apply_term (leftify_term rule1.rhs) sigma,
	 Substitution.apply_term (rightify_term rule2.rhs) sigma)
    with
	No_solution -> raise No_solution

let deep_critical_pairs sign (*i vars i*) rule1 (* l -> r *) rule2 (* g -> d *) =
  let lhs1 = leftify_term rule1.lhs
  and rhs1 = leftify_term rule1.rhs
  and lhs2 = rightify_term rule2.lhs 
  and rhs2 = rightify_term rule2.rhs in
  let rec rec_deep_cp p sub_term_rule1 (* l|_p *) = 
    match sub_term_rule1 with
	Var _ -> []
      | Term(_,l) -> 
	  Listutils.flat_mapi
	    (fun i ti -> match ti with
		 Var _ -> []
	       | Term _ -> 
		   let pi = build_pos p i in
		   let deeper_cps =
		     rec_deep_cp pi ti in
		     try
		       let current_unifier = 
			 free_unification sign (*i vars i*) 
			   ti (* l|_{p.i} *) lhs2 (* d *) in
		       let rule1_lhs_with_rule2_rhs_at_pos_pi =
			 replace_subterm_at_position_in_term 
			   rhs2 pi lhs1 in
		       let current_cp =
			 (Substitution.apply_term 
			    rule1_lhs_with_rule2_rhs_at_pos_pi current_unifier,
			    Substitution.apply_term rhs1 current_unifier) in
		     
			 current_cp :: deeper_cps
		     with No_solution -> deeper_cps)
	    l in
    
    rec_deep_cp Top lhs1

let critical_pairs sign (*i vars i*) rule1 rule2 =
  let deep_cps = (deep_critical_pairs sign (*i vars i*) rule1 rule2) @ 
		 (deep_critical_pairs sign (*i vars i*) rule2 rule1) in
  try
    let head_cp = head_critical_pair sign (*i vars i*) rule1 rule2 in
    head_cp :: deep_cps
  with 
      No_solution -> deep_cps
	

let self_critical_pairs sign (*i vars i*) rule =
  deep_critical_pairs sign (*i vars i*) rule rule 
    

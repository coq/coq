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

let head_critical_pairs sign lhs1 rhs1 lhs2 rhs2 =
  let unifiers = 
    Ac_unification.set_of_solutions sign lhs1 lhs2 
  in
  List.map
    (fun sigma ->
       (Substitution.substitute sign sigma rhs1,
	Substitution.substitute sign sigma rhs2))
    unifiers
;;

let deep_critical_pairs sign lhs1 rhs1 lhs2 rhs2 =
  let rec rec_deep_cp p sub_term_rule1 (* l|_p *) = 
    match sub_term_rule1 with
	Var _ -> []
      | Term(_,l) -> 
	  Listutils.flat_mapi
	    (fun i ti -> match ti with
		 Var _ -> []
	       | Term _ -> 
		   let pi = build_pos p i in
		   let deeper_cps = rec_deep_cp pi ti in
		   let unifiers = 
		     Ac_unification.set_of_solutions sign 
		       ti (* l|_{p.i} *) lhs2 (* d *) 
		   in
		   let new_pairs =
		     List.map 
		       (fun sigma ->
			  let rule1_lhs_with_rule2_rhs_at_pos_pi =
			    replace_subterm_at_position_in_term 
			      rhs2 pi lhs1 
			  in
			  (Substitution.substitute 
			     sign sigma
			     rule1_lhs_with_rule2_rhs_at_pos_pi,
			     Substitution.substitute sign sigma rhs1))
		       unifiers
		   in
		   new_pairs @ deeper_cps)
	    l 
  in
    rec_deep_cp Top lhs1

let critical_pairs sign rule1 rule2 =
  let lhs1 = leftify_term rule1.lhs
  and rhs1 = leftify_term rule1.rhs
  and lhs2 = rightify_term rule2.lhs 
  and rhs2 = rightify_term rule2.rhs 
  in
  (deep_critical_pairs sign lhs1 rhs1 lhs2 rhs2) @ 
  (deep_critical_pairs sign lhs2 rhs2 lhs1 rhs1) @
  (head_critical_pairs sign lhs1 rhs1 lhs2 rhs2) @
  (match rule1.ext,rule2.ext with 
     | None,None -> [] 
     | Some(elhs1,erhs1),None -> 
	 let elhs1 = leftify_term elhs1
	 and erhs1 = leftify_term erhs1
	 in
	 (deep_critical_pairs sign elhs1 erhs1 lhs2 rhs2) @ 
	 (deep_critical_pairs sign lhs2 rhs2 elhs1 erhs1) @
	 (head_critical_pairs sign elhs1 erhs1 lhs2 rhs2) 
     | None,Some(elhs2,erhs2) -> 
	 let elhs2 = rightify_term elhs2
	 and erhs2 = rightify_term erhs2
	 in
	 (deep_critical_pairs sign lhs1 rhs1 elhs2 erhs2) @ 
	 (deep_critical_pairs sign elhs2 erhs2 lhs1 rhs1) @
	 (head_critical_pairs sign lhs1 rhs1 elhs2 erhs2) 
     | Some(elhs1,erhs1),Some(elhs2,erhs2) -> 
	 let elhs1 = leftify_term elhs1
	 and erhs1 = leftify_term erhs1
	 and elhs2 = rightify_term elhs2
	 and erhs2 = rightify_term erhs2
	 in
	 (deep_critical_pairs sign elhs1 erhs1 lhs2 rhs2) @ 
	 (deep_critical_pairs sign lhs2 rhs2 elhs1 erhs1) @
	 (head_critical_pairs sign elhs1 erhs1 lhs2 rhs2) @
	 (deep_critical_pairs sign lhs1 rhs1 elhs2 erhs2) @ 
	 (deep_critical_pairs sign elhs2 erhs2 lhs1 rhs1) @
	 (head_critical_pairs sign lhs1 rhs1 elhs2 erhs2) @
	 (deep_critical_pairs sign elhs1 erhs1 elhs2 erhs2) @
	 (deep_critical_pairs sign elhs2 erhs2 elhs1 erhs1) @
	 (head_critical_pairs sign elhs1 erhs1 elhs2 erhs2))

let self_critical_pairs sign rule =
  let lhs1 = leftify_term rule.lhs
  and rhs1 = leftify_term rule.rhs
  and lhs2 = rightify_term rule.lhs
  and rhs2 = rightify_term rule.rhs
  in
  (deep_critical_pairs sign lhs1 rhs1 lhs2 rhs2) @
  (head_critical_pairs sign lhs1 rhs1 lhs2 rhs2) @
  (match rule.ext with
     | None -> []
     | Some(elhs,erhs) ->
	 let elhs1 = leftify_term elhs
	 and erhs1 = leftify_term erhs
	 and elhs2 = rightify_term elhs
	 and erhs2 = rightify_term erhs
	 in
	 (deep_critical_pairs sign elhs1 erhs1 lhs2 rhs2) @
	 (deep_critical_pairs sign lhs1 rhs1 elhs2 erhs2) @
	 (deep_critical_pairs sign elhs1 erhs1 elhs2 erhs2) @
	 (head_critical_pairs sign lhs1 rhs1 elhs2 erhs2) @
	 (head_critical_pairs sign elhs1 erhs1 elhs2 erhs2))
    









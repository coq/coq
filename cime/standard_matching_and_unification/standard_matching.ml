(***************************************************************************

Standard matching

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



open Gen_terms


(* [(match pattern subject)] returns the most general filter of
  [subject] over [pattern]. Raises No_match if no math is found.

   This is standard matching : all symbols are assumed to be free.

*)

exception No_match;;


let rec matching patt subj = 
  match patt with
      Var x ->  Variables.VarMap.add x subj Variables.VarMap.empty
    | Term(f,l) ->
	match subj with
	    Var _ -> raise No_match
	  | Term(g,m) ->
	      if f=g
	      then
		try
		  List.fold_right2 
		    (fun pat1 sub1 subst ->
		       Substitution.merge_substs (matching pat1 sub1) subst)
		    l m Variables.VarMap.empty
		with 
		    Invalid_argument _ -> raise No_match
		  | Substitution.Conflict -> raise No_match

	      else raise No_match
;;









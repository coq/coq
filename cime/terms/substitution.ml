(***************************************************************************

Standard substitutions

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



open Gen_terms
open Rewrite_rules
open Format


type 'symbol substitution = (unit,'symbol term) Variables.VarMap.t;;

(* 

   [(merge_subst subst1 subst2)] merges substitutions [subst1] and
   [subst2], that is put them together verifying that if [subst1]
   binds a variable $x$ to a term $t_1$ and [subst2] binds the same
   variable to $t_2$, then $t_1=t_2$

   Raises Conflict if not.

   This is standard substitution merging: equality of $t_1$ and $t_2$
   is performed assuming that all symbols are free.

*)

exception Conflict;;


let rec merge_substs s1 s2 = 
  Variables.VarMap.fold
    (fun x t subst ->
       try
	 let t' = Variables.VarMap.find x subst
	 in
	   if t=t'
	   then subst
	   else raise Conflict
       with
	   Not_found ->
	     Variables.VarMap.add x t subst)
    s1 s2


let rec apply_term t sigma = 
  match t with 
      Term(f,l) -> Term(f,List.map (function t -> apply_term t sigma) l )
    | Var(x) -> 
	try 
	  Variables.VarMap.find x sigma
	with
	    Not_found -> t

let apply_rewrite_rule sign r sigma = 
  let r_lhs_sigma = apply_term r.lhs sigma
  and r_rhs_sigma = apply_term r.rhs sigma in
  {
    lhs= r_lhs_sigma;
    rhs= r_rhs_sigma;
    ext= 
     begin
       match r.ext with 
	   None -> None
	 | Some(t1,t2) -> Some(apply_term t1 sigma , apply_term t2 sigma)
     end;
    is_or = r.is_or;
    nb = r.nb
  }


let rec substitute signature sigma t = 
  match t with
      Var id as x -> 
	begin
	  try 
	    Variables.VarMap.find id sigma
	  with Not_found -> x
	end
    | Term (f,l) -> 
	if signature#is_ac f 
	then
	  let reverted_list_of_substituted_subterms = 
	    List.fold_left
	      (fun acc x -> 
		 let x_sigma = substitute signature sigma x in
		   begin
		     match x_sigma with 
			 Term (s,l2) -> 
			   if s = f then l2 @ acc else x_sigma :: acc
		       | Var _ -> x_sigma::acc
		   end)
	      [] l in
	  Term(f, List.rev reverted_list_of_substituted_subterms)
	else Term(f, List.map (substitute signature sigma) l)
;;

let apply_subst_to_eqs signature sigma list_of_equations = 
  List.map
    (function (s,t) -> 
       (substitute signature sigma s, substitute signature sigma t))
    list_of_equations


let print sigma vars s =
  Variables.VarMap.iter 
    (fun x t ->
       print_string (vars#string_of_var x);
       print_string " -> ";
       Gen_terms.print_term sigma vars t;
       print_newline();
    )
    s

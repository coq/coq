(***************************************************************************

Module defining rewrite rules.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Gen_terms;;
open Variables;;


(*

the type rewrite_rule, defined by the lefthand side, the righthand
side, and optionally the lhs and the rhs of the AC-extension. 

*)

type 'symbol rewrite_rule = 
    {
      lhs : 'symbol term;
      rhs : 'symbol term;
      ext : ('symbol term * 'symbol term) option;
      is_or : bool;
      nb : int;
    }
;;


(*

  printing functions

*)

open Format;;

let print_rewrite_rule sigma vars r =
  printf "@[<hov>";
  print_term sigma vars r.lhs;
  if r.is_or
  then printf "@ ->@ "
  else printf "@ <->@ ";
  print_term sigma vars r.rhs;
  printf "@]"
;;


let print_rewrite_rule_set sigma vars = function
   []   -> (print_string "{}")
 | r::l ->
   let rec print_end_list n = function
       [] -> 
	 begin
           print_string " }";
           print_break 1 0;
           print_string "(";
           print_int n;
           print_string " rules)"                 
	 end
     | (r::l) -> 
	 begin
           print_string  ",";
           force_newline ();
           print_rewrite_rule sigma vars r;
           print_end_list (succ n) l
         end
   in 
     begin
       print_string "{ ";
       open_hovbox 0;
       print_rewrite_rule sigma vars r;
       print_end_list 1 l;
       close_box ()
     end
;;


(*

  auxiliary functions for checking whether a rewrite rule needs to
  extended or not. A rule needs to be AC-extended if :

  1) the root symbol f of the lhs l is AC
  2) there is no variable x in l such that :
    1.1) x occurs once in l, at depth 1
    1.2) the rhs is either x, or of the form f(x,r) where x does not occur in r

*)


(*

  [(increment_occ x m) increments by one the number associated to [x]
  in the map [m]

*)

let increment_occ x m = 
  try
    let n = VarMap.find x m
    in VarMap.add x (succ n) m
  with
      Not_found ->
	VarMap.add x 1 m
;;

(*

  [(increment_occurences m t)] increments the numbers of the var map
  [m] by the number of occurrences of variables in [t]

*)

 
let rec increment_occurences m = function
    Var(x) -> increment_occ x m
  | Term(_,l)  -> 
      List.fold_left increment_occurences m l
;;
  
(*

  [(scan_for_variables l)] scans the list of terms [l] and returns a
  pair [(x,m)] where [x] is the list of variables occuring in [l] (but
  not inside a term in [l]), and [m] is a map giving for each
  variables occuring in l (even inside a term in [l]) the number of
  its occurences

*)

let rec scan_for_variables = function
    [] -> ([],VarMap.empty)
  | s::l -> 
      let (v,m) = scan_for_variables l 
      in
     	match s with
            Var(x) -> 
	      if List.mem x v 
              then v,(increment_occ x m)
              else x::v,(increment_occ x m)
	  | _  ->  v,(increment_occurences m s)
;;

(*

  [(look_for_a_linear_variables m l)] returns the sublist of variables
  x in the list [l] such that the number associated to x in the map
  [m] is 1

*)

let look_for_linear_variables m l = 
  List.filter
    (function x -> 
       try
	 VarMap.find x m = 1
       with
	   Not_found -> false)
    l
;;


let rule_need_extension sigma lhs rhs =
  match lhs with
      Var(_) -> failwith "the left-hand side of a rule cannot be a variable"
    | Term(f,l) ->
    	if sigma#is_ac f
    	then 
	  let (vars_at_depth_1,var_occurences) = scan_for_variables l in
      	  let possible_vars = 
	    look_for_linear_variables var_occurences vars_at_depth_1 in
	    match rhs with
		Var(x) -> not (List.mem x possible_vars)
	      | Term(f',l') ->
		  if f=f'
		  then 
		    let (vars_at_depth_1',var_occurences') = 
		      scan_for_variables l' in
		    let possible_vars' = 
		      look_for_linear_variables 
			var_occurences' vars_at_depth_1'
		    in Listutils.intersect possible_vars possible_vars' = []
		  else true
	else false
;;

(*

[(make_rule l r)] builds a rewrite with lefthand side [l] and
righthand side [r]. Determines whether the rule needs to be
AC-extended.

*)


let make_numbered_rule_or_eq n o sigma l r = 
  (*
    let v = new user_variables ["x"]
    in
    print_string " Regle a fabriquer : ";
    Gen_terms.print_term sigma v l;
    print_string " -> ";
    Gen_terms.print_term sigma v r;
    print_newline();
  *)
  if rule_need_extension sigma l r
  then 
    begin
    (*
      print_string " Besoin d'extension ";
      print_newline();
    *)
    let x = Var(var_outside_set (set_of_variables l))
    in
      match l with
	  Var _ -> 
	    failwith "the left-hand side of a rule cannot be a variable"
    	| Term(f,ll) ->
	    let ext = Term(f,x::ll),head_flatten_term sigma (Term(f,[x;r])) in
	      {
      		lhs = l;
      		rhs = r;
      		ext = Some ext;
		is_or = o;
		nb = n
	      }
    end
  else 
    begin
(*
    print_string " Pas besoin d'extension ";
    print_newline();
*)
    {
      lhs = l;
      rhs = r;
      ext = None;
      is_or = o;
      nb = n
    }
    end
;;

let make_numbered_rule n sigma l r = 
  make_numbered_rule_or_eq n true sigma l r;;

let make_rule sigma l r = 
  make_numbered_rule_or_eq 0 true sigma l r;;

let make_non_oriented_numbered_rule n sigma l r =  
  make_numbered_rule_or_eq n false sigma l r;;

let make_non_oriented_rule sigma l r = 
  make_numbered_rule_or_eq 0 false sigma l r;;

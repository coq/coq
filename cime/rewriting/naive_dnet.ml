(***************************************************************************

Discrimination nets in a naive way: non linearity is not handled,
subterms whose top is a non-free symbol are considered.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Gen_terms;;
open Rewrite_rules;;

type 'a tagged_rule = int * 'a rewrite_rule

module TaggedRules =
  Inttagset.MakePoly
    (struct 
       type 'a t = 'a tagged_rule
       let tag = fst 
     end)


type 'a ruleset = 'a TaggedRules.t

(*i
let print_rule_set s =
  Format.printf "{";
  TaggedRules.iter (fun (n,_) -> Format.printf "%d," n) s;
  Format.printf "}@.";
  s
;;
i*)
  
type 'symbol dnet =
    {
      var_match : 'symbol ruleset;
      switch : ('symbol * 'symbol case) list;
    }
and 'symbol case =
  | Constant of 'symbol ruleset
  | Arguments of 'symbol dnet list (* always non-empty list *)
;;

let rec do_discriminate net t =
    match t with
      | Var _ -> net.var_match
      | Term(f,l) ->
	  try 
	    let c = List.assoc f net.switch in
	    match c,l with
	      | Constant(e),_ -> 
		  (*i
		    Format.printf "node C: ";
		    print_rule_set (
		    i*)
		  TaggedRules.union e net.var_match
		    (*i ) i*)
	      | Arguments(net1::netlist),arg1::arglist ->
		  let e =
		    List.fold_left2
		      (fun accu net arg ->
			 let discr = do_discriminate net arg in
			 TaggedRules.inter accu discr)
		      (do_discriminate net1 arg1)
		      netlist arglist
		  in
		  (*i
		    Format.printf "node N: inter = ";
		    let _ = print_rule_set e in
		    Format.printf "node N: union = ";
		    print_rule_set (
		    i*)
		  TaggedRules.union e net.var_match
		    (*i ) i*)
	      | _ -> assert false
		    
	  with
	      Not_found -> net.var_match
;;

let discriminate net t =
  let ruleset = do_discriminate net t in
  TaggedRules.fold (fun (_,r) accu -> r::accu) ruleset []
;;


let rec add_multiassoc_list key data list =
  match list with
    | [] -> [(key,[data])]
    | (x,d)::l ->
	if x=key 
	then (x,data::d)::l
	else (x,d)::(add_multiassoc_list key data l)
;;

(*

  [(transpose_aux x [y1;..;yk] [l1;..;lk])] returns
  [[(x,y1)::l1;..;(x,yk)::lk]]

*)

let rec transpose_aux x y l =
  match (y,l) with
    | [],[] -> []
    | (y1::y),(l1::l) -> ((x,y1)::l1)::(transpose_aux x y l)
    | _ -> assert false
;;

(*

  [(transpose [(x1,[y11;..;y1n]);..;(xk,[yk1;..;ykn])])] returns
  [[[(x1,y11);..;(xk,yk1)];..;[(x1,y1n);..;(xk,ykn)]]]

*)

let rec transpose l = match l with
  | [] -> assert false
  | [(x,y)] -> List.map (fun y -> [(x,y)]) y
  | (x,y)::l -> 
      transpose_aux x y (transpose l)
;;



let compile sigma r = 
  let n = ref 0 in
  let init_rules_terms =
    List.fold_left
      (fun accu r -> incr n; ((!n,r),r.lhs)::accu)
      []
      r
  in
  let rec do_compile rules_terms =
    let (var_match,cases) =
      List.fold_left
	(fun (v,c) (r,t) ->
	   match t with
	     | Var _ -> (TaggedRules.add r v,c)
	     | Term(f,l) ->
		 (v,add_multiassoc_list f (r,l) c))
	(TaggedRules.empty,[])
	rules_terms
    in
    let switch =
      List.fold_left
	(fun accu (f,rules_terms_list) ->
	   let case =
	     if not (sigma#is_free f) or sigma#arity f = 0
	     then 
	       let ruleset =
		 List.fold_left
		   (fun accu (r,_) -> TaggedRules.add r accu)
		   TaggedRules.empty
		   rules_terms_list
	       in
	       Constant(ruleset)
	     else
	       let netlist = 
		 List.map do_compile (transpose rules_terms_list)
	       in
	       Arguments(netlist)
	   in
	   (f,case)::accu
	)
	[]
	cases
    in
    {
      var_match = var_match;
      switch = switch
    }
  in
  do_compile init_rules_terms
;;

       





open Format;;


let print_set s = 
  printf "{";
  TaggedRules.iter (fun (n,_) -> printf "%d," n) s;
  printf "}"
;;

let rec print sigma d =
  printf "var_match = ";
  print_set d.var_match;
  printf "@,switch = ";
  printf "@[<v 2>";
  List.iter 
    (fun (f,l) ->
       printf "%s -> " (sigma#string_of_symbol f);
       match l with
	 | Constant(e) -> 
	     printf "C(";
	     print_set e;
	     printf ")@,"
	 | Arguments(l) ->
	     printf "@[<v 2>N@ ";
	     List.iter (print sigma) l;
	     printf "@,@]@,")
    d.switch;
  printf "@,@]@,"
;;


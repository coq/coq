(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Util
open Names

open General
open Dpctypes
open Subst
open Unif
open Graph

(* Herbrand form *************)

let h_fun v ex f = 
  let lt = List.map (fun x -> VAR(x)) ex
  in subst v (APP (GLOB (SK v)::lt)) f

let free_her fv f = 
  let rec fh_rec f = function
       v::ll -> let f0 = subst v (APP [GLOB (SK v)]) f
                in fh_rec f0 ll
     | [] -> f
  in fh_rec f fv

let herbrand f = 
  let rec h_rec ex sign f = match f with
      ForAll(v,f1) -> if sign then (h_rec ex sign (h_fun v ex f1))
      	       	       	      else (h_rec (v::ex) sign f1)
    | Exists(v,f1) -> if sign then (h_rec (v::ex) sign f1)
      	       	       	      else (h_rec ex sign (h_fun v ex f1))
    | Neg(f1) -> let (e,h) = (h_rec ex ((not (sign))) f1)
                 in (e , Neg h)
    | Atom(s,lt) -> (ex,Atom(s,lt))
    | Imp(f1,f2) -> (let (ex1,h1) = (h_rec ex ((not (sign))) f1)
      	       	     and (ex2,h2) = (h_rec ex sign f2)
		     in (union ex1 ex2,Imp(h1,h2)))
    | Conj(f1,f2) -> (let (ex1,h1) = (h_rec ex sign f1)
      	       	      and (ex2,h2) = (h_rec ex sign f2)
		      in (union ex1 ex2,Conj(h1,h2)))
    | Disj(f1,f2) -> (let (ex1,h1) = (h_rec ex sign f1)
      	       	      and (ex2,h2) = (h_rec ex sign f2)
		      in (union ex1 ex2,Disj(h1,h2)))
  in let (ex,f0) = h_rec [] true f
  in let fv = free_var_formula f
  in (ex,free_her fv f0)

let separate f = 
  let n = ref 0 
  in let rec sep_rec f = match f with
       Atom((s,0),lt) -> n := !n+1;
       	       	     Atom((s,!n),lt)
     | Atom((s,_),_) -> anomaly "separate"
     | Neg(f1) -> Neg(sep_rec f1)
     | ForAll(s,f1) -> ForAll(s,sep_rec f1)
     | Exists(s,f1) -> Exists(s,sep_rec f1)
     | Imp(f1,f2)-> Imp(sep_rec f1,sep_rec f2)
     | Conj(f1,f2) -> Conj(sep_rec f1,sep_rec f2)
     | Disj(f1,f2) -> Disj(sep_rec f1,sep_rec f2)
  in sep_rec f

(* Searching for paths... *********)

let lit_conj f =  
  let rec lc_rec sign = function
      Atom(_,_) as a -> if sign then ([a],[],[]) else ([],[a],[])
    | Neg(f1) -> lc_rec ((not (sign))) f1
    | Conj(f1,f2) -> let (p1,n1,c1) = lc_rec sign f1
      	       	     and (p2,n2,c2) = lc_rec sign f2
		     in let c = if sign then [((f1,f2),(p1@n1,p2@n2))]
		                        else []
		     in (p1@p2,n1@n2,c@c1@c2)
    | Disj(f1,f2) -> let (p1,n1,c1) = lc_rec sign f1
      	       	     and (p2,n2,c2) = lc_rec sign f2
		     in let c = if sign then []
		                        else [((f1,f2),(p1@n1,p2@n2))]
		     in (p1@p2,n1@n2,c@c1@c2)
    | Imp(f1,f2) -> let (p1,n1,c1) = lc_rec ((not (sign))) f1
      	       	    and (p2,n2,c2) = lc_rec sign f2
		    in let c = if sign then []
		                       else [((f1,f2),(p1@n1,p2@n2))]
		    in (p1@p2,n1@n2,c@c1@c2)
    | _ -> raise Impossible_case
  in lc_rec true f


(* Finding all matches ********)

let mb p q =
  let rec mb_rec = function
      (_,(lf1,lf2))::ll -> ((not((  ((List.mem p lf1) & (List.mem q lf2))
      	       	       	      or ((List.mem q lf1) & (List.mem p lf2))))) )
			   & (mb_rec ll)
    | [] -> true
  in mb_rec


let all_matches pos neg lcj = 
  let rec all_matches_p (x,y) = function
      ((Atom (x_0,x_1)) as q::neg1) -> 
             let lm = try [((Atom (x,y)),q,unif_atoms (x,y) (x_0,x_1))] 
                      with Not_unifiable -> []
             in if mb (Atom (x,y)) q lcj then lm@(all_matches_p (x,y) neg1)
		                      else (all_matches_p (x,y) neg1)
    | _ -> []
  and all_matches_rec  = function
      ((Atom (x_0,x_1))::pos1) -> (all_matches_p (x_0,x_1) neg)@(all_matches_rec pos1)
    | _ -> []
  in all_matches_rec pos

(* combine_path P L : returns the least path containing all the matches
      	       	      in P and L. If no such path exists, it raises
		      CP_error *********)

exception CP_error

let rec lit_unicity = function
    (p::ll) -> if List.mem p ll then false else lit_unicity ll
  | [] -> true

let combine_path (m1,u1) (m2,u2) =
     let lm  = union m1 m2
  in let llt = List.map (fun (p,q,_) -> [p;q]) lm
  in let lt  = List.flatten llt
  in if lit_unicity lt 
     then let u = try up u1 u2 with Up_error -> raise CP_error
          in (lm , u)
     else raise CP_error

(* lit_in_matches : formula list -> (match list) -> bool *****)

let lit_in_matches lF ml = 
  let rec lim_rec  = function
      ((p,q,_)::mmll) -> if (List.mem p lF) or (List.mem q lF)
      	       	       	 then true
			 else lim_rec mmll
    | [] -> false
  in lim_rec ml

(* 16.III.94 *********)
(* Simple Depth First Search (p.138) *******)
(* NB : path = match list * unifier ********)

let rec matches_pos p = function
    ((p1,q,u) as m::mM) -> if p=p1 
      	       	       	   then [([m] , u)]@(matches_pos p mM)
			   else matches_pos p mM
  | [] -> [] 

let rec matches_neg q = function
    ((p,q1,u) as m::mM) -> if q=q1 
      	       	       	   then [([m] , u)]@(matches_neg q mM)
      	       	       	   else matches_neg q mM
  | [] -> [] 

let uncovered (ml,_) lcj = 
  let rec uncov_rec = function
      (((f1,f2),(lf1,lf2))::llccjj) ->
       	  let sat1 = lit_in_matches lf1 ml
       in let sat2 = lit_in_matches lf2 ml 
       in if sat1 & ((not (sat2)))
	  then (f2,lf2)::(uncov_rec llccjj)
	  else if sat2 & ((not (sat1)))
	       then (f1,lf1)::(uncov_rec llccjj)
	       else (uncov_rec llccjj)
    | [] -> []
  in uncov_rec lcj

let paths pos neg m lcj =
  let rec paths_rec = function
      ((_,_,u) as m_0::mM) -> (extend ([m_0],u))@(paths_rec mM)
    | [] -> []
  and extension p (f1,lf1) =
       let lm  = glue (List.map (fun x -> if List.mem x pos
      	                             then matches_pos x m
				     else matches_neg x m) lf1)
    in let rec ext_rec = function
         (l::ll) ->( try (combine_path p l)::(ext_rec ll)
	             with CP_error -> ext_rec ll
		   )
       | [] -> []
    in ext_rec lm
  and extend p = 
       let uc = uncovered p lcj
    in if uc = [] 
       then [p]
       else glue (List.map (fun x -> (glue (List.map extend (extension p x)))) uc)
  in paths_rec m

(* Dealing with cycles... ******)

let conj_graph lm lc lt =
  let rec nb_of_x = function
      (p::lpp) -> (try let q = List.assoc p lm in q::(nb_of_x lpp)
                   with Not_found -> nb_of_x lpp)
    | [] -> []
  and nb_rec x = function
      ((l1,l2)::lcc) -> 
          if List.mem x l1 
	  then (nb_of_x l2)@(nb_rec x lcc)
	  else if List.mem x l2 
	       then (nb_of_x l1)@(nb_rec x lcc)
	       else nb_rec x lcc
    | [] -> []
  and conj_graph_rec = function
      (p::ll) -> (p,nb_rec p lc)::(conj_graph_rec ll)
    | [] -> []
  in conj_graph_rec lt

let is_cyclic_path lcj (lmu,u) = 
     let lm = List.flatten (List.map (fun (p,q,_) -> [(p,q);(q,p)]) lmu)
  in let lc = List.map (fun (_,pl) -> pl) lcj
  in let lt = List.map (fun (p,_) -> p) lm
  in let g  = conj_graph lm lc lt
  in have_cycle g

let good_paths lcj lp = 
  let rec good_paths_rec = function
      (p::pp) -> if is_cyclic_path lcj p 
               then good_paths_rec pp
	       else p::(good_paths_rec pp)
    | [] -> []
  in good_paths_rec lp




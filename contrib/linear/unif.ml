(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

          (* UNIFICATION : Martelli & Montanari's algorithm *)
          (* ---------------------------------------------- *)

(* Terms are of the type :
 *     type term = Var of identifier
 *		 | Glob of constname
 * 		 | App of term list
 *     
 * Unification of two atomic formulae :
 *     unif_atoms : atom_id * term list -> atom_id * term list 
 *                  -> (term*term) list  
 *
 *  Unification of two terms :
 *     unif_terms : term -> term -> (term*term) list
 *
 *)

open Nameops
open General
open Dpctypes
open Subst

exception Not_unifiable
exception Up_error

let rec vars_of_list l = match l with
    t::ll -> let vll = vars_of_list ll
      	       in let vt = vars_of_term t
	       in union vt vll
  | []    -> []
and vars_of_term t = match t with
      VAR x  -> [VAR(x)]
    | GLOB _ -> []
    | APP lt -> vars_of_list lt

let rec nb_occ_term x t = match t with
    VAR y  -> if x=VAR(y) then 1 else 0
  | APP lt -> nb_occ_list x lt
  | _      -> 0
and nb_occ_list x l = match l with
    t::ll -> (nb_occ_term x t)+(nb_occ_list x ll)
  | []    -> 0

let cpt = ref 0

let w_atom = "-"

let new_id () = 
  cpt := !cpt+1;
  make_ident w_atom (Some !cpt)
 
let rec initU l1 l2 = match (l1,l2) with
     ((a1::ll1),(a2::ll2)) -> let w = new_id()
       	       	       	      in let equ = ([VAR w],[a1; a2])
			      in equ::(initU ll1 ll2)
   | ([],[]) -> []
   | _ -> raise Impossible_case

let initT l1 l2 =
  let lt =l1@l2
  in List.map (fun x -> ([x],[])) (vars_of_list lt)
  
let rec cF (t1,t2) = match t1 with 
    VAR(x1) -> 
      	(match t2 with
	    VAR _ -> ([t1] , [([t1; t2],[])])
	  | _     -> ([] , [([t1],[t2])])
      	)
  | GLOB _ -> (match t2 with
                 GLOB _ -> if t1=t2 then ([t1] , []) else raise Not_unifiable
	       | VAR _  -> ([] , [([t2],[t1])])
	       | _      -> raise Not_unifiable)
  | APP lt1 -> 
      	(match t2 with
	    VAR _   -> ([] , [([t2],[t1])])
	  | GLOB _  -> raise Not_unifiable
      	  | APP lt2 -> 
      	       if (List.length lt1)=(List.length lt2)
	       then    let lcf = List.map cF (List.combine lt1 lt2)
		    in let lc  = List.map (function ([x],_) -> x
		                        | ([],e) -> List.hd (fst (List.hd e))
      	       	       	       	       	| _ -> failwith "Imp.CF") lcf
		    in let llf = List.map (fun (_,x) -> x) lcf
		    in  ([APP lc] , glue llf)
	       else raise Not_unifiable
	)

let assocT x t =
  let rec assocT_rec = function 
      ((lv , _) as equ::tT) -> if List.mem x lv then equ
      	       	       	       	       	   else assocT_rec tT
    | [] -> raise Not_found
  in assocT_rec t					     

let rec sub_elem_list x = function
    (a::l) -> if a=x then l else a::(sub_elem_list x l)
  | [] -> []

let newUT1 x1 x2 u t = 
     let (lv1,lt1) as equ1 = assocT x1 t
  in let (lv2,lt2) as equ2 = assocT x2 t	
  in let nT = sub_elem_list equ1 (sub_elem_list equ2 t)
  in if equ1=equ2 
     then (u , t)
     else    if lt1=[] or lt2=[] 
      	     then (u , (lv1@lv2 , lt1@lt2)::nT)
	     else let t1 = List.hd lt1 and t2 = List.hd lt2 
		  in let (c,f) = cF (t1,t2)
		  in (f@u , (lv1@lv2 , c)::nT) 

let newUT2 x1 t1 u t =
     let (lv1,lt1) as equ1 = assocT x1 t
  in let nT = sub_elem_list equ1 t
  in match lt1 with
       [t2] -> let (c,f) = cF (t1,t2) 
               in (f@u , (lv1 , c)::nT)
     | [] -> (u , (lv1 , [t1])::nT)
     | _ -> failwith "Imp.newUT2"

let newUT3 w t1 t2 u t =
     let (c,f) = cF (t1,t2)
  in match t1 with
       VAR(_) as x1 -> let (lv1,lt1) as equ1 = assocT x1 t  
       	       	       in let nT = sub_elem_list equ1 t
		       in let tT = (w::lv1,lt1)::nT
      	       	       in (match t2 with
		              VAR(_) as x2 -> (([x1;x2],[])::u , tT)
                            | _ -> (([x1],[t2])::u , tT)
      	       	       	  )
     | _ -> (match t2 with
       	       	 VAR(_) as x2 -> let (lv2,lt2) as equ2 = assocT x2 t
		                 in let nT = sub_elem_list equ2 t
				 in let tT = (w::lv2,lt2)::nT
				 in (([x2],[t1])::u , tT)
	       | _ -> let (c,f) = cF (t1,t2)
	              in (f@u , ([w],c)::t)
      	    )

  (* mm : Compute the derivation of (U,T) until U=[] ***********)

let rec mm u t = match u with
    ((v,s)::uU) -> 
      	(match s with 
	    []      -> (match v with
	                  [x1;x2] -> let (nU,nT) = newUT1 x1 x2 uU t
			             in mm nU nT
			| _ -> failwith "Imp.cas 1"
      	       	       )
	  | [t1]    -> (match v with
	                  [x1] -> let (nU,nT) = newUT2 x1 t1 uU t
			          in mm nU nT
			| _ -> failwith "Imp.cas 2"
      	       	       )
	  | [t1;t2] -> (match v with
	                  [x1] -> let (nU,nT) = newUT3 x1 t1 t2 uU t
			          in mm nU nT
			| _ -> failwith "Imp.cas 3"
      	       	       )
	  | _ -> raise Impossible_case
	) 
  | [] -> t


let nb_occ_list_list lv ltt = 
  let rec nb_occ_ll_rec = function 
      (v::lv1) -> (nb_occ_list v ltt)+(nb_occ_ll_rec lv1)
    | [] -> 0
  in nb_occ_ll_rec lv

let rec gro_aux = function
    (VAR x)::ll -> if (atompart_of_id x) = w_atom then gro_aux ll
      	       	       	       	       	   else (VAR x)::(gro_aux ll)
  | h::ll       -> h::(gro_aux ll)
  | []          -> [] 

let rec gro_aux_T = function 
    ((lv,lt)::tT) -> 
      	 let lv0 = gro_aux lv 
         in (match lv0 with 	       	 
      	       [] -> gro_aux_T tT
	     | _ -> (lv0,lt)::(gro_aux_T tT)
	    )
  | [] -> []

(* From now on, the equations of T are associated with the number of
   occurences of their variables in the right equations *********)

let rec find_null = function
    ((r,(_,_)) as equ::tT) -> if !r=0 then equ else find_null tT
  | [] -> raise Not_unifiable

let rec recompute t1 t = match t1 with
    ((r,(lv,lt))::tT) -> let n = nb_occ_list_list lv [t]
       	       	       	 in (ref (!r-n),(lv,lt))::(recompute tT t)
  | [] -> []

let rec sorted_Tc t sT = 
  if t=[] then sT else
       let (_,(lv,lt)) as equ = find_null t
    in let t1 = sub_elem_list equ t
    in match lt with
         []  -> sorted_Tc t1 (equ::sT)
       | [t_0] -> sorted_Tc (recompute t1 t_0) (equ::sT)
       | _   -> raise Impossible_case

let rec apply_subst s = function
    VAR(_) as v -> if List.mem_assoc v s then List.assoc v s
      	       	       	       	    else v
  | GLOB _ as x -> x				   
  | APP lt      -> APP (List.map (apply_subst s) lt)

let rec unif_from_sTc un = function
     ((_,(lv,lt))::tT) -> 
           (match lt with
	        []  ->    let x1 = List.hd lv and lv1 = List.tl lv
		       in let u0 = List.map (fun x->(x,x1)) lv1
		       in unif_from_sTc (un@u0) tT
	      | [t] ->    let t0 = apply_subst un t
      	       	       in let u0 = List.map (fun x->(x,t0)) lv
		       in unif_from_sTc (un@u0) tT
	      | _   -> raise Impossible_case
      	   ) 
   | [] -> un

let unif_from_T t0 =
     let t = gro_aux_T t0
  in let llt = List.map (fun (_,x) -> x) t
  in let ltt  = glue llt
  in let rec comp_nb t1 = match t1 with
           ((lv,lt)::tT1) -> (ref (nb_occ_list_list lv ltt),(lv,lt)):: 
	                         (comp_nb tT1)
         | _ -> []
  in let tc = comp_nb t
  in let sTc = sorted_Tc tc []
  in unif_from_sTc [] sTc

(* unif_atoms : atom -> atom -> unifier ******)

let unif_atoms (p1,l1) (p2,l2) = 
  if (fst p1)<>(fst p2) or (List.length l1)<>(List.length l2)
  then raise Not_unifiable
  else cpt := 0;
       let t = mm (initU l1 l2) (initT l1 l2)
       in unif_from_T t

(* unif_terms : term -> term -> unifier *******)

let unif_terms t1 t2 = 
  cpt := 0;
  let l1 = [t1] and l2 =[t2]
  in let t = mm (initU l1 l2) (initT l1 l2)
  in unif_from_T t

(* assoc_unif : unifier -> variable -> term ******)

let assoc_unif v u = 
  try List.assoc v u
  with Not_found -> v

(* apply_unif : unifier -> term -> term ******)

let apply_unif u t = 
  let rec au_rec = function
      VAR _  as v -> assoc_unif v u
    | GLOB _ as x -> x
    | APP lt      -> APP (List.map au_rec lt)
  in au_rec t

(* appear_var_term : variable -> term -> bool ********)

let appear_var_term v t = 
  let rec avt_rec  = function
      VAR _ as v1 -> v1=v
    | GLOB _      -> false
    | APP lt      -> List.fold_left (fun x t1 -> x or (avt_rec t1)) false lt
  in avt_rec t

(* up u1 u2 : returns the least unifier greater than u1 and u2
              If no such unifier exists, it raises Up_error   *******)

let rec up u1 u2 = match u2 with
    (((VAR s1) as y1,t1) as eq::uu2) -> 
      	if List.mem_assoc y1 u1
	then    let m1 = List.assoc y1 u1
	     in let t1' = apply_unif u1 t1
	     in let u0 = try unif_terms m1 t1'
	                 with Not_unifiable -> raise Up_error
	     in let u1' = List.map (fun (x,t) -> (x,apply_unif u0 t)) u1
	     in up (u1'@u0) uu2
	else    let t1' = apply_unif u1 t1
	     in if t1' = y1 
      	       	then u1
	        else if appear_var_term y1 t1'
		     then raise Up_error
		     else let u1' = 
      	       	       	     List.map (fun (x,t) -> (x,subst_term s1 t1' t)) u1
      	       	       	  in up ((y1,t1')::u1') uu2 
  | [] -> u1
  | _  -> failwith "unif__up: impossible case"

(* $Id$ *)

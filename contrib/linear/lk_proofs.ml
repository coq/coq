(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Names

open General
open Dpctypes
open Subst
open Unif

let proj = function
   (Po x) -> x
 | (No x) -> x


let all_lit_sfla f = 
  all_lit (proj f)

let sat p t = 
     let f = proj t
  in let lt = all_lit f
  in let rec sat_rec = function
        ((p,q,_)::lm) -> if (List.mem p lt) or (List.mem q lt)
	                 then true
			 else sat_rec lm
      | [] -> false
  in sat_rec (fst p)

let decomp s p =
  let rec decomp_rec = function
      (t1::llTT) -> 
      	   let (ns,disj,at,nat,conj,rneg,lneg) = decomp_rec llTT
	in if (not ((sat p t1)))
	   then (t1::ns,disj,at,nat,conj,rneg,lneg)
	   else (match t1 with
	           Po(Atom(_)) -> (ns,disj,t1::at,nat,conj,rneg,lneg)
		 | No(Atom(_)) -> (ns,disj,at,t1::nat,conj,rneg,lneg)
		 | Po(Neg(_)) -> (ns,disj,at,nat,conj,t1::rneg,lneg)
		 | No(Neg(_)) -> (ns,disj,at,nat,conj,rneg,t1::lneg)
		 | Po(Conj(_,_)) -> (ns,disj,at,nat,t1::conj,rneg,lneg)
		 | No(Disj(_,_)) -> (ns,disj,at,nat,t1::conj,rneg,lneg)
		 | No(Imp(_,_)) -> (ns,disj,at,nat,t1::conj,rneg,lneg)
		 | Po(Disj(_,_)) -> (ns,t1::disj,at,nat,conj,rneg,lneg)
		 | Po(Imp(_,_)) -> (ns,t1::disj,at,nat,conj,rneg,lneg)
		 | No(Conj(_,_)) -> (ns,t1::disj,at,nat,conj,rneg,lneg)
		 | _ -> failwith "decomp_rec : quantified formula !"
      	       	)
    | [] -> ([],[],[],[],[],[],[])
  in decomp_rec s

let rec apply_weakening ((Proof2(sq1,sq2,_)) as pr) = function
    (t::llTT) -> (match t with 
        (Po(f)) -> apply_weakening (Proof2(sq1,f::sq2,RWeakening2(f,pr))) llTT
      | (No(f)) -> apply_weakening (Proof2(f::sq1,sq2,LWeakening2(f,pr))) llTT
      )
  | [] -> pr

let one_disj_comp = function
    Po(Disj(f1,f2)) -> (Po(f1),Po(f2))
  | No(Conj(f1,f2)) -> (No(f1),No(f2))
  | Po(Imp(f1,f2)) -> (No(f1),Po(f2))
  | _ -> failwith "Not a disjunction in one_disj_comp !"


let apply_one_disj ((Proof2(sq1,sq2,r)) as lk) d = 
    (match d with
	   Po(Disj(f1,f2)) -> 
	        let sq2' = substract sq2 [f1;f2]
      	       	in (Proof2(sq1,Disj(f1,f2)::sq2',RDisj2(f1,f2,lk)))
	 | No(Conj(f1,f2)) ->
	        let sq1' = substract sq1 [f1;f2]
      	       	in (Proof2(Conj(f1,f2)::sq1',sq2,LConj2(f1,f2,lk)))
	 | Po(Imp(f1,f2)) ->
	        let sq1' = substract sq1 [f1]
		and sq2' = substract sq2 [f2]
      	       	in (Proof2(sq1',Imp(f1,f2)::sq2',RImp2(f1,f2,lk)))
	 | _ -> failwith "Not a disjunction in apply_one_disj !"
      )

let rec apply_disj lk = function
    (d::ld) -> let lk1 = apply_disj lk ld
      	       in apply_one_disj lk1 d
  | [] -> lk

let find_axiom (at,nat) p =
  let rec find_axiom_rec = function
      ((a,b,_)::lm) -> if (List.mem (Po a) at) & (List.mem (No b) nat)
       	       	       then (a,b)
		       else find_axiom_rec lm
    | [] -> raise Not_found
  in find_axiom_rec (fst p)

let sep_at at llt (lmu,_) = 
     let lm = List.map (fun (p,q,_) -> (p,q)) lmu
  in let rec sep_at_rec = function
      ((Po a)::ll) -> let (l1,l2) = sep_at_rec ll
      	       	 in if (try let b = List.assoc a lm in List.mem b llt
		        with Not_found -> false)
      	       	    then ((Po a)::l1,l2)
		    else (l1,(Po a)::l2)
    | [] -> ([],[])
  in sep_at_rec at
     
let sep_nat nat llt (lmu,_) = 
     let lm = List.map (fun (p,q,_) -> (q,p)) lmu
  in let rec sep_nat_rec = function
      ((No a)::ll) -> let (l1,l2) = sep_nat_rec ll
      	       	 in if (try let b = List.assoc a lm in List.mem b llt
		        with Not_found -> false)
      	       	    then ((No a)::l1,l2)
		    else (l1,(No a)::l2)
    | [] -> ([],[])
  in sep_nat_rec nat

let sep_neg neg llt (lmu,_) = 
     let lm = glue (List.map (fun (p,q,_) -> [(p,q);(q,p)]) lmu)
  in let rec connect = function
      	p::pp -> if (try let q = List.assoc p lm in List.mem q llt
	             with Not_found -> false)
		 then true
		 else connect pp
      | [] -> false
  in let rec sep_neg_rec = function
      (g::ll) -> let (l1,l2) = sep_neg_rec ll
      	       	   in let lit = all_lit_sfla g
		   in if connect lit then (g::l1,l2)
      	       	       	       	     else (l1,g::l2)
    | [] -> ([],[])
  in sep_neg_rec neg

(*** connect_graph : tree list -> path -> (tree,tree list,tree list) list 
  etant donnee une liste de conjonctions et un path,
  rend le graphe des connections des formules conjonctives
  sous la forme d'une liste de 
    (conjonction C, conjonctions reliees a C par la gauche,
     conjonctions reliees a C par la droite) **********)

let connect_graph conj (lmu,_) =
     let lm = glue (List.map (fun (p,q,_) -> [(p,q);(q,p)]) lmu)
  in let fun_lit = function
       	   Po(Conj(f1,f2)) -> (all_lit f1,all_lit f2)
	 | No(Disj(f1,f2)) -> (all_lit f1,all_lit f2)
	 | No(Imp(f1,f2)) -> (all_lit f1,all_lit f2)
	 | _ -> failwith "Not a conjunction in connect_graph !"
  in let lt = List.map (fun x -> (x,fun_lit x)) conj
  in let in_which b = let rec in_which_rec = function
      	       	          ((c,(l1,l2))::ll) -> if (List.mem b l1) or (List.mem b l2)
		                               then c else in_which_rec ll
		        | [] -> raise Not_found
                      in in_which_rec lt
  in let rec fun_nb c = function
      (a::ll) -> let lnb = fun_nb c ll
      	       	 in (try let b = List.assoc a lm 
      	       	       	 in let c1 = in_which b
		         in if c1=c then lnb else c1::lnb
		     with Not_found -> lnb)
    | [] -> []
  in let fun_cg c = let (l1,l2) = List.assoc c lt
      	       	    in (fun_nb c l1,fun_nb c l2)
  in List.map (fun x -> let (l1,l2) = fun_cg x in (x,l1,l2)) conj

let cut_path (lm,u) lt = 
  let rec cut_path_rec  = function
      ((p,q,_) as m::llmm) -> let (llmm1,llmm2) = cut_path_rec llmm
      	       	       	      in if (List.mem p lt) or (List.mem q lt)
			         then (m::llmm1,llmm2)
				 else (llmm1,m::llmm2)
    | [] -> ([],[])
  in let (lm1,lm2) = cut_path_rec lm
  in ((lm1,u),(lm2,u))
    
(*** sep_path : (at,nat,conj) -> path -> tree,(sequent,path),(sequent,path) 
  etant donnes (at,nat,conj) et p, fait la separation en deux couples
  (sequent,path) correspondant aux deux membres d'une conjonction
  et rend egalement la conjonction en question ********)

let sep_path (at,nat,conj,rneg,lneg) p =
     let g = connect_graph conj p
  in let rec find_all_X0 = function
      	((x,l1,l2) as gd::ll) -> if disjoint l1 l2 then 
                                   gd::(find_all_X0 ll)
                                 else find_all_X0 ll
      | [] -> []
  in let all_X0 = find_all_X0 g
  in let rec find_X0 = function
      [x] -> x
    | ((Po(Conj _),_,_) as c::_) -> c     (** on recherche d'abord A/\B **)
    | _::ll -> find_X0 ll
  in let (x0,l1,l2) = if all_X0=[] then 
                       failwith "Can't find X0 in sep_path ! (impossible case)"
                      else find_X0 all_X0
  in let (g,d) = (match x0 with
      	       	      Po(Conj(f1,f2)) -> (Po(f1),Po(f2))
		    | No(Disj(f1,f2)) -> (No(f1),No(f2))
		    | No(Imp(f1,f2)) -> (Po(f1),No(f2))
		    | _ -> failwith "Not a conjunction in sep_path !")
  in let s1 = g::l1
  in let s2 = d::(substract conj (x0::l1))
  in let litS1 = glue (List.map (fun x -> all_lit_sfla x) s1)
  in let (at1,at2) = sep_at at litS1 p
     and (nat1,nat2) = sep_nat nat litS1 p
  in let neg = lneg @ (List.map (fun (Po (Neg f)) -> (No f)) rneg)
  in let (neg1,neg2) = sep_neg neg litS1 p
  in let lit_at1 = List.map proj at1
     and lit_nat1 = List.map proj nat1
     and lit_neg1 = List.map proj neg1
  in let (p1,p2) = cut_path p (lit_at1@lit_nat1@lit_neg1@litS1)
  in let sq1 = s1 @ at1 @ nat1 @ neg1
  in let sq2 = s2 @ at2 @ nat2 @ neg2
  in (x0,(sq1,p1),(sq2,p2))

let conj_case x0 ((Proof2(sq11,sq12,rl1)) as pr1) 
                 ((Proof2(sq21,sq22,rl2)) as pr2) = 
     (match x0 with
      	     Po(Conj(f1,f2)) -> 
      	       	    let sq2 = (substract sq12 [f1])@(substract sq22 [f2])
	            in (Proof2(sq11@sq21,Conj(f1,f2)::sq2,
      	       	       	       	       	    RConj2(f1,pr1,f2,pr2)))
	   | No(Disj(f1,f2)) ->
      	       	    let sq1 = (substract sq11 [f1])@(substract sq21 [f2])
	            in (Proof2(Disj(f1,f2)::sq1,sq12@sq22,
      	       	       	       	       	    LDisj2(f1,pr1,f2,pr2)))
	   | No(Imp(f1,f2)) ->
      	       	    let sq1 = sq11@(substract sq21 [f2])
		    and sq2 = (substract sq12 [f1])@sq22
	            in (Proof2(Imp(f1,f2)::sq1,sq2,LImp2(f1,pr1,f2,pr2))) 
	   | _ -> failwith "Not a conjunction in conj_case !"
      )

let rec rneg_case pr = function
     ((Po(Neg f))::lng) -> 
      	     let ((Proof2(sq1,sq2,_)) as pr1) = rneg_case pr lng
       	  in let sq1' = substract sq1 [f]
	     and sq2' = (Neg f)::sq2
	  in (Proof2(sq1',sq2',RNeg2(f,pr1)))
   | [] -> pr

let lneg_case ((Proof2(sq1,sq2,_)) as pr) (No(Neg f)) = 
   let sq1' = (Neg f)::sq1
   and sq2' = substract sq2 [f]
   in (Proof2(sq1',sq2',LNeg2(f,pr)))

let find_lneg lneg = 
  let rec is_negneg = function
      t::ll -> (match t with
      	       	   No(Neg(Neg(f))) -> t
		 | _ -> is_negneg ll
	       )
    | [] -> raise Not_found
  in try is_negneg lneg
     with Not_found -> List.hd lneg

let rec proof_of_path sT p = 
     let (ns,disj,at,nat,conj,rneg,lneg) = decomp sT p
  in let sT1 = substract sT ns
  in let pr1 = if disj=[]
      	       then cases (at,nat,conj,rneg,lneg) p
	       else disj_case disj sT1 p
  in apply_weakening pr1 ns
and disj_case disj sT1 p =
  let rec disj_case_rec s = function
      d::ld -> let (a,b) = one_disj_comp d
      	       in let nsatA = (not ((sat p a)))
                  and nsatB = (not ((sat p b)))
      	       in let s1 = substract s [d]
      	       in let s2 = if nsatA then b::s1
	                   else if nsatB then a::s1
			   else a::(b::s1)
	       in let pr = disj_case_rec s2 ld
	       in let pr1 = if nsatA then apply_weakening pr [a]
	                    else if nsatB then apply_weakening pr [b]
			    else pr
      	       in apply_one_disj pr1 d
    | [] -> proof_of_path s p
  in disj_case_rec sT1 disj
and cases (at,nat,conj,rneg,lneg) p =
  try    let (a,b) = find_axiom (at,nat) p
      in let pr = (Proof2([b],[a],Axiom2(a)))
      in let wk =  (substract at [(Po a)])
                  @(substract nat [(No b)])
		  @conj@rneg@lneg
      in apply_weakening pr wk
  with Not_found -> 
    if conj<>[] then 
         let (x0,(s1,p1),(s2,p2)) = sep_path (at,nat,conj,rneg,lneg) p
      in let pr1 = proof_of_path s1 p1
      in let pr2 = proof_of_path s2 p2
      in let pr  = conj_case x0 pr1 pr2
      in rneg_case pr rneg
   else
      if rneg<>[] then
      	 let s = at@nat@lneg@(List.map (fun (Po (Neg f)) -> (No f)) rneg)
	 in let pr = proof_of_path s p
	 in rneg_case pr rneg
      else 
      	 let (No (Neg f)) as g = find_lneg lneg
	 in let s = at@nat@(substract lneg [g])@[Po f]
	 in let pr = proof_of_path s p
	 in lneg_case pr g


(* pi_formula : separated formula -> formula 
   pi_proof   : separated proof   -> proof *******)

let rec pi_formula  = function
    Atom((s,_),lt) -> Atom((s,0),lt)
  | Neg(f) -> Neg(pi_formula f)
  | Imp(f1,f2) -> Imp(pi_formula f1,pi_formula f2)
  | Conj(f1,f2) -> Conj(pi_formula f1,pi_formula f2)
  | Disj(f1,f2) -> Disj(pi_formula f1,pi_formula f2)
  | ForAll(s,f) -> ForAll(s,pi_formula f)
  | Exists(s,f) -> Exists(s,pi_formula f)

let rec pi_proof (Proof2(sq1,sq2,rule)) = 
     let sq1' = List.map pi_formula sq1
     and sq2' = List.map pi_formula sq2
  in let rule1 = match rule with
       Axiom2(f) -> Axiom2(pi_formula f)
     | RWeakening2(f,p) -> RWeakening2(pi_formula f,pi_proof p)
     | LWeakening2(f,p) -> LWeakening2(pi_formula f,pi_proof p)
     | RNeg2(f,p) -> RNeg2(pi_formula f,pi_proof p)
     | LNeg2(f,p) -> LNeg2(pi_formula f,pi_proof p)
     | RConj2(f1,p1,f2,p2) 
      	 -> RConj2(pi_formula f1,pi_proof p1,pi_formula f2,pi_proof p2)
     | LDisj2(f1,p1,f2,p2) 
      	 -> LDisj2(pi_formula f1,pi_proof p1,pi_formula f2,pi_proof p2)
     | LImp2(f1,p1,f2,p2) 
      	 -> LImp2(pi_formula f1,pi_proof p1,pi_formula f2,pi_proof p2)
     | LConj2(f1,f2,p) -> LConj2(pi_formula f1,pi_formula f2,pi_proof p)
     | RDisj2(f1,f2,p) -> RDisj2(pi_formula f1,pi_formula f2,pi_proof p)
     | RImp2(f1,f2,p) -> RImp2(pi_formula f1,pi_formula f2,pi_proof p)
     | RForAll2(s,f,p) -> RForAll2(s,pi_formula f,pi_proof p)
     | LExists2(s,f,p) -> LExists2(s,pi_formula f,pi_proof p)
     | LForAll2(s,t,f,p) -> LForAll2(s,t,pi_formula f,pi_proof p)
     | RExists2(s,t,f,p) -> RExists2(s,t,pi_formula f,pi_proof p)
  in (Proof2(sq1',sq2',rule1))

(*** Introduction of quantifiers in proof ******)

type quantifier = Universal of identifier * formula * bool
      	        | Existential of identifier * formula * bool


let her v ex = 
   let lt = List.map (fun x-> VAR(x)) ex
   in (v,APP (GLOB (SK v)::lt))

(*** quant_var returns all the quantifiers of a formula *****)

let quant_var f = 
   let rec qv_rec sign = function
       ForAll(v,f) -> let qt = qv_rec sign f in
      	       	      if sign then (Universal(v,f,true))::qt 
       	       	       	      else (Existential(v,f,false))::qt
     | Exists(v,f) -> let qt = qv_rec sign f in
      	       	      if sign then (Existential(v,f,true))::qt
       	       	       	      else (Universal(v,f,false))::qt
     | Atom(_) -> []
     | Neg(f) -> qv_rec ((not (sign))) f
     | Imp(f1,f2) -> let qt1 = qv_rec ((not (sign))) f1
                     and qt2 = qv_rec sign f2
		     in qt1@qt2
     | Conj(f1,f2) -> let qt1 = qv_rec sign f1
                      and qt2 = qv_rec sign f2
		      in qt1@qt2
     | Disj(f1,f2) -> let qt1 = qv_rec sign f1
                      and qt2 = qv_rec sign f2
		      in qt1@qt2
   in qv_rec true f

(*** replace the skolem functions by their corresponding variables ****)

let rec unher_term lv = function
   | APP (GLOB (SK v)::_) -> VAR v
   | APP lt -> APP (unher_list_term lv lt)			
   | x -> x
and unher_list_term lv lt = 
   List.map (unher_term lv) lt

let rec unher_unif lv = function
     ((x,t)::ll) -> (x,unher_term lv t)::(unher_unif lv ll)
   | [] -> []

let rec unher_formula lv = function
    Atom(s,lt) -> Atom(s,unher_list_term lv lt)
  | Neg(f) -> Neg(unher_formula lv f)
  | Imp(f1,f2) -> Imp(unher_formula lv f1,unher_formula lv f2)
  | Conj(f1,f2) -> Conj(unher_formula lv f1,unher_formula lv f2)
  | Disj(f1,f2) -> Disj(unher_formula lv f1,unher_formula lv f2)
  | ForAll(s,f) -> ForAll(s,unher_formula lv f)
  | Exists(s,f) -> Exists(s,unher_formula lv f)

let rec unher_sequent lv = function
    (f::ll) -> (unher_formula lv f)::(unher_sequent lv ll)
  | [] -> []

let rec unher_proof lv (Proof2(sq1,sq2,rule)) = 
     let sq1' = unher_sequent lv sq1
     and sq2' = unher_sequent lv sq2
  in let rule1 = match rule with
       Axiom2(f) -> Axiom2(unher_formula lv f)
     | RWeakening2(f,p) -> RWeakening2(unher_formula lv f,unher_proof lv p)
     | LWeakening2(f,p) -> LWeakening2(unher_formula lv f,unher_proof lv p)
     | RNeg2(f,p) -> RNeg2(unher_formula lv f,unher_proof lv p)
     | LNeg2(f,p) -> LNeg2(unher_formula lv f,unher_proof lv p)
     | RConj2(f1,p1,f2,p2) -> RConj2(unher_formula lv f1,unher_proof lv p1,
       	       	       	       	   unher_formula lv f2,unher_proof lv p2)
     | LDisj2(f1,p1,f2,p2) -> LDisj2(unher_formula lv f1,unher_proof lv p1,
       	       	       	       	   unher_formula lv f2,unher_proof lv p2)
     | LImp2(f1,p1,f2,p2) -> LImp2(unher_formula lv f1,unher_proof lv p1,
       	       	       	       	   unher_formula lv f2,unher_proof lv p2)
     | LConj2(f1,f2,p) -> LConj2(unher_formula lv f1,unher_formula lv f2,
      	       	       	       	   unher_proof lv p)
     | RDisj2(f1,f2,p) -> RDisj2(unher_formula lv f1,unher_formula lv f2,
      	       	       	       	   unher_proof lv p)
     | RImp2(f1,f2,p) -> RImp2(unher_formula lv f1,unher_formula lv f2,
      	       	       	       	   unher_proof lv p)
     | RForAll2(s,f,p) -> RForAll2(s,unher_formula lv f,unher_proof lv p)
     | LExists2(s,f,p) -> LExists2(s,unher_formula lv f,unher_proof lv p)
     | LForAll2(s,t,f,p) -> LForAll2(s,t,unher_formula lv f,unher_proof lv p)
     | RExists2(s,t,f,p) -> RExists2(s,t,unher_formula lv f,unher_proof lv p)
  in (Proof2(sq1',sq2',rule1))

(*** subst_f_qt : quantifier_list -> formula -> formula *****)

let subst_f_qt sqt f = 
  let rec sub_rec f0 = function 
      q::ll -> let f1 = sub_rec f0 ll in
      	       (match q with
       	       	   Universal(id,f_0,t) -> let f' = if t then ForAll(id,f_0)
		                                      else Exists(id,f_0)
					in subst_f_f f_0 f' f1
                 | Existential(id,f_0,t) -> let f' = if t then Exists(id,f_0)
		                                        else ForAll(id,f_0)
					  in subst_f_f f_0 f' f1
      	       )
    | [] -> f0
  in sub_rec f sqt


let quant_in id f = 
  let rec qi = function
      Atom(_) -> false	
    | Neg(f1) -> qi f1
    | Conj(f1,f2) -> (qi f1) or (qi f2)
    | Disj(f1,f2) -> (qi f1) or (qi f2)
    | Imp(f1,f2) -> (qi f1) or (qi f2)
    | ForAll(id',f1) -> if id=id' then true else qi f1
    | Exists(id',f1) -> if id=id' then true else qi f1
  in qi f


let weak_quant f = 
  let rec wq_rec = function
     ((Universal(id,_,_)) as q)::ll -> if quant_in id f then q::(wq_rec ll)
      	       	       	       	      else wq_rec ll
   | ((Existential(id,_,_)) as q)::ll -> if quant_in id f then q::(wq_rec ll)
      	       	       	       	      else wq_rec ll
   | [] -> []
  in wq_rec


let proof_quant (Proof2(sq1,sq2,_)) sqt = 
  let sq = List.map (subst_f_qt sqt)(sq1@sq2)
  in
  let id_in_sq id = 
    List.fold_left (fun r f -> if r then true else (id_in_formula id f)) false sq
  in 
  let rec pq_rec = function
     ((Universal(id,_,_)) as q)::ll -> if id_in_sq id then q::(pq_rec ll)
      	       	       	       	      else pq_rec ll
   | ((Existential(id,_,_)) as q)::ll -> if id_in_sq id then q::(pq_rec ll)
      	       	       	       	      else pq_rec ll
   | [] -> []
  in pq_rec sqt

     
let find_quant pog sq1' sq2' = 
  let appear = function
      (Universal(id,f,t)) 
      	     -> let qf = if t then ForAll(id,f) else Exists(id,f)
       	       	in (List.mem qf sq1') or (List.mem qf sq2')
    | (Existential(id,f,t)) 
      	     -> let qf = if t then Exists(id,f) else ForAll(id,f)
	        in (List.mem qf sq1') or (List.mem qf sq2')
  in
  let rec find_rec = function
      (q,r)::l -> if !r=0 then if appear q then q 
      	       	       	       	       	   else find_rec l
			  else find_rec l
    | [] -> raise Not_found
  in find_rec pog


(*** make_pog : make partial order graph
     make_pog : quantifier list -> (quantifier * quantifier) list 
                -> (quantifier * int ref) list *******)

let make_pog qt cst =
  let pog0 = List.map (fun x -> (x,ref 0)) qt
  in 
  let rec make_rec = function
      (q,q')::l -> if (List.mem q qt) & (List.mem q' qt) then
      	       	     let r = List.assoc q' pog0 in r := !r + 1
		   else () ;
		   make_rec l
    | [] -> pog0
  in
  make_rec cst


let update_pog cst pog lq = 
  let remove_one q0 = 
    let rec rm_rec = function
        (q,r)::ll -> if q=q0 
      	       	     then rm_rec ll
	             else if List.mem (q0,q) cst 
		          then begin r := !r - 1; (q,r)::(rm_rec ll) end
			  else (q,r)::(rm_rec ll)
      | [] -> []
    in rm_rec
  in 
  let rec remove_all pog0 = function
      q::ll -> let pog1 = remove_one q pog0 in
               remove_all pog1 ll
    | [] -> pog0
  in
  remove_all pog lq


(*** sort_pog : pog -> quantifier list *****)

let sort_pog cst pog =
  let pog' = List.map (fun (x,r) -> (x,ref (!r))) pog 
  in
  let decrease_one x = 
    let rec dec_rec = function
      	(q,q')::ll -> if (q=x) & (List.mem_assoc q' pog')
      	       	      then begin
      	       	       	     let r = List.assoc q' pog' in 
      	       	       	     r := !r - 1; dec_rec ll
			   end
		      else dec_rec ll
      | [] -> ()
    in dec_rec cst
  in
  let rec decrease = function 
      x::ll -> decrease_one x; decrease ll
    | [] -> ()
  in
  let rec find_min = function
      (x,r)::ll -> if !r=0 
	           then begin r := -1; x::(find_min ll) end	
		   else find_min ll
    | [] -> []
  in
  let rec loop od = 
    let m = find_min pog' in
    if m=[] then od
      	    else begin decrease m; loop (od@m) end
  in loop []


(*** quant_proof : cst -> pog -> lkproof2 -> lkproof2 ********)

let rec quant_proof cst pog ((Proof2(sq1,sq2,rule)) as pr) = 
  if pog=[] then pr
  else
  let sqt = sort_pog cst pog in
  let sq1' = List.map (subst_f_qt sqt) sq1
  and sq2' = List.map (subst_f_qt sqt) sq2
  in
  let rule' = match rule with
      LWeakening2(f,p) -> let f' = subst_f_qt sqt f in
      	       	       	  let wq = weak_quant f' sqt in
		    LWeakening2(f',quant_proof cst (update_pog cst pog wq) p)
    | RWeakening2(f,p) -> let f' = subst_f_qt sqt f in
      	       	       	  let wq = weak_quant f' sqt in
		    RWeakening2(f',quant_proof cst (update_pog cst pog wq) p)
    | _ -> (try
      	     let q1 = find_quant pog sq1' sq2' in
      	     let pr' = quant_proof cst (update_pog cst pog [q1]) pr in
	     (match q1 with 
	         Universal(id,f,t) -> if t then RForAll2(id,f,pr')
		                           else LExists2(id,f,pr')
	       | Existential(id,f,t) -> if t then RExists2(id,VAR id,f,pr')
	                                     else LForAll2(id,VAR id,f,pr') )
  	   with Not_found ->
	     (match rule with
	         Axiom2(f) -> Axiom2(f)
	       | RNeg2(f,p) -> RNeg2(subst_f_qt sqt f,quant_proof cst pog p)
	       | LNeg2(f,p) -> LNeg2(subst_f_qt sqt f,quant_proof cst pog p)
	       | RConj2(f1,p1,f2,p2) 
      	       	     -> let sqt1 = proof_quant p1 sqt in
      	       	       	let pog1 = make_pog sqt1 cst in
		        let pog2 = make_pog (substract sqt sqt1) cst in
		        RConj2(subst_f_qt sqt f1,quant_proof cst pog1 p1,
			       subst_f_qt sqt f2,quant_proof cst pog2 p2)
	       | LConj2(f1,f2,p) -> LConj2(subst_f_qt sqt f1,subst_f_qt sqt f2,
	                                   quant_proof cst pog p)
	       | RDisj2(f1,f2,p) -> RDisj2(subst_f_qt sqt f1,subst_f_qt sqt f2,
	                                   quant_proof cst pog p)
	       | LDisj2(f1,p1,f2,p2) 
      	       	     -> let sqt1 = proof_quant p1 sqt in
      	       	       	let pog1 = make_pog sqt1 cst in
		        let pog2 = make_pog (substract sqt sqt1) cst in
		        LDisj2(subst_f_qt sqt f1,quant_proof cst pog1 p1,
			       subst_f_qt sqt f2,quant_proof cst pog2 p2)
               | RImp2(f1,f2,p) -> RImp2(subst_f_qt sqt f1,subst_f_qt sqt f2,
	                                   quant_proof cst pog p)
               | LImp2(f1,p1,f2,p2) 
      	       	     -> let sqt1 = proof_quant p1 sqt in
      	       	       	let pog1 = make_pog sqt1 cst in
		        let pog2 = make_pog (substract sqt sqt1) cst in
		        LImp2(subst_f_qt sqt f1,quant_proof cst pog1 p1,
			       subst_f_qt sqt f2,quant_proof cst pog2 p2)
      	       | _ -> raise Impossible_case
	     ))
  in (Proof2(sq1',sq2',rule'))


(*** apply_unif_f : unifier -> formula -> formula *****)

let apply_unif_f u =
  let rec auf_rec = function
      Atom(n,lt) -> Atom(n,List.map (apply_unif u) lt)
    | Neg(f) -> Neg(auf_rec f)
    | Conj(f1,f2) -> Conj(auf_rec f1,auf_rec f2)
    | Disj(f1,f2) -> Disj(auf_rec f1,auf_rec f2)
    | Imp(f1,f2) -> Imp(auf_rec f1,auf_rec f2)
    | ForAll(id,f) -> ForAll(id,auf_rec f)
    | Exists(id,f) -> Exists(id,auf_rec f)
  in auf_rec


(*** witness_proof : quantifier list -> unifier -> lkproof2 -> lkproof2 ****)

let witness_proof u0 pr = 
  let rec wit_rec u (Proof2(sq1,sq2,rule)) = 
    let sq1' = List.map (apply_unif_f u) sq1 
    and sq2' = List.map (apply_unif_f u) sq2 in
    let rule' = match rule with
        Axiom2(f) -> Axiom2(apply_unif_f u f)
      | RWeakening2(f,p) -> RWeakening2(apply_unif_f u f,wit_rec u p)
      | LWeakening2(f,p) -> LWeakening2(apply_unif_f u f,wit_rec u p)
      | RNeg2(f,p) -> RNeg2(apply_unif_f u f,wit_rec u p)
      | LNeg2(f,p) -> LNeg2(apply_unif_f u f,wit_rec u p)
      | RConj2(f1,p1,f2,p2) -> RConj2(apply_unif_f u f1,wit_rec u p1,
      	       	       	       	      apply_unif_f u f2,wit_rec u p2)
      | LConj2(f1,f2,p) -> LConj2(apply_unif_f u f1,apply_unif_f u f2,
      	       	       	       	  wit_rec u p)
      | RDisj2(f1,f2,p) -> RDisj2(apply_unif_f u f1,apply_unif_f u f2,
      	       	       	       	  wit_rec u p)
      | LDisj2(f1,p1,f2,p2) -> LDisj2(apply_unif_f u f1,wit_rec u p1,
      	       	       	       	      apply_unif_f u f2,wit_rec u p2)
      | RImp2(f1,f2,p) -> RImp2(apply_unif_f u f1,apply_unif_f u f2,
      	       	       	       	wit_rec u p)
      | LImp2(f1,p1,f2,p2) -> LImp2(apply_unif_f u f1,wit_rec u p1,
      	       	       	       	    apply_unif_f u f2,wit_rec u p2)
      | RForAll2(id,f,p) -> RForAll2(id,apply_unif_f u f,wit_rec u p)
      | LForAll2(id,_,f,p) -> let f' = apply_unif_f u f in
      	       	       	      let t = assoc_unif (VAR id) u0 in
			      LForAll2(id,t,f',wit_rec ((VAR id,t)::u) p)
      | RExists2(id,_,f,p) -> let f' = apply_unif_f u f in
      	       	       	      let t = assoc_unif (VAR id) u0 in
			      RExists2(id,t,f',wit_rec ((VAR id,t)::u) p)
      | LExists2(id,f,p) -> LExists2(id,apply_unif_f u f,wit_rec u p) 
    in (Proof2(sq1',sq2',rule'))
  in wit_rec [] pr


(*** make constraints on quantifiers ******)
(*** make_constraints : 
         quantifier list -> unifier -> (quantifier * quantifier) list ***)

let in_witness id t = 
  let vt = all_var_term t 
  in List.mem id vt


let before u = fun
   p_0 p_1 -> match p_0,p_1 with ((Universal(id,f,_)), (Universal(id',f',_))) 
      -> if id=id' then false 
      	       	   else quant_in id' f
 | ((Universal(id,f,_)), (Existential(id',f',_))) 
      -> (quant_in id' f) or (in_witness id (assoc_unif (VAR id') u))
 | ((Existential(id,f,_)), (Universal(id',f',_))) 
      -> quant_in id' f
 | ((Existential(id,f,_)), (Existential(id',f',_))) 
      -> if id=id' then false
      	 else (quant_in id' f) or (in_witness id (assoc_unif (VAR id') u))


let make_constraints qt u = 
  let rec goods = function
      (a,b)::ll -> if before u a b 
                   then (a,b)::(goods ll)
		   else goods ll
    | [] -> []
  in 
  let all = glue (List.map (fun a -> (List.map (fun b -> (a,b)) qt)) qt)
  in 
  goods all



(*** Introduce all the quantifiers in a proof (one after each other,
     using apply_ex and apply_un) ********)

let int_quant f u pr = 
     let qt = quant_var f
  in let un_qt = such_that qt (function (Universal _) -> true | _ -> false)
     and fr_var = free_var_formula f
  in let un_var = List.map (fun (Universal(id,_,_)) -> id) un_qt
  in let sk_var  = un_var @ fr_var
  in let u0 = unher_unif sk_var u
  in let pr0 = pi_proof pr
  in let pr1 = unher_proof sk_var pr0
  in let cst = make_constraints qt u0
  in let pog = make_pog qt cst
  in let qpr = quant_proof cst pog pr1
  in witness_proof u0 qpr


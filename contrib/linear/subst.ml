(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open General
open Names
open Dpctypes

(* subst_term      : identifier -> term -> term -> term
   subst_list_term : identifier -> term -> term list -> term list *****)

let rec subst_term v t = function
    VAR(s)      -> if s=v then t else (VAR s)
  | GLOB _ as x -> x
  | APP(lt)     -> APP(subst_list_term v t lt)
and subst_list_term v t = function
  t1::l1 -> (subst_term v t t1)::(subst_list_term v t l1)
| [] -> []

(* subst : identifier -> term -> formula -> formula *)

let subst v t =
  let rec subst_rec f = match f with
      Atom(s,lt) -> Atom(s,subst_list_term v t lt)
    | Neg(f1) -> Neg(subst_rec f1)
    | Imp(f1,f2) -> Imp(subst_rec f1,subst_rec f2)
    | Conj(f1,f2) -> Conj(subst_rec f1, subst_rec f2)
    | Disj(f1,f2) -> Disj(subst_rec f1, subst_rec f2)
    | ForAll(s,f1) -> ForAll(s,subst_rec f1)
    | Exists(s,f1) -> Exists(s, subst_rec f1)
  in subst_rec

(* all_lit : formula -> formula list *)

let rec all_lit = function
    Atom((x_0,x_1)) -> [Atom((x_0,x_1))]
  | Neg(f) -> all_lit f
  | Conj(f1,f2) -> (all_lit f1)@(all_lit f2)
  | Disj(f1,f2) -> (all_lit f1)@(all_lit f2)
  | Imp(f1,f2) -> (all_lit f1)@(all_lit f2)
  | _ -> raise Impossible_case

(* occurs : formula -> formula -> bool *)

let occurs s =
  let rec occurs_rec f = if s=f then true else match f with
      Neg(f1) -> (occurs_rec f1)
    | ForAll(s,f1) -> (occurs_rec f1)
    | Exists(s,f1) -> (occurs_rec f1)
    | Imp(f1,f2) -> (occurs_rec f1) or (occurs_rec f2)
    | Conj(f1,f2) -> (occurs_rec f1) or (occurs_rec f2)
    | Disj(f1,f2) -> (occurs_rec f1) or (occurs_rec f2)
    | _ -> false
  in occurs_rec

(* subst_f_f : formula -> formula -> formula -> formula *)

let rec subst_f_f fa fb f = 
  if f=fa 
  then fb
  else match f with
      Atom(_,_) as a -> a
    | Neg(f1) -> Neg(subst_f_f fa fb f1)
    | Conj(f1,f2) -> Conj(subst_f_f fa fb f1,subst_f_f fa fb f2)
    | Disj(f1,f2) -> Disj(subst_f_f fa fb f1,subst_f_f fa fb f2)
    | Imp(f1,f2) -> Imp(subst_f_f fa fb f1,subst_f_f fa fb f2)
    | ForAll(s,f1) -> ForAll(s,subst_f_f fa fb f1)
    | Exists(s,f1) -> Exists(s,subst_f_f fa fb f1)

(* subst_proof2 : identifier -> term -> lkproof2 -> lkproof2 *)

let rec subst_proof2 v t (Proof2(sq1,sq2,rule)) = 
  let sq1' = List.map (subst v t) sq1
  and sq2' = List.map (subst v t) sq2
  in let rule1 = match rule with
       Axiom2(f) -> Axiom2(subst v t f)
     | RWeakening2(f,p) -> RWeakening2(subst v t f,subst_proof2 v t p)
     | LWeakening2(f,p) -> LWeakening2(subst v t f,subst_proof2 v t p)
     | RNeg2(f,p) -> RNeg2(subst v t f,subst_proof2 v t p)
     | LNeg2(f,p) -> LNeg2(subst v t f,subst_proof2 v t p)
     | RConj2(f1,p1,f2,p2) -> RConj2(subst v t f1,subst_proof2 v t p1,
       	       	       	       	   subst v t f2,subst_proof2 v t p2)
     | LDisj2(f1,p1,f2,p2) -> LDisj2(subst v t f1,subst_proof2 v t p1,
       	       	       	       	   subst v t f2,subst_proof2 v t p2)
     | LImp2(f1,p1,f2,p2) -> LImp2(subst v t f1,subst_proof2 v t p1,
       	       	       	       	   subst v t f2,subst_proof2 v t p2)
     | LConj2(f1,f2,p) -> LConj2(subst v t f1,subst v t f2,
      	       	       	       	   subst_proof2 v t p)
     | RDisj2(f1,f2,p) -> RDisj2(subst v t f1,subst v t f2,
      	       	       	       	   subst_proof2 v t p)
     | RImp2(f1,f2,p) -> RImp2(subst v t f1,subst v t f2,
      	       	       	       	   subst_proof2 v t p)
     | RForAll2(s,f,p) -> RForAll2(s,subst v t f,subst_proof2 v t p)
     | LExists2(s,f,p) -> LExists2(s,subst v t f,subst_proof2 v t p)
     | LForAll2(s,t1,f,p) -> LForAll2(s,subst_term v t t1,
      	       	       	       	    subst v t f,subst_proof2 v t p)
     | RExists2(s,t1,f,p) -> RExists2(s,subst_term v t t1,
      	       	       	       	    subst v t f,subst_proof2 v t p)
  in (Proof2(sq1',sq2',rule1))

(* All the free variables of a formula... ******)

let rec all_var_term  = function
     VAR s  -> [s]
   | GLOB _ -> []
   | APP lt -> all_var_list_term lt
and all_var_list_term = function
     t::ll -> union (all_var_term t) (all_var_list_term ll)
   | [] -> []

(* free_var_formula : formula -> identifier list ******)

let rec free_var_formula  = function
    Atom(s,lt) -> all_var_list_term lt
  | Neg(f) -> free_var_formula f
  | Imp(f1,f2) -> union (free_var_formula f1) (free_var_formula f2)
  | Conj(f1,f2) -> union (free_var_formula f1) (free_var_formula f2)
  | Disj(f1,f2) -> union (free_var_formula f1) (free_var_formula f2)
  | ForAll(s,f) -> substract (free_var_formula f) [s]
  | Exists(s,f) -> substract (free_var_formula f) [s]

(*** id_in_term : identifier -> term -> bool
     id_in_list : identifier -> term list -> bool ****)

let rec id_in_term id = function
    VAR id' -> id=id'
  | GLOB _  -> false
  | APP lt  -> id_in_list id lt
and id_in_list id = 
    List.fold_left (fun r t -> if r then true else id_in_term id t) false 


(*** id_in_formula : identifier -> formula -> bool ****)

let rec id_in_formula id = function
     Atom(_,lt) -> id_in_list id lt
   | Neg(f) -> id_in_formula id f
   | Conj(f1,f2) -> (id_in_formula id f1) or (id_in_formula id f2)
   | Disj(f1,f2) -> (id_in_formula id f1) or (id_in_formula id f2)
   | Imp(f1,f2) -> (id_in_formula id f1) or (id_in_formula id f2)
   | ForAll(id',f) -> (id=id') or (id_in_formula id f)
   | Exists(id',f) -> (id=id') or (id_in_formula id f)



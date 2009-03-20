(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

open Big_int
open Num
open Sos

module Mc = Micromega
module Ml2C = Mutils.CamlToCoq
module C2Ml = Mutils.CoqToCaml

let debug = false

module M =
struct
 open Mc

 let rec expr_to_term = function
  |  PEc z ->  Const  (C2Ml.q_to_num z)
  |  PEX v ->  Var ("x"^(string_of_int (C2Ml.index v)))
  |  PEmul(p1,p2) -> 
      let p1 = expr_to_term p1 in
      let p2 = expr_to_term p2 in
      let res = Mul(p1,p2) in 	   res

  | PEadd(p1,p2) -> Add(expr_to_term p1, expr_to_term p2)
  | PEsub(p1,p2) -> Sub(expr_to_term p1, expr_to_term p2)
  | PEpow(p,n)   -> Pow(expr_to_term p , C2Ml.n n)
  |  PEopp p ->  Opp (expr_to_term p)

      


(* let term_to_expr e =
  let e' = term_to_expr e in
   if debug 
   then Printf.printf "term_to_expr : %s - %s\n"  
    (string_of_poly (poly_of_term  e)) 
    (string_of_poly (poly_of_term (expr_to_term e')));
   e' *)

end 
open M      

open List
open Mutils 




let rec canonical_sum_to_string = function s -> failwith "not implemented"

let print_canonical_sum m = Format.print_string (canonical_sum_to_string m)

let print_list_term l = 
 print_string "print_list_term\n";
 List.iter (fun (Mc.Pair(e,k)) -> Printf.printf "q: %s %s ;" 
  (string_of_poly (poly_of_term (expr_to_term e))) 
  (match k with 
    Mc.Equal -> "= " 
   | Mc.Strict -> "> " 
   | Mc.NonStrict -> ">= " 
   | _ -> failwith "not_implemented")) l ;
 print_string "\n"


let partition_expr l = 
 let rec f i = function
  | [] -> ([],[],[])
  | Mc.Pair(e,k)::l -> 
     let (eq,ge,neq) = f (i+1) l in
      match k with 
       | Mc.Equal -> ((e,i)::eq,ge,neq)
       | Mc.NonStrict -> (eq,(e,Axiom_le i)::ge,neq)
       | Mc.Strict    -> (* e > 0 == e >= 0 /\ e <> 0 *) 
	  (eq, (e,Axiom_lt i)::ge,(e,Axiom_lt i)::neq)
       | Mc.NonEqual -> (eq,ge,(e,Axiom_eq i)::neq) 
	  (* Not quite sure -- Coq interface has changed *)
 in f 0 l


let rec sets_of_list l =
 match l with
  | [] -> [[]]
  | e::l -> let s = sets_of_list l in
	     s@(List.map (fun s0 -> e::s0) s) 

(* The exploration is probably not complete - for simple cases, it works... *)
let real_nonlinear_prover d l =
 try 
  let (eq,ge,neq) = partition_expr l in

  let rec elim_const  = function
    [] ->  []
   | (x,y)::l -> let p = poly_of_term (expr_to_term x) in
		  if poly_isconst p 
		  then elim_const l 
		  else (p,y)::(elim_const l) in

  let eq = elim_const eq in
  let peq = List.map  fst eq in
   
  let pge = List.map 
   (fun (e,psatz) -> poly_of_term (expr_to_term e),psatz) ge in
   
  let monoids = List.map (fun m ->  (List.fold_right (fun (p,kd) y -> 
   let p = poly_of_term (expr_to_term p) in
    match kd with
     | Axiom_lt i -> poly_mul p y
     | Axiom_eq i -> poly_mul (poly_pow p 2) y
     |   _        -> failwith "monoids") m (poly_const (Int 1)) , map  snd m))
   (sets_of_list neq) in

  let (cert_ideal, cert_cone,monoid) = deepen_until d (fun d -> 
   list_try_find (fun m -> let (ci,cc) = 
    real_positivnullstellensatz_general false d peq pge (poly_neg (fst m) ) in
		      (ci,cc,snd m)) monoids) 0 in
   
  let proofs_ideal = map2 (fun q i -> Eqmul(term_of_poly q,Axiom_eq i))  
   cert_ideal (List.map snd eq) in

  let proofs_cone = map term_of_sos cert_cone in
   
  let proof_ne =  
   let (neq , lt) = List.partition 
    (function  Axiom_eq _ -> true | _ -> false ) monoid in
   let sq = match 
     (List.map (function Axiom_eq i -> i | _ -> failwith "error") neq) 
    with
    | []  -> Rational_lt (Int 1)
    | l   -> Monoid l in
    List.fold_right (fun x y -> Product(x,y)) lt sq in

  let proof = list_fold_right_elements 
   (fun s t -> Sum(s,t)) (proof_ne :: proofs_ideal @ proofs_cone) in
   Some proof
 with 
  | Sos.TooDeep -> None


(* This is somewhat buggy, over Z, strict inequality vanish... *)
let pure_sos  l =
 (* If there is no strict inequality, 
    I should nonetheless be able to try something - over Z  > is equivalent to -1  >= *)
 try 
  let l = List.combine l (interval 0 (length l -1)) in
  let (lt,i) =  try (List.find (fun (x,_) -> snd' x =  Mc.Strict) l) 
   with Not_found -> List.hd l in
  let plt = poly_neg (poly_of_term (expr_to_term (fst' lt))) in
  let (n,polys) = sumofsquares plt in (* n * (ci * pi^2) *)
  let pos = Product (Rational_lt n, 
		    List.fold_right (fun (c,p) rst -> Sum (Product (Rational_lt c, Square
		     (term_of_poly p)), rst)) 
		     polys (Rational_lt (Int 0))) in
  let proof = Sum(Axiom_lt i, pos) in
(*  let s,proof' = scale_certificate proof in
  let cert  = snd (cert_of_pos proof') in *)
   Some proof
 with
  | Not_found -> (* This is no strict inequality *) None
  |  x        -> None


type micromega_polys = (Micromega.q Mc.pExpr, Mc.op1) Micromega.prod list
type csdp_certificate = Sos.positivstellensatz option
type provername = string * int option

let main () =
  if Array.length Sys.argv <> 3 then
    (Printf.printf "Usage: csdpcert inputfile outputfile\n"; exit 1);
  let input_file = Sys.argv.(1) in
  let output_file = Sys.argv.(2) in
  let inch = open_in input_file in
  let (prover,poly) = (input_value inch : provername * micromega_polys) in
  close_in inch;
  let cert =
    match prover with
    | "real_nonlinear_prover", Some d -> real_nonlinear_prover d poly
    | "pure_sos", None -> pure_sos poly
    | prover, _ -> (Printf.printf "unknown prover: %s\n" prover; exit 1) in
  let outch = open_out output_file in
  output_value outch (cert:csdp_certificate);
  close_out outch;
  exit 0;;

let _ = main () in ()

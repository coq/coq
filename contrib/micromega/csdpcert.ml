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
  |  PEc z ->  Const  (Big_int (C2Ml.z_big_int z))
  |  PEX v ->  Var ("x"^(string_of_int (C2Ml.index v)))
  |  PEmul(p1,p2) -> 
      let p1 = expr_to_term p1 in
      let p2 = expr_to_term p2 in
      let res = Mul(p1,p2) in 	   res

  | PEadd(p1,p2) -> Add(expr_to_term p1, expr_to_term p2)
  | PEsub(p1,p2) -> Sub(expr_to_term p1, expr_to_term p2)
  | PEpow(p,n)   -> Pow(expr_to_term p , C2Ml.n n)
  |  PEopp p ->  Opp (expr_to_term p)

      
 let rec term_to_expr = function
  | Const n ->  PEc (Ml2C.bigint (big_int_of_num n))
  | Zero   ->  PEc ( Z0)
  | Var s   ->  PEX (Ml2C.index 
		      (int_of_string (String.sub s 1 (String.length s - 1))))
  | Mul(p1,p2) ->  PEmul(term_to_expr p1, term_to_expr p2)
  | Add(p1,p2) ->   PEadd(term_to_expr p1, term_to_expr p2)
  | Opp p ->   PEopp (term_to_expr p)
  | Pow(t,n) ->  PEpow (term_to_expr t,Ml2C.n n)
  | Sub(t1,t2) ->  PEsub (term_to_expr t1,  term_to_expr t2)
  | _ -> failwith "term_to_expr: not implemented"

 let term_to_expr e =
  let e' = term_to_expr e in
   if debug 
   then Printf.printf "term_to_expr : %s - %s\n"  
    (string_of_poly (poly_of_term  e)) 
    (string_of_poly (poly_of_term (expr_to_term e')));
   e'

end 
open M      

open List
open Mutils 

let rec scale_term t = 
 match t with
  | Zero    -> unit_big_int , Zero
  | Const n ->  (denominator n) , Const (Big_int (numerator n))
  | Var n   -> unit_big_int , Var n
  | Inv _   -> failwith "scale_term : not implemented"
  | Opp t   -> let s, t = scale_term t in s, Opp t
  | Add(t1,t2) -> let s1,y1 = scale_term t1 and s2,y2 = scale_term t2 in
    let g = gcd_big_int s1 s2 in
    let s1' = div_big_int s1 g in
    let s2' = div_big_int s2 g in
    let e = mult_big_int g (mult_big_int s1' s2') in
     if (compare_big_int e unit_big_int) = 0
     then (unit_big_int, Add (y1,y2))
     else 	e, Add (Mul(Const (Big_int s2'), y1),
		       Mul (Const (Big_int s1'), y2))
  | Sub _ -> failwith "scale term: not implemented"
  | Mul(y,z) ->       let s1,y1 = scale_term y and s2,y2 = scale_term z in
		       mult_big_int s1 s2 , Mul (y1, y2)
  |  Pow(t,n) -> let s,t = scale_term t in
		  power_big_int_positive_int s  n , Pow(t,n)
  |   _ -> failwith "scale_term : not implemented"

let scale_term t =
 let (s,t') = scale_term t in
  s,t'
   



let rec scale_certificate pos = match pos with
 | Axiom_eq i ->  unit_big_int , Axiom_eq i
 | Axiom_le i ->  unit_big_int , Axiom_le i
 | Axiom_lt i ->   unit_big_int , Axiom_lt i
 | Monoid l   -> unit_big_int , Monoid l
 | Rational_eq n ->  (denominator n) , Rational_eq (Big_int (numerator n))
 | Rational_le n ->  (denominator n) , Rational_le (Big_int (numerator n))
 | Rational_lt n ->  (denominator n) , Rational_lt (Big_int (numerator n))
 | Square t -> let s,t' =  scale_term t in 
		mult_big_int s s , Square t'
 | Eqmul (t, y) -> let s1,y1 = scale_term t and s2,y2 = scale_certificate y in
		    mult_big_int s1 s2 , Eqmul (y1,y2)
 | Sum (y, z) -> let s1,y1 = scale_certificate y 
   and s2,y2 = scale_certificate z in
   let g = gcd_big_int s1 s2 in
   let s1' = div_big_int s1 g in
   let s2' = div_big_int s2 g in
    mult_big_int g (mult_big_int s1' s2'), 
    Sum (Product(Rational_le (Big_int s2'), y1),
	Product (Rational_le (Big_int s1'), y2))
 | Product (y, z) -> 
    let s1,y1 = scale_certificate y and s2,y2 = scale_certificate z in
     mult_big_int s1 s2 , Product (y1,y2)


let is_eq = function  Mc.Equal -> true | _ -> false
let is_le = function  Mc.NonStrict -> true | _ -> false
let is_lt = function  Mc.Strict -> true | _ -> false

let get_index_of_ith_match f i l  =
 let rec get j res l =
  match l with
   | [] -> failwith "bad index"
   | e::l -> if f e
     then 
       (if j = i then res else get (j+1) (res+1) l )
     else get j (res+1) l in
  get 0 0 l


let  cert_of_pos eq le lt ll l pos = 
 let s,pos = (scale_certificate pos) in
 let rec _cert_of_pos = function
   Axiom_eq i -> let idx = get_index_of_ith_match is_eq i l in
		  Mc.S_In (Ml2C.nat idx)
  | Axiom_le i -> let idx = get_index_of_ith_match is_le i l in
		   Mc.S_In (Ml2C.nat idx)
  | Axiom_lt i -> let idx = get_index_of_ith_match is_lt i l in
		   Mc.S_In (Ml2C.nat idx)
  | Monoid l  -> Mc.S_Monoid (Ml2C.list Ml2C.nat l)
  | Rational_eq n | Rational_le n | Rational_lt n -> 
     if compare_num n (Int 0) = 0 then Mc.S_Z else
      Mc.S_Pos (Ml2C.bigint (big_int_of_num  n))
  | Square t -> Mc.S_Square (term_to_expr  t)
  | Eqmul (t, y) -> Mc.S_Ideal(term_to_expr t, _cert_of_pos y)
  | Sum (y, z) -> Mc.S_Add  (_cert_of_pos y, _cert_of_pos z)
  | Product (y, z) -> Mc.S_Mult (_cert_of_pos y, _cert_of_pos z) in
  s, Certificate.simplify_cone Certificate.z_spec (_cert_of_pos pos)


let  term_of_cert l pos = 
 let l = List.map fst' l in
 let rec _cert_of_pos = function
  | Mc.S_In i -> expr_to_term (List.nth l (C2Ml.nat i))
  | Mc.S_Pos p -> Const (C2Ml.num  p)
  | Mc.S_Z     -> Const (Int 0)
  | Mc.S_Square t -> Mul(expr_to_term t, expr_to_term t)
  | Mc.S_Monoid m -> List.fold_right 
     (fun x m -> Mul (expr_to_term (List.nth l (C2Ml.nat x)),m)) 
     (C2Ml.list (fun x -> x) m)  (Const (Int 1))
  | Mc.S_Ideal (t, y) -> Mul(expr_to_term t, _cert_of_pos y)
  | Mc.S_Add (y, z) -> Add  (_cert_of_pos y, _cert_of_pos z)
  | Mc.S_Mult (y, z) -> Mul (_cert_of_pos y, _cert_of_pos z) in
  (_cert_of_pos pos)

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

let  cert_of_pos  pos = 
 let s,pos = (scale_certificate pos) in
 let rec _cert_of_pos = function
   Axiom_eq i ->  Mc.S_In (Ml2C.nat i)
  | Axiom_le i ->  Mc.S_In (Ml2C.nat i)
  | Axiom_lt i ->  Mc.S_In (Ml2C.nat i)
  | Monoid l  -> Mc.S_Monoid (Ml2C.list Ml2C.nat l)
  | Rational_eq n | Rational_le n | Rational_lt n -> 
     if compare_num n (Int 0) = 0 then Mc.S_Z else
      Mc.S_Pos (Ml2C.bigint (big_int_of_num  n))
  | Square t -> Mc.S_Square (term_to_expr  t)
  | Eqmul (t, y) -> Mc.S_Ideal(term_to_expr t, _cert_of_pos y)
  | Sum (y, z) -> Mc.S_Add  (_cert_of_pos y, _cert_of_pos z)
  | Product (y, z) -> Mc.S_Mult (_cert_of_pos y, _cert_of_pos z) in
  s, Certificate.simplify_cone Certificate.z_spec (_cert_of_pos pos)

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
   
  let s,proof' = scale_certificate proof in
  let cert  = snd (cert_of_pos proof') in
   if debug 
   then Printf.printf "cert poly : %s\n" 
    (string_of_poly (poly_of_term (term_of_cert l cert)));
   match Mc.zWeakChecker (Ml2C.list (fun x -> x) l)  cert with
    | Mc.True -> Some cert
    | Mc.False ->  (print_string "buggy certificate" ; flush stdout) ;None
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
  let s,proof' = scale_certificate proof in
  let cert  = snd (cert_of_pos proof') in
   Some cert
 with
  | Not_found -> (* This is no strict inequality *) None
  |  x        -> None


type micromega_polys = (Micromega.z Mc.pExpr, Mc.op1) Micromega.prod list
type csdp_certificate = Certificate.Mc.z Certificate.Mc.coneMember option
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

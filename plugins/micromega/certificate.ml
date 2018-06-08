(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

(* We take as input a list of polynomials [p1...pn] and return an unfeasibility
   certificate polynomial. *)

let debug = false

open Util
open Big_int
open Num
open Polynomial

module Mc = Micromega
module Ml2C = Mutils.CamlToCoq
module C2Ml = Mutils.CoqToCaml


open Mutils
type 'a number_spec = {
 bigint_to_number : big_int -> 'a;
 number_to_num : 'a  -> num;
 zero : 'a;
 unit : 'a;
 mult : 'a -> 'a -> 'a;
 eqb  : 'a -> 'a -> bool
}

let z_spec = {
 bigint_to_number = Ml2C.bigint ;
 number_to_num = (fun x -> Big_int (C2Ml.z_big_int x));
 zero = Mc.Z0;
 unit = Mc.Zpos Mc.XH;
 mult = Mc.Z.mul;
 eqb  = Mc.zeq_bool
}
 

let q_spec = {
 bigint_to_number = (fun x -> {Mc.qnum = Ml2C.bigint x; Mc.qden = Mc.XH});
 number_to_num = C2Ml.q_to_num;
 zero = {Mc.qnum = Mc.Z0;Mc.qden = Mc.XH};
 unit = {Mc.qnum =  (Mc.Zpos Mc.XH) ; Mc.qden = Mc.XH};
 mult = Mc.qmult;
 eqb  = Mc.qeq_bool
}

let dev_form n_spec  p =
 let rec dev_form p = 
  match p with
  | Mc.PEc z ->  Poly.constant (n_spec.number_to_num z)
  | Mc.PEX v ->  Poly.variable (C2Ml.positive v)
  | Mc.PEmul(p1,p2) -> 
   let p1 = dev_form p1 in
   let p2 = dev_form p2 in
   Poly.product p1 p2 
  | Mc.PEadd(p1,p2) -> Poly.addition (dev_form p1) (dev_form p2)
  | Mc.PEopp p ->  Poly.uminus (dev_form p)
  | Mc.PEsub(p1,p2) ->  Poly.addition (dev_form p1) (Poly.uminus (dev_form p2))
  | Mc.PEpow(p,n)   ->  
   let p = dev_form p in
   let n = C2Ml.n n in
   let rec pow n = 
    if Int.equal n 0 
    then Poly.constant (n_spec.number_to_num n_spec.unit)
    else Poly.product p (pow (n-1)) in
   pow n in
 dev_form p

let rec fixpoint f x =
 let y' = f x in
 if Pervasives.(=) y' x then y'
 else fixpoint f y'

let  rec_simpl_cone n_spec e = 
 let simpl_cone = 
  Mc.simpl_cone n_spec.zero n_spec.unit n_spec.mult n_spec.eqb in

 let rec rec_simpl_cone  = function
  | Mc.PsatzMulE(t1, t2) -> 
   simpl_cone  (Mc.PsatzMulE (rec_simpl_cone t1, rec_simpl_cone t2))
  | Mc.PsatzAdd(t1,t2)  -> 
   simpl_cone (Mc.PsatzAdd (rec_simpl_cone t1, rec_simpl_cone t2))
  |  x           -> simpl_cone x in
 rec_simpl_cone e
  
  
let simplify_cone n_spec c = fixpoint (rec_simpl_cone n_spec) c

let factorise_linear_cone c =
 
 let rec cone_list  c l = 
  match c with
  | Mc.PsatzAdd (x,r) -> cone_list  r (x::l)
  |  _        ->  c :: l in
 
 let factorise c1 c2 =
  match c1 , c2 with
  | Mc.PsatzMulC(x,y) , Mc.PsatzMulC(x',y') -> 
   if Pervasives.(=) x x' then Some (Mc.PsatzMulC(x, Mc.PsatzAdd(y,y'))) else None
  | Mc.PsatzMulE(x,y) , Mc.PsatzMulE(x',y') -> 
   if Pervasives.(=) x x' then Some (Mc.PsatzMulE(x, Mc.PsatzAdd(y,y'))) else None
  |  _     -> None in
 
 let rec rebuild_cone l pending  =
  match l with
  | [] -> (match pending with
   | None -> Mc.PsatzZ
   | Some p -> p
  )
  | e::l -> 
   (match pending with
   | None -> rebuild_cone l (Some e) 
   | Some p -> (match factorise p e with
    | None -> Mc.PsatzAdd(p, rebuild_cone l (Some e))
    | Some f -> rebuild_cone l (Some f) )
   ) in

 (rebuild_cone (List.sort Pervasives.compare (cone_list c [])) None)



(* The binding with Fourier might be a bit obsolete 
   -- how does it handle equalities ? *)

(* Certificates are elements of the cone such that P = 0  *)

(* To begin with, we search for certificates of the form:
   a1.p1 + ... an.pn + b1.q1 +... + bn.qn + c = 0   
   where pi >= 0 qi > 0
   ai >= 0 
   bi >= 0
   Sum bi + c >= 1
   This is a linear problem: each monomial is considered as a variable.
   Hence, we can use fourier.

   The variable c is at index 0
*)

open Mfourier

(* fold_left followed by a rev ! *)

let constrain_monomial mn l  = 
 let coeffs = List.fold_left (fun acc p -> (Poly.get mn p)::acc) [] l in
 if Pervasives.(=) mn Monomial.const
 then  
  { coeffs = Vect.from_list ((Big_int unit_big_int):: (List.rev coeffs)) ; 
    op = Eq ; 
    cst = Big_int zero_big_int  }
 else
  { coeffs = Vect.from_list ((Big_int zero_big_int):: (List.rev coeffs)) ; 
    op = Eq ; 
    cst = Big_int zero_big_int  }

   
let positivity l = 
 let rec xpositivity i l = 
  match l with
  | [] -> []
  | (_,Mc.Equal)::l -> xpositivity (i+1) l
  | (_,_)::l -> 
   {coeffs = Vect.update (i+1) (fun _ -> Int 1) Vect.null ; 
    op = Ge ; 
    cst = Int 0 }  :: (xpositivity (i+1) l)
 in
 xpositivity 0 l

module MonSet = Set.Make(Monomial)

(* If the certificate includes at least one strict inequality, 
   the obtained polynomial can also be 0 *)
let build_linear_system l =

 (* Gather the monomials:  HINT add up of the polynomials ==> This does not work anymore *)
 let l' = List.map fst l in

 let monomials = 
  List.fold_left (fun acc p -> 
   Poly.fold (fun m _ acc -> MonSet.add m acc) p acc) 
   (MonSet.singleton Monomial.const) l'
 in  (* For each monomial, compute a constraint *)
 let s0 = 
  MonSet.fold (fun mn  res -> (constrain_monomial mn l')::res) monomials [] in
 (* I need at least something strictly positive *)
 let strict = {
  coeffs = Vect.from_list ((Big_int unit_big_int)::
                            (List.map (fun (x,y) -> 
                             match y with Mc.Strict -> 
                              Big_int unit_big_int 
                             | _ -> Big_int zero_big_int) l));
  op = Ge ; cst = Big_int unit_big_int } in
  (* Add the positivity constraint *)
 {coeffs = Vect.from_list ([Big_int unit_big_int]) ; 
  op = Ge ; 
  cst = Big_int zero_big_int}::(strict::(positivity l)@s0)

(* For Q, this is a pity that the certificate has been scaled 
   -- at a lower layer, certificates are using nums... *)
let make_certificate n_spec (cert,li) = 
 let bint_to_cst = n_spec.bigint_to_number in
 match cert with
 | [] -> failwith "empty_certificate"
 | e::cert' -> 
      (*      let cst = match compare_big_int e zero_big_int with
              | 0 -> Mc.PsatzZ
              | 1 ->  Mc.PsatzC (bint_to_cst e) 
              | _ -> failwith "positivity error" 
              in *)
  let rec scalar_product cert l =
   match cert with
   | [] -> Mc.PsatzZ
   | c::cert -> 
    match l with
    | [] -> failwith "make_certificate(1)"
    | i::l ->  
     let r = scalar_product cert l in
     match compare_big_int c  zero_big_int with
     | -1 -> Mc.PsatzAdd (
      Mc.PsatzMulC (Mc.Pc ( bint_to_cst c), Mc.PsatzIn (Ml2C.nat i)), 
      r)
     | 0  -> r
     | _ ->  Mc.PsatzAdd (
      Mc.PsatzMulE (Mc.PsatzC (bint_to_cst c), Mc.PsatzIn (Ml2C.nat i)),
      r) in
  (factorise_linear_cone 
    (simplify_cone n_spec (scalar_product cert' li)))


exception Strict

module MonMap = Map.Make(Monomial)

let primal l = 
 let vr = ref 0 in

 let vect_of_poly map p =
  Poly.fold (fun mn vl (map,vect) -> 
   if Pervasives.(=) mn Monomial.const 
   then (map,vect)
   else 
    let (mn,m) = try (MonMap.find mn map,map) with Not_found -> let res = (!vr, MonMap.add mn !vr map) in incr vr ; res in
    (m,if Int.equal (sign_num vl) 0 then vect else (mn,vl)::vect)) p (map,[]) in
 
 let op_op = function Mc.NonStrict -> Ge |Mc.Equal -> Eq | _ -> raise Strict in

 let cmp x y = Int.compare (fst x) (fst y) in

 snd (List.fold_right (fun  (p,op) (map,l) ->
  let (mp,vect) = vect_of_poly map p in  
  let cstr = {coeffs = List.sort cmp vect; op = op_op op ; cst = minus_num (Poly.get Monomial.const p)} in

  (mp,cstr::l)) l (MonMap.empty,[]))

let dual_raw_certificate (l:  (Poly.t * Mc.op1) list) = 
 (*  List.iter (fun (p,op) -> Printf.fprintf stdout "%a %s 0\n" Poly.pp p (string_of_op op) ) l ; *)
 
 let sys = build_linear_system l in

 try 
  match Fourier.find_point sys with
  | Inr _ -> None
  | Inl cert ->  Some (rats_to_ints (Vect.to_list cert)) 
  (* should not use rats_to_ints *)
 with x when CErrors.noncritical x ->
  if debug
  then (Printf.printf "raw certificate %s" (Printexc.to_string x);
        flush stdout) ;
  None


let raw_certificate l = 
 try 
  let p = primal l in
  match Fourier.find_point p with
  | Inr prf -> 
   if debug then Printf.printf "AProof : %a\n" pp_proof prf ; 
   let cert = List.map (fun (x,n) -> x+1,n) (fst (List.hd (Proof.mk_proof p prf))) in
   if debug then Printf.printf "CProof : %a" Vect.pp_vect cert ; 
   Some (rats_to_ints (Vect.to_list cert))
  | Inl _   -> None
 with Strict -> 
    (* Fourier elimination should handle > *)
  dual_raw_certificate l 


let simple_linear_prover  l =
 let (lc,li) = List.split l in
 match raw_certificate lc with
 |  None -> None (* No certificate *)
 | Some cert -> Some (cert,li)
  




let linear_prover n_spec l  =
 let build_system n_spec l = 
  let li = List.combine l (CList.interval 0 (List.length l -1)) in
  let (l1,l') = List.partition 
   (fun (x,_) -> if Pervasives.(=) (snd x) Mc.NonEqual then true else false) li in
  List.map 
   (fun ((x,y),i) -> match y with
    Mc.NonEqual -> failwith "cannot happen"
   |  y -> ((dev_form n_spec x, y),i)) l' in
 let l' = build_system n_spec l in 
 simple_linear_prover (*n_spec*) l' 


let linear_prover n_spec l  =
 try linear_prover n_spec l
 with x when CErrors.noncritical x ->
  (print_string (Printexc.to_string x); None)

let compute_max_nb_cstr l d =
 let len = List.length l in
 max len (max d (len * d)) 

let linear_prover_with_cert prfdepth spec  l = 
 max_nb_cstr := compute_max_nb_cstr l prfdepth ;
 match linear_prover spec l with
 | None -> None
 | Some cert -> Some (make_certificate spec cert)

let nlinear_prover prfdepth (sys: (Mc.q Mc.pExpr * Mc.op1) list) = 
 LinPoly.MonT.clear ();
 max_nb_cstr := compute_max_nb_cstr sys prfdepth ;
 (* Assign a proof to the initial hypotheses *)
 let sys  = List.mapi (fun i c -> (c,Mc.PsatzIn (Ml2C.nat i))) sys in


 (* Add all the product of hypotheses *)
 let prod = all_pairs (fun ((c,o),p) ((c',o'),p') -> 
  ((Mc.PEmul(c,c') , Mc.opMult o o') , Mc.PsatzMulE(p,p'))) sys in

 (* Only filter those have a meaning *)
 let prod = List.fold_left (fun l ((c,o),p) -> 
  match o with
  | None -> l
  | Some o -> ((c,o),p) :: l) [] prod in

 let sys = sys @ prod in

 let square = 
  (* Collect the squares and state that they are positive *)
  let pols = List.map (fun ((p,_),_) -> dev_form q_spec p) sys in
  let square = 
   List.fold_left (fun acc p -> 
    Poly.fold 
     (fun m _ acc -> 
      match Monomial.sqrt m with
      | None -> acc
      | Some s -> MonMap.add  s m acc)  p acc) MonMap.empty pols in

  let pol_of_mon m =
   Monomial.fold (fun x v p -> Mc.PEmul(Mc.PEpow(Mc.PEX(Ml2C.positive x),Ml2C.n v),p)) m (Mc.PEc q_spec.unit) in

  let norm0 =
   Mc.norm q_spec.zero q_spec.unit Mc.qplus Mc.qmult Mc.qminus Mc.qopp Mc.qeq_bool in
  
  
  MonMap.fold (fun s m acc -> ((pol_of_mon m , Mc.NonStrict), Mc.PsatzSquare(norm0 (pol_of_mon s)))::acc) square [] in

 let sys = sys @ square in


 (* Call the linear prover without the proofs *)
 let sys_no_prf = List.map fst sys in

 match linear_prover q_spec sys_no_prf with
 | None -> None
 | Some cert -> 
  let cert = make_certificate q_spec cert in
  let rec map_psatz = function
   | Mc.PsatzIn n        -> snd (List.nth sys (C2Ml.nat n))
   | Mc.PsatzSquare c    -> Mc.PsatzSquare c
   | Mc.PsatzMulC(c,p)   -> Mc.PsatzMulC(c, map_psatz p)
   | Mc.PsatzMulE(p1,p2) -> Mc.PsatzMulE(map_psatz p1,map_psatz p2)
   | Mc.PsatzAdd(p1,p2)  -> Mc.PsatzAdd(map_psatz p1,map_psatz p2)
   | Mc.PsatzC c         -> Mc.PsatzC c
   | Mc.PsatzZ           -> Mc.PsatzZ in
  Some (map_psatz cert)

(* The prover is (probably) incomplete -- 
   only searching for naive cutting planes *)

let develop_constraint z_spec (e,k) = 
 match k with
 | Mc.NonStrict -> (dev_form z_spec e , Ge)
 | Mc.Equal     ->  (dev_form z_spec e , Eq)
 | _     -> assert false

open Sos_types

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
                 if Int.equal (compare_big_int e unit_big_int) 0
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


open Micromega
let rec term_to_q_expr = function
 | Const n ->  PEc (Ml2C.q n)
 | Zero   ->  PEc ( Ml2C.q (Int 0))
 | Var s   ->  PEX (Ml2C.index 
		     (int_of_string (String.sub s 1 (String.length s - 1))))
 | Mul(p1,p2) ->  PEmul(term_to_q_expr p1, term_to_q_expr p2)
 | Add(p1,p2) ->   PEadd(term_to_q_expr p1, term_to_q_expr p2)
 | Opp p ->   PEopp (term_to_q_expr p)
 | Pow(t,n) ->  PEpow (term_to_q_expr t,Ml2C.n n)
 | Sub(t1,t2) ->  PEsub (term_to_q_expr t1,  term_to_q_expr t2)
 | _ -> failwith "term_to_q_expr: not implemented"

let term_to_q_pol e = Mc.norm_aux (Ml2C.q (Int 0)) (Ml2C.q (Int 1)) Mc.qplus  Mc.qmult Mc.qminus Mc.qopp Mc.qeq_bool (term_to_q_expr e)


let rec product l = 
 match l with
 | [] -> Mc.PsatzZ
 | [i] -> Mc.PsatzIn (Ml2C.nat i)
 | i ::l -> Mc.PsatzMulE(Mc.PsatzIn (Ml2C.nat i), product l)


let  q_cert_of_pos  pos = 
 let rec _cert_of_pos = function
 Axiom_eq i ->  Mc.PsatzIn (Ml2C.nat i)
  | Axiom_le i ->  Mc.PsatzIn (Ml2C.nat i)
  | Axiom_lt i ->  Mc.PsatzIn (Ml2C.nat i)
  | Monoid l  -> product l
  | Rational_eq n | Rational_le n | Rational_lt n -> 
   if Int.equal (compare_num n (Int 0)) 0 then Mc.PsatzZ else
    Mc.PsatzC (Ml2C.q   n)
  | Square t -> Mc.PsatzSquare (term_to_q_pol  t)
  | Eqmul (t, y) -> Mc.PsatzMulC(term_to_q_pol t, _cert_of_pos y)
  | Sum (y, z) -> Mc.PsatzAdd  (_cert_of_pos y, _cert_of_pos z)
  | Product (y, z) -> Mc.PsatzMulE (_cert_of_pos y, _cert_of_pos z) in
 simplify_cone q_spec (_cert_of_pos pos)


let rec term_to_z_expr = function
 | Const n ->  PEc (Ml2C.bigint (big_int_of_num n))
 | Zero   ->  PEc ( Z0)
 | Var s   ->  PEX (Ml2C.index 
		     (int_of_string (String.sub s 1 (String.length s - 1))))
 | Mul(p1,p2) ->  PEmul(term_to_z_expr p1, term_to_z_expr p2)
 | Add(p1,p2) ->   PEadd(term_to_z_expr p1, term_to_z_expr p2)
 | Opp p ->   PEopp (term_to_z_expr p)
 | Pow(t,n) ->  PEpow (term_to_z_expr t,Ml2C.n n)
 | Sub(t1,t2) ->  PEsub (term_to_z_expr t1,  term_to_z_expr t2)
 | _ -> failwith "term_to_z_expr: not implemented"

let term_to_z_pol e = Mc.norm_aux (Ml2C.z 0) (Ml2C.z 1) Mc.Z.add  Mc.Z.mul Mc.Z.sub Mc.Z.opp Mc.zeq_bool (term_to_z_expr e)

let  z_cert_of_pos  pos = 
 let s,pos = (scale_certificate pos) in
 let rec _cert_of_pos = function
 Axiom_eq i ->  Mc.PsatzIn (Ml2C.nat i)
  | Axiom_le i ->  Mc.PsatzIn (Ml2C.nat i)
  | Axiom_lt i ->  Mc.PsatzIn (Ml2C.nat i)
  | Monoid l  -> product l
  | Rational_eq n | Rational_le n | Rational_lt n -> 
   if Int.equal (compare_num n (Int 0)) 0 then Mc.PsatzZ else
    Mc.PsatzC (Ml2C.bigint (big_int_of_num  n))
  | Square t -> Mc.PsatzSquare (term_to_z_pol  t)
  | Eqmul (t, y) -> 
   let is_unit =
    match t with
    | Const n -> n =/ Int 1 
    |   _     -> false in
   if is_unit
   then _cert_of_pos y
   else Mc.PsatzMulC(term_to_z_pol t, _cert_of_pos y)
  | Sum (y, z) -> Mc.PsatzAdd  (_cert_of_pos y, _cert_of_pos z)
  | Product (y, z) -> Mc.PsatzMulE (_cert_of_pos y, _cert_of_pos z) in
 simplify_cone z_spec (_cert_of_pos pos)

(** All constraints (initial or derived) have an index and have a justification i.e., proof.
    Given a constraint, all the coefficients are always integers.
*)
open Mutils
open Mfourier
open Num
open Big_int
open Polynomial


module Env = 
struct

 let id_of_hyp hyp l = 
  let rec xid_of_hyp i l = 
   match l with
   | [] -> failwith "id_of_hyp"
   | hyp'::l -> if Pervasives.(=) hyp hyp' then i else xid_of_hyp (i+1) l in
  xid_of_hyp 0 l

end


let  coq_poly_of_linpol (p,c) = 

 let pol_of_mon m =
  Monomial.fold (fun x v p -> Mc.PEmul(Mc.PEpow(Mc.PEX(Ml2C.positive x),Ml2C.n v),p)) m (Mc.PEc (Mc.Zpos Mc.XH)) in

 List.fold_left (fun acc (x,v) -> 
  let mn = LinPoly.MonT.retrieve x in
  Mc.PEadd(Mc.PEmul(Mc.PEc (Ml2C.bigint (numerator v)), pol_of_mon mn),acc)) (Mc.PEc (Ml2C.bigint (numerator c))) p
  



let rec cmpl_prf_rule env = function
 | Hyp i | Def i -> Mc.PsatzIn (Ml2C.nat (Env.id_of_hyp i env))
 | Cst i         -> Mc.PsatzC (Ml2C.bigint i)
 | Zero          -> Mc.PsatzZ
 | MulPrf(p1,p2)      -> Mc.PsatzMulE(cmpl_prf_rule env p1, cmpl_prf_rule env p2)
 | AddPrf(p1,p2)      -> Mc.PsatzAdd(cmpl_prf_rule env p1 , cmpl_prf_rule env p2)
 | MulC(lp,p)  -> let lp = Mc.norm0 (coq_poly_of_linpol lp) in
                  Mc.PsatzMulC(lp,cmpl_prf_rule env p)
 | Square lp      -> Mc.PsatzSquare (Mc.norm0 (coq_poly_of_linpol lp))
 | _                  -> failwith "Cuts should already be compiled"
  

let rec cmpl_proof env = function
 | Done ->  Mc.DoneProof
 | Step(i,p,prf) -> 
  begin
   match p with
   | CutPrf p' -> 
    Mc.CutProof(cmpl_prf_rule env p', cmpl_proof (i::env) prf)
   |   _       -> Mc.RatProof(cmpl_prf_rule env p,cmpl_proof (i::env) prf)
  end
 | Enum(i,p1,_,p2,l) -> 
  Mc.EnumProof(cmpl_prf_rule env p1,cmpl_prf_rule env p2,List.map (cmpl_proof (i::env)) l)


let compile_proof env prf = 
 let id = 1 + proof_max_id prf in
 let _,prf = normalise_proof id prf in
 if debug then Printf.fprintf stdout "compiled proof %a\n" output_proof prf;
 cmpl_proof env prf

type prf_sys = (cstr_compat * prf_rule) list


let xlinear_prover sys = 
 match Fourier.find_point sys with
 | Inr prf -> 
  if debug then Printf.printf "AProof : %a\n" pp_proof prf ; 
  let cert = (*List.map (fun (x,n) -> x+1,n)*) (fst (List.hd (Proof.mk_proof sys prf))) in
  if debug then Printf.printf "CProof : %a" Vect.pp_vect cert ; 
  Some (rats_to_ints (Vect.to_list cert))
 | Inl _   -> None


let proof_of_farkas prf cert = 
  (*  Printf.printf "\nproof_of_farkas  %a , %a \n" (pp_list output_prf_rule) prf (pp_list output_bigint) cert ;  *)
 let rec mk_farkas acc prf cert = 
  match prf, cert with
  |   _  , []   -> acc
  |  []  , _    -> failwith "proof_of_farkas : not enough hyps"
  |  p::prf,c::cert -> 
   mk_farkas (add_proof (mul_proof c p) acc) prf cert in
 let res =  mk_farkas Zero prf cert in
    (*Printf.printf "==> %a" output_prf_rule res ; *)
 res


let linear_prover sys =
 let (sysi,prfi) = List.split sys in
 match xlinear_prover sysi with
 | None -> None
 | Some cert -> Some (proof_of_farkas prfi cert)

let linear_prover  = 
 if debug 
 then 
  fun sys -> 
   Printf.printf "<linear_prover"; flush stdout ;
   let res = linear_prover sys in
   Printf.printf ">"; flush stdout ;
   res
 else linear_prover
  



(** A single constraint can be unsat for the following reasons:
    - 0 >= c for c a negative constant
    - 0 =  c for c a non-zero constant
    - e = c  when the coeffs of e are all integers and c is rational
*)

type checksat = 
| Tauto (* Tautology *)
| Unsat of prf_rule (* Unsatisfiable *)
| Cut of cstr_compat * prf_rule (* Cutting plane *)
| Normalise of cstr_compat * prf_rule (* coefficients are relatively prime *)
  

(** [check_sat] 
    - detects constraints that are not satisfiable;
    - normalises constraints and generate cuts.
*)

let check_sat (cstr,prf) = 
 let {coeffs=coeffs ; op=op ; cst=cst} = cstr in
 match coeffs with
 | [] -> 
  if eval_op op (Int 0) cst then Tauto else Unsat prf
 | _  -> 
  let gcdi =  (gcd_list (List.map snd coeffs)) in
  let gcd = Big_int gcdi in
  if eq_num gcd (Int 1)
  then Normalise(cstr,prf) 
  else
   if Int.equal (sign_num (mod_num cst gcd)) 0
   then (* We can really normalise *)
    begin
     assert (sign_num gcd >=1 ) ;
     let cstr = {
      coeffs = List.map (fun (x,v) -> (x, v // gcd)) coeffs; 
      op = op ; cst = cst // gcd
     } in 
     Normalise(cstr,Gcd(gcdi,prf))
	      (*		    Normalise(cstr,CutPrf prf)*)
    end
   else
    match op with
    | Eq -> Unsat (CutPrf prf)
    | Ge -> 
     let cstr = {
      coeffs = List.map (fun (x,v) -> (x, v // gcd)) coeffs; 
      op = op ; cst = ceiling_num (cst // gcd)
     } in Cut(cstr,CutPrf prf)


(** Proof generating pivoting over variable v *)
let pivot v (c1,p1) (c2,p2) = 
 let {coeffs = v1 ; op = op1 ; cst = n1} = c1
 and {coeffs = v2 ; op = op2 ; cst = n2} = c2 in



  (* Could factorise gcd... *)
 let xpivot cv1 cv2 =
  (
   {coeffs = Vect.add (Vect.mul cv1 v1) (Vect.mul cv2 v2) ;
    op = Proof.add_op op1 op2 ;
    cst = n1 */ cv1 +/ n2 */ cv2 },

   AddPrf(mul_proof (numerator cv1) p1,mul_proof (numerator cv2) p2)) in
 
 match Vect.get v v1 , Vect.get v v2 with
 | None , _ | _ , None -> None
 | Some a   , Some b   ->
  if Int.equal ((sign_num a) * (sign_num b)) (-1)
  then 
   let cv1 = abs_num b 
   and cv2 = abs_num a  in
   Some (xpivot cv1 cv2)
  else 
   if op1 == Eq
   then 
    let cv1 = minus_num (b */ (Int (sign_num a)))
    and cv2 = abs_num a in
    Some (xpivot cv1 cv2)
   else if op2 == Eq
   then
    let cv1 = abs_num b 
    and cv2 = minus_num (a */ (Int  (sign_num b))) in
    Some (xpivot cv1 cv2)
   else  None (* op2 could be Eq ... this might happen *)
    
exception FoundProof of  prf_rule

let simpl_sys sys = 
 List.fold_left (fun acc (c,p) -> 
  match check_sat (c,p) with
  | Tauto -> acc
  | Unsat prf -> raise (FoundProof prf)
  | Cut(c,p)  -> (c,p)::acc
  | Normalise (c,p) -> (c,p)::acc) [] sys


(** [ext_gcd a b] is the extended Euclid algorithm.
    [ext_gcd a b = (x,y,g)] iff [ax+by=g]
    Source: http://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
*)
let rec ext_gcd a b = 
 if Int.equal (sign_big_int b) 0 
 then (unit_big_int,zero_big_int)
 else
  let (q,r) = quomod_big_int a b in
  let (s,t) = ext_gcd b r in
  (t, sub_big_int s (mult_big_int q t))

let extract_coprime (c1,p1) (c2,p2) = 
 let rec exist2 vect1 vect2 = 
  match vect1 , vect2 with
  | _ , [] | [], _ -> None
  | (v1,n1)::vect1' , (v2, n2) :: vect2' -> 
   if Pervasives.(=) v1 v2
   then 
    if Int.equal (compare_big_int (gcd_big_int (numerator n1) (numerator n2)) unit_big_int) 0
    then Some (v1,n1,n2)
    else 
     exist2 vect1' vect2'
   else
    if v1 < v2 
    then exist2 vect1' vect2
    else exist2 vect1 vect2' in
 
 if c1.op == Eq && c2.op == Eq 
 then exist2 c1.coeffs c2.coeffs
 else None

let extract2 pred l =
 let rec xextract2 rl l = 
  match l with
  | [] -> (None,rl) (* Did not find *)
  | e::l ->
   match extract (pred e) l with
   | None,_ -> xextract2 (e::rl) l
   | Some (r,e'),l' -> Some (r,e,e'), List.rev_append rl l' in
 
 xextract2 [] l


let extract_coprime_equation psys = 
 extract2 extract_coprime psys


let apply_and_normalise f psys =
 List.fold_left (fun acc pc' -> 
  match f pc' with
  | None -> pc'::acc
  | Some pc' -> 
   match check_sat pc' with
   | Tauto -> acc
   | Unsat prf -> raise (FoundProof prf)
   | Cut(c,p)  -> (c,p)::acc
   | Normalise (c,p) -> (c,p)::acc
 ) [] psys




let pivot_sys v pc psys = apply_and_normalise (pivot v pc) psys


let reduce_coprime psys = 
 let oeq,sys = extract_coprime_equation psys in
 match oeq with
 | None -> None (* Nothing to do *)
 | Some((v,n1,n2),(c1,p1),(c2,p2) ) -> 
  let (l1,l2) = ext_gcd (numerator n1) (numerator n2) in
  let l1' = Big_int l1 and l2' = Big_int l2 in
  let cstr = 
   {coeffs = Vect.add (Vect.mul l1' c1.coeffs) (Vect.mul l2' c2.coeffs);
    op = Eq ; 
    cst = (l1' */ c1.cst) +/ (l2' */ c2.cst) 
   } in
  let prf = add_proof (mul_proof (numerator l1') p1) (mul_proof (numerator l2') p2) in

  Some (pivot_sys v (cstr,prf) ((c1,p1)::sys))

(** If there is an equation [eq] of the form 1.x + e = c, do a pivot over x with equation [eq] *)
let reduce_unary psys = 
 let is_unary_equation (cstr,prf) = 
  if cstr.op == Eq 
  then 
   try 
    Some (fst (List.find (fun (_,n) -> n =/ (Int 1) || n=/ (Int (-1))) cstr.coeffs))
   with Not_found -> None
  else None in

 let (oeq,sys) =  extract is_unary_equation psys in
 match oeq with
 | None -> None (* Nothing to do *)
 | Some(v,pc) -> 
  Some(pivot_sys v pc sys)

let reduce_non_lin_unary psys = 

 let is_unary_equation (cstr,prf) = 
  if cstr.op == Eq 
  then 
   try 
    let x = fst (List.find (fun (x,n) ->  (n =/ (Int 1) || n=/ (Int (-1))) && Monomial.is_var (LinPoly.MonT.retrieve x) ) cstr.coeffs) in
    let x' = LinPoly.MonT.retrieve x in
    if List.for_all (fun (y,_) -> Pervasives.(=) y x  || Int.equal (snd (Monomial.div (LinPoly.MonT.retrieve y) x')) 0) cstr.coeffs 
    then Some x
    else None
   with Not_found -> None
  else None in


 let (oeq,sys) =   extract is_unary_equation psys in
 match oeq with
 | None -> None (* Nothing to do *)
 | Some(v,pc) -> 
  Some(apply_and_normalise (LinPoly.pivot_eq v pc) sys)

let reduce_var_change psys = 

 let rec rel_prime vect = 
  match vect with
  | [] -> None
  | (x,v)::vect -> 
   let v = numerator v in
   try 
    let (x',v') = List.find (fun (_,v') -> 
     let v' = numerator v' in 
     eq_big_int (gcd_big_int  v v') unit_big_int) vect in
    Some ((x,v),(x',numerator v'))
   with Not_found -> rel_prime vect in

 let rel_prime (cstr,prf) =  if cstr.op == Eq then rel_prime cstr.coeffs else None in

 let (oeq,sys) = extract rel_prime psys in
 
 match oeq with
 | None -> None
 | Some(((x,v),(x',v')),(c,p)) -> 
  let (l1,l2) = ext_gcd  v  v' in
  let l1,l2 = Big_int l1 , Big_int l2 in

  let get v vect = 
   match Vect.get v vect with
   | None -> Int 0
   | Some n -> n in

  let pivot_eq (c',p') = 
   let {coeffs = coeffs ; op = op ; cst = cst} = c' in
   let vx = get x coeffs in
   let vx' = get x' coeffs in
   let m = minus_num (vx */ l1 +/ vx' */ l2) in
   Some ({coeffs = 
     Vect.add (Vect.mul m c.coeffs) coeffs ; op = op ; cst = m */ c.cst +/ cst} , 
	 AddPrf(MulC(([], m),p),p')) in

  Some (apply_and_normalise pivot_eq sys)

let iterate_until_stable f x = 
 let rec iter x = 
  match f x with
  | None -> x
  | Some x' -> iter x' in
 iter x

let rec app_funs l x = 
 match l with
 | [] -> None
 | f::fl -> 
  match f x with
  | None    -> app_funs fl x
  | Some x' -> Some x'

let reduction_equations psys =
 iterate_until_stable (app_funs 
			[reduce_unary ; reduce_coprime ; 
			 reduce_var_change (*; reduce_pivot*)]) psys 

let reduction_non_lin_equations psys =
 iterate_until_stable (app_funs 
			[reduce_non_lin_unary (*; reduce_coprime ; 
			                        reduce_var_change ; reduce_pivot *)]) psys 




  (** [get_bound sys] returns upon success an interval (lb,e,ub) with proofs *)
let get_bound sys = 
 let is_small (v,i) = 
  match Itv.range i with
  | None -> false
  | Some i -> i <=/ (Int 1) in
 
 let select_best (x1,i1) (x2,i2) = 
  if Itv.smaller_itv i1 i2
  then (x1,i1) else (x2,i2) in

    (* For lia, there are no equations => these precautions are not needed *)
    (* For nlia, there are equations => do not enumerate over equations! *)
 let all_planes sys = 
  let (eq,ineq) = List.partition (fun c -> c.op == Eq) sys in
  match eq with
  | [] -> List.rev_map (fun c -> c.coeffs) ineq
  | _  -> 
   List.fold_left (fun acc c -> 
    if List.exists (fun c' -> Vect.equal c.coeffs c'.coeffs) eq
    then acc else c.coeffs ::acc) [] ineq in

 let smallest_interval = 
  List.fold_left 
   (fun acc vect ->
    if is_small acc
    then acc
    else 
     match Fourier.optimise vect sys with
     | None -> acc
     | Some i -> 
      if debug then Printf.printf "Found a new bound %a" Vect.pp_vect vect ;
      select_best (vect,i) acc)  (Vect.null, (None,None)) (all_planes sys) in
 let smallest_interval =
  match smallest_interval
  with
  | (x,(Some i, Some j))  -> Some(i,x,j)
  |   x        ->   None (* This should not be possible *)
 in
 match smallest_interval with
 | Some (lb,e,ub) -> 
  let (lbn,lbd) = (sub_big_int (numerator lb)  unit_big_int, denominator lb) in
  let (ubn,ubd) = (add_big_int unit_big_int (numerator ub) , denominator ub) in
  (match
               (* x <= ub ->  x  > ub *)
    xlinear_prover   ({coeffs = Vect.mul (Big_int ubd)  e ; op = Ge ; cst = Big_int ubn} :: sys),
               (* lb <= x  -> lb > x *)
   xlinear_prover
    ({coeffs = Vect.mul (minus_num (Big_int lbd)) e ; op = Ge ; cst = minus_num (Big_int lbn)} :: sys)
   with
   | Some cub , Some clb  -> Some(List.tl clb,(lb,e,ub), List.tl cub)
   |         _            -> failwith "Interval without proof"
  )
 | None -> None


let check_sys sys = 
 List.for_all (fun (c,p) -> List.for_all (fun (_,n) -> sign_num n <> 0) c.coeffs) sys


let xlia (can_enum:bool)  reduction_equations  sys = 

 
 let rec enum_proof (id:int) (sys:prf_sys) : proof option = 
  if debug then (Printf.printf "enum_proof\n" ; flush stdout) ;
  assert (check_sys sys) ; 

  let nsys,prf = List.split sys in
  match get_bound nsys with
  | None -> None (* Is the systeme really unbounded ? *)
  | Some(prf1,(lb,e,ub),prf2) -> 
   if debug then Printf.printf "Found interval: %a in [%s;%s] -> " Vect.pp_vect e (string_of_num lb) (string_of_num ub) ; 
   (match start_enum  id  e  (ceiling_num lb)  (floor_num ub) sys
    with
    | Some prfl -> 
     Some(Enum(id,proof_of_farkas prf prf1,e, proof_of_farkas prf prf2,prfl))
    | None -> None
   )

 and start_enum id e clb cub sys = 
  if clb >/ cub
  then Some []
  else
   let eq = {coeffs = e ; op = Eq ; cst = clb} in
   match aux_lia (id+1) ((eq, Def id) :: sys) with
   | None -> None 
   | Some prf  -> 
    match start_enum id e (clb +/ (Int 1)) cub sys with
    | None -> None
    | Some l -> Some (prf::l)

 and aux_lia (id:int)  (sys:prf_sys) : proof option  = 
  assert (check_sys sys) ; 
  if debug then Printf.printf "xlia:  %a \n" (pp_list (fun o (c,_) -> output_cstr o c)) sys ; 
  try 
   let sys = reduction_equations sys in
   if debug then 
    Printf.printf "after reduction:  %a \n" (pp_list (fun o (c,_) -> output_cstr o c)) sys ; 	    	    
   match linear_prover sys with
   | Some prf -> Some (Step(id,prf,Done))
   | None ->  if can_enum then enum_proof id sys else None
  with FoundProof prf -> 
      (* [reduction_equations] can find a proof *)
   Some(Step(id,prf,Done)) in

  (*  let sys' = List.map (fun (p,o) -> Mc.norm0 p , o) sys in*)
 let id  = List.length sys in
 let orpf = 
  try 
   let sys = simpl_sys sys in
   aux_lia id sys
  with FoundProof pr -> Some(Step(id,pr,Done)) in
 match orpf with
 | None -> None
 | Some prf -> 
	 (*Printf.printf "direct proof %a\n" output_proof prf ; *)
  let env = List.mapi (fun i _ -> i) sys in
  let prf = compile_proof env prf in
	   (*try 
	     if Mc.zChecker sys' prf then Some prf else 
	     raise Certificate.BadCertificate
	     with Failure s -> (Printf.printf "%s" s ; Some prf)
	   *) Some prf
  

let cstr_compat_of_poly (p,o) = 
 let (v,c) = LinPoly.linpol_of_pol p in
 {coeffs = v ; op = o ; cst = minus_num c }


let lia (can_enum:bool) (prfdepth:int) sys = 
 LinPoly.MonT.clear ();
 max_nb_cstr := compute_max_nb_cstr sys prfdepth ;
 let sys = List.map (develop_constraint z_spec) sys in
 let (sys:cstr_compat list) = List.map cstr_compat_of_poly sys in
 let sys = List.mapi (fun i c -> (c,Hyp i)) sys in
 xlia can_enum reduction_equations sys


let nlia enum prfdepth sys = 
 LinPoly.MonT.clear ();
 max_nb_cstr := compute_max_nb_cstr sys prfdepth;
 let sys = List.map (develop_constraint z_spec) sys in
 let sys = List.mapi (fun i c -> (c,Hyp i)) sys in

 let is_linear =  List.for_all (fun ((p,_),_) -> Poly.is_linear p) sys in

 let collect_square = 
  List.fold_left (fun acc ((p,_),_) -> Poly.fold 
   (fun m _ acc -> 
    match Monomial.sqrt m with
    | None -> acc
    | Some s -> MonMap.add  s m acc)  p acc) MonMap.empty sys in
 let sys = MonMap.fold (fun s m acc -> 
  let s = LinPoly.linpol_of_pol (Poly.add s (Int 1) (Poly.constant (Int 0))) in
  let m = Poly.add m (Int 1) (Poly.constant (Int 0)) in
  ((m, Ge), (Square s))::acc) collect_square  sys in

    (*      List.iter (fun ((p,_),_) -> Printf.printf "square %a\n" Poly.pp p) gen_square*)

 let sys = 
  if is_linear then sys
  else sys @ (all_sym_pairs (fun ((c,o),p) ((c',o'),p') -> 
   ((Poly.product c c',opMult o o'), MulPrf(p,p'))) sys) in

 let sys = List.map (fun (c,p) -> cstr_compat_of_poly c,p) sys in
 assert (check_sys sys) ; 
 xlia enum (if is_linear then reduction_equations else reduction_non_lin_equations) sys



(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)

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

open Num
open Sos
open Sos_types
open Sos_lib

module Mc = Micromega
module C2Ml = Mutils.CoqToCaml

type micromega_polys = (Micromega.q Mc.pol * Mc.op1) list
type csdp_certificate = S of Sos_types.positivstellensatz option | F of string
type provername = string * int option


let flags = [Open_append;Open_binary;Open_creat]

let chan = open_out_gen flags 0o666 "trace"


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


end
open M

let partition_expr l =
 let rec f i = function
  | [] -> ([],[],[])
  | (e,k)::l ->
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
  let l = List.map (fun (e,op) -> (Mc.denorm e,op)) l in
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
     |   _        -> failwith "monoids") m (poly_const (Int 1)) , List.map snd m))
   (sets_of_list neq) in

  let (cert_ideal, cert_cone,monoid) = deepen_until d (fun d ->
   tryfind (fun m -> let (ci,cc) =
    real_positivnullstellensatz_general false d peq pge (poly_neg (fst m) ) in
		      (ci,cc,snd m)) monoids) 0 in

  let proofs_ideal = List.map2 (fun q i -> Eqmul(term_of_poly q,Axiom_eq i))
   cert_ideal (List.map snd eq) in

  let proofs_cone = List.map term_of_sos cert_cone in

  let proof_ne =
   let (neq , lt) = List.partition
    (function  Axiom_eq _ -> true | _ -> false ) monoid in
   let sq = match
     (List.map (function Axiom_eq i -> i | _ -> failwith "error") neq)
    with
    | []  -> Rational_lt (Int 1)
    | l   -> Monoid l in
    List.fold_right (fun x y -> Product(x,y)) lt sq in

  let proof = end_itlist
   (fun s t -> Sum(s,t)) (proof_ne :: proofs_ideal @ proofs_cone) in
   S (Some proof)
 with
  | Sos_lib.TooDeep -> S None
  | any -> F (Printexc.to_string any)

(* This is somewhat buggy, over Z, strict inequality vanish... *)
let pure_sos  l =
  let l = List.map (fun (e,o) -> Mc.denorm e, o) l in

 (* If there is no strict inequality,
    I should nonetheless be able to try something - over Z  > is equivalent to -1  >= *)
 try
  let l = List.combine l (CList.interval 0 (List.length l -1)) in
  let (lt,i) =  try (List.find (fun (x,_) -> Pervasives.(=) (snd x) Mc.Strict) l)
   with Not_found -> List.hd l in
  let plt = poly_neg (poly_of_term (expr_to_term (fst lt))) in
  let (n,polys) = sumofsquares plt in (* n * (ci * pi^2) *)
  let pos = Product (Rational_lt n,
		    List.fold_right (fun (c,p) rst -> Sum (Product (Rational_lt c, Square
		     (term_of_poly p)), rst))
		     polys (Rational_lt (Int 0))) in
  let proof = Sum(Axiom_lt i, pos) in
(*  let s,proof' = scale_certificate proof in
  let cert  = snd (cert_of_pos proof') in *)
    S (Some proof)
 with
(*   | Sos.CsdpNotFound -> F "Sos.CsdpNotFound" *)
   | any -> (* May be that could be refined *) S None



let run_prover prover pb =
    match prover with
    | "real_nonlinear_prover", Some d -> real_nonlinear_prover d pb
    | "pure_sos", None -> pure_sos pb
    | prover, _ -> (Printf.printf "unknown prover: %s\n" prover; exit 1)

let main () =
  try
    let (prover,poly) = (input_value stdin : provername * micromega_polys) in
    let cert = run_prover prover poly in
(*      Printf.fprintf chan "%a -> %a" print_list_term poly output_csdp_certificate cert ;
      close_out chan ;   *)

      output_value stdout (cert:csdp_certificate);
      flush stdout ;
      Marshal.to_channel  chan (cert:csdp_certificate) [] ;
      flush chan ;
      exit 0
  with any -> (Printf.fprintf chan "error %s" (Printexc.to_string any)  ; exit 1)

;;

let _ = main () in ()

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)

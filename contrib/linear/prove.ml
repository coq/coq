(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Dpctypes;;
open Kwc;;
open Lk_proofs;;

exception Not_provable_in_DPC of string
;;
exception No_intuitionnistic_proof of int
;;

(* is_int_proof : lkproof2 -> bool *******)

let rec is_int_proof (Proof2(sq1,sq2,rule)) = 
  if (List.length sq2)>1 then false
  else match rule with
      Axiom2(_) -> true
    | RWeakening2(_,p) -> is_int_proof p
    | LWeakening2(_,p) -> is_int_proof p
    | RNeg2(_,p) -> is_int_proof p
    | LNeg2(_,p) -> is_int_proof p
    | RConj2(_,p1,_,p2) -> (is_int_proof p1) & (is_int_proof p2)
    | LConj2(_,_,p) -> is_int_proof p
    | RDisj2(f1,f2,Proof2(_,_,RWeakening2(f3,p))) ->
      	 if (f3=f1) or (f3=f2) then is_int_proof p
       	       	       	       else false
    | RDisj2(_,_,_) -> false
    | LDisj2(_,p1,_,p2) -> (is_int_proof p1) & (is_int_proof p2)
    | RImp2(_,_,p) -> is_int_proof p
    | LImp2(_,p1,_,p2) -> (is_int_proof p1) & (is_int_proof p2)
    | RForAll2(_,_,p) -> is_int_proof p
    | LForAll2(_,_,_,p) -> is_int_proof p
    | RExists2(_,_,_,p) -> is_int_proof p
    | LExists2(_,_,p) -> is_int_proof p
;;

(* find_int_proof : f -> f1 -> path list -> lkproof2 *****)

let find_int_proof f f1 all_v_paths = 
  let rec find_rec = function
      p::ll -> let pr0 = proof_of_path [Po(f1)] p in
      	       if is_int_proof pr0
	       then int_quant f (snd p) pr0
	       else find_rec ll
    | [] -> raise Not_found
  in find_rec all_v_paths
;;

(* prove_f : formula -> lk_proof2 
   prove   : string  -> lk_proof2 *******)

let prove_f f =
     let f0 = separate f
  in let (ex,f1) = herbrand f0
  in let (pos,neg,lcj) = lit_conj f1
  in let cj = List.map (fun (c,_) -> c) lcj
  in let m = all_matches pos neg lcj
  in if m = []  
     then raise (Not_provable_in_DPC "(No match)")

  else let all_paths = paths pos neg m lcj
     in if all_paths = [] 
     then raise (Not_provable_in_DPC "(No path)")

  else let all_valid_paths = good_paths lcj all_paths
     in if all_valid_paths = []
     then raise (Not_provable_in_DPC "(No valid path)")

  else try find_int_proof f f1 all_valid_paths
       with Not_found -> let n = List.length all_valid_paths
      	       	       	 in raise (No_intuitionnistic_proof n)
;;

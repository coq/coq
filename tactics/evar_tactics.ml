(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Term
open Util
open Evar_refiner
open Tacmach
open Tacexpr
open Refiner
open Proof_type
open Evd
open Sign
open Termops

(* The instantiate tactic *)

let evar_list evc c = 
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (n, _) when Evd.mem evc n -> c :: acc
    | _ -> fold_constr evrec acc c
  in 
    evrec [] c

let instantiate n (ist,rawc) ido gl = 
  let sigma = gl.sigma in
  let evl = 
    match ido with
	ConclLocation () -> evar_list sigma gl.it.evar_concl 
      | HypLocation (id,hloc) ->
	  let decl = Environ.lookup_named_val id gl.it.evar_hyps in
	    match hloc with
		InHyp ->  
		  (match decl with 
		      (_,None,typ) -> evar_list sigma typ
		    | _ -> error 
			"Please be more specific: in type or value?")
	      | InHypTypeOnly ->
		  let (_, _, typ) = decl in evar_list sigma typ
	      | InHypValueOnly ->
		  (match decl with 
		      (_,Some body,_) -> evar_list sigma body
		    | _ -> error "Not a defined hypothesis.") in
    if List.length evl < n then
      error "Not enough uninstantiated existential variables.";
    if n <= 0 then error "Incorrect existential variable index.";
    let evk,_ = destEvar (List.nth evl (n-1)) in
    let evi = Evd.find sigma evk in
    let ltac_vars = Tacinterp.extract_ltac_vars ist sigma (Evd.evar_env evi) in
    let sigma' = w_refine (evk,evi) (ltac_vars,rawc) sigma in
      tclTHEN
        (tclEVARS sigma')
        tclNORMEVAR
        gl
	
let let_evar name typ gls =
  let sigma',evar = Evarutil.new_evar gls.sigma (pf_env gls) typ in
  Refiner.tclTHEN (Refiner.tclEVARS sigma')
    (Tactics.letin_tac None name evar None nowhere) gls
 

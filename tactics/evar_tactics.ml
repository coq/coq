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
open Proof_type
open Evd

(* The instantiate tactic *)

let evars_of evc c = 
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (n, _) when Evd.in_dom evc n -> c :: acc
    | _ -> fold_constr evrec acc c
  in 
    evrec [] c

let instantiate n rawc ido gl = 
  let wc = Refiner.project_with_focus gl in
  let evl = 
    match ido with
	ConclLocation () -> evars_of wc.sigma gl.it.evar_concl 
      | HypLocation (id,hloc) ->
	  let decl = Sign.lookup_named id gl.it.evar_hyps in
	    match hloc with
		InHyp ->  
		  (match decl with 
		       (_,None,typ) -> evars_of wc.sigma typ
		     | _ -> error 
			 "please be more specific : in type or value ?")
	      | InHypTypeOnly ->
		  let (_, _, typ) = decl in evars_of wc.sigma typ
	      | InHypValueOnly ->
		  (match decl with 
		       (_,Some body,_) -> evars_of wc.sigma body
		     | _ -> error "not a let .. in  hypothesis") in
    if List.length evl < n then
      error "not enough uninstantiated existential variables";
    if n <= 0 then error "incorrect existential variable index";
    let ev,_ =  destEvar (List.nth evl (n-1)) in
    let wc' = w_refine ev rawc wc in
      Tacticals.tclIDTAC {gl with sigma = wc'.sigma}
	
(*
let pfic gls c =
  let evc = gls.sigma in 
  Constrintern.interp_constr evc (Global.env_of_context gls.it.evar_hyps) c

let instantiate_tac = function
  | [Integer n; Command com] ->
      (fun gl -> instantiate n (pfic gl com) gl)
  | [Integer n; Constr c] ->
      (fun gl -> instantiate n c gl)
  | _ -> invalid_arg "Instantiate called with bad arguments"
*)

let let_evar nam typ gls =
  let sp = Evarutil.new_evar () in
  let evd = Evarutil.create_evar_defs gls.sigma in
  let evd' = Unification.w_Declare (pf_env gls) sp typ evd in
  let ngls = {gls with sigma = Evarutil.evars_of evd'} in
    Tactics.forward true nam (mkEvar(sp,[||])) ngls 

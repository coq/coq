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

let instantiate n rawc ido gl = 
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
			"please be more specific : in type or value ?")
	      | InHypTypeOnly ->
		  let (_, _, typ) = decl in evar_list sigma typ
	      | InHypValueOnly ->
		  (match decl with 
		      (_,Some body,_) -> evar_list sigma body
		    | _ -> error "not a let .. in  hypothesis") in
    if List.length evl < n then
      error "not enough uninstantiated existential variables";
    if n <= 0 then error "incorrect existential variable index";
    let ev,_ =  destEvar (List.nth evl (n-1)) in
    let evd' = w_refine ev rawc (create_goal_evar_defs sigma) in
      tclTHEN
        (tclEVARS (evars_of evd'))
        tclNORMEVAR
        gl
	
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

let let_evar name typ gls =
  let evd = Evd.create_goal_evar_defs gls.sigma in
  let evd',evar = Evarutil.new_evar evd (pf_env gls) typ in
  Refiner.tclTHEN (Refiner.tclEVARS (evars_of evd'))
    (Tactics.letin_tac true name evar nowhere) gls
 

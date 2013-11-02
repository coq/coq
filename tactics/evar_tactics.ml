(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Errors
open Evar_refiner
open Tacmach
open Tacexpr
open Refiner
open Evd
open Locus

(* The instantiate tactic *)

let instantiate n (ist,rawc) ido gl =
  let sigma = gl.sigma in
  let evl =
    match ido with
	ConclLocation () -> evar_list sigma (pf_concl gl)
      | HypLocation (id,hloc) ->
	  let decl = Environ.lookup_named_val id (Goal.V82.hyps sigma (sig_it gl)) in
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
    let evk,_ = List.nth evl (n-1) in
    let evi = Evd.find sigma evk in
    let filtered = Evd.evar_filtered_env evi in
    let constrvars = Tacinterp.extract_ltac_constr_values ist filtered in
    let sigma' = w_refine (evk,evi) ((constrvars, ist.Geninterp.lfun),rawc) sigma in
      tclTHEN
        (tclEVARS sigma')
        tclNORMEVAR
        gl

open Proofview.Notations
let let_evar name typ =
  let src = (Loc.ghost,Evar_kinds.GoalEvar) in
  Proofview.tclEVARMAP >= fun sigma ->
  Proofview.Goal.env >>= fun env ->
  let sigma',evar = Evarutil.new_evar sigma env ~src typ in
  Tacticals.New.tclTHEN (Proofview.V82.tactic (Refiner.tclEVARS sigma'))
    (Tactics.letin_tac None name evar None Locusops.nowhere)

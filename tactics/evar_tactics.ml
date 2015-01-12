(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Errors
open Evar_refiner
open Tacmach
open Tacexpr
open Refiner
open Evd
open Locus

(* The instantiate tactic *)

let instantiate_evar evk (ist,rawc) sigma =
  let evi = Evd.find sigma evk in
  let filtered = Evd.evar_filtered_env evi in
  let constrvars = Tacinterp.extract_ltac_constr_values ist filtered in
  let lvar = {
    Pretyping.ltac_constrs = constrvars;
    ltac_uconstrs = Names.Id.Map.empty;
    ltac_idents = Names.Id.Map.empty;
    ltac_genargs = ist.Geninterp.lfun;
  } in
  let sigma' = w_refine (evk,evi) (lvar ,rawc) sigma in
  tclEVARS sigma'

let instantiate_tac n c ido =
  Proofview.V82.tactic begin fun gl ->
  let sigma = gl.sigma in
  let evl =
    match ido with
	ConclLocation () -> evar_list (pf_concl gl)
      | HypLocation (id,hloc) ->
	  let decl = Environ.lookup_named_val id (Goal.V82.hyps sigma (sig_it gl)) in
	    match hloc with
		InHyp ->
		  (match decl with
		      (_,None,typ) -> evar_list typ
		    | _ -> error
			"Please be more specific: in type or value?")
	      | InHypTypeOnly ->
		  let (_, _, typ) = decl in evar_list typ
	      | InHypValueOnly ->
		  (match decl with
		      (_,Some body,_) -> evar_list body
		    | _ -> error "Not a defined hypothesis.") in
  if List.length evl < n then
    error "Not enough uninstantiated existential variables.";
  if n <= 0 then error "Incorrect existential variable index.";
  let evk,_ = List.nth evl (n-1) in
  instantiate_evar evk c sigma gl
  end

let instantiate_tac_by_name id c =
  Proofview.V82.tactic begin fun gl ->
  let sigma = gl.sigma in
  let evk =
    try Evd.evar_key id sigma
    with Not_found -> error "Unknown existential variable." in
  instantiate_evar evk c sigma gl
  end

let let_evar name typ =
  let src = (Loc.ghost,Evar_kinds.GoalEvar) in
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let id = Namegen.id_of_name_using_hdchar env typ name in
    let id = Namegen.next_ident_away_in_goal id (Termops.ids_of_named_context (Environ.named_context env)) in
    let sigma',evar = Evarutil.new_evar env sigma ~src ~naming:(Misctypes.IntroFresh id) typ in
    Tacticals.New.tclTHEN (Proofview.V82.tactic (Refiner.tclEVARS sigma'))
      (Tactics.letin_tac None (Names.Name id) evar None Locusops.nowhere)
  end

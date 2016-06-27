(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open CErrors
open Evar_refiner
open Tacmach
open Tacexpr
open Refiner
open Evd
open Locus
open Sigma.Notations
open Proofview.Notations
open Context.Named.Declaration

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
                    | LocalAssum (_,typ) -> evar_list typ
		    | _ -> error
			"Please be more specific: in type or value?")
	      | InHypTypeOnly ->
		  evar_list (get_type decl)
	      | InHypValueOnly ->
		  (match decl with
		    | LocalDef (_,body,_) -> evar_list body
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
  Proofview.Goal.s_enter { s_enter = begin fun gl ->
    let sigma = Tacmach.New.project gl in
    let env = Proofview.Goal.env gl in
    let sigma = ref sigma in
    let _ = Typing.e_sort_of env sigma typ in
    let sigma = Sigma.Unsafe.of_evar_map !sigma in
    let id = match name with
    | Names.Anonymous -> 
      let id = Namegen.id_of_name_using_hdchar env typ name in
      Namegen.next_ident_away_in_goal id (Termops.ids_of_named_context (Environ.named_context env))
    | Names.Name id -> id
    in
    let Sigma (evar, sigma, p) = Evarutil.new_evar env sigma ~src ~naming:(Misctypes.IntroFresh id) typ in
    let tac =
      (Tactics.letin_tac None (Names.Name id) evar None Locusops.nowhere)
    in
    Sigma (tac, sigma, p)
  end }

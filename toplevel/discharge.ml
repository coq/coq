(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Names
open Util
open Sign
open Term
open Entries
open Declarations
open Cooking

(********************************)
(* Discharging mutual inductive *)

let detype_param = function
  | (Name id,None,p) -> id, Entries.LocalAssum p
  | (Name id,Some p,_) -> id, Entries.LocalDef p
  | (Anonymous,_,_) -> anomaly"Unnamed inductive local variable"

(* Replace

     Var(y1)..Var(yq):C1..Cq |- Ij:Bj
     Var(y1)..Var(yq):C1..Cq; I1..Ip:B1..Bp |- ci : Ti

   by

     |- Ij: (y1..yq:C1..Cq)Bj
     I1..Ip:(B1 y1..yq)..(Bp y1..yq) |- ci : (y1..yq:C1..Cq)Ti[Ij:=(Ij y1..yq)]
*)

let abstract_inductive hyps nparams inds =
  let ntyp = List.length inds in
  let nhyp = named_context_length hyps in
  let args = instance_from_named_context (List.rev hyps) in
  let subs = list_tabulate (fun k -> lift nhyp (mkApp(mkRel (k+1),args))) ntyp in
  let inds' =
    List.map
      (function (tname,arity,cnames,lc) ->
	let lc' = List.map (substl subs) lc in
	let lc'' = List.map (fun b -> Termops.it_mkNamedProd_wo_LetIn b hyps) lc' in
	let arity' = Termops.it_mkNamedProd_wo_LetIn arity hyps in
        (tname,arity',cnames,lc''))
      	inds in
  let nparams' = nparams + Array.length args in
(* To be sure to be the same as before, should probably be moved to process_inductive *)
  let params' = let (_,arity,_,_) = List.hd inds' in
		let (params,_) = decompose_prod_n_assum nparams' arity in
		  List.map detype_param params
  in
  let ind'' =
  List.map
    (fun (a,arity,c,lc) ->
      let _, short_arity = decompose_prod_n_assum nparams' arity in
      let shortlc =
	List.map (fun c -> snd (decompose_prod_n_assum nparams' c)) lc in
      { mind_entry_typename = a;
	mind_entry_arity = short_arity;
	mind_entry_consnames = c;
	mind_entry_lc = shortlc })
    inds'
  in (params',ind'')


let process_inductive sechyps modlist mib =
  let nparams = mib.mind_nparams in
  let inds =
    array_map_to_list
      (fun mip ->
	 let arity = expmod_constr modlist (Termops.refresh_universes_strict (Inductive.type_of_inductive (Global.env()) (mib,mip))) in
	 let lc = Array.map (expmod_constr modlist) mip.mind_user_lc in
	 (mip.mind_typename,
	  arity,
	  Array.to_list mip.mind_consnames,
	  Array.to_list lc))
      mib.mind_packets in
  let sechyps' = map_named_context (expmod_constr modlist) sechyps in
  let (params',inds') = abstract_inductive sechyps' nparams inds in
  { mind_entry_record = mib.mind_record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params';
    mind_entry_inds = inds' }

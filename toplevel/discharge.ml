(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Errors
open Util
open Context
open Term
open Vars
open Entries
open Declarations
open Cooking

(********************************)
(* Discharging mutual inductive *)

let detype_param = function
  | (Name id,None,p) -> id, Entries.LocalAssum p
  | (Name id,Some p,_) -> id, Entries.LocalDef p
  | (Anonymous,_,_) -> anomaly (Pp.str "Unnamed inductive local variable")

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
  let args = Array.of_list args in
  let subs = List.init ntyp (fun k -> lift nhyp (mkApp(mkRel (k+1),args))) in
  let inds' =
    List.map
      (function (tname,arity,template,cnames,lc) ->
	let lc' = List.map (substl subs) lc in
	let lc'' = List.map (fun b -> Termops.it_mkNamedProd_wo_LetIn b hyps) lc' in
	let arity' = Termops.it_mkNamedProd_wo_LetIn arity hyps in
        (tname,arity',template,cnames,lc''))
      	inds in
  let nparams' = nparams + Array.length args in
(* To be sure to be the same as before, should probably be moved to process_inductive *)
  let params' = let (_,arity,_,_,_) = List.hd inds' in
		let (params,_) = decompose_prod_n_assum nparams' arity in
		  List.map detype_param params
  in
  let ind'' =
  List.map
    (fun (a,arity,template,c,lc) ->
      let _, short_arity = decompose_prod_n_assum nparams' arity in
      let shortlc =
	List.map (fun c -> snd (decompose_prod_n_assum nparams' c)) lc in
      { mind_entry_typename = a;
	mind_entry_arity = short_arity;
	mind_entry_template = template;
	mind_entry_consnames = c;
	mind_entry_lc = shortlc })
    inds'
  in (params',ind'')

let refresh_polymorphic_type_of_inductive (_,mip) =
  match mip.mind_arity with
  | RegularArity s -> s.mind_user_arity, false
  | TemplateArity ar ->
    let ctx = List.rev mip.mind_arity_ctxt in
      mkArity (List.rev ctx, Type ar.template_level), true

let process_inductive (sechyps,abs_ctx) modlist mib =
  let nparams = mib.mind_nparams in
  let subst, univs = 
    if mib.mind_polymorphic then 
      let inst = Univ.UContext.instance mib.mind_universes in
      let cstrs = Univ.UContext.constraints mib.mind_universes in
	inst, Univ.UContext.make (inst, Univ.subst_instance_constraints inst cstrs)
    else Univ.Instance.empty, mib.mind_universes
  in
  let inds =
    Array.map_to_list
      (fun mip ->
	let ty, template = refresh_polymorphic_type_of_inductive (mib,mip) in
	let arity = expmod_constr modlist ty in
	let arity = Vars.subst_instance_constr subst arity in
	let lc = Array.map 
	  (fun c -> Vars.subst_instance_constr subst (expmod_constr modlist c))
	  mip.mind_user_lc 
	in
	  (mip.mind_typename,
	   arity, template,
	   Array.to_list mip.mind_consnames,
	   Array.to_list lc))
      mib.mind_packets in
  let sechyps' = map_named_context (expmod_constr modlist) sechyps in
  let (params',inds') = abstract_inductive sechyps' nparams inds in
  let abs_ctx = Univ.instantiate_univ_context abs_ctx in
  let univs = Univ.UContext.union abs_ctx univs in
  let record = match mib.mind_record with
    | Some (Some (id, _, _)) -> Some (Some id)
    | Some None -> Some None
    | None -> None
  in
  { mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params';
    mind_entry_inds = inds';
    mind_entry_polymorphic = mib.mind_polymorphic;
    mind_entry_private = mib.mind_private;
    mind_entry_universes = univs
  }

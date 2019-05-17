(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Term
open Constr
open Vars
open Declarations
open Cooking
open Entries

(********************************)
(* Discharging mutual inductive *)

(* Replace

     Var(y1)..Var(yq):C1..Cq |- Ij:Bj
     Var(y1)..Var(yq):C1..Cq; I1..Ip:B1..Bp |- ci : Ti

   by

     |- Ij: (y1..yq:C1..Cq)Bj
     I1..Ip:(B1 y1..yq)..(Bp y1..yq) |- ci : (y1..yq:C1..Cq)Ti[Ij:=(Ij y1..yq)]
*)

let it_mkNamedProd_wo_LetIn b d =
  List.fold_left (fun c d -> mkNamedProd_wo_LetIn d c) b d

let abstract_inductive decls nparamdecls inds =
  let ntyp = List.length inds in
  let ndecls = Context.Named.length decls in
  let args = Context.Named.to_instance mkVar (List.rev decls) in
  let args = Array.of_list args in
  let subs = List.init ntyp (fun k -> lift ndecls (mkApp(mkRel (k+1),args))) in
  let inds' =
    List.map
      (function (tname,arity,template,cnames,lc) ->
	let lc' = List.map (substl subs) lc in
        let lc'' = List.map (fun b -> it_mkNamedProd_wo_LetIn b decls) lc' in
        let arity' = it_mkNamedProd_wo_LetIn arity decls in
        (tname,arity',template,cnames,lc''))
      	inds in
  let nparamdecls' = nparamdecls + Array.length args in
(* To be sure to be the same as before, should probably be moved to process_inductive *)
  let params' = let (_,arity,_,_,_) = List.hd inds' in
		let (params,_) = decompose_prod_n_assum nparamdecls' arity in
    params
  in
  let ind'' =
  List.map
    (fun (a,arity,template,c,lc) ->
      let _, short_arity = decompose_prod_n_assum nparamdecls' arity in
      let shortlc =
	List.map (fun c -> snd (decompose_prod_n_assum nparamdecls' c)) lc in
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
      mkArity (List.rev ctx, Sorts.sort_of_univ ar.template_level), true

let dummy_variance = let open Entries in function
  | Monomorphic_entry _ -> assert false
  | Polymorphic_entry (_,uctx) -> Array.make (Univ.UContext.size uctx) Univ.Variance.Irrelevant

let discharge_abstract_universe_context subst abs_ctx auctx =
  let open Univ in
  let ainst = make_abstract_instance auctx in
  let subst = Instance.append subst ainst in
  let subst = make_instance_subst subst in
  let auctx = Univ.subst_univs_level_abstract_universe_context subst auctx in
  subst, AUContext.union abs_ctx auctx

let process_inductive section_decls subst abs_uctx modlist mib =
  let nparamdecls = Context.Rel.length mib.mind_params_ctxt in
  let subst, ind_univs =
    match mib.mind_universes with
    | Monomorphic ctx -> Univ.empty_level_subst, Monomorphic_entry ctx
    | Polymorphic auctx ->
      let subst, auctx = discharge_abstract_universe_context subst abs_uctx auctx in
      let nas = Univ.AUContext.names auctx in
      let auctx = Univ.AUContext.repr auctx in
      subst, Polymorphic_entry (nas, auctx)
  in
  let variance = match mib.mind_variance with
    | None -> None
    | Some _ -> Some (dummy_variance ind_univs)
  in
  let discharge c = Vars.subst_univs_level_constr subst (expmod_constr modlist c) in
  let inds =
    Array.map_to_list
      (fun mip ->
	let ty, template = refresh_polymorphic_type_of_inductive (mib,mip) in
        let arity = discharge ty in
        let lc = Array.map discharge mip.mind_user_lc  in
	  (mip.mind_typename,
	   arity, template,
	   Array.to_list mip.mind_consnames,
	   Array.to_list lc))
      mib.mind_packets in
  let section_decls' = Context.Named.map discharge section_decls in
  let (params',inds') = abstract_inductive section_decls' nparamdecls inds in
  let record = match mib.mind_record with
    | PrimRecord info ->
      Some (Some (Array.map (fun (x,_,_,_) -> x) info))
    | FakeRecord -> Some None
    | NotRecord -> None
  in
  { mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params';
    mind_entry_inds = inds';
    mind_entry_private = mib.mind_private;
    mind_entry_variance = variance;
    mind_entry_universes = ind_univs
  }


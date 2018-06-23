(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open CErrors
open Util
open Term
open Constr
open Vars
open Declarations
open Cooking
open Entries
open Context.Rel.Declaration

(********************************)
(* Discharging mutual inductive *)

let detype_param =
  function
  | LocalAssum (Name id, p) -> id, LocalAssumEntry p
  | LocalDef (Name id, p,_) -> id, LocalDefEntry p
  | _ -> anomaly (Pp.str "Unnamed inductive local variable.")

(* Replace

     Var(y1)..Var(yq):C1..Cq |- Ij:Bj
     Var(y1)..Var(yq):C1..Cq; I1..Ip:B1..Bp |- ci : Ti

   by

     |- Ij: (y1..yq:C1..Cq)Bj
     I1..Ip:(B1 y1..yq)..(Bp y1..yq) |- ci : (y1..yq:C1..Cq)Ti[Ij:=(Ij y1..yq)]
*)

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
	let lc'' = List.map (fun b -> Termops.it_mkNamedProd_wo_LetIn b decls) lc' in
	let arity' = Termops.it_mkNamedProd_wo_LetIn arity decls in
        (tname,arity',template,cnames,lc''))
      	inds in
  let nparamdecls' = nparamdecls + Array.length args in
(* To be sure to be the same as before, should probably be moved to process_inductive *)
  let params' = let (_,arity,_,_,_) = List.hd inds' in
		let (params,_) = decompose_prod_n_assum nparamdecls' arity in
                List.map detype_param params
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
      mkArity (List.rev ctx, Type ar.template_level), true

let process_inductive info modlist mib =
  let section_decls = Lib.named_of_variable_context info.Lib.abstr_ctx in
  let nparamdecls = Context.Rel.length mib.mind_params_ctxt in
  let subst, ind_univs =
    match mib.mind_universes with
    | Monomorphic_ind ctx -> Univ.empty_level_subst, Monomorphic_ind_entry ctx
    | Polymorphic_ind auctx ->
      let subst, auctx = Lib.discharge_abstract_universe_context info auctx in
      let auctx = Univ.AUContext.repr auctx in
      subst, Polymorphic_ind_entry auctx
    | Cumulative_ind cumi ->
      let auctx = Univ.ACumulativityInfo.univ_context cumi in
      let subst, auctx = Lib.discharge_abstract_universe_context info auctx in
      let auctx = Univ.AUContext.repr auctx in
      subst, Cumulative_ind_entry (Univ.CumulativityInfo.from_universe_context auctx)
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
      Some (Some (Array.map pi1 info))
    | FakeRecord -> Some None
    | NotRecord -> None
  in
  { mind_entry_record = record;
    mind_entry_finite = mib.mind_finite;
    mind_entry_params = params';
    mind_entry_inds = inds';
    mind_entry_private = mib.mind_private;
    mind_entry_universes = ind_univs
  }


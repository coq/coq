(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Libnames
open Nameops
open Term
open Termops
open Environ
open Declarations
open Entries
open Declare
open Nametab
open Coqast
open Constrintern
open Command
open Inductive
open Safe_typing
open Decl_kinds
open Indtypes
open Type_errors
open Topconstr

(********** definition d'un record (structure) **************)

let name_of id = if id = wildcard then Anonymous else Name id

let interp_decl sigma env = function
  | Vernacexpr.AssumExpr(id,t) -> (name_of id,None,interp_type Evd.empty env t)
  | Vernacexpr.DefExpr(id,c,t) ->
      let c = match t with
	| None -> c
	| Some t -> mkCastC (c,t)
      in
      let j = judgment_of_rawconstr Evd.empty env c in
      (Name id,Some j.uj_val, j.uj_type)

let build_decl_entry sigma env (id,t) =
  (id,Entries.LocalAssum (interp_type Evd.empty env t))

let typecheck_params_and_fields ps fs =
  let env0 = Global.env () in
  let env1,newps =
    List.fold_left
      (fun (env,newps) (id,t) -> 
        let decl = interp_decl Evd.empty env (Vernacexpr.AssumExpr (id,t)) in
        (push_rel decl env,decl::newps))
      (env0,[]) ps
  in
  let env2,newfs =
    List.fold_left
      (fun (env,newfs) d ->
         let decl = interp_decl Evd.empty env d in
         (push_rel decl env, decl::newfs))
      (env1,[]) fs
  in
  newps, newfs

let degenerate_decl id = function
    (_,None,t) -> (id,Entries.LocalAssum t)
  | (_,Some c,t) -> (id,Entries.LocalDef c)

type record_error =
  | MissingProj of identifier * identifier list
  | BadTypedProj of identifier * env * Type_errors.type_error

let warning_or_error coe indsp err =
  let st = match err with
    | MissingProj (fi,projs) ->
	let s,have = if List.length projs > 1 then "s","have" else "","has" in
        (str(string_of_id fi) ++
	   str" cannot be defined because the projection" ++ str s ++ spc () ++
           prlist_with_sep pr_coma pr_id projs ++ spc () ++ str have ++ str "n't.")
    | BadTypedProj (fi,ctx,te) ->
	match te with
	  | ElimArity (_,_,_,_,Some (_,_,NonInformativeToInformative)) ->
              (str (string_of_id fi) ++ 
		str" cannot be defined because it is informative and " ++
		Printer.pr_inductive (Global.env()) indsp ++
		str " is not.")   
	  | ElimArity (_,_,_,_,Some (_,_,StrongEliminationOnNonSmallType)) ->
	      (str (string_of_id fi) ++ 
		str" cannot be defined because it is large and " ++
		Printer.pr_inductive (Global.env()) indsp ++
		str " is not.")
	  | _ -> 
	      (str " cannot be defined because it is not typable")
  in
  if coe then errorlabstrm "structure" st;
  Options.if_verbose ppnl (hov 0 (str"Warning: " ++ st))

type field_status =
  | NoProjection of name
  | Projection of constr

exception NotDefinable of record_error

(* This replaces previous projection bodies in current projection *)
(* Undefined projs are collected and, at least one undefined proj occurs *)
(* in the body of current projection then the latter can not be defined *)
(* [c] is defined in ctxt [[params;fields]] and [l] is an instance of *)
(* [[fields]] defined in ctxt [[params;x:ind]] *)
let subst_projection fid l c =
  let lv = List.length l in
  let bad_projs = ref [] in
  let rec substrec depth c = match kind_of_term c with
    | Rel k ->
	(* We are in context [[params;fields;x:ind;...depth...]] *)
        if k <= depth+1 then 
	  c
        else if k-depth-1 <= lv then
	  match List.nth l (k-depth-2) with
	    | Projection t -> lift depth t
	    | NoProjection (Name id) -> bad_projs := id :: !bad_projs; mkRel k
	    | NoProjection Anonymous -> assert false
        else 
	  mkRel (k-lv)
    | _ -> map_constr_with_binders succ substrec depth c
  in
  let c' = lift 1 c in (* to get [c] defined in ctxt [[params;fields;x:ind]] *)
  let c'' = substrec 0 c' in
  if !bad_projs <> [] then 
    raise (NotDefinable (MissingProj (fid,List.rev !bad_projs)));
  c''

(* We build projections *)
let declare_projections indsp coers fields =
  let env = Global.env() in
  let (mib,mip) = Global.lookup_inductive indsp in
  let paramdecls = mip.mind_params_ctxt in
  let r = mkInd indsp in
  let rp = applist (r, extended_rel_list 0 paramdecls) in
  let paramargs = extended_rel_list 1 paramdecls in (*def in [[params;x:rp]]*)
  let x = Termops.named_hd (Global.env()) r Anonymous in
  let lifted_fields = lift_rel_context 1 fields in
  let (_,sp_projs,_) =
    List.fold_left2
      (fun (nfi,sp_projs,subst) coe (fi,optci,ti) ->
	match fi with
	| Anonymous ->
	    (nfi-1, None::sp_projs,NoProjection fi::subst)
	| Name fid ->
            try
              let ccl = subst_projection fid subst ti in
	      let body = match optci with
              | Some ci -> subst_projection fid subst ci
              | None ->
	        (* [ccl] is defined in context [params;x:rp] *)
		(* [ccl'] is defined in context [params;x:rp;x:rp] *)
		let ccl' = liftn 1 2 ccl in
		let p = mkLambda (x, lift 1 rp, ccl') in
		let branch = it_mkLambda_or_LetIn (mkRel nfi) lifted_fields in
		let ci = Inductiveops.make_case_info env indsp
		  LetStyle [| RegularPat |] in
		mkCase (ci, p, mkRel 1, [|branch|]) in
	      let proj =
	        it_mkLambda_or_LetIn (mkLambda (x,rp,body)) paramdecls in
              let projtyp =
                it_mkProd_or_LetIn (mkProd (x,rp,ccl)) paramdecls in
	      let (sp,kn) =
	        try
		  let cie = {
		    const_entry_body = proj;
                    const_entry_type = Some projtyp;
                    const_entry_opaque = false } in
		  declare_constant fid (DefinitionEntry cie,IsDefinition)
                with Type_errors.TypeError (ctx,te) ->
                  raise (NotDefinable (BadTypedProj (fid,ctx,te))) in
	      let refi = ConstRef kn in
	      let constr_fi = mkConst kn in
	      if coe then begin
	        let cl = Class.class_of_ref (IndRef indsp) in
	        Class.try_add_new_coercion_with_source refi Global cl
	      end;
	      let proj_args = (*Rel 1 refers to "x"*) paramargs@[mkRel 1] in
	      let constr_fip = applist (constr_fi,proj_args) in
	      (nfi-1, (Some kn)::sp_projs, Projection constr_fip::subst)
            with NotDefinable why ->
	      warning_or_error coe indsp why;
	      (nfi-1, None::sp_projs,NoProjection fi::subst))
      (List.length fields,[],[]) coers (List.rev fields)
  in sp_projs

(* [fs] corresponds to fields and [ps] to parameters; [coers] is a boolean 
   list telling if the corresponding fields must me declared as coercion *)
let definition_structure ((is_coe,idstruc),ps,cfs,idbuild,s) =
  let coers,fs = List.split cfs in
  let nparams = List.length ps in
  let idps = List.map fst ps in
  let extract_name = function Vernacexpr.AssumExpr(id,_) -> id | Vernacexpr.DefExpr (id,_,_) -> id in
  let allnames =  idstruc::idps@(List.map extract_name fs) in
  if not (list_distinct allnames) then error "Two objects have the same name";
  (* Now, younger decl in params and fields is on top *)
  let params,fields = typecheck_params_and_fields ps fs in
(*  let args =  List.map mkVar idps in*)
  let args = extended_rel_list (List.length fields) params in
(*  let ind = applist (mkVar idstruc, args) in*)
  let ind = applist (mkRel (1+List.length params+List.length fields), args) in
  let subst = List.rev (idstruc::idps) in
(*  let named_type_constructor = it_mkNamedProd_or_LetIn ind fields in*)
  let named_type_constructor = it_mkProd_or_LetIn ind fields in
  let type_constructor = (* subst_vars subst *) named_type_constructor in
  let mie_ind =
    { mind_entry_params = List.map2 degenerate_decl (List.rev idps) params;
      mind_entry_typename = idstruc;
      mind_entry_arity = mkSort s;
      mind_entry_consnames = [idbuild];
      mind_entry_lc = [type_constructor] } in
  let mie =
    { mind_entry_finite = true;
      mind_entry_inds = [mie_ind] } in
  let sp = declare_mutual_with_eliminations mie in
  let rsp = (sp,0) in (* This is ind path of idstruc *)
  let sp_projs = declare_projections rsp coers fields in
  let build = ConstructRef (rsp,1) in (* This is construct path of idbuild *)
  if is_coe then Class.try_add_new_coercion build Global;
  Recordops.add_new_struc (rsp,idbuild,nparams,List.rev sp_projs)

(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $:Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Environ
open Declarations
open Declare
open Coqast
open Astterm
open Command
open Inductive
open Safe_typing
open Nametab
open Indtypes
open Type_errors

(********** definition d'un record (structure) **************)

let make_constructor idstruc idps fields  =
  let app_constructor = 
    Ast.ope("APPLISTEXPL",
        (Ast.nvar idstruc):: List.map (fun id -> Ast.nvar id) idps) in
  let rec aux fields =
    match fields with
      | [] -> app_constructor
      | (id,true,ty)::l -> Ast.ope("PROD",[ty; Ast.slam(Some id, aux l)])
      | (id,false,c)::l -> Ast.ope("LETIN",[c; Ast.slam(Some id, aux l)])
  in 
  aux fields

let occur_fields id fs =
  List.exists (fun (_,_,a) -> Ast.occur_var_ast id a) fs

let interp_decl sigma env (id,assum,t) =
  if assum then
    (id,None,interp_type Evd.empty env t)
  else
    let j = judgment_of_rawconstr Evd.empty env t in
    (id,Some j.uj_val, j.uj_type)

let typecheck_params_and_field ps fs =
  let env0 = Global.env () in
  let env1,newps =
    List.fold_left
      (fun (env,newps) (id,t) -> 
         let decl = interp_decl Evd.empty env (id,true,t) in
         (push_named_decl decl env,decl::newps))
      (env0,[]) ps
  in
  let env2,newfs =
    List.fold_left
      (fun (env,newfs) d ->
         let decl = interp_decl Evd.empty env d in
         (push_named_decl decl env, decl::newfs))
      (env1,[]) fs
  in
  newps, newfs

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

(* We build projections *)
let declare_projections indsp coers fields =
  let env = Global.env() in
  let (mib,mip) = Global.lookup_inductive indsp in
  let paramdecls = mip.mind_params_ctxt in
  let paramdecls = 
    List.map (fun (na,b,t) -> match na with Name id -> (id,b,t) | _ -> assert false)
      paramdecls in
  let r = mkInd indsp in
  let paramargs = List.rev (List.map (fun (id,_,_) -> mkVar id) paramdecls) in
  let rp = applist (r, paramargs) in
  let x = Termops.named_hd (Global.env()) r Anonymous in
  let proj_args = (* Rel 1 refers to "x" *) paramargs@[mkRel 1] in
  let (sp_projs,_,_) =
    List.fold_left2
      (fun (sp_projs,ids_not_ok,subst) coe (fi,optci,ti) ->
	 let fv_ti = match optci with
	   | Some ci -> global_vars env ci (* Type is then meaningless *)
	   | None -> global_vars env ti in
	 let bad_projs = (list_intersect ids_not_ok fv_ti) in
	 if bad_projs <> [] then begin
	   warning_or_error coe indsp (MissingProj (fi,bad_projs));
           (None::sp_projs,fi::ids_not_ok,subst)
         end else
	   let body = match optci with
	     | Some ci -> replace_vars subst ci
	     | None ->
		 let p = mkLambda (x, rp, replace_vars subst ti) in
		 let branch = it_mkNamedLambda_or_LetIn (mkVar fi) fields in
		 let ci = Inductiveops.make_case_info env indsp
			    (Some PrintLet) [| RegularPat |] in
		 mkCase (ci, p, mkRel 1, [|branch|]) in
	   let proj =
	     it_mkNamedLambda_or_LetIn (mkLambda (x, rp, body)) paramdecls in
	   let name = 
	     try
	       let cie = { const_entry_body = proj;
                           const_entry_type = None;
                           const_entry_opaque = false } in
	       let sp =
		 declare_constant fi (ConstantEntry cie,NeverDischarge)
	       in Some sp
             with Type_errors.TypeError (ctx,te) -> begin
               warning_or_error coe indsp (BadTypedProj (fi,ctx,te));
	       None
	     end in
	   match name with
	     | None -> (None::sp_projs, fi::ids_not_ok, subst)
	     | Some sp ->
		 let refi = ConstRef sp in
		 let constr_fi = mkConst sp in
		 if coe then begin
		   let cl = Class.class_of_ref (IndRef indsp) in
		   Class.try_add_new_coercion_with_source 
		     refi NeverDischarge cl
		 end;
		 let constr_fip = applist (constr_fi,proj_args) in
		 (name::sp_projs, ids_not_ok, (fi,constr_fip)::subst))
      ([],[],[]) coers (List.rev fields)
  in sp_projs

let degenerate_decl env =
  snd 
    (List.fold_right
       (fun (id,c,t) (ids,env) ->
	  let d = match c with
	    | None -> Typeops.LocalAssum (subst_vars ids t)
	    | Some c -> Typeops.LocalDef (subst_vars ids c) in
	  (id::ids, (id,d)::env))
       env ([],[]))

(* [fs] corresponds to fields and [ps] to parameters; [coers] is a boolean 
   list telling if the corresponding fields must me declared as coercion *)
let definition_structure (is_coe,idstruc,ps,cfs,idbuild,s) =
  let coers,fs = List.split cfs in
  let nparams = List.length ps in
  let idps = List.map fst ps in
  let allnames =  idstruc::idps@(List.map (fun (id,_,_) -> id) fs) in
  if not (list_distinct allnames) then error "Two objects have the same name";
  if occur_fields idstruc fs then error "A record cannot be recursive";
  (* Now, younger decl in params and fields is on top *)
  let params,fields = typecheck_params_and_field ps fs in
  let args =  List.map mkVar idps in
  let ind = applist (mkVar idstruc, args) in
  let subst = List.rev (idstruc::idps) in
  let named_type_constructor = it_mkNamedProd_or_LetIn ind fields in
  let type_constructor = subst_vars subst named_type_constructor in
  let mie_ind =
    { mind_entry_nparams = nparams;
      mind_entry_params = degenerate_decl params;
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
  if is_coe then Class.try_add_new_coercion build NeverDischarge;
  Recordops.add_new_struc (rsp,idbuild,nparams,List.rev sp_projs)

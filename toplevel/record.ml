
(* $:Id$ *)

open Pp
open Util
open Names
open Term
open Environ
open Declarations
open Declare
open Coqast
open Astterm
open Command

(********** definition d'un record (structure) **************)

let make_constructor idstruc idps fields  =
  let app_constructor = 
    Ast.ope("APPLISTEXPL",
        (Ast.nvar (string_of_id idstruc))::
        List.map (fun id -> Ast.nvar(string_of_id id)) idps) in
  let rec aux fields =
    match fields with
      | [] -> app_constructor
      | (id,true,ty)::l ->
	  Ast.ope("PROD",[ty; Ast.slam(Some (string_of_id id), aux l)])
      | (id,false,c)::l ->
	  Ast.ope("LETIN",[c; Ast.slam(Some (string_of_id id), aux l)])
  in 
  aux fields

let occur_fields id fs =
  List.exists (fun (_,_,a) -> Ast.occur_var_ast (string_of_id id) a) fs

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
  | BadTypedProj of identifier * path_kind * env * Type_errors.type_error

let warning_or_error coe err =
  let st = match err with
    | MissingProj (fi,projs) ->
	let s,have = if List.length projs > 1 then "s","have" else "","has" in
        [< 'sTR(string_of_id fi);
	   'sTR" cannot be defined because the projection"; 'sTR s; 'sPC;
           prlist_with_sep pr_coma pr_id projs; 'sPC; 'sTR have; 'sTR "n't." >]
    | BadTypedProj (fi,k,ctx,te) ->
        [<'sTR (string_of_id fi); 
          'sTR" cannot be defined for the following reason:";
	  'fNL; 'sTR "  "; hOV 2 (Himsg.explain_type_error k ctx te) >]
  in
  if coe then errorlabstrm "structure" st;
  pPNL (hOV 0 [< 'sTR"Warning: "; st >])

(* We build projections *)
let declare_projections indsp coers fields =
  let mispec = Global.lookup_mind_specif (indsp,[||]) in
  let paramdecls = Inductive.mis_params_ctxt mispec in
  let paramdecls = 
    List.map (fun (na,b,t) -> match na with Name id -> (id,b,t) | _ -> assert false)
      paramdecls in
  let r = constr_of_reference Evd.empty (Global.env()) (IndRef indsp) in
  let paramargs = List.rev (List.map (fun (id,_,_) -> mkVar id) paramdecls) in
  let rp = applist (r, paramargs) in
  let x = Environ.named_hd (Global.env()) r Anonymous in
  let proj_args = (* Rel 1 refers to "x" *) paramargs@[mkRel 1] in
  let (sp_projs,_,_) =
    List.fold_left2
      (fun (sp_projs,ids_not_ok,subst) coe (fi,optci,ti) ->
	 let fv_ti = match optci with
	   | Some ci -> global_vars ci (* Type is then meaningless *)
	   | None -> global_vars ti in
	 let bad_projs = (list_intersect ids_not_ok fv_ti) in
	 if bad_projs <> [] then begin
	   warning_or_error coe (MissingProj (fi,bad_projs));
           (None::sp_projs,fi::ids_not_ok,subst)
         end else
	   let body = match optci with
	     | Some ci -> replace_vars subst ci
	     | None ->
		 let p = mkLambda (x, rp, replace_vars subst ti) in
		 let branch = it_mkNamedLambda_or_LetIn (mkVar fi) fields in
		 let ci = Inductive.make_case_info
			    (Global.lookup_mind_specif (destMutInd r))
			    (Some PrintLet) [| RegularPat |] in
		 mkMutCase (ci, p, mkRel 1, [|branch|]) in
	   let proj =
	     it_mkNamedLambda_or_LetIn (mkLambda (x, rp, body)) paramdecls in
	   let name = 
	     try
	       let proj = instantiate_inductive_section_params proj indsp in
	       let cie = { const_entry_body = proj; const_entry_type = None} in
	       let sp =
		 declare_constant fi (ConstantEntry cie,NeverDischarge,false)
	       in Some sp
             with Type_errors.TypeError (k,ctx,te) -> begin
               warning_or_error coe (BadTypedProj (fi,k,ctx,te));
	       None
	     end in
	   match name with
	     | None -> (None::sp_projs, fi::ids_not_ok, subst)
	     | Some sp ->
		 let refi = ConstRef sp in
		 let constr_fi =
		   constr_of_reference Evd.empty (Global.env()) refi in
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
	    | None -> LocalAssum (subst_vars ids t)
	    | Some c -> LocalDef (subst_vars ids c) in
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

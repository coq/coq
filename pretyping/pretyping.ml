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
open Sign
open Evd
open Term
open Termops
open Reductionops
open Environ
open Type_errors
open Typeops
open Libnames
open Classops
open List
open Recordops 
open Evarutil
open Pretype_errors
open Rawterm
open Evarconv
open Coercion
open Pattern
open Dyn


(***********************************************************************)
(* This concerns Cases *)
open Declarations
open Inductive
open Inductiveops
open Instantiate

let lift_context n l = 
  let k = List.length l in 
  list_map_i (fun i (name,c) -> (name,liftn n (k-i) c)) 0 l

let transform_rec loc env sigma (pj,c,lf) indt = 
  let p = pj.uj_val in
  let (indf,realargs) = dest_ind_type indt in
  let (ind,params) = dest_ind_family indf in
  let (mib,mip) = lookup_mind_specif env ind in
  let recargs = mip.mind_recargs in
  let mI = mkInd ind in
  let ci = make_default_case_info env (if Options.do_translate() then RegularStyle else MatchStyle) ind in
  let nconstr = Array.length mip.mind_consnames in
  if Array.length lf <> nconstr then 
    (let cj = {uj_val=c; uj_type=mkAppliedInd indt} in
     error_number_branches_loc loc env sigma cj nconstr);
  let tyi = snd ind in
  if mis_is_recursive_subset [tyi] recargs then
    let dep =
      is_dependent_elimination env (nf_evar sigma pj.uj_type) indf in 
    let init_depFvec i = if i = tyi then Some(dep,mkRel 1) else None in
    let depFvec = Array.init mib.mind_ntypes init_depFvec in
    (* build now the fixpoint *)
    let lnames,_ = get_arity env indf in
    let nar = List.length lnames in
    let nparams = mip.mind_nparams in
    let constrs = get_constructors env (lift_inductive_family (nar+2) indf) in
    let branches = 
      array_map3
	(fun f t reca -> 
	   whd_beta
             (Indrec.make_rec_branch_arg env sigma
                (nparams,depFvec,nar+1)
                f t reca))
        (Array.map (lift (nar+2)) lf) constrs (dest_subterms recargs) 
    in 
    let deffix = 
      it_mkLambda_or_LetIn_name env
	(lambda_create env
	   (applist (mI,List.append (List.map (lift (nar+1)) params)
                       (extended_rel_list 0 lnames)),
            mkCase (ci, lift (nar+2) p, mkRel 1, branches)))
        (lift_rel_context 1 lnames) 
    in
    if noccurn 1 deffix then 
      whd_beta (applist (pop deffix,realargs@[c]))
    else
      let ind = applist (mI,(List.append 
			     (List.map (lift nar) params)
			     (extended_rel_list 0 lnames))) in
      let typPfix = 
	it_mkProd_or_LetIn_name env
	  (prod_create env 
	     (ind,
	      (if dep then
		 let ext_lnames = (Anonymous,None,ind)::lnames in
		 let args = extended_rel_list 0 ext_lnames in
		 whd_beta (applist (lift (nar+1) p, args))
	       else
		 let args = extended_rel_list 1 lnames in
		 whd_beta (applist (lift (nar+1) p, args)))))
          lnames in
      let fix =
        mkFix (([|nar|],0),
	       ([|Name(id_of_string "F")|],[|typPfix|],[|deffix|])) in
      applist (fix,realargs@[c])
  else
    mkCase (ci, p, c, lf)

(***********************************************************************)

(* To embed constr in rawconstr *)
let ((constr_in : constr -> Dyn.t),
     (constr_out : Dyn.t -> constr)) = create "constr"

let mt_evd = Evd.empty

let vect_lift_type = Array.mapi (fun i t -> type_app (lift i) t)

(* Utilisé pour inférer le prédicat des Cases *)
(* Semble exagérement fort *)
(* Faudra préférer une unification entre les types de toutes les clauses *)
(* et autoriser des ? à rester dans le résultat de l'unification *)

let evar_type_fixpoint loc env isevars lna lar vdefj =
  let lt = Array.length vdefj in 
    if Array.length lar = lt then 
      for i = 0 to lt-1 do 
        if not (the_conv_x_leq env isevars
		  (vdefj.(i)).uj_type
		  (lift lt lar.(i))) then
          error_ill_typed_rec_body_loc loc env (evars_of isevars)
            i lna vdefj lar
      done

let check_branches_message loc env isevars c (explft,lft) = 
  for i = 0 to Array.length explft - 1 do
    if not (the_conv_x_leq env isevars lft.(i) explft.(i)) then 
      let sigma = evars_of isevars in
      error_ill_formed_branch_loc loc env sigma c i lft.(i) explft.(i)
  done

(* coerce to tycon if any *)
let inh_conv_coerce_to_tycon loc env isevars j = function
   | None -> j
   | Some typ -> inh_conv_coerce_to loc env isevars j typ

let push_rels vars env = List.fold_right push_rel vars env

(*
let evar_type_case isevars env ct pt lft p c =
  let (mind,bty,rslty) = type_case_branches env (evars_of isevars) ct pt p c
  in check_branches_message isevars env (c,ct) (bty,lft); (mind,rslty)
*)

let strip_meta id = (* For Grammar v7 compatibility *)
  let s = string_of_id id in
  if s.[0]='$' then id_of_string (String.sub s 1 (String.length s - 1))
  else id

let pretype_id loc env (lvar,unbndltacvars) id =
  let id = strip_meta id in (* May happen in tactics defined by Grammar *)
  try
    List.assoc id lvar
  with Not_found ->
  try
    let (n,typ) = lookup_rel_id id (rel_context env) in
    { uj_val  = mkRel n; uj_type = type_app (lift n) typ }
  with Not_found ->
  try
    let (_,_,typ) = lookup_named id env in
    { uj_val  = mkVar id; uj_type = typ }
  with Not_found ->
  try (* To build a nicer ltac error message *)
    match List.assoc id unbndltacvars with
      | None -> user_err_loc (loc,"",
	  str (string_of_id id ^ " ist not bound to a term"))
      | Some id0 -> Pretype_errors.error_var_not_found_loc loc id0
  with Not_found ->
    error_var_not_found_loc loc id

(* make a dependent predicate from an undependent one *)

let make_dep_of_undep env (IndType (indf,realargs)) pj =
  let n = List.length realargs in
  let rec decomp n p =
    if n=0 then p else
      match kind_of_term p with
	| Lambda (_,_,c) -> decomp (n-1) c
	| _ -> decomp (n-1) (applist (lift 1 p, [mkRel 1])) 
  in
  let sign,s = decompose_prod_n n pj.uj_type in
  let ind = build_dependent_inductive env indf in
  let s' = mkProd (Anonymous, ind, s) in
  let ccl = lift 1 (decomp n pj.uj_val) in
  let ccl' = mkLambda (Anonymous, ind, ccl) in
  {uj_val=lam_it ccl' sign; uj_type=prod_it s' sign} 

(*************************************************************************)
(* Main pretyping function                                               *)

let pretype_ref isevars env ref = 
  let c = constr_of_reference ref in
  make_judge c (Retyping.get_type_of env Evd.empty c)

let pretype_sort = function
  | RProp c -> judge_of_prop_contents c
  | RType _ -> judge_of_new_Type ()

(* [pretype tycon env isevars lvar lmeta cstr] attempts to type [cstr] *)
(* in environment [env], with existential variables [(evars_of isevars)] and *)
(* the type constraint tycon *)
let rec pretype tycon env isevars lvar = function

  | RRef (loc,ref) ->
      inh_conv_coerce_to_tycon loc env isevars
	(pretype_ref isevars env ref)
	tycon

  | RVar (loc, id) ->
      inh_conv_coerce_to_tycon loc env isevars
	(pretype_id loc env lvar id)
	tycon

  | REvar (loc, ev, instopt) ->
      (* Ne faudrait-il pas s'assurer que hyps est bien un
      sous-contexte du contexte courant, et qu'il n'y a pas de Rel "caché" *)
      let hyps = (Evd.map (evars_of isevars) ev).evar_hyps in
      let args = match instopt with
        | None -> instance_from_named_context hyps
        | Some inst -> failwith "Evar subtitutions not implemented" in
      let c = mkEvar (ev, args) in
      let j = (Retyping.get_judgment_of env (evars_of isevars) c) in
      inh_conv_coerce_to_tycon loc env isevars j tycon

  | RPatVar (loc,(someta,n)) -> 
      anomaly "Found a pattern variable in a rawterm to type"
	   
  | RHole (loc,k) ->
      if !compter then nbimpl:=!nbimpl+1;
      (match tycon with
	 | Some ty ->
	     { uj_val = new_isevar isevars env (loc,k) ty; uj_type = ty }
	 | None -> error_unsolvable_implicit loc env (evars_of isevars) k)

  | RRec (loc,fixkind,names,bl,lar,vdef) ->
      let rec type_bl env ctxt = function
          [] -> ctxt
        | (na,None,ty)::bl ->
            let ty' = pretype_type empty_valcon env isevars lvar ty in
            let dcl = (na,None,ty'.utj_val) in
            type_bl (push_rel dcl env) (add_rel_decl dcl ctxt) bl
        | (na,Some bd,ty)::bl ->
            let ty' = pretype_type empty_valcon env isevars lvar ty in
            let bd' = pretype (mk_tycon ty'.utj_val) env isevars lvar ty in
            let dcl = (na,Some bd'.uj_val,ty'.utj_val) in
            type_bl (push_rel dcl env) (add_rel_decl dcl ctxt) bl in
      let ctxtv = Array.map (type_bl env empty_rel_context) bl in
      let larj =
        array_map2
          (fun e ar ->
            pretype_type empty_valcon (push_rel_context e env) isevars lvar ar)
          ctxtv lar in
      let lara = Array.map (fun a -> a.utj_val) larj in
      let ftys = array_map2 (fun e a -> it_mkProd_or_LetIn a e) ctxtv lara in
      let nbfix = Array.length lar in
      let names = Array.map (fun id -> Name id) names in
      (* Note: bodies are not used by push_rec_types, so [||] is safe *)
      let newenv = push_rec_types (names,ftys,[||]) env in
      let vdefj =
	array_map2_i 
	  (fun i ctxt def ->
            (* we lift nbfix times the type in tycon, because of
	     * the nbfix variables pushed to newenv *)
            let (ctxt,ty) =
              decompose_prod_n_assum (rel_context_length ctxt)
                (lift nbfix ftys.(i)) in
            let nenv = push_rel_context ctxt newenv in
            let j = pretype (mk_tycon ty) nenv isevars lvar def in
            { uj_val = it_mkLambda_or_LetIn j.uj_val ctxt;
              uj_type = it_mkProd_or_LetIn j.uj_type ctxt })
          ctxtv vdef in
      evar_type_fixpoint loc env isevars names ftys vdefj;
      let fixj =
	match fixkind with
	  | RFix (vn,i as vni) ->
	      let fix = (vni,(names,ftys,Array.map j_val vdefj)) in
	      (try check_fix env fix with e -> Stdpp.raise_with_loc loc e);
	      make_judge (mkFix fix) ftys.(i)
	  | RCoFix i -> 
	      let cofix = (i,(names,ftys,Array.map j_val vdefj)) in
	      (try check_cofix env cofix with e -> Stdpp.raise_with_loc loc e);
	      make_judge (mkCoFix cofix) ftys.(i) in
      inh_conv_coerce_to_tycon loc env isevars fixj tycon

  | RSort (loc,s) ->
      inh_conv_coerce_to_tycon loc env isevars (pretype_sort s) tycon

  | RApp (loc,f,args) -> 
      let fj = pretype empty_tycon env isevars lvar f in
      let floc = loc_of_rawconstr f in
      let rec apply_rec env n resj = function
	| [] -> resj
	| c::rest ->
	    let argloc = loc_of_rawconstr c in
	    let resj = inh_app_fun env isevars resj in
            let resty =
              whd_betadeltaiota env (evars_of isevars) resj.uj_type in
      	    match kind_of_term resty with
	      | Prod (na,c1,c2) ->
		  let hj = pretype (mk_tycon c1) env isevars lvar c in
		  let newresj =
      		    { uj_val = applist (j_val resj, [j_val hj]);
		      uj_type = subst1 hj.uj_val c2 } in
		  apply_rec env (n+1) newresj rest

	      | _ ->
		  let hj = pretype empty_tycon env isevars lvar c in
		  error_cant_apply_not_functional_loc 
		    (join_loc floc argloc) env (evars_of isevars)
	      	    resj [hj]

      in let resj = apply_rec env 1 fj args in
      (*
	let apply_one_arg (floc,tycon,jl) c =
	let (dom,rng) = split_tycon floc env isevars tycon in
	let cj = pretype dom env isevars lvar c in
	let rng_tycon = option_app (subst1 cj.uj_val) rng in
	let argloc = loc_of_rawconstr c in
	(join_loc floc argloc,rng_tycon,(argloc,cj)::jl)  in
	let _,_,jl =
	List.fold_left apply_one_arg (floc,mk_tycon j.uj_type,[]) args in
	let jl = List.rev jl in
	let resj = inh_apply_rel_list loc env isevars jl (floc,j) tycon in
      *)
      inh_conv_coerce_to_tycon loc env isevars resj tycon

  | RLambda(loc,name,c1,c2)      ->
      let (name',dom,rng) = split_tycon loc env isevars tycon in
      let dom_valcon = valcon_of_tycon dom in
      let j = pretype_type dom_valcon env isevars lvar c1 in
      let var = (name,None,j.utj_val) in
      let j' = pretype rng (push_rel var env) isevars lvar c2 in 
      judge_of_abstraction env name j j'

  | RProd(loc,name,c1,c2)        ->
      let j = pretype_type empty_valcon env isevars lvar c1 in
      let var = (name,j.utj_val) in
      let env' = push_rel_assum var env in
      let j' = pretype_type empty_valcon env' isevars lvar c2 in
      let resj =
	try judge_of_product env name j j'
	with TypeError _ as e -> Stdpp.raise_with_loc loc e in
      inh_conv_coerce_to_tycon loc env isevars resj tycon
	
  | RLetIn(loc,name,c1,c2)      ->
      let j = pretype empty_tycon env isevars lvar c1 in
      let t = Evarutil.refresh_universes j.uj_type in
      let var = (name,Some j.uj_val,t) in
        let tycon = option_app (lift 1) tycon in
      let j' = pretype tycon (push_rel var env) isevars lvar c2 in
      { uj_val = mkLetIn (name, j.uj_val, t, j'.uj_val) ;
	uj_type = type_app (subst1 j.uj_val) j'.uj_type }

  | RLetTuple (loc,nal,(na,po),c,d) ->
      let cj = pretype empty_tycon env isevars lvar c in
      let (IndType (indf,realargs) as indt) = 
	try find_rectype env (evars_of isevars) cj.uj_type
	with Not_found ->
	  let cloc = loc_of_rawconstr c in
	  error_case_not_inductive_loc cloc env (evars_of isevars) cj 
      in
      let cstrs = get_constructors env indf in
      if Array.length cstrs <> 1 then
        user_err_loc (loc,"",str "Destructing let is only for inductive types with one constructor");
      let cs = cstrs.(0) in
      if List.length nal <> cs.cs_nargs then
        user_err_loc (loc,"", str "Destructing let on this type expects " ++ int cs.cs_nargs ++ str " variables");
      let fsign = List.map2 (fun na (_,c,t) -> (na,c,t))
        (List.rev nal) cs.cs_args in
      let env_f = push_rels fsign env in
      (* Make dependencies from arity signature impossible *)
      let arsgn,_ = get_arity env indf in
      let arsgn = List.map (fun (_,b,t) -> (Anonymous,b,t)) arsgn in
      let psign = (na,None,build_dependent_inductive env indf)::arsgn in
      let nar = List.length arsgn in
      (match po with
	 | Some p ->
             let env_p = push_rels psign env in
             let pj = pretype_type empty_valcon env_p isevars lvar p in
             let ccl = nf_evar (evars_of isevars) pj.utj_val in
	     let psign = make_arity_signature env true indf in (* with names *)
	     let p = it_mkLambda_or_LetIn ccl psign in
             let inst = 
	       (Array.to_list cs.cs_concl_realargs)
	       @[build_dependent_constructor cs] in
	     let lp = lift cs.cs_nargs p in
             let fty = hnf_lam_applist env (evars_of isevars) lp inst in
	     let fj = pretype (mk_tycon fty) env_f isevars lvar d in
	     let f = it_mkLambda_or_LetIn fj.uj_val fsign in
	     let v =
	       let mis,_ = dest_ind_family indf in
	       let ci = make_default_case_info env LetStyle mis in
	       mkCase (ci, p, cj.uj_val,[|f|]) in 
             let cs = build_dependent_constructor cs in
	     { uj_val = v; uj_type = substl (realargs@[cj.uj_val]) ccl }

	 | None -> 
             let tycon = option_app (lift cs.cs_nargs) tycon in
	     let fj = pretype tycon env_f isevars lvar d in
	     let f = it_mkLambda_or_LetIn fj.uj_val fsign in
	     let ccl = nf_evar (evars_of isevars) fj.uj_type in
             let ccl =
               if noccur_between 1 cs.cs_nargs ccl then
                 lift (- cs.cs_nargs) ccl 
               else
                 error_cant_find_case_type_loc loc env (evars_of isevars) 
                   cj.uj_val in
             let p = it_mkLambda_or_LetIn (lift (nar+1) ccl) psign in
	     let v =
	       let mis,_ = dest_ind_family indf in
	       let ci = make_default_case_info env LetStyle mis in
	       mkCase (ci, p, cj.uj_val,[|f|] ) 
	     in
	     { uj_val = v; uj_type = ccl })

  (* Special Case for let constructions to avoid exponential behavior *)      
  | ROrderedCase (loc,st,po,c,[|f|],xx) when st <> MatchStyle ->
      let cj = pretype empty_tycon env isevars lvar c in
      let (IndType (indf,realargs) as indt) = 
	try find_rectype env (evars_of isevars) cj.uj_type
	with Not_found ->
	  let cloc = loc_of_rawconstr c in
	  error_case_not_inductive_loc cloc env (evars_of isevars) cj 
      in
      let j = match po with
	 | Some p ->
             let pj = pretype empty_tycon env isevars lvar p in
             let dep = is_dependent_elimination env pj.uj_type indf in
             let ar =
               arity_of_case_predicate env indf dep (Type (new_univ())) in
             let _ = the_conv_x_leq env isevars pj.uj_type ar in
	     let pj = j_nf_evar (evars_of isevars) pj in
	     let pj = if dep then pj else make_dep_of_undep env indt pj in
	     let (bty,rsty) = 
	       Indrec.type_rec_branches 
		 false env (evars_of isevars) indt pj.uj_val cj.uj_val 
	     in
	     if Array.length bty <> 1 then
	       error_number_branches_loc 
		 loc env (evars_of isevars) cj (Array.length bty);
	     let fj = 
	       let tyc = bty.(0) in 
	       pretype (mk_tycon tyc) env isevars lvar f 
	     in
	     let fv = j_val fj in
	     let ft = fj.uj_type in
	     check_branches_message loc env isevars cj.uj_val (bty,[|ft|]);
	     let v =
	       let mis,_ = dest_ind_family indf in
	       let ci = make_default_case_info env st mis in
	       mkCase (ci, (nf_betaiota pj.uj_val), cj.uj_val,[|fv|])
	     in 
	     { uj_val = v;  uj_type = rsty }

	 | None -> 
             (* get type information from type of branches *)
	     let expbr = Cases.branch_scheme env isevars false indf in
	     if Array.length expbr <> 1 then
	       error_number_branches_loc loc env (evars_of isevars) 
		 cj (Array.length expbr);
             let expti = expbr.(0) in
	     let fj = pretype (mk_tycon expti) env isevars lvar f in
	     let use_constraint () =
               (* get type information from constraint *)
               (* warning: if the constraint comes from an evar type, it *)
               (* may be Type while Prop or Set would be expected *)
	       match tycon with
		 | Some pred ->
		     let arsgn = make_arity_signature env true indf in
                     let pred = lift (List.length arsgn) pred in
  		     let pred = 
                       it_mkLambda_or_LetIn (nf_evar (evars_of isevars) pred)
			 arsgn in
                     false, pred
	         | None ->
                     let sigma = evars_of isevars in
                     error_cant_find_case_type_loc loc env sigma cj.uj_val
	     in
             let ok, p =
	       try
		 let pred = 
		   Cases.pred_case_ml 
		     env (evars_of isevars) false indt (0,fj.uj_type) 
		 in 
		 if has_undefined_isevars isevars pred then
		   use_constraint ()
		 else
		   true, pred
	       with Cases.NotInferable _ ->
		 use_constraint ()
	     in 
	     let p = nf_evar (evars_of isevars) p in
	     let (bty,rsty) =
	       Indrec.type_rec_branches
		 false env (evars_of isevars) indt p cj.uj_val 
	     in
	     let _ = option_app (the_conv_x_leq env isevars rsty) tycon in
	     let fj = 
	       if ok then fj 
	       else pretype (mk_tycon bty.(0)) env isevars lvar f 
	     in
	     let fv = fj.uj_val in
	     let ft = fj.uj_type in
	     let v =
	       let mis,_ = dest_ind_family indf in
	       let ci = make_default_case_info env st mis in
	       mkCase (ci, (nf_betaiota p), cj.uj_val,[|fv|] ) 
	     in
	     { uj_val = v; uj_type = rsty } in

      (* Build the LetTuple form for v8 *)
      let c =
        let (ind,params) = dest_ind_family indf in
        let rtntypopt, indnalopt = match po with
          | None -> None, (Anonymous,None)
          | Some p ->
              let pj = pretype empty_tycon env isevars lvar p in
              let dep = is_dependent_elimination env pj.uj_type indf in
              let rec decomp_lam_force n avoid l p =
                (* avoid is not exhaustive ! *)
                if n = 0 then (List.rev l,p,avoid) else
                  match p with
                    | RLambda (_,(Name id as na),_,c) -> 
                        decomp_lam_force (n-1) (id::avoid) (na::l) c
                    | RLambda (_,(Anonymous as na),_,c) ->
                        decomp_lam_force (n-1) avoid (na::l) c
                    | _ ->
                        let x = Nameops.next_ident_away (id_of_string "x") avoid in
                        decomp_lam_force (n-1) (x::avoid) (Name x :: l) 
                          (* eta-expansion *)
                          (RApp (dummy_loc,p, [RVar (dummy_loc,x)])) in
              let (nal,p,avoid) = 
                decomp_lam_force (List.length realargs) [] [] p in
              let na,rtntyp,_ = 
                if dep then decomp_lam_force 1 avoid [] p
                else [Anonymous],p,[] in
              let intyp =
                if List.for_all
                  (function
                    | Anonymous -> true
                    | Name id -> not (occur_rawconstr id rtntyp)) nal
                then (* No dependency in realargs *)
                  None
                else
                  let args = List.map (fun _ -> Anonymous) params @ nal in
                  Some (dummy_loc,ind,args) in
              (Some rtntyp,(List.hd na,intyp)) in
        let cs = (get_constructors env indf).(0) in
        match indnalopt with
          | (na,None) -> (* Represented as a let *)
              let rec decomp_lam_force n avoid l p =
                if n = 0 then (List.rev l,p) else
                  match p with
                    | RLambda (_,(Name id as na),_,c) -> 
                        decomp_lam_force (n-1) (id::avoid) (na::l) c
                    | RLambda (_,(Anonymous as na),_,c) -> 
                        decomp_lam_force (n-1) avoid (na::l) c
                    | _ ->
                        let x = Nameops.next_ident_away (id_of_string "x") avoid in
                        decomp_lam_force (n-1) (x::avoid) (Name x :: l) 
                          (* eta-expansion *)
                          (let a = RVar (dummy_loc,x) in
                          match p with
                            | RApp (loc,p,l) -> RApp (loc,p,l@[a])
                            | _ -> (RApp (dummy_loc,p,[a]))) in
              let (nal,d) = decomp_lam_force cs.cs_nargs [] [] f in
              RLetTuple (loc,nal,(na,rtntypopt),c,d)
          | _ -> (* Represented as a match *)
            let detype_eqn constr construct_nargs branch =
              let name_cons = function 
                | Anonymous -> fun l -> l
                | Name id -> fun l -> id::l in
              let make_pat na avoid b ids =
                PatVar (dummy_loc,na),
                name_cons na avoid,name_cons na ids
              in
              let rec buildrec ids patlist avoid n b =
                if n=0 then
                  (dummy_loc, ids, 
                  [PatCstr(dummy_loc, constr, List.rev patlist,Anonymous)],
                  b)
                else
                  match b with
	            | RLambda (_,x,_,b) -> 
	                let pat,new_avoid,new_ids = make_pat x avoid b ids in
                        buildrec new_ids (pat::patlist) new_avoid (n-1) b
                          
	            | RLetIn (_,x,_,b) -> 
	                let pat,new_avoid,new_ids = make_pat x avoid b ids in
                        buildrec new_ids (pat::patlist) new_avoid (n-1) b
                          
	            | RCast (_,c,_) ->    (* Oui, il y a parfois des cast *)
	                buildrec ids patlist avoid n c
                        
	            | _ -> (* eta-expansion *)
                        (* nommage de la nouvelle variable *)
                        let id = Nameops.next_ident_away (id_of_string "x") avoid in
	                let new_b = RApp (dummy_loc, b, [RVar(dummy_loc,id)])in
                        let pat,new_avoid,new_ids =
	                  make_pat (Name id) avoid new_b ids in
	                buildrec new_ids (pat::patlist) new_avoid (n-1) new_b
	                  
              in 
              buildrec [] [] [] construct_nargs branch in
            let eqn = detype_eqn (ind,1) cs.cs_nargs f in
            RCases (loc,(po,ref rtntypopt),[c,ref indnalopt],[eqn])
      in
      xx := Some c;
      (* End building the v8 syntax *)
      j

  | RIf (loc,c,(na,po),b1,b2) ->
      let cj = pretype empty_tycon env isevars lvar c in
      let (IndType (indf,realargs) as indt) = 
	try find_rectype env (evars_of isevars) cj.uj_type
	with Not_found ->
	  let cloc = loc_of_rawconstr c in
	  error_case_not_inductive_loc cloc env (evars_of isevars) cj in
      let cstrs = get_constructors env indf in 
      if Array.length cstrs <> 2 then
        user_err_loc (loc,"",
	  str "If is only for inductive types with two constructors");

      (* Make dependencies from arity signature impossible *)
      let arsgn,_ = get_arity env indf in
      let arsgn = List.map (fun (_,b,t) -> (Anonymous,b,t)) arsgn in
      let nar = List.length arsgn in
      let psign = (na,None,build_dependent_inductive env indf)::arsgn in
      let pred,p = match po with
	| Some p ->
	    let env_p = push_rels psign env in
            let pj = pretype_type empty_valcon env_p isevars lvar p in
            let ccl = nf_evar (evars_of isevars) pj.utj_val in
	    let pred = it_mkLambda_or_LetIn ccl psign in
	    pred, lift (- nar) (beta_applist (pred,[cj.uj_val]))
	| None -> 
	    let p = match tycon with
	    | Some ty -> ty
	    | None -> new_isevar isevars env (loc,InternalHole) (new_Type ())
	    in
	    it_mkLambda_or_LetIn (lift (nar+1) p) psign, p in
      let f cs b =
	let n = rel_context_length cs.cs_args in
	let pi = liftn n 2 pred in
	let pi = beta_applist (pi, [build_dependent_constructor cs]) in
	let csgn = List.map (fun (_,b,t) -> (Anonymous,b,t)) cs.cs_args in
	let env_c = push_rels csgn env in 
	let bj = pretype (Some pi) env_c isevars lvar b in
	it_mkLambda_or_LetIn bj.uj_val cs.cs_args in
      let b1 = f cstrs.(0) b1 in
      let b2 = f cstrs.(1) b2 in
      let pred = nf_evar (evars_of isevars) pred in
      let p = nf_evar (evars_of isevars) p in
      let v =
	let mis,_ = dest_ind_family indf in
	let ci = make_default_case_info env IfStyle mis in
	mkCase (ci, pred, cj.uj_val, [|b1;b2|])
      in
      { uj_val = v; uj_type = p }

  | ROrderedCase (loc,st,po,c,lf,x) ->
      let isrec = (st = MatchStyle) in
      let cj = pretype empty_tycon env isevars lvar c in
      let (IndType (indf,realargs) as indt) = 
	try find_rectype env (evars_of isevars) cj.uj_type
	with Not_found ->
	  let cloc = loc_of_rawconstr c in
	  error_case_not_inductive_loc cloc env (evars_of isevars) cj in
      let (dep,pj) = match po with
	| Some p ->
            let pj = pretype empty_tycon env isevars lvar p in
            let dep = is_dependent_elimination env pj.uj_type indf in
            let ar =
              arity_of_case_predicate env indf dep (Type (new_univ())) in
            let _ = the_conv_x_leq env isevars pj.uj_type ar in
            (dep, pj)
	| None -> 
            (* get type information from type of branches *)
	    let expbr = Cases.branch_scheme env isevars isrec indf in
	    let rec findtype i =
	      if i >= Array.length lf
	      then
                (* get type information from constraint *)
                (* warning: if the constraint comes from an evar type, it *)
                (* may be Type while Prop or Set would be expected *)
	        match tycon with
		  | Some pred ->
		      let arsgn = make_arity_signature env true indf in
                      let pred = lift (List.length arsgn) pred in
  		      let pred = 
			it_mkLambda_or_LetIn (nf_evar (evars_of isevars) pred)
			  arsgn in
                      (true, 
                       Retyping.get_judgment_of env (evars_of isevars) pred)
	          | None ->
                      let sigma = evars_of isevars in
                      error_cant_find_case_type_loc loc env sigma cj.uj_val
	      else
		try
		  let expti = expbr.(i) in
		  let fj =
		    pretype (mk_tycon expti) env isevars lvar lf.(i) in
		  let pred = 
		    Cases.pred_case_ml (* eta-expanse *)
                      env (evars_of isevars) isrec indt (i,fj.uj_type) in
		  if has_undefined_isevars isevars pred then findtype (i+1)
		  else 
		    let pty =
                      Retyping.get_type_of env (evars_of isevars) pred in
		    let pj = { uj_val = pred; uj_type = pty } in
(*
                    let _ = option_app (the_conv_x_leq env isevars pred) tycon
                    in
*)
                    (true,pj)
		with Cases.NotInferable _ -> findtype (i+1) in
	    findtype 0 
      in
      let pj = j_nf_evar (evars_of isevars) pj in
      let pj = if dep then pj else make_dep_of_undep env indt pj in
      let (bty,rsty) =
	Indrec.type_rec_branches
          isrec env (evars_of isevars) indt pj.uj_val cj.uj_val in
      let _ = option_app (the_conv_x_leq env isevars rsty) tycon in
      if Array.length bty <> Array.length lf then
	error_number_branches_loc loc env (evars_of isevars) 
	  cj (Array.length bty)
      else
	let lfj =
	  array_map2
            (fun tyc f -> pretype (mk_tycon tyc) env isevars lvar f) bty
            lf in
	let lfv = Array.map j_val lfj in
	let lft = Array.map (fun j -> j.uj_type) lfj in
	check_branches_message loc env isevars cj.uj_val (bty,lft);
	let v =
	  if isrec
	  then 
	    transform_rec loc env (evars_of isevars)(pj,cj.uj_val,lfv) indt
	  else
	    let mis,_ = dest_ind_family indf in
	    let ci = make_default_case_info env st mis in
	    mkCase (ci, (nf_betaiota pj.uj_val), cj.uj_val,
                       Array.map (fun j-> j.uj_val) lfj)
	in
        (* Build the Cases form for v8 *)
        let c =
          let (ind,params) = dest_ind_family indf in
          let (mib,mip) = lookup_mind_specif env ind in
          let recargs = mip.mind_recargs in
          let mI = mkInd ind in
          let nconstr = Array.length mip.mind_consnames in
          let tyi = snd ind in
          if isrec && mis_is_recursive_subset [tyi] recargs then
            Some (Detyping.detype (false,env)
	      (ids_of_context env) (names_of_rel_context env)
              (nf_evar (evars_of isevars) v))
	  else
	    (* Translate into a "match ... with" *)
            let rtntypopt, indnalopt = match po with
              | None -> None, (Anonymous,None)
              | Some p ->
                  let rec decomp_lam_force n avoid l p =
                    (* avoid is not exhaustive ! *)
                    if n = 0 then (List.rev l,p,avoid) else
                      match p with
                        | RLambda (_,(Name id as na),_,c) -> 
                            decomp_lam_force (n-1) (id::avoid) (na::l) c
                        | RLambda (_,(Anonymous as na),_,c) ->
                            decomp_lam_force (n-1) avoid (na::l) c
                        | _ ->
                            let x = Nameops.next_ident_away (id_of_string "x") avoid in
                            decomp_lam_force (n-1) (x::avoid) (Name x :: l) 
                              (* eta-expansion *)
                              (RApp (dummy_loc,p, [RVar (dummy_loc,x)])) in
                  let (nal,p,avoid) = 
                    decomp_lam_force (List.length realargs) [] [] p in
                  let na,rtntyopt,_ = 
                    if dep then decomp_lam_force 1 avoid [] p
                    else [Anonymous],p,[] in
		  let intyp =
		    if nal=[] then None else
                      let args = List.map (fun _ -> Anonymous) params @ nal in
		      Some (dummy_loc,ind,args) in
                  (Some rtntyopt,(List.hd na,intyp)) in
	    let rawbranches =
	      array_map3 (fun bj b cstr ->
		let rec strip n r = if n=0 then r else
		  match r with
		    | RLambda (_,_,_,t) -> strip (n-1) t
		    | RLetIn (_,_,_,t) -> strip (n-1) t
		    | _ -> assert false in
		let n = rel_context_length cstr.cs_args in
		try
		  let _,ccl = decompose_lam_n_assum n bj.uj_val in
		  if noccur_between 1 n ccl then Some (strip n b) else None
		with _ -> (* Not eta-expanded or not reduced *) None)
		lfj lf (get_constructors env indf) in
	    if st = IfStyle & snd indnalopt = None 
	       & rawbranches.(0) <> None && rawbranches.(1) <> None then
	      (* Translate into a "if ... then ... else" *)
	      (* TODO: translate into a "if" even if po is dependent *)
	      Some (RIf (loc,c,(fst indnalopt,rtntypopt),
	          out_some rawbranches.(0),out_some rawbranches.(1)))
	    else
            let detype_eqn constr construct_nargs branch =
              let name_cons = function 
                | Anonymous -> fun l -> l
                | Name id -> fun l -> id::l in
              let make_pat na avoid b ids =
                PatVar (dummy_loc,na),
                name_cons na avoid,name_cons na ids
              in
              let rec buildrec ids patlist avoid n b =
                if n=0 then
                  (dummy_loc, ids, 
                  [PatCstr(dummy_loc, constr, List.rev patlist,Anonymous)],
                  b)
                else
                  match b with
	            | RLambda (_,x,_,b) -> 
	                let pat,new_avoid,new_ids = make_pat x avoid b ids in
                        buildrec new_ids (pat::patlist) new_avoid (n-1) b
                          
	            | RLetIn (_,x,_,b) -> 
	                let pat,new_avoid,new_ids = make_pat x avoid b ids in
                        buildrec new_ids (pat::patlist) new_avoid (n-1) b
                          
	            | RCast (_,c,_) ->    (* Oui, il y a parfois des cast *)
	                buildrec ids patlist avoid n c
                        
	            | _ -> (* eta-expansion *)
                        (* nommage de la nouvelle variable *)
                        let id = Nameops.next_ident_away (id_of_string "x") avoid in
	                let new_b = RApp (dummy_loc, b, [RVar(dummy_loc,id)])in
                        let pat,new_avoid,new_ids =
	                  make_pat (Name id) avoid new_b ids in
	                buildrec new_ids (pat::patlist) new_avoid (n-1) new_b
	                  
              in 
              buildrec [] [] [] construct_nargs branch in
            let (mib,mip) = Inductive.lookup_mind_specif (Global.env()) ind in
            let get_consnarg j = 
              let typi = mis_nf_constructor_type (ind,mib,mip) (j+1) in
              let _,t = decompose_prod_n_assum mip.mind_nparams typi in
              List.rev (fst (decompose_prod_assum t)) in
            let consnargs = Array.init (Array.length mip.mind_consnames) get_consnarg in
            let consnargsl = Array.map List.length consnargs in
            let constructs = Array.init (Array.length lf) (fun i -> (ind,i+1)) in
            let eqns = array_map3 detype_eqn constructs consnargsl lf in
            Some (RCases (loc,(po,ref rtntypopt),[c,ref indnalopt],Array.to_list eqns)) in
        x := c;
        (* End build the Cases form for v8 *)
	{ uj_val = v;
	  uj_type = rsty }

  | RCases (loc,po,tml,eqns) ->
      Cases.compile_cases loc
	((fun vtyc env -> pretype vtyc env isevars lvar),isevars)
	tycon env (* loc *) (po,tml,eqns)

  | RCast(loc,c,t) ->
      let tj = pretype_type empty_tycon env isevars lvar t in
      let cj = pretype (mk_tycon tj.utj_val) env isevars lvar c in
      (* User Casts are for helping pretyping, experimentally not to be kept*)
      (* ... except for Correctness *)
      let v = mkCast (cj.uj_val, tj.utj_val) in
      let cj = { uj_val = v; uj_type = tj.utj_val } in
      inh_conv_coerce_to_tycon loc env isevars cj tycon

  | RDynamic (loc,d) ->
    if (tag d) = "constr" then
      let c = constr_out d in
      let j = (Retyping.get_judgment_of env (evars_of isevars) c) in
      j
      (*inh_conv_coerce_to_tycon loc env isevars j tycon*)
    else
      user_err_loc (loc,"pretype",(str "Not a constr tagged Dynamic"))

(* [pretype_type valcon env isevars lvar c] coerces [c] into a type *)
and pretype_type valcon env isevars lvar = function
  | RHole loc ->
      if !compter then nbimpl:=!nbimpl+1;
      (match valcon with
	 | Some v ->
	     { utj_val = v;
	       utj_type = Retyping.get_sort_of env (evars_of isevars) v }
	 | None ->
	     let s = new_Type_sort () in
	     { utj_val = new_isevar isevars env loc (mkSort s);
	       utj_type = s})
  | c ->
      let j = pretype empty_tycon env isevars lvar c in
      let tj = inh_coerce_to_sort env isevars j in
      match valcon with
	| None -> tj
	| Some v ->
	    if the_conv_x_leq env isevars v tj.utj_val then tj
	    else
	      error_unexpected_type_loc
                (loc_of_rawconstr c) env (evars_of isevars) tj.utj_val v


let unsafe_infer tycon isevars env lvar constr =
  let j = pretype tycon env isevars lvar constr in
  j_nf_evar (evars_of isevars) j

let unsafe_infer_type valcon isevars env lvar constr =
  let tj = pretype_type valcon env isevars lvar constr in
  tj_nf_evar (evars_of isevars) tj

(* If fail_evar is false, [process_evars] builds a meta_map with the
   unresolved Evar that were not in initial sigma; otherwise it fail
   on the first unresolved Evar not already in the initial sigma. *)
(* [fail_evar] says how to process unresolved evars:
 *   true -> raise an error message
 *   false -> convert them into new Metas (casted with their type)
 *)
(* assumes the defined existentials have been replaced in c (should be
   done in unsafe_infer and unsafe_infer_type) *)
let check_evars fail_evar env initial_sigma isevars c =
  let sigma = evars_of isevars in
  let rec proc_rec c =
    match kind_of_term c with
      | Evar (ev,args as k) ->
          assert (Evd.in_dom sigma ev);
	  if not (Evd.in_dom initial_sigma ev) then
	    (if fail_evar then
              let (loc,k) = evar_source ev isevars in
	       error_unsolvable_implicit loc env sigma k)
      | _ -> iter_constr proc_rec c      
  in
  proc_rec c

(* TODO: comment faire remonter l'information si le typage a resolu des
       variables du sigma original. il faudrait que la fonction de typage
       retourne aussi le nouveau sigma...
*)

(* constr with holes *)
type open_constr = evar_map * constr

let ise_resolve_casted_gen fail_evar sigma env lvar typ c =
  let isevars = create_evar_defs sigma in
  let j = unsafe_infer (mk_tycon typ) isevars env lvar c in
  check_evars fail_evar env sigma isevars (mkCast(j.uj_val,j.uj_type));
  (evars_of isevars, j)

let ise_resolve_casted sigma env typ c =
  ise_resolve_casted_gen true sigma env ([],[]) typ c

(* Raw calls to the unsafe inference machine: boolean says if we must fail
   on unresolved evars, or replace them by Metas; the unsafe_judgment list
   allows us to extend env with some bindings *)
let ise_infer_gen fail_evar sigma env lvar exptyp c =
  let tycon = match exptyp with None -> empty_tycon | Some t -> mk_tycon t in
  let isevars = create_evar_defs sigma in
  let j = unsafe_infer tycon isevars env lvar c in
  check_evars fail_evar env sigma isevars (mkCast(j.uj_val,j.uj_type));
  (evars_of isevars, j)

let ise_infer_type_gen fail_evar sigma env lvar c =
  let isevars = create_evar_defs sigma in
  let tj = unsafe_infer_type empty_valcon isevars env lvar c in
  check_evars fail_evar env sigma isevars tj.utj_val;
  (evars_of isevars, tj)

type var_map = (identifier * unsafe_judgment) list

let understand_judgment sigma env c =
  snd (ise_infer_gen true sigma env ([],[]) None c)

let understand_type_judgment sigma env c =
  snd (ise_infer_type_gen true sigma env ([],[]) c)

let understand sigma env c =
  let _, c = ise_infer_gen true sigma env ([],[]) None c in
  c.uj_val

let understand_type sigma env c =
  let _,c = ise_infer_type_gen true sigma env ([],[]) c in
  c.utj_val

let understand_gen_ltac sigma env lvar ~expected_type:exptyp c =
  let _, c = ise_infer_gen true sigma env lvar exptyp c in
  c.uj_val

let understand_gen sigma env lvar ~expected_type:exptyp c =
  let _, c = ise_infer_gen true sigma env (lvar,[]) exptyp c in
  c.uj_val

let understand_gen_tcc sigma env lvar exptyp c =
  let metamap, c = ise_infer_gen false sigma env (lvar,[]) exptyp c in
  metamap, c.uj_val

let interp_sort = function
  | RProp c -> Prop c
  | RType _ -> new_Type_sort ()

let interp_elimination_sort = function
  | RProp Null -> InProp
  | RProp Pos  -> InSet
  | RType _ -> InType

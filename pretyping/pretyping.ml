
(* $Id$ *)

open Pp
open Util
open Names
open Sign
open Evd
open Term
open Reduction
open Environ
open Type_errors
open Typeops
open Classops
open List
open Recordops 
open Evarutil
open Pretype_errors
open Rawterm
open Evarconv
open Coercion


(***********************************************************************)
(* This concerns Cases *)
open Inductive
open Instantiate

let lift_context n l = 
  let k = List.length l in 
  list_map_i (fun i (name,c) -> (name,liftn n (k-i) c)) 0 l

let transform_rec loc env sigma (p,c,lf) (indt,pt) = 
  let (indf,realargs) = dest_ind_type indt in
  let (mispec,params) = dest_ind_family indf in
  let mI = mkMutInd (mis_inductive mispec) in
  let recargs = mis_recarg mispec in
  let tyi = mis_index mispec in
  if Array.length lf <> mis_nconstr mispec then 
    error_number_branches_loc loc CCI env c
      (mkAppliedInd indt) (mis_nconstr mispec);
  if mis_is_recursive_subset [tyi] mispec then
    let dep = find_case_dep_nparams env sigma (c,p) indf pt in 
    let init_depFvec i = if i = tyi then Some(dep,mkRel 1) else None in
    let depFvec = Array.init (mis_ntypes mispec) init_depFvec in
    let constrs = get_constructors indf in
    (* build now the fixpoint *)
    let lnames,_ = get_arity indf in
    let nar = List.length lnames in
    let nparams = mis_nparams mispec in
    let ci = make_default_case_info mispec in
    let branches = 
      array_map3
	(fun f t reca -> 
	   whd_beta
             (Indrec.make_rec_branch_arg env sigma
                (nparams,depFvec,nar+1)
                f t reca))
        (Array.map (lift (nar+2)) lf) constrs recargs 
    in 
    let deffix = 
      it_mkLambda_or_LetIn_name env
	(lambda_create env
	   (applist (mI,List.append (List.map (lift (nar+1)) params)
                       (rel_list 0 nar)),
            mkMutCase (ci, lift (nar+2) p, mkRel 1, branches)))
        (lift_rel_context 1 lnames) 
    in
    if noccurn 1 deffix then 
      whd_beta (applist (pop deffix,realargs@[c]))
    else
      let typPfix = 
	it_mkProd_or_LetIn_name env
	  (prod_create env
	     (applist (mI,(List.append 
			     (List.map (lift nar) params)
			     (rel_list 0 nar))),
	      (if dep then 
		 whd_beta (applist (lift (nar+1) p, rel_list 0 (nar+1)))
	       else 
		 whd_beta (applist (lift (nar+1) p, rel_list 1 nar)))))
          lnames 
      in
      let fix = mkFix (([|nar|],0),
		       ([|typPfix|],[Name(id_of_string "F")],[|deffix|])) in
      applist (fix,realargs@[c])
  else
    let ci = make_default_case_info mispec in
    mkMutCase (ci, p, c, lf)

(***********************************************************************)

let ctxt_of_ids cl = cl

let mt_evd = Evd.empty

let vect_lift_type = Array.mapi (fun i t -> type_app (lift i) t)

let j_nf_ise sigma {uj_val=v;uj_type=t} =
  {uj_val=nf_ise1 sigma v;uj_type=type_app (nf_ise1 sigma) t}

let jv_nf_ise sigma = Array.map (j_nf_ise sigma)

(* Utilisé pour inférer le prédicat des Cases *)
(* Semble exagérement fort *)
(* Faudra préférer une unification entre les types de toutes les clauses *)
(* et autoriser des ? à rester dans le résultat de l'unification *)

let evar_type_fixpoint env isevars lna lar vdefj =
  let lt = Array.length vdefj in 
    if Array.length lar = lt then 
      for i = 0 to lt-1 do 
        if not (the_conv_x_leq env isevars
		  (vdefj.(i)).uj_type
		  (lift lt lar.(i))) then
          error_ill_typed_rec_body CCI env i lna 
	    (jv_nf_ise !isevars vdefj) 
	    (Array.map (type_app (nf_ise1 !isevars)) lar)
      done

let let_path = make_path ["Core"] (id_of_string "let") CCI

let wrong_number_of_cases_message loc env isevars (c,ct) expn = 
  let c = nf_ise1 !isevars c and ct = nf_ise1 !isevars ct in
  error_number_branches_loc loc CCI env c ct expn

let check_branches_message loc env isevars c (explft,lft) = 
  for i = 0 to Array.length explft - 1 do
    if not (the_conv_x_leq env isevars lft.(i) explft.(i)) then 
      let c = nf_ise1 !isevars c
      and lfi = nf_betaiota env !isevars (nf_ise1 !isevars lft.(i)) in
      error_ill_formed_branch_loc loc CCI env c i lfi 
	(nf_betaiota env !isevars explft.(i))
  done

(* coerce to tycon if any *)
let inh_conv_coerce_to_tycon loc env isevars j = function
   | None -> j
   | Some typ -> inh_conv_coerce_to loc env isevars j typ

(*
let evar_type_case isevars env ct pt lft p c =
  let (mind,bty,rslty) = type_case_branches env !isevars ct pt p c
  in check_branches_message isevars env (c,ct) (bty,lft); (mind,rslty)
*)

let pretype_id loc env lvar id = 
  try
    List.assoc id lvar
  with Not_found ->
  try
    let (n,typ) = lookup_rel_id id (rel_context env) in
    { uj_val  = mkRel n; uj_type = type_app (lift n) typ }
  with Not_found ->
  try
    let typ = lookup_id_type id (named_context env) in
    { uj_val  = mkVar id; uj_type = typ }
  with Not_found ->
    error_var_not_found_loc loc CCI id

(*************************************************************************)
(* Main pretyping function                                               *)

let pretype_ref isevars env lvar ref = 
  let c = Declare.constr_of_reference !isevars env ref in
  make_judge c (Retyping.get_type_of env Evd.empty c)

(*
let pretype_ref _ isevars env lvar ref =
...

| RConst (sp,ctxt) ->
    let cst = (sp,Array.map pretype ctxt) in
    make_judge (mkConst cst) (type_of_constant env !isevars cst)
*)
(* A traiter mais les tables globales nécessaires à cela pour l'instant
| REVar (sp,ctxt) ->
    let ev = (sp,Array.map pretype ctxt) in
    let body = 
      if Evd.is_defined !isevars sp then
	existential_value !isevars ev
      else
	mkEvar ev
    in
    let typ = existential_type !isevars ev in
    make_judge body typ

| RInd (ind_sp,ctxt) ->
    let ind = (ind_sp,Array.map pretype ctxt) in
    make_judge (mkMutInd ind) (type_of_inductive env !isevars ind)
 
| RConstruct (cstr_sp,ctxt) ->
    let cstr = (cstr_sp,Array.map pretype ctxt) in
    let typ = type_of_constructor env !isevars cstr in
    { uj_val=mkMutConstruct cstr; uj_type=typ }
*)
let pretype_sort = function
  | RProp c -> judge_of_prop_contents c
  | RType ->
      { uj_val = dummy_sort;
	uj_type = dummy_sort }

(* pretype tycon isevars env constr tries to solve the *)
(* existential variables in constr in environment env with the *)
(* constraint tycon (see Tradevar). *)
(* Invariant : Prod and Lambda types are casted !! *)
let rec pretype tycon env isevars lvar lmeta cstr =
  match cstr with   (* Où teste-t-on que le résultat doit satisfaire tycon ? *)

    | RRef (loc,ref) ->
	inh_conv_coerce_to_tycon loc env isevars
	  (pretype_ref isevars env lvar ref)
	  tycon

    | RVar (loc, id) ->
	inh_conv_coerce_to_tycon loc env isevars
	  (pretype_id loc env lvar id)
	  tycon

    | RMeta (loc,n) ->
	let j =
	  try
	    List.assoc n lmeta
	  with
              Not_found ->
		user_err_loc (loc,"pretype",
			      [< 'sTR "Metavariable "; 'iNT n; 'sTR" is unbound" >])
	in inh_conv_coerce_to_tycon loc env isevars j tycon

    | RHole loc ->
	if !compter then nbimpl:=!nbimpl+1;
	(match tycon with
	   | Some ty -> { uj_val = new_isevar isevars env ty CCI; uj_type = ty }
	   | None ->
	       (match loc with
		    None -> anomaly "There is an implicit argument I cannot solve"
		  | Some loc -> 
		      user_err_loc
			(loc,"pretype",
			 [< 'sTR "Cannot infer a term for this placeholder" >])))

    | RRec (loc,fixkind,lfi,lar,vdef) ->
	let larj = Array.map (pretype_type empty_valcon env isevars lvar lmeta) lar in
	let lara = Array.map (fun a -> a.utj_val) larj in
	let nbfix = Array.length lfi in
	let lfi = List.map (fun id -> Name id) (Array.to_list lfi) in
	let newenv =
	  array_fold_left2 (fun env id ar -> (push_rel_assum (id,ar) env))
	    env (Array.of_list (List.rev lfi)) (vect_lift_type lara) in
	let vdefj =
	  Array.mapi 
	    (fun i def -> (* we lift nbfix times the type in tycon, because of
			   * the nbfix variables pushed to newenv *)
               pretype (mk_tycon (lift nbfix (larj.(i).utj_val))) newenv isevars lvar
		 lmeta def) vdef in
	evar_type_fixpoint env isevars lfi lara vdefj;
	let fixj =
	  match fixkind with
	    | RFix (vn,i as vni) ->
		let fix = (vni,(lara,List.rev lfi,Array.map j_val vdefj)) in
		check_fix env !isevars fix;
		make_judge (mkFix fix) lara.(i)
	    | RCoFix i -> 
		let cofix = (i,(lara,List.rev lfi,Array.map j_val vdefj)) in
		check_cofix env !isevars cofix;
		make_judge (mkCoFix cofix) lara.(i) in
	inh_conv_coerce_to_tycon loc env isevars fixj tycon

    | RSort (loc,s) ->
	inh_conv_coerce_to_tycon loc env isevars (pretype_sort s) tycon

    | RApp (loc,f,args) -> 
	let fj = pretype empty_tycon env isevars lvar lmeta f in
	let floc = loc_of_rawconstr f in
	let rec apply_rec env n resj = function
	  | [] -> resj
	  | c::rest ->
	      let argloc = loc_of_rawconstr c in
	      let resj = inh_app_fun env isevars resj in
      	      match kind_of_term (whd_betadeltaiota env !isevars resj.uj_type) with
		| IsProd (na,c1,c2) ->
		    let hj = pretype (mk_tycon c1) env isevars lvar lmeta c in
		    let newresj =
      		      { uj_val = applist (j_val resj, [j_val hj]);
			uj_type = subst1 hj.uj_val c2 } in
		    apply_rec env (n+1) newresj rest

		| _ ->
		    let j_nf_ise env sigma {uj_val=v;uj_type=t} =
		      { uj_val = nf_ise1 sigma v; 
			uj_type = nf_ise1 sigma t } in
		    let hj = pretype empty_tycon env isevars lvar lmeta c in
		    error_cant_apply_not_functional_loc 
		      (Rawterm.join_loc floc argloc) env
	      	      (j_nf_ise env !isevars resj)
		      [j_nf_ise env !isevars hj]

	in let resj = apply_rec env 1 fj args in
	(*
	  let apply_one_arg (floc,tycon,jl) c =
	  let (dom,rng) = split_tycon floc env isevars tycon in
	  let cj = pretype dom env isevars lvar lmeta c in
	  let rng_tycon = option_app (subst1 cj.uj_val) rng in
	  let argloc = loc_of_rawconstr c in
	  (join_loc floc argloc,rng_tycon,(argloc,cj)::jl)  in
	  let _,_,jl =
	  List.fold_left apply_one_arg (floc,mk_tycon j.uj_type,[]) args in
	  let jl = List.rev jl in
	  let resj = inh_apply_rel_list loc env isevars jl (floc,j) tycon in
	*)
	inh_conv_coerce_to_tycon loc env isevars resj tycon

    | RBinder(loc,BLambda,name,c1,c2)      ->
	let (dom,rng) = split_tycon loc env isevars tycon in
	let dom_valcon = valcon_of_tycon dom in
	let j = pretype_type dom_valcon env isevars lvar lmeta c1 in
	let var = (name,j.utj_val) in
	let j' = pretype rng (push_rel_assum var env) isevars lvar lmeta c2 
	in 
	fst (abs_rel env !isevars name j.utj_val j')

    | RBinder(loc,BProd,name,c1,c2)        ->
	let j = pretype_type empty_tycon env isevars lvar lmeta c1 in
	let var = (name,j.utj_val) in
	(* Ici, faudrait appeler pretype_type mais gen_rel n'a pas la bonne 
           interface, tout ca pour preserver le message d'erreur de gen_rel *)

	let j' = pretype empty_tycon (push_rel_assum var env) isevars lvar lmeta c2 in
	let resj =
	  try fst (gen_rel env !isevars name j j')
	  with TypeError _ as e -> Stdpp.raise_with_loc loc e in
	inh_conv_coerce_to_tycon loc env isevars resj tycon

    | RBinder(loc,BLetIn,name,c1,c2)      ->
	let j = pretype empty_tycon env isevars lvar lmeta c1 in
	let var = (name,j.uj_val,j.uj_type) in
	let j' = pretype tycon (push_rel_def var env) isevars lvar lmeta c2 in
	{ uj_val = mkLetIn (name, j.uj_val, j.uj_type, j'.uj_val) ;
	  uj_type = type_app (subst1 j.uj_val) j'.uj_type }

    | ROldCase (loc,isrec,po,c,lf) ->
	let cj = pretype empty_tycon env isevars lvar lmeta c in
	let (IndType (indf,realargs) as indt) = 
	  try find_rectype env !isevars cj.uj_type
	  with Induc -> error_case_not_inductive CCI env
	      (nf_ise1 !isevars cj.uj_val) (nf_ise1 !isevars cj.uj_type) in
	let pj = match po with
	  | Some p -> pretype empty_tycon env isevars lvar lmeta p
	  | None -> 
	      try match tycon with
		  Some pred -> 
		    let predj = Retyping.get_judgment_of env !isevars pred in
		    let tj = inh_coerce_to_sort env isevars predj in (* Utile ?? *)
		    let { utj_val = v; utj_type = s } = tj in
		    { uj_val = v; uj_type = mkSort s }
		| None -> error "notype"
	      with UserError _ -> (* get type information from type of branches *)
		let expbr = Cases.branch_scheme env isevars isrec indf in
		let rec findtype i =
		  if i >= Array.length lf
		  then error_cant_find_case_type_loc loc env cj.uj_val
		  else
		    try
		      let expti = expbr.(i) in
		      let fj =
			pretype (mk_tycon expti) env isevars lvar lmeta lf.(i) in
		      let efjt = nf_ise1 !isevars fj.uj_type in 
		      let pred = 
			Cases.pred_case_ml_onebranch env !isevars isrec indt
			  (i,fj.uj_val,efjt) in
		      if has_undefined_isevars isevars pred then findtype (i+1)
		      else 
			let pty = Retyping.get_type_of env !isevars pred in
			{ uj_val = pred; 
			  uj_type = pty }
		    with UserError _ -> findtype (i+1) in
		findtype 0 in

	let evalct = find_rectype env !isevars cj.uj_type (*Pour normaliser evars*)
	and evalPt = nf_ise1 !isevars pj.uj_type in

	let (bty,rsty) =
	  Indrec.type_rec_branches isrec env !isevars evalct evalPt pj.uj_val cj.uj_val in
	if Array.length bty <> Array.length lf then
	  wrong_number_of_cases_message loc env isevars 
	    (cj.uj_val,nf_ise1 !isevars cj.uj_type)
	    (Array.length bty)
	else
	  let lfj =
	    array_map2
              (fun tyc f -> pretype (mk_tycon tyc) env isevars lvar lmeta f) bty
              lf in
	  let lfv = Array.map j_val lfj in
	  let lft = Array.map (fun j -> j.uj_type) lfj in
	  check_branches_message loc env isevars cj.uj_val (bty,lft);
	  let v =
	    if isrec
	    then 
	      transform_rec loc env !isevars(pj.uj_val,cj.uj_val,lfv) (evalct,evalPt)
	    else
	      let mis,_ = dest_ind_family indf in
	      let ci = make_default_case_info mis in
	      mkMutCase (ci, pj.uj_val, cj.uj_val, Array.map (fun j-> j.uj_val) lfj)
	  in
	  {uj_val = v;
	   uj_type = rsty }

    | RCases (loc,prinfo,po,tml,eqns) ->
	Cases.compile_cases loc
	  ((fun vtyc env -> pretype vtyc env isevars lvar lmeta),isevars)
	  tycon env (* loc *) (po,tml,eqns)

    | RCast(loc,c,t) ->
	let tj = pretype_type (valcon_of_tycon tycon) env isevars lvar lmeta t in
	let cj = pretype (mk_tycon tj.utj_val) env isevars lvar lmeta c in
	inh_conv_coerce_to_tycon loc env isevars cj tycon

	     (* [pretype_type valcon env isevars lvar lmeta c] coerces [c] into a type *)
	     and pretype_type valcon env isevars lvar lmeta = function
	       | RHole loc ->
		   if !compter then nbimpl:=!nbimpl+1;
		   (match valcon with
		      | Some v ->
			  { utj_val = v;
			    utj_type = Retyping.get_sort_of env !isevars v }
		      | None ->
			  { utj_val = new_isevar isevars env dummy_sort CCI;
			    utj_type = Type Univ.dummy_univ })
	       | c ->
		   let j = pretype empty_tycon env isevars lvar lmeta c in
		   let tj = inh_coerce_to_sort env isevars j in
		   match valcon with
		     | None -> tj
		     | Some v ->
			 if the_conv_x_leq env isevars v tj.utj_val
			 then
			   { utj_val = nf_ise1 !isevars tj.utj_val;
			     utj_type = tj.utj_type }
			 else
			   error_unexpected_type_loc (loc_of_rawconstr c) env tj.utj_val v


let unsafe_infer tycon isevars env lvar lmeta constr =
  reset_problems ();
  pretype tycon env isevars lvar lmeta constr

let unsafe_infer_type valcon isevars env lvar lmeta constr =
  reset_problems ();
  pretype_type valcon env isevars lvar lmeta constr

(* If fail_evar is false, [process_evars] turns unresolved Evar that
   were not in initial sigma into Meta's; otherwise it fail on the first
   unresolved Evar not already in the initial sigma
   Rem: Does a side-effect on reference metamap *)
(* [fail_evar] says how to process unresolved evars:
 *   true -> raise an error message
 *   false -> convert them into new Metas (casted with their type)
 *)
let process_evars fail_evar initial_sigma sigma metamap c =
  let rec proc_rec c =
    match kind_of_term c with
      | IsEvar (ev,args as k) when Evd.in_dom sigma ev ->
	  if Evd.is_defined sigma ev then
      	    proc_rec (existential_value sigma k)
	  else
	    if Evd.in_dom initial_sigma ev then
	      c
	    else
	      if fail_evar then
		errorlabstrm "whd_ise"
		  [< 'sTR"There is an unknown subterm I cannot solve" >]
	      else
		let n = new_meta () in
		metamap := (n, existential_type sigma k) :: !metamap;
		mkMeta n
      | _ -> map_constr proc_rec c      
  in
  proc_rec c
 
(* TODO: comment faire remonter l'information si le typage a resolu des
       variables du sigma original. il faudrait que la fonction de typage
       retourne aussi le nouveau sigma...
*)

type meta_map = (int * unsafe_judgment) list
type var_map = (identifier * unsafe_judgment) list

let ise_resolve_casted_gen fail_evar sigma env lvar lmeta typ c =
  let isevars = ref sigma in
  let j = unsafe_infer (mk_tycon typ) isevars env lvar lmeta c in
  let metamap = ref [] in
  let v = process_evars fail_evar sigma !isevars metamap j.uj_val in
  let t = type_app (process_evars fail_evar sigma !isevars metamap) j.uj_type in
  !metamap, {uj_val = v; uj_type = t }

let ise_resolve_casted sigma env typ c =
  ise_resolve_casted_gen true sigma env [] [] typ c

(* Raw calls to the unsafe inference machine: boolean says if we must fail
   on unresolved evars, or replace them by Metas; the unsafe_judgment list
   allows us to extend env with some bindings *)
let ise_infer_gen fail_evar sigma env lvar lmeta exptyp c =
  let tycon = match exptyp with None -> empty_tycon | Some t -> mk_tycon t in
  let isevars = ref sigma in
  let j = unsafe_infer tycon isevars env lvar lmeta c in
  let metamap = ref [] in
  let v = process_evars fail_evar sigma !isevars metamap j.uj_val in
  let t = type_app (process_evars fail_evar sigma !isevars metamap) j.uj_type in
  !metamap, {uj_val = v; uj_type = t }

let ise_infer_type_gen fail_evar sigma env lvar lmeta c =
  let isevars = ref sigma in
  let tj = unsafe_infer_type empty_valcon isevars env lvar lmeta c in
  let metamap = ref [] in
  let v = process_evars fail_evar sigma !isevars metamap tj.utj_val in
  !metamap, {utj_val = v; utj_type = tj.utj_type }

let understand_judgment sigma env c =
  snd (ise_infer_gen true sigma env [] [] None c)

let understand_type_judgment sigma env c =
  snd (ise_infer_type_gen true sigma env [] [] c)

let understand sigma env c =
  let _, c = ise_infer_gen true sigma env [] [] None c in
  c.uj_val

let understand_type sigma env c =
  let _,c = ise_infer_type_gen true sigma env [] [] c in
  c.utj_val

let understand_gen sigma env lvar lmeta exptyp c =
  let _, c = ise_infer_gen true sigma env lvar lmeta exptyp c in
  c.uj_val

let understand_gen_tcc sigma env lvar lmeta exptyp c =
  let metamap, c = ise_infer_gen false sigma env lvar lmeta exptyp c in
  metamap, c.uj_val

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
open Classops
open List
open Recordops 
open Evarutil
open Pretype_errors
open Rawterm
open Evarconv
open Coercion
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
  let ci = make_default_case_info env ind in
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

let error_unsolvable_implicit (loc,kind) =
  let message = match kind with
    | QuestionMark -> str "Cannot infer a term for this placeholder"
    | CasesType ->
	str "Cannot infer the type of this pattern-matching problem"
    | AbstractionType (Name id) ->
	str "Cannot infer a type for " ++ Nameops.pr_id id
    | AbstractionType Anonymous ->
	str "Cannot infer a type of this anonymous abstraction"
    | ImplicitArg (c,n) ->
	str "Cannot infer the " ++ pr_ord n ++
	str " implicit argument of " ++ Nametab.pr_global_env (Global.env()) c
    | InternalHole ->
        str "Cannot infer a term for an internal placeholder"
  in
    user_err_loc (loc,"pretype",message)

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

(*
let evar_type_case isevars env ct pt lft p c =
  let (mind,bty,rslty) = type_case_branches env (evars_of isevars) ct pt p c
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
    let (_,_,typ) = lookup_named id env in
    { uj_val  = mkVar id; uj_type = typ }
  with Not_found ->
    error_var_not_found_loc loc id

(*************************************************************************)
(* Main pretyping function                                               *)

let pretype_ref isevars env lvar ref = 
  let c = Declare.constr_of_reference ref in
  make_judge c (Retyping.get_type_of env Evd.empty c)

let pretype_sort = function
  | RProp c -> judge_of_prop_contents c
  | RType _ -> judge_of_new_Type ()

(* [pretype tycon env isevars lvar lmeta cstr] attempts to type [cstr] *)
(* in environment [env], with existential variables [(evars_of isevars)] and *)
(* the type constraint tycon *)
let rec pretype tycon env isevars lvar lmeta = function

  | RRef (loc,ref) ->
      inh_conv_coerce_to_tycon loc env isevars
	(pretype_ref isevars env lvar ref)
	tycon

  | RVar (loc, id) ->
      inh_conv_coerce_to_tycon loc env isevars
	(pretype_id loc env lvar id)
	tycon

  | REvar (loc, ev) ->
      (* Ne faudrait-il pas s'assurer que hyps est bien un
      sous-contexte du contexte courant, et qu'il n'y a pas de Rel "caché" *)
      let hyps = (Evd.map (evars_of isevars) ev).evar_hyps in
      let args = instance_from_named_context hyps in
      let c = mkEvar (ev, args) in
      let j = (Retyping.get_judgment_of env (evars_of isevars) c) in
      inh_conv_coerce_to_tycon loc env isevars j tycon

  | RMeta (loc,n) ->
      let j =
	try
	  List.assoc n lmeta
	with
            Not_found ->
	      user_err_loc
		(loc,"pretype",
		 str "Metavariable " ++ int n ++ str " is unbound")
      in inh_conv_coerce_to_tycon loc env isevars j tycon
	   
  | RHole loc ->
      if !compter then nbimpl:=!nbimpl+1;
      (match tycon with
	 | Some ty ->
	     { uj_val = new_isevar isevars env loc ty; uj_type = ty }
	 | None -> error_unsolvable_implicit loc)

  | RRec (loc,fixkind,names,lar,vdef) ->
      let larj =
        Array.map (pretype_type empty_valcon env isevars lvar lmeta) lar in
      let lara = Array.map (fun a -> a.utj_val) larj in
      let nbfix = Array.length lar in
      let names = Array.map (fun id -> Name id) names in
      let newenv = push_rec_types (names,lara,[||]) env in
      let vdefj =
	Array.mapi 
	  (fun i def -> (* we lift nbfix times the type in tycon, because of
			 * the nbfix variables pushed to newenv *)
             pretype (mk_tycon (lift nbfix (larj.(i).utj_val)))
               newenv isevars lvar lmeta def)
          vdef in
      evar_type_fixpoint loc env isevars names lara vdefj;
      let fixj =
	match fixkind with
	  | RFix (vn,i as vni) ->
	      let fix = (vni,(names,lara,Array.map j_val vdefj)) in
	      check_fix env fix;
	      make_judge (mkFix fix) lara.(i)
	  | RCoFix i -> 
	      let cofix = (i,(names,lara,Array.map j_val vdefj)) in
	      check_cofix env cofix;
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
            let resty =
              whd_betadeltaiota env (evars_of isevars) resj.uj_type in
      	    match kind_of_term resty with
	      | Prod (na,c1,c2) ->
		  let hj = pretype (mk_tycon c1) env isevars lvar lmeta c in
		  let newresj =
      		    { uj_val = applist (j_val resj, [j_val hj]);
		      uj_type = subst1 hj.uj_val c2 } in
		  apply_rec env (n+1) newresj rest

	      | _ ->
		  let hj = pretype empty_tycon env isevars lvar lmeta c in
		  error_cant_apply_not_functional_loc 
		    (Rawterm.join_loc floc argloc) env (evars_of isevars)
	      	    resj [hj]

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

  | RLambda(loc,name,c1,c2)      ->
      let (dom,rng) = split_tycon loc env isevars tycon in
      let dom_valcon = valcon_of_tycon dom in
      let j = pretype_type dom_valcon env isevars lvar lmeta c1 in
      let var = (name,None,j.utj_val) in
      let j' = pretype rng (push_rel var env) isevars lvar lmeta c2 in 
      judge_of_abstraction env name j j'

  | RProd(loc,name,c1,c2)        ->
      let j = pretype_type empty_valcon env isevars lvar lmeta c1 in
      let var = (name,j.utj_val) in
      let env' = push_rel_assum var env in
      let j' = pretype_type empty_valcon env' isevars lvar lmeta c2 in
      let resj =
	try judge_of_product env name j j'
	with TypeError _ as e -> Stdpp.raise_with_loc loc e in
      inh_conv_coerce_to_tycon loc env isevars resj tycon
	
  | RLetIn(loc,name,c1,c2)      ->
      let j = pretype empty_tycon env isevars lvar lmeta c1 in
      let t = Evarutil.refresh_universes j.uj_type in
      let var = (name,Some j.uj_val,t) in
        let tycon = option_app (lift 1) tycon in
      let j' = pretype tycon (push_rel var env) isevars lvar lmeta c2 in
      { uj_val = mkLetIn (name, j.uj_val, t, j'.uj_val) ;
	uj_type = type_app (subst1 j.uj_val) j'.uj_type }
      
  | ROldCase (loc,isrec,po,c,lf) ->
      let cj = pretype empty_tycon env isevars lvar lmeta c in
      let (IndType (indf,realargs) as indt) = 
	try find_rectype env (evars_of isevars) cj.uj_type
	with Not_found ->
	  let cloc = loc_of_rawconstr c in
	  error_case_not_inductive_loc cloc env (evars_of isevars) cj in
      let (dep,pj) = match po with
	| Some p ->
            let pj = pretype empty_tycon env isevars lvar lmeta p in
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
                      (false,
                       Retyping.get_judgment_of env (evars_of isevars) pred)
	          | None ->
                      let sigma = evars_of isevars in
                      error_cant_find_case_type_loc loc env sigma cj.uj_val
	      else
		try
		  let expti = expbr.(i) in
		  let fj =
		    pretype (mk_tycon expti) env isevars lvar lmeta lf.(i) in
		  let pred = 
		    Cases.pred_case_ml
                      env (evars_of isevars) isrec indt (i,fj.uj_type) in
		  if has_undefined_isevars isevars pred then findtype (i+1)
		  else 
		    let pty =
                      Retyping.get_type_of env (evars_of isevars) pred in
		    let pj = { uj_val = pred; uj_type = pty } in
                    let _ = option_app (the_conv_x_leq env isevars pred) tycon
                    in (false,pj)
		with Cases.NotInferable _ -> findtype (i+1) in
	    findtype 0 in
      let pj = j_nf_evar (evars_of isevars) pj in

      let pj =
	if dep then pj else
	  let n = List.length realargs in
	  let rec decomp n p =
	    if n=0 then p else
	      match kind_of_term p with
		| Lambda (_,_,c) -> decomp (n-1) c
		| _ -> decomp (n-1) (applist (lift 1 p, [mkRel 1])) in
	  let sign,s = decompose_prod_n n pj.uj_type in
	  let ind = build_dependent_inductive env indf in
	  let s' = mkProd (Anonymous, ind, s) in
	  let ccl = lift 1 (decomp n pj.uj_val) in
	  let ccl' = mkLambda (Anonymous, ind, ccl) in
	  {uj_val=lam_it ccl' sign; uj_type=prod_it s' sign} in
      let (bty,rsty) =
	Indrec.type_rec_branches
          isrec env (evars_of isevars) indt pj cj.uj_val in
      if Array.length bty <> Array.length lf then
	error_number_branches_loc loc env (evars_of isevars) 
	  cj (Array.length bty)
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
	    transform_rec loc env (evars_of isevars)(pj,cj.uj_val,lfv) indt
	  else
	    let mis,_ = dest_ind_family indf in
	    let ci = make_default_case_info env mis in
	    mkCase (ci, (nf_betaiota pj.uj_val), cj.uj_val,
                       Array.map (fun j-> j.uj_val) lfj)
	in
	{ uj_val = v;
	  uj_type = rsty }

  | RCases (loc,prinfo,po,tml,eqns) ->
      Cases.compile_cases loc
	((fun vtyc env -> pretype vtyc env isevars lvar lmeta),isevars)
	tycon env (* loc *) (po,tml,eqns)

  | RCast(loc,c,t) ->
      let tj = pretype_type empty_tycon env isevars lvar lmeta t in
      let cj = pretype (mk_tycon tj.utj_val) env isevars lvar lmeta c in
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

(* [pretype_type valcon env isevars lvar lmeta c] coerces [c] into a type *)
and pretype_type valcon env isevars lvar lmeta = function
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
      let j = pretype empty_tycon env isevars lvar lmeta c in
      let tj = inh_coerce_to_sort env isevars j in
      match valcon with
	| None -> tj
	| Some v ->
	    if the_conv_x_leq env isevars v tj.utj_val then tj
	    else
	      error_unexpected_type_loc
                (loc_of_rawconstr c) env (evars_of isevars) tj.utj_val v


let unsafe_infer tycon isevars env lvar lmeta constr =
  let j = pretype tycon env isevars lvar lmeta constr in
  j_nf_evar (evars_of isevars) j

let unsafe_infer_type valcon isevars env lvar lmeta constr =
  let tj = pretype_type valcon env isevars lvar lmeta constr in
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
let check_evars fail_evar initial_sigma isevars c =
  let sigma = evars_of isevars in
  let rec proc_rec c =
    match kind_of_term c with
      | Evar (ev,args as k) ->
          assert (Evd.in_dom sigma ev);
	  if not (Evd.in_dom initial_sigma ev) then
	    (if fail_evar then
	       error_unsolvable_implicit (evar_source ev isevars))
      | _ -> iter_constr proc_rec c      
  in
  proc_rec c

(* TODO: comment faire remonter l'information si le typage a resolu des
       variables du sigma original. il faudrait que la fonction de typage
       retourne aussi le nouveau sigma...
*)

(* constr with holes *)
type open_constr = evar_map * constr

let ise_resolve_casted_gen fail_evar sigma env lvar lmeta typ c =
  let isevars = create_evar_defs sigma in
  let j = unsafe_infer (mk_tycon typ) isevars env lvar lmeta c in
  check_evars fail_evar sigma isevars (mkCast(j.uj_val,j.uj_type));
  (evars_of isevars, j)

let ise_resolve_casted sigma env typ c =
  ise_resolve_casted_gen true sigma env [] [] typ c

(* Raw calls to the unsafe inference machine: boolean says if we must fail
   on unresolved evars, or replace them by Metas; the unsafe_judgment list
   allows us to extend env with some bindings *)
let ise_infer_gen fail_evar sigma env lvar lmeta exptyp c =
  let tycon = match exptyp with None -> empty_tycon | Some t -> mk_tycon t in
  let isevars = create_evar_defs sigma in
  let j = unsafe_infer tycon isevars env lvar lmeta c in
  check_evars fail_evar sigma isevars (mkCast(j.uj_val,j.uj_type));
  (evars_of isevars, j)

let ise_infer_type_gen fail_evar sigma env lvar lmeta c =
  let isevars = create_evar_defs sigma in
  let tj = unsafe_infer_type empty_valcon isevars env lvar lmeta c in
  check_evars fail_evar sigma isevars tj.utj_val;
  (evars_of isevars, tj)

type meta_map = (int * unsafe_judgment) list
type var_map = (identifier * unsafe_judgment) list

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

let understand_gen sigma env lvar lmeta ~expected_type:exptyp c =
  let _, c = ise_infer_gen true sigma env lvar lmeta exptyp c in
  c.uj_val

let understand_gen_tcc sigma env lvar lmeta exptyp c =
  let metamap, c = ise_infer_gen false sigma env lvar lmeta exptyp c in
  metamap, c.uj_val

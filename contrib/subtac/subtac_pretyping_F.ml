(* -*- compile-command: "make -C ../.. bin/coqtop.byte" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Nameops
open Classops
open List
open Recordops 
open Evarutil
open Pretype_errors
open Rawterm
open Evarconv
open Pattern
open Dyn
open Pretyping

(************************************************************************)
(* This concerns Cases *)
open Declarations
open Inductive
open Inductiveops

module SubtacPretyping_F (Coercion : Coercion.S) = struct

  module Cases = Subtac_cases.Cases_F(Coercion)

  (* Allow references to syntaxically inexistent variables (i.e., if applied on an inductive) *)
  let allow_anonymous_refs = ref true

  let evd_comb0 f isevars =
    let (evd',x) = f !isevars in
      isevars := evd';
      x

  let evd_comb1 f isevars x =
    let (evd',y) = f !isevars x in
      isevars := evd';
      y

  let evd_comb2 f isevars x y =
    let (evd',z) = f !isevars x y in
      isevars := evd';
      z

  let evd_comb3 f isevars x y z =
    let (evd',t) = f !isevars x y z in
      isevars := evd';
      t
	
  let mt_evd = Evd.empty
    
  (* Utilisé pour inférer le prédicat des Cases *)
  (* Semble exagérement fort *)
  (* Faudra préférer une unification entre les types de toutes les clauses *)
  (* et autoriser des ? à rester dans le résultat de l'unification *)
  
  let evar_type_fixpoint loc env isevars lna lar vdefj =
    let lt = Array.length vdefj in 
      if Array.length lar = lt then 
	for i = 0 to lt-1 do 
          if not (e_cumul env isevars (vdefj.(i)).uj_type
		    (lift lt lar.(i))) then
            error_ill_typed_rec_body_loc loc env (evars_of !isevars)
              i lna vdefj lar
	done

  let check_branches_message loc env isevars c (explft,lft) = 
    for i = 0 to Array.length explft - 1 do
      if not (e_cumul env isevars lft.(i) explft.(i)) then 
	let sigma = evars_of !isevars in
	  error_ill_formed_branch_loc loc env sigma c i lft.(i) explft.(i)
    done

  (* coerce to tycon if any *)
  let inh_conv_coerce_to_tycon loc env isevars j = function
    | None -> j_nf_isevar !isevars j
    | Some t -> evd_comb2 (Coercion.inh_conv_coerce_to loc env) isevars j t

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
	let (n,typ) = lookup_rel_id id (rel_context env) in
	  { uj_val  = mkRel n; uj_type = lift n typ }
      with Not_found ->
	try
	  List.assoc id lvar
	with Not_found ->
	  try
	    let (_,_,typ) = lookup_named id env in
	      { uj_val  = mkVar id; uj_type = typ }
	  with Not_found ->
	    try (* To build a nicer ltac error message *)
	      match List.assoc id unbndltacvars with
		| None -> user_err_loc (loc,"",
					str "variable " ++ pr_id id ++ str " should be bound to a term")
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
    let c = constr_of_global ref in
      make_judge c (Retyping.get_type_of env Evd.empty c)

  let pretype_sort = function
    | RProp c -> judge_of_prop_contents c
    | RType _ -> judge_of_new_Type ()

  (* [pretype tycon env isevars lvar lmeta cstr] attempts to type [cstr] *)
  (* in environment [env], with existential variables [(evars_of isevars)] and *)
  (* the type constraint tycon *)
  let rec pretype (tycon : type_constraint) env isevars lvar c = 
(*     let _ = try Subtac_utils.trace (str "pretype " ++ Subtac_utils.my_print_rawconstr env c ++ *)
(* 			       str " with tycon " ++ Evarutil.pr_tycon env tycon)  *)
(*     with _ -> () *)
(*     in *)
    match c with
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
	let hyps = evar_context (Evd.find (evars_of !isevars) ev) in
	let args = match instopt with
          | None -> instance_from_named_context hyps
          | Some inst -> failwith "Evar subtitutions not implemented" in
	let c = mkEvar (ev, args) in
	let j = (Retyping.get_judgment_of env (evars_of !isevars) c) in
	  inh_conv_coerce_to_tycon loc env isevars j tycon

    | RPatVar (loc,(someta,n)) -> 
	anomaly "Found a pattern variable in a rawterm to type"
	  
    | RHole (loc,k) ->
	let ty =
          match tycon with 
            | Some (None, ty) -> ty
            | None | Some _ ->
		e_new_evar isevars env ~src:(loc,InternalHole) (new_Type ()) in
	  { uj_val = e_new_evar isevars env ~src:(loc,k) ty; uj_type = ty }

    | RRec (loc,fixkind,names,bl,lar,vdef) ->
	let rec type_bl env ctxt = function
            [] -> ctxt
          | (na,k,None,ty)::bl ->
              let ty' = pretype_type empty_valcon env isevars lvar ty in
              let dcl = (na,None,ty'.utj_val) in
		type_bl (push_rel dcl env) (add_rel_decl dcl ctxt) bl
          | (na,k,Some bd,ty)::bl ->
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
	let fixi = match fixkind with RFix (vn, i) -> i | RCoFix i -> i in
	let vdefj =
	  array_map2_i 
	    (fun i ctxt def ->
	      let fty = 
		let ty = ftys.(i) in
		  if i = fixi then (
		    Option.iter (fun tycon ->
		      isevars := Coercion.inh_conv_coerces_to loc env !isevars ftys.(i) tycon)
		      tycon;
		    nf_isevar !isevars ty)
		  else ty
	      in
              (* we lift nbfix times the type in tycon, because of
	       * the nbfix variables pushed to newenv *)
              let (ctxt,ty) =
		decompose_prod_n_assum (rel_context_length ctxt)
                  (lift nbfix fty) in
              let nenv = push_rel_context ctxt newenv in
              let j = pretype (mk_tycon ty) nenv isevars lvar def in
		{ uj_val = it_mkLambda_or_LetIn j.uj_val ctxt;
		  uj_type = it_mkProd_or_LetIn j.uj_type ctxt })
            ctxtv vdef in
	evar_type_fixpoint loc env isevars names ftys vdefj;
	let ftys = Array.map (nf_evar (evars_of !isevars)) ftys in
	let fdefs = Array.map (fun x -> nf_evar (evars_of !isevars) (j_val x)) vdefj in
	let fixj = match fixkind with
	  | RFix (vn,i) ->
	      (* First, let's find the guard indexes. *)
	      (* If recursive argument was not given by user, we try all args.
	         An earlier approach was to look only for inductive arguments,
		 but doing it properly involves delta-reduction, and it finally 
                 doesn't seem worth the effort (except for huge mutual 
		 fixpoints ?) *)
	      let possible_indexes = Array.to_list (Array.mapi 
		(fun i (n,_) -> match n with 
		   | Some n -> [n]
		   | None -> list_map_i (fun i _ -> i) 0 ctxtv.(i))
		vn)
	      in 
	      let fixdecls = (names,ftys,fdefs) in 
	      let indexes = search_guard loc env possible_indexes fixdecls in 
	      make_judge (mkFix ((indexes,i),fixdecls)) ftys.(i)
	  | RCoFix i -> 
	      let cofix = (i,(names,ftys,fdefs)) in
	      (try check_cofix env cofix with e -> Stdpp.raise_with_loc loc e);
	      make_judge (mkCoFix cofix) ftys.(i) in
	inh_conv_coerce_to_tycon loc env isevars fixj tycon

    | RSort (loc,s) ->
	inh_conv_coerce_to_tycon loc env isevars (pretype_sort s) tycon

    | RApp (loc,f,args) -> 
	let length = List.length args in 
	let ftycon = 
	  if length > 0 then
	    match tycon with
	    | None -> None
	    | Some (None, ty) -> mk_abstr_tycon length ty
	    | Some (Some (init, cur), ty) ->
		Some (Some (length + init, length + cur), ty)
	  else tycon
	in
	let fj = pretype ftycon env isevars lvar f in
 	let floc = loc_of_rawconstr f in
	let rec apply_rec env n resj tycon = function
	  | [] -> resj
	  | c::rest ->
	      let argloc = loc_of_rawconstr c in
	      let resj = evd_comb1 (Coercion.inh_app_fun env) isevars resj in
              let resty = whd_betadeltaiota env (evars_of !isevars) resj.uj_type in
      		match kind_of_term resty with
		  | Prod (na,c1,c2) ->
		      Option.iter (fun ty -> isevars :=
			Coercion.inh_conv_coerces_to loc env !isevars resty ty) tycon;
		      let evd, (_, _, tycon) = split_tycon loc env !isevars tycon in
		      isevars := evd;
		      let hj = pretype (mk_tycon (nf_isevar !isevars c1)) env isevars lvar c in
		      let value, typ = applist (j_val resj, [j_val hj]), subst1 hj.uj_val c2 in
		      let typ' = nf_isevar !isevars typ in
			apply_rec env (n+1) 
			  { uj_val = nf_isevar !isevars value;
			    uj_type = nf_isevar !isevars typ' }
			  (Option.map (fun (abs, c) -> abs, nf_isevar !isevars c) tycon) rest

		  | _ ->
		      let hj = pretype empty_tycon env isevars lvar c in
			error_cant_apply_not_functional_loc 
			  (join_loc floc argloc) env (evars_of !isevars)
	      		  resj [hj]
	in
	let resj = j_nf_evar (evars_of !isevars) (apply_rec env 1 fj ftycon args) in
	let resj =
	  match kind_of_term resj.uj_val with
	  | App (f,args) when isInd f or isConst f ->
	      let sigma = evars_of !isevars in
	      let c = mkApp (f,Array.map (whd_evar sigma) args) in
	      let t = Retyping.get_type_of env sigma c in
	      make_judge c t
	  | _ -> resj in
	  inh_conv_coerce_to_tycon loc env isevars resj tycon

    | RLambda(loc,name,k,c1,c2)      ->
	let tycon' = evd_comb1 
	  (fun evd tycon -> 
	    match tycon with 
	    | None -> evd, tycon 
	    | Some ty -> 
		let evd, ty' = Coercion.inh_coerce_to_prod loc env evd ty in
		  evd, Some ty') 
	  isevars tycon 
	in
	let (name',dom,rng) = evd_comb1 (split_tycon loc env) isevars tycon' in
	let dom_valcon = valcon_of_tycon dom in
	let j = pretype_type dom_valcon env isevars lvar c1 in
	let var = (name,None,j.utj_val) in
	let j' = pretype rng (push_rel var env) isevars lvar c2 in 
	let resj = judge_of_abstraction env name j j' in
	  inh_conv_coerce_to_tycon loc env isevars resj tycon

    | RProd(loc,name,k,c1,c2)        ->
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
	let t = refresh_universes j.uj_type in
	let var = (name,Some j.uj_val,t) in
        let tycon = lift_tycon 1 tycon in
	let j' = pretype tycon (push_rel var env) isevars lvar c2 in
	  { uj_val = mkLetIn (name, j.uj_val, t, j'.uj_val) ;
	    uj_type = subst1 j.uj_val j'.uj_type }

    | RLetTuple (loc,nal,(na,po),c,d) ->
	let cj = pretype empty_tycon env isevars lvar c in
	let (IndType (indf,realargs)) = 
	  try find_rectype env (evars_of !isevars) cj.uj_type
	  with Not_found ->
	    let cloc = loc_of_rawconstr c in
	      error_case_not_inductive_loc cloc env (evars_of !isevars) cj 
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
	let arsgn =
	  let arsgn,_ = get_arity env indf in
	    if not !allow_anonymous_refs then
	      List.map (fun (_,b,t) -> (Anonymous,b,t)) arsgn
	    else arsgn
	in
	    let psign = (na,None,build_dependent_inductive env indf)::arsgn in
	    let nar = List.length arsgn in
	      (match po with
		 | Some p ->
		     let env_p = push_rels psign env in
		     let pj = pretype_type empty_valcon env_p isevars lvar p in
		     let ccl = nf_evar (evars_of !isevars) pj.utj_val in
		     let psign = make_arity_signature env true indf in (* with names *)
		     let p = it_mkLambda_or_LetIn ccl psign in
		     let inst = 
		       (Array.to_list cs.cs_concl_realargs)
		       @[build_dependent_constructor cs] in
		     let lp = lift cs.cs_nargs p in
		     let fty = hnf_lam_applist env (evars_of !isevars) lp inst in
		     let fj = pretype (mk_tycon fty) env_f isevars lvar d in
		     let f = it_mkLambda_or_LetIn fj.uj_val fsign in
		     let v =
		       let mis,_ = dest_ind_family indf in
		       let ci = make_case_info env mis LetStyle in
			 mkCase (ci, p, cj.uj_val,[|f|]) in 
		       { uj_val = v; uj_type = substl (realargs@[cj.uj_val]) ccl }

		 | None -> 
		     let tycon = lift_tycon cs.cs_nargs tycon in
		     let fj = pretype tycon env_f isevars lvar d in
		     let f = it_mkLambda_or_LetIn fj.uj_val fsign in
		     let ccl = nf_evar (evars_of !isevars) fj.uj_type in
		     let ccl =
		       if noccur_between 1 cs.cs_nargs ccl then
			 lift (- cs.cs_nargs) ccl 
		       else
			 error_cant_find_case_type_loc loc env (evars_of !isevars) 
			   cj.uj_val in
		     let p = it_mkLambda_or_LetIn (lift (nar+1) ccl) psign in
		     let v =
		       let mis,_ = dest_ind_family indf in
		       let ci = make_case_info env mis LetStyle in
			 mkCase (ci, p, cj.uj_val,[|f|] ) 
		     in
		       { uj_val = v; uj_type = ccl })

    | RIf (loc,c,(na,po),b1,b2) ->
	let cj = pretype empty_tycon env isevars lvar c in
	let (IndType (indf,realargs)) = 
	  try find_rectype env (evars_of !isevars) cj.uj_type
	  with Not_found ->
	    let cloc = loc_of_rawconstr c in
	      error_case_not_inductive_loc cloc env (evars_of !isevars) cj in
	let cstrs = get_constructors env indf in 
	  if Array.length cstrs <> 2 then
            user_err_loc (loc,"",
			  str "If is only for inductive types with two constructors");

	  let arsgn = 
	    let arsgn,_ = get_arity env indf in
	      if not !allow_anonymous_refs then
		(* Make dependencies from arity signature impossible *)
		List.map (fun (_,b,t) -> (Anonymous,b,t)) arsgn 
	      else arsgn
	  in
	  let nar = List.length arsgn in
	  let psign = (na,None,build_dependent_inductive env indf)::arsgn in
	  let pred,p = match po with
	    | Some p ->
		let env_p = push_rels psign env in
		let pj = pretype_type empty_valcon env_p isevars lvar p in
		let ccl = nf_evar (evars_of !isevars) pj.utj_val in
		let pred = it_mkLambda_or_LetIn ccl psign in
		let typ = lift (- nar) (beta_applist (pred,[cj.uj_val])) in
		let jtyp = inh_conv_coerce_to_tycon loc env isevars {uj_val = pred;
								     uj_type = typ} tycon 
		in
		  jtyp.uj_val, jtyp.uj_type
	    | None -> 
		let p = match tycon with
		  | Some (None, ty) -> ty
		  | None | Some _ ->
                      e_new_evar isevars env ~src:(loc,InternalHole) (new_Type ())
		in
		  it_mkLambda_or_LetIn (lift (nar+1) p) psign, p in
	  let pred = nf_evar (evars_of !isevars) pred in
	  let p = nf_evar (evars_of !isevars) p in
	 (*   msgnl (str "Pred is: " ++ Termops.print_constr_env env pred);*)
	  let f cs b =
	    let n = rel_context_length cs.cs_args in
	    let pi = lift n pred in (* liftn n 2 pred ? *)
	    let pi = beta_applist (pi, [build_dependent_constructor cs]) in
	    let csgn = 
	      if not !allow_anonymous_refs then
		List.map (fun (_,b,t) -> (Anonymous,b,t)) cs.cs_args 
	      else 
		List.map 
		  (fun (n, b, t) ->
		     match n with
                         Name _ -> (n, b, t)
                       | Anonymous -> (Name (id_of_string "H"), b, t))
		cs.cs_args
	    in
	    let env_c = push_rels csgn env in 
(* 	      msgnl (str "Pi is: " ++ Termops.print_constr_env env_c pi); *)
	    let bj = pretype (mk_tycon pi) env_c isevars lvar b in
	      it_mkLambda_or_LetIn bj.uj_val cs.cs_args in
	  let b1 = f cstrs.(0) b1 in
	  let b2 = f cstrs.(1) b2 in
	  let v =
	    let mis,_ = dest_ind_family indf in
	    let ci = make_case_info env mis IfStyle in
	      mkCase (ci, pred, cj.uj_val, [|b1;b2|])
	  in
	    { uj_val = v; uj_type = p }

    | RCases (loc,sty,po,tml,eqns) ->
	Cases.compile_cases loc sty
	  ((fun vtyc env isevars -> pretype vtyc env isevars lvar),isevars)
	  tycon env (* loc *) (po,tml,eqns)

    | RCast(loc,c,k) ->
	let cj =
	  match k with
	      CastCoerce ->
		let cj = pretype empty_tycon env isevars lvar c in
		  evd_comb1 (Coercion.inh_coerce_to_base loc env) isevars cj
	    | CastConv (k,t) ->
		let tj = pretype_type empty_valcon env isevars lvar t in
		let cj = pretype (mk_tycon tj.utj_val) env isevars lvar c in
		  (* User Casts are for helping pretyping, experimentally not to be kept*)
		  (* ... except for Correctness *)
		let v = mkCast (cj.uj_val, k, tj.utj_val) in
		  { uj_val = v; uj_type = tj.utj_val }
	in
	  inh_conv_coerce_to_tycon loc env isevars cj tycon

    | RDynamic (loc,d) ->
	if (tag d) = "constr" then
	  let c = constr_out d in
	  let j = (Retyping.get_judgment_of env (evars_of !isevars) c) in
	    j
	      (*inh_conv_coerce_to_tycon loc env isevars j tycon*)
	else
	  user_err_loc (loc,"pretype",(str "Not a constr tagged Dynamic"))

  (* [pretype_type valcon env isevars lvar c] coerces [c] into a type *)
  and pretype_type valcon env isevars lvar = function
    | RHole loc ->
	(match valcon with
	   | Some v ->
               let s =
		 let sigma = evars_of !isevars in
		 let t = Retyping.get_type_of env sigma v in
		   match kind_of_term (whd_betadeltaiota env sigma t) with
                     | Sort s -> s
                     | Evar v when is_Type (existential_type sigma v) -> 
			 evd_comb1 (define_evar_as_sort) isevars v
                     | _ -> anomaly "Found a type constraint which is not a type"
               in
		 { utj_val = v;
		   utj_type = s }
	   | None ->
	       let s = new_Type_sort () in
		 { utj_val = e_new_evar isevars env ~src:loc (mkSort s);
		   utj_type = s})
    | c ->
	let j = pretype empty_tycon env isevars lvar c in
	let loc = loc_of_rawconstr c in
	let tj = evd_comb1 (Coercion.inh_coerce_to_sort loc env) isevars j in
	  match valcon with
	    | None -> tj
	    | Some v ->
		if e_cumul env isevars v tj.utj_val then tj
		else
		  error_unexpected_type_loc
                    (loc_of_rawconstr c) env (evars_of !isevars) tj.utj_val v

  let pretype_gen_aux isevars env lvar kind c =
    let c' = match kind with
      | OfType exptyp ->
	  let tycon = match exptyp with None -> empty_tycon | Some t -> mk_tycon t in
	    (pretype tycon env isevars lvar c).uj_val
      | IsType ->
	  (pretype_type empty_valcon env isevars lvar c).utj_val in
    let evd,_ = consider_remaining_unif_problems env !isevars in
      isevars:=evd;
      nf_evar (evars_of !isevars) c'

  let pretype_gen isevars env lvar kind c =
    let c = pretype_gen_aux isevars env lvar kind c in
      isevars := Typeclasses.resolve_typeclasses ~onlyargs:true ~fail:false env !isevars;
      nf_evar (evars_of !isevars) c

  (* TODO: comment faire remonter l'information si le typage a resolu des
     variables du sigma original. il faudrait que la fonction de typage
     retourne aussi le nouveau sigma...
  *)

  let understand_judgment sigma env c =
    let isevars = ref (create_evar_defs sigma) in
    let j = pretype empty_tycon env isevars ([],[]) c in
    let j = j_nf_evar (evars_of !isevars) j in
    let isevars,_ = consider_remaining_unif_problems env !isevars in
      check_evars env sigma isevars (mkCast(j.uj_val,DEFAULTcast, j.uj_type));
      j

  let understand_judgment_tcc isevars env c =
    let j = pretype empty_tycon env isevars ([],[]) c in
    let sigma = evars_of !isevars in
    let j = j_nf_evar sigma j in
      j

  (* Raw calls to the unsafe inference machine: boolean says if we must
     fail on unresolved evars; the unsafe_judgment list allows us to
     extend env with some bindings *)

  let ise_pretype_gen fail_evar sigma env lvar kind c =
    let isevars = ref (Evd.create_evar_defs sigma) in
    let c = pretype_gen isevars env lvar kind c in
    let evd = !isevars in
      if fail_evar then check_evars env Evd.empty evd c;
      evd, c
	
  (** Entry points of the high-level type synthesis algorithm *)

  let understand_gen kind sigma env c =
    snd (ise_pretype_gen true sigma env ([],[]) kind c)

  let understand sigma env ?expected_type:exptyp c =
    snd (ise_pretype_gen true sigma env ([],[]) (OfType exptyp) c)

  let understand_type sigma env c =
    snd (ise_pretype_gen false sigma env ([],[]) IsType c)

  let understand_ltac sigma env lvar kind c =
    ise_pretype_gen false sigma env lvar kind c
      
  let understand_tcc_evars evdref env kind c =
    pretype_gen evdref env ([],[]) kind c 

  let understand_tcc ?(resolve_classes=true) sigma env ?expected_type:exptyp c =
    let ev, t = 
      if resolve_classes then
	ise_pretype_gen false sigma env ([],[]) (OfType exptyp) c 
      else
	let isevars = ref (Evd.create_evar_defs sigma) in
	let c = pretype_gen_aux isevars env ([],[]) (OfType exptyp) c in
	  !isevars, c
    in
      Evd.evars_of ev, t
end

module Default : S = SubtacPretyping_F(Coercion.Default)

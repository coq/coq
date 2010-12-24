(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Compat
open Util
open Names
open Sign
open Evd
open Term
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
open Glob_term
open Evarconv
open Pattern
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

  let evd_comb0 f evdref =
    let (evd',x) = f !evdref in
      evdref := evd';
      x

  let evd_comb1 f evdref x =
    let (evd',y) = f !evdref x in
      evdref := evd';
      y

  let evd_comb2 f evdref x y =
    let (evd',z) = f !evdref x y in
      evdref := evd';
      z

  let evd_comb3 f evdref x y z =
    let (evd',t) = f !evdref x y z in
      evdref := evd';
      t

  let mt_evd = Evd.empty

  (* Utilisé pour inférer le prédicat des Cases *)
  (* Semble exagérement fort *)
  (* Faudra préférer une unification entre les types de toutes les clauses *)
  (* et autoriser des ? à rester dans le résultat de l'unification *)

  let evar_type_fixpoint loc env evdref lna lar vdefj =
    let lt = Array.length vdefj in
      if Array.length lar = lt then
	for i = 0 to lt-1 do
          if not (e_cumul env evdref (vdefj.(i)).uj_type
		    (lift lt lar.(i))) then
            error_ill_typed_rec_body_loc loc env !evdref
              i lna vdefj lar
	done

  let check_branches_message loc env evdref c (explft,lft) =
    for i = 0 to Array.length explft - 1 do
      if not (e_cumul env evdref lft.(i) explft.(i)) then
	let sigma =  !evdref in
	  error_ill_formed_branch_loc loc env sigma c i lft.(i) explft.(i)
    done

  (* coerce to tycon if any *)
  let inh_conv_coerce_to_tycon loc env evdref j = function
    | None -> j_nf_evar !evdref j
    | Some t -> evd_comb2 (Coercion.inh_conv_coerce_to loc env) evdref j t

  let push_rels vars env = List.fold_right push_rel vars env

  (*
    let evar_type_case evdref env ct pt lft p c =
    let (mind,bty,rslty) = type_case_branches env ( evdref) ct pt p c
    in check_branches_message evdref env (c,ct) (bty,lft); (mind,rslty)
  *)

  let strip_meta id = (* For Grammar v7 compatibility *)
    let s = string_of_id id in
      if s.[0]='$' then id_of_string (String.sub s 1 (String.length s - 1))
      else id

  let invert_ltac_bound_name env id0 id =
    try mkRel (pi1 (Termops.lookup_rel_id id (rel_context env)))
    with Not_found ->
      errorlabstrm "" (str "Ltac variable " ++ pr_id id0 ++
	str " depends on pattern variable name " ++ pr_id id ++
	str " which is not bound in current context")

  let pretype_id loc env sigma (lvar,unbndltacvars) id =
    let id = strip_meta id in (* May happen in tactics defined by Grammar *)
      try
	let (n,_,typ) = Termops.lookup_rel_id id (rel_context env) in
	  { uj_val  = mkRel n; uj_type = lift n typ }
      with Not_found ->
	try
	  let (ids,c) = List.assoc id lvar in
	  let subst = List.map (invert_ltac_bound_name env id) ids in
	  let c = substl subst c in
	  { uj_val = c; uj_type = Retyping.get_type_of env sigma c }
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
      {uj_val=Termops.it_mkLambda ccl' sign; uj_type=Termops.it_mkProd s' sign}

  (*************************************************************************)
  (* Main pretyping function                                               *)

  let pretype_ref evdref env ref =
    let c = constr_of_global ref in
      make_judge c (Retyping.get_type_of env Evd.empty c)

  let pretype_sort = function
    | GProp c -> judge_of_prop_contents c
    | GType _ -> judge_of_new_Type ()

  let split_tycon_lam loc env evd tycon =
    let rec real_split evd c =
      let t = whd_betadeltaiota env evd c in
	match kind_of_term t with
	| Prod (na,dom,rng) -> evd, (na, dom, rng)
	| Evar ev when not (Evd.is_defined_evar evd ev) ->
	    let (evd',prod) = define_evar_as_product evd ev in
	    let (_,dom,rng) = destProd prod in
	      evd',(Anonymous, dom, rng)
	| _ -> error_not_product_loc loc env evd c
    in
      match tycon with
      | None -> evd,(Anonymous,None,None)
      | Some (abs, c) ->
	  (match abs with
	   | None ->
	       let evd', (n, dom, rng) = real_split evd c in
		 evd', (n, mk_tycon dom, mk_tycon rng)
	   | Some (init, cur) ->
	       evd, (Anonymous, None, Some (Some (init, succ cur), c)))
	    
	    
  (* [pretype tycon env evdref lvar lmeta cstr] attempts to type [cstr] *)
  (* in environment [env], with existential variables [( evdref)] and *)
  (* the type constraint tycon *)
  let rec pretype (tycon : type_constraint) env evdref lvar c =
(*     let _ = try Subtac_utils.trace (str "pretype " ++ Subtac_utils.my_print_glob_constr env c ++ *)
(* 			       str " with tycon " ++ Evarutil.pr_tycon env tycon)  *)
(*     with _ -> () *)
(*     in *)
    match c with
    | GRef (loc,ref) ->
	inh_conv_coerce_to_tycon loc env evdref
	  (pretype_ref evdref env ref)
	  tycon

    | GVar (loc, id) ->
	inh_conv_coerce_to_tycon loc env evdref
	  (pretype_id loc env !evdref lvar id)
	  tycon

    | GEvar (loc, ev, instopt) ->
	(* Ne faudrait-il pas s'assurer que hyps est bien un
	   sous-contexte du contexte courant, et qu'il n'y a pas de Rel "caché" *)
	let hyps = evar_context (Evd.find !evdref ev) in
	let args = match instopt with
          | None -> instance_from_named_context hyps
          | Some inst -> failwith "Evar subtitutions not implemented" in
	let c = mkEvar (ev, args) in
	let j = (Retyping.get_judgment_of env !evdref c) in
	  inh_conv_coerce_to_tycon loc env evdref j tycon

    | GPatVar (loc,(someta,n)) ->
	anomaly "Found a pattern variable in a glob_constr to type"

    | GHole (loc,k) ->
	let ty =
          match tycon with
            | Some (None, ty) -> ty
            | None | Some _ ->
		e_new_evar evdref env ~src:(loc, InternalHole) (Termops.new_Type ()) in
	  { uj_val = e_new_evar evdref env ~src:(loc,k) ty; uj_type = ty }

    | GRec (loc,fixkind,names,bl,lar,vdef) ->
	let rec type_bl env ctxt = function
            [] -> ctxt
          | (na,k,None,ty)::bl ->
              let ty' = pretype_type empty_valcon env evdref lvar ty in
              let dcl = (na,None,ty'.utj_val) in
		type_bl (push_rel dcl env) (add_rel_decl dcl ctxt) bl
          | (na,k,Some bd,ty)::bl ->
              let ty' = pretype_type empty_valcon env evdref lvar ty in
              let bd' = pretype (mk_tycon ty'.utj_val) env evdref lvar ty in
              let dcl = (na,Some bd'.uj_val,ty'.utj_val) in
		type_bl (push_rel dcl env) (add_rel_decl dcl ctxt) bl in
	let ctxtv = Array.map (type_bl env empty_rel_context) bl in
	let larj =
          array_map2
            (fun e ar ->
               pretype_type empty_valcon (push_rel_context e env) evdref lvar ar)
            ctxtv lar in
	let lara = Array.map (fun a -> a.utj_val) larj in
	let ftys = array_map2 (fun e a -> it_mkProd_or_LetIn a e) ctxtv lara in
	let nbfix = Array.length lar in
	let names = Array.map (fun id -> Name id) names in
	  (* Note: bodies are not used by push_rec_types, so [||] is safe *)
	let newenv =
	  let marked_ftys =
	    Array.map (fun ty -> let sort = Retyping.get_type_of env !evdref ty in
			 mkApp (delayed_force Subtac_utils.fix_proto, [| sort; ty |]))
	      ftys
	  in
	    push_rec_types (names,marked_ftys,[||]) env
	in
	let fixi = match fixkind with GFix (vn, i) -> i | GCoFix i -> i in
	let vdefj =
	  array_map2_i
	    (fun i ctxt def ->
	      let fty =
		let ty = ftys.(i) in
		  if i = fixi then (
		    Option.iter (fun tycon ->
		      evdref := Coercion.inh_conv_coerces_to loc env !evdref ftys.(i) tycon)
		      tycon;
		    nf_evar !evdref ty)
		  else ty
	      in
              (* we lift nbfix times the type in tycon, because of
	       * the nbfix variables pushed to newenv *)
              let (ctxt,ty) =
		decompose_prod_n_assum (rel_context_length ctxt)
                  (lift nbfix fty) in
              let nenv = push_rel_context ctxt newenv in
              let j = pretype (mk_tycon ty) nenv evdref lvar def in
		{ uj_val = it_mkLambda_or_LetIn j.uj_val ctxt;
		  uj_type = it_mkProd_or_LetIn j.uj_type ctxt })
            ctxtv vdef in
	evar_type_fixpoint loc env evdref names ftys vdefj;
	let ftys = Array.map (nf_evar !evdref) ftys in
	let fdefs = Array.map (fun x -> nf_evar !evdref (j_val x)) vdefj in
	let fixj = match fixkind with
	  | GFix (vn,i) ->
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
	  | GCoFix i ->
	      let cofix = (i,(names,ftys,fdefs)) in
	      (try check_cofix env cofix with e -> Loc.raise loc e);
	      make_judge (mkCoFix cofix) ftys.(i) in
	inh_conv_coerce_to_tycon loc env evdref fixj tycon

    | GSort (loc,s) ->
	inh_conv_coerce_to_tycon loc env evdref (pretype_sort s) tycon

    | GApp (loc,f,args) ->
	let length = List.length args in
	let ftycon =
	  let ty =
	    if length > 0 then
	      match tycon with
	      | None -> None
	      | Some (None, ty) -> mk_abstr_tycon length ty
	      | Some (Some (init, cur), ty) ->
		  Some (Some (length + init, length + cur), ty)
 	    else tycon
	  in
	    match ty with
	    | Some (_, t) when Subtac_coercion.disc_subset t = None -> ty
	    | _ -> None
	in
	let fj = pretype ftycon env evdref lvar f in
 	let floc = loc_of_glob_constr f in
	let rec apply_rec env n resj tycon = function
	  | [] -> resj
	  | c::rest ->
	      let argloc = loc_of_glob_constr c in
	      let resj = evd_comb1 (Coercion.inh_app_fun env) evdref resj in
              let resty = whd_betadeltaiota env !evdref resj.uj_type in
      		match kind_of_term resty with
		  | Prod (na,c1,c2) ->
		      Option.iter (fun ty -> evdref :=
			Coercion.inh_conv_coerces_to loc env !evdref resty ty) tycon;
		      let evd, (_, _, tycon) = split_tycon loc env !evdref tycon in
		      evdref := evd;
		      let hj = pretype (mk_tycon (nf_evar !evdref c1)) env evdref lvar c in
		      let value, typ = applist (j_val resj, [j_val hj]), subst1 hj.uj_val c2 in
		      let typ' = nf_evar !evdref typ in
			apply_rec env (n+1)
			  { uj_val = nf_evar !evdref value;
			    uj_type = nf_evar !evdref typ' }
			  (Option.map (fun (abs, c) -> abs, nf_evar !evdref c) tycon) rest

		  | _ ->
		      let hj = pretype empty_tycon env evdref lvar c in
			error_cant_apply_not_functional_loc
			  (join_loc floc argloc) env !evdref
	      		  resj [hj]
	in
	let resj = j_nf_evar !evdref (apply_rec env 1 fj ftycon args) in
	let resj =
	  match kind_of_term resj.uj_val with
	  | App (f,args) when isInd f or isConst f ->
	      let sigma =  !evdref in
	      let c = mkApp (f,Array.map (whd_evar sigma) args) in
	      let t = Retyping.get_type_of env sigma c in
	      make_judge c t
	  | _ -> resj in
	  inh_conv_coerce_to_tycon loc env evdref resj tycon

    | GLambda(loc,name,k,c1,c2)      ->
	let tycon' = evd_comb1
	  (fun evd tycon ->
	    match tycon with
	    | None -> evd, tycon
	    | Some ty ->
		let evd, ty' = Coercion.inh_coerce_to_prod loc env evd ty in
		  evd, Some ty')
	  evdref tycon
	in
	let (name',dom,rng) = evd_comb1 (split_tycon_lam loc env) evdref tycon' in
	let dom_valcon = valcon_of_tycon dom in
	let j = pretype_type dom_valcon env evdref lvar c1 in
	let var = (name,None,j.utj_val) in
	let j' = pretype rng (push_rel var env) evdref lvar c2 in
	let resj = judge_of_abstraction env name j j' in
	  inh_conv_coerce_to_tycon loc env evdref resj tycon

    | GProd(loc,name,k,c1,c2)        ->
	let j = pretype_type empty_valcon env evdref lvar c1 in
	let var = (name,j.utj_val) in
	let env' = Termops.push_rel_assum var env in
	let j' = pretype_type empty_valcon env' evdref lvar c2 in
	let resj =
	  try judge_of_product env name j j'
	  with TypeError _ as e -> Loc.raise loc e in
	  inh_conv_coerce_to_tycon loc env evdref resj tycon

    | GLetIn(loc,name,c1,c2)      ->
	let j = pretype empty_tycon env evdref lvar c1 in
	let t = Termops.refresh_universes j.uj_type in
	let var = (name,Some j.uj_val,t) in
        let tycon = lift_tycon 1 tycon in
	let j' = pretype tycon (push_rel var env) evdref lvar c2 in
	  { uj_val = mkLetIn (name, j.uj_val, t, j'.uj_val) ;
	    uj_type = subst1 j.uj_val j'.uj_type }

    | GLetTuple (loc,nal,(na,po),c,d) ->
	let cj = pretype empty_tycon env evdref lvar c in
	let (IndType (indf,realargs)) =
	  try find_rectype env !evdref cj.uj_type
	  with Not_found ->
	    let cloc = loc_of_glob_constr c in
	      error_case_not_inductive_loc cloc env !evdref cj
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
		     let pj = pretype_type empty_valcon env_p evdref lvar p in
		     let ccl = nf_evar !evdref pj.utj_val in
		     let psign = make_arity_signature env true indf in (* with names *)
		     let p = it_mkLambda_or_LetIn ccl psign in
		     let inst =
		       (Array.to_list cs.cs_concl_realargs)
		       @[build_dependent_constructor cs] in
		     let lp = lift cs.cs_nargs p in
		     let fty = hnf_lam_applist env !evdref lp inst in
		     let fj = pretype (mk_tycon fty) env_f evdref lvar d in
		     let f = it_mkLambda_or_LetIn fj.uj_val fsign in
		     let v =
		       let mis,_ = dest_ind_family indf in
		       let ci = make_case_info env mis LetStyle in
			 mkCase (ci, p, cj.uj_val,[|f|]) in
		       { uj_val = v; uj_type = substl (realargs@[cj.uj_val]) ccl }

		 | None ->
		     let tycon = lift_tycon cs.cs_nargs tycon in
		     let fj = pretype tycon env_f evdref lvar d in
		     let f = it_mkLambda_or_LetIn fj.uj_val fsign in
		     let ccl = nf_evar !evdref fj.uj_type in
		     let ccl =
		       if noccur_between 1 cs.cs_nargs ccl then
			 lift (- cs.cs_nargs) ccl
		       else
			 error_cant_find_case_type_loc loc env !evdref
			   cj.uj_val in
		     let p = it_mkLambda_or_LetIn (lift (nar+1) ccl) psign in
		     let v =
		       let mis,_ = dest_ind_family indf in
		       let ci = make_case_info env mis LetStyle in
			 mkCase (ci, p, cj.uj_val,[|f|] )
		     in
		       { uj_val = v; uj_type = ccl })

    | GIf (loc,c,(na,po),b1,b2) ->
	let cj = pretype empty_tycon env evdref lvar c in
	let (IndType (indf,realargs)) =
	  try find_rectype env !evdref cj.uj_type
	  with Not_found ->
	    let cloc = loc_of_glob_constr c in
	      error_case_not_inductive_loc cloc env !evdref cj in
	let cstrs = get_constructors env indf in
	  if Array.length cstrs <> 2 then
            user_err_loc (loc,"",
			  str "If is only for inductive types with two constructors.");

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
		let pj = pretype_type empty_valcon env_p evdref lvar p in
		let ccl = nf_evar !evdref pj.utj_val in
		let pred = it_mkLambda_or_LetIn ccl psign in
		let typ = lift (- nar) (beta_applist (pred,[cj.uj_val])) in
		let jtyp = inh_conv_coerce_to_tycon loc env evdref {uj_val = pred;
								     uj_type = typ} tycon
		in
		  jtyp.uj_val, jtyp.uj_type
	    | None ->
		let p = match tycon with
		  | Some (None, ty) -> ty
		  | None | Some _ ->
                      e_new_evar evdref env ~src:(loc,InternalHole) (Termops.new_Type ())
		in
		  it_mkLambda_or_LetIn (lift (nar+1) p) psign, p in
	  let pred = nf_evar !evdref pred in
	  let p = nf_evar !evdref p in
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
	    let bj = pretype (mk_tycon pi) env_c evdref lvar b in
	      it_mkLambda_or_LetIn bj.uj_val cs.cs_args in
	  let b1 = f cstrs.(0) b1 in
	  let b2 = f cstrs.(1) b2 in
	  let v =
	    let mis,_ = dest_ind_family indf in
	    let ci = make_case_info env mis IfStyle in
	      mkCase (ci, pred, cj.uj_val, [|b1;b2|])
	  in
	    { uj_val = v; uj_type = p }

    | GCases (loc,sty,po,tml,eqns) ->
	Cases.compile_cases loc sty
	  ((fun vtyc env evdref -> pretype vtyc env evdref lvar),evdref)
	  tycon env (* loc *) (po,tml,eqns)

    | GCast (loc,c,k) ->
	let cj =
	  match k with
	      CastCoerce ->
		let cj = pretype empty_tycon env evdref lvar c in
		  evd_comb1 (Coercion.inh_coerce_to_base loc env) evdref cj
	    | CastConv (k,t) ->
		let tj = pretype_type empty_valcon env evdref lvar t in
		let cj = pretype (mk_tycon tj.utj_val) env evdref lvar c in
		  (* User Casts are for helping pretyping, experimentally not to be kept*)
		  (* ... except for Correctness *)
		let v = mkCast (cj.uj_val, k, tj.utj_val) in
		  { uj_val = v; uj_type = tj.utj_val }
	in
	  inh_conv_coerce_to_tycon loc env evdref cj tycon

    | GDynamic (loc,d) ->
	if (Dyn.tag d) = "constr" then
	  let c = constr_out d in
	  let j = (Retyping.get_judgment_of env !evdref c) in
	    j
	      (*inh_conv_coerce_to_tycon loc env evdref j tycon*)
	else
	  user_err_loc (loc,"pretype",(str "Not a constr tagged Dynamic."))

  (* [pretype_type valcon env evdref lvar c] coerces [c] into a type *)
  and pretype_type valcon env evdref lvar = function
    | GHole loc ->
	(match valcon with
	   | Some v ->
               let s =
		 let sigma =  !evdref in
		 let t = Retyping.get_type_of env sigma v in
		   match kind_of_term (whd_betadeltaiota env sigma t) with
                     | Sort s -> s
                     | Evar ev when is_Type (existential_type sigma ev) ->
			 evd_comb1 (define_evar_as_sort) evdref ev
                     | _ -> anomaly "Found a type constraint which is not a type"
               in
		 { utj_val = v;
		   utj_type = s }
	   | None ->
	       let s = Termops.new_Type_sort () in
		 { utj_val = e_new_evar evdref env ~src:loc (mkSort s);
		   utj_type = s})
    | c ->
	let j = pretype empty_tycon env evdref lvar c in
	let loc = loc_of_glob_constr c in
	let tj = evd_comb1 (Coercion.inh_coerce_to_sort loc env) evdref j in
	  match valcon with
	    | None -> tj
	    | Some v ->
		if e_cumul env evdref v tj.utj_val then tj
		else
		  error_unexpected_type_loc
                    (loc_of_glob_constr c) env !evdref tj.utj_val v

  let pretype_gen expand_evar fail_evar resolve_classes evdref env lvar kind c =
    let c' = match kind with
      | OfType exptyp ->
	  let tycon = match exptyp with None -> empty_tycon | Some t -> mk_tycon t in
	  (pretype tycon env evdref lvar c).uj_val
      | IsType ->
	  (pretype_type empty_valcon env evdref lvar c).utj_val 
    in
      if resolve_classes then
	evdref := Typeclasses.resolve_typeclasses ~onlyargs:false
	  ~split:true ~fail:fail_evar env !evdref;
      evdref := consider_remaining_unif_problems env !evdref;
      let c = if expand_evar then nf_evar !evdref c' else c' in
      if fail_evar then check_evars env Evd.empty !evdref c;
      c

  (* TODO: comment faire remonter l'information si le typage a resolu des
     variables du sigma original. il faudrait que la fonction de typage
     retourne aussi le nouveau sigma...
  *)

  let understand_judgment sigma env c =
    let evdref = ref (create_evar_defs sigma) in
    let j = pretype empty_tycon env evdref ([],[]) c in
    let evd = consider_remaining_unif_problems env !evdref in
    let j = j_nf_evar evd j in
    check_evars env sigma evd (mkCast(j.uj_val,DEFAULTcast, j.uj_type));
    j

  let understand_judgment_tcc evdref env c =
    let j = pretype empty_tycon env evdref ([],[]) c in
    j_nf_evar !evdref j

  (* Raw calls to the unsafe inference machine: boolean says if we must
     fail on unresolved evars; the unsafe_judgment list allows us to
     extend env with some bindings *)

  let ise_pretype_gen expand_evar fail_evar resolve_classes sigma env lvar kind c =
    let evdref = ref (Evd.create_evar_defs sigma) in
    let c = pretype_gen expand_evar fail_evar resolve_classes evdref env lvar kind c in
    !evdref, c

  (** Entry points of the high-level type synthesis algorithm *)

  let understand_gen kind sigma env c =
    snd (ise_pretype_gen true true true sigma env ([],[]) kind c)

  let understand sigma env ?expected_type:exptyp c =
    snd (ise_pretype_gen true true true sigma env ([],[]) (OfType exptyp) c)

  let understand_type sigma env c =
    snd (ise_pretype_gen true false true sigma env ([],[]) IsType c)

  let understand_ltac expand_evar sigma env lvar kind c =
    ise_pretype_gen expand_evar false true sigma env lvar kind c

  let understand_tcc ?(resolve_classes=true) sigma env ?expected_type:exptyp c =
    ise_pretype_gen true false resolve_classes sigma env ([],[]) (OfType exptyp) c

  let understand_tcc_evars ?(fail_evar=false) ?(resolve_classes=true) evdref env kind c =
    pretype_gen true fail_evar resolve_classes evdref env ([],[]) kind c
end

module Default : S = SubtacPretyping_F(Coercion.Default)

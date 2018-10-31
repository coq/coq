(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Cic
open Term
open Inductive
open Reduction
open Typeops
open Pp
open Declarations
open Environ

let rec debug_string_of_mp = function
  | MPfile sl -> DirPath.to_string sl
  | MPbound uid -> "bound("^MBId.to_string uid^")"
  | MPdot (mp,l) -> debug_string_of_mp mp ^ "." ^ Label.to_string l

let rec string_of_mp = function
  | MPfile sl -> DirPath.to_string sl
  | MPbound uid -> MBId.to_string uid
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ Label.to_string l

let string_of_mp mp =
  if !Flags.debug then debug_string_of_mp mp else string_of_mp mp

let prkn kn =
  let (mp,_,l) = KerName.repr kn in
  str(string_of_mp mp ^ "." ^ Label.to_string l)
let prcon c =
  let ck = Constant.canonical c in
  let uk = Constant.user c in
  if KerName.equal ck uk then prkn uk else (prkn uk ++str"(="++prkn ck++str")")

(* Same as noccur_between but may perform reductions.
   Could be refined more...  *)
let weaker_noccur_between env x nvars t =
  if noccur_between x nvars t then Some t
  else
   let t' = whd_all env t in
   if noccur_between x nvars t' then Some t'
   else None

let is_constructor_head t =
  match fst(decompose_app t) with
  | Rel _ -> true
  | _ -> false

let conv_ctxt_prefix env (ctx1:rel_context) ctx2 =
  let rec chk env rctx1 rctx2 =
    match rctx1, rctx2 with
        (LocalAssum (_,ty1) as d1)::rctx1', LocalAssum (_,ty2)::rctx2' ->
          conv env ty1 ty2;
          chk (push_rel d1 env) rctx1' rctx2'
      | (LocalDef (_,bd1,ty1) as d1)::rctx1', LocalDef (_,bd2,ty2)::rctx2' ->
          conv env ty1 ty2;
          conv env bd1 bd2;
          chk (push_rel d1 env) rctx1' rctx2'
      | [],_ -> ()
      | _ -> failwith "non convertible contexts" in
  chk env (List.rev ctx1) (List.rev ctx2)

(************************************************************************)
(* Various well-formedness check for inductive declarations            *)

(* Errors related to inductive constructions *)
type inductive_error =
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * constr * constr
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of Id.t
  | SameNamesConstructors of Id.t
  | SameNamesOverlap of Id.t list
  | NotAnArity of Id.t
  | BadEntry

exception InductiveError of inductive_error

(************************************************************************)
(************************************************************************)

(* Typing the arities and constructor types *)

let rec sorts_of_constr_args env t =
  let t = whd_allnolet env t in
  match t with
    | Prod (name,c1,c2) ->
        let varj = infer_type env c1 in
	let env1 = push_rel (LocalAssum (name,c1)) env in
	varj :: sorts_of_constr_args env1 c2
    | LetIn (name,def,ty,c) ->
        let env1 = push_rel (LocalDef (name,def,ty)) env in
	sorts_of_constr_args env1 c
    | _ when is_constructor_head t -> []
    | _ -> anomaly ~label:"infos_and_sort" (Pp.str "not a positive constructor.")


(* Prop and Set are small *)
let is_small_sort = function
  | Prop | Set -> true
  | _ -> false

let is_logic_sort = function
| Prop -> true
| _ -> false

(* [infos] is a sequence of pair [islogic,issmall] for each type in
   the product of a constructor or arity *)

let is_small_constr infos = List.for_all (fun s -> is_small_sort s) infos
let is_logic_constr infos = List.for_all (fun s -> is_logic_sort s) infos

(* An inductive definition is a "unit" if it has only one constructor
   and that all arguments expected by this constructor are
   logical, this is the case for equality, conjunction of logical properties
*)
let is_unit constrsinfos =
  match constrsinfos with  (* One info = One constructor *)
   | [|constrinfos|] -> is_logic_constr constrinfos
   | [||] -> (* type without constructors *) true
   | _ -> false

let small_unit constrsinfos =
  let issmall = Array.for_all is_small_constr constrsinfos
  and isunit = is_unit constrsinfos in
  issmall, isunit

(* check information related to inductive arity *)
let typecheck_arity env params inds =
  let nparamargs = rel_context_nhyps params in
  let nparamdecls = rel_context_length params in
  let check_arity arctxt = function
    | RegularArity mar ->
        let ar = mar.mind_user_arity in
        let _ = infer_type env ar in
        conv env (it_mkProd_or_LetIn (Sort mar.mind_sort) arctxt) ar;
        ar
    | TemplateArity par ->
      check_polymorphic_arity env params par;
      it_mkProd_or_LetIn (Sort(Type par.template_level)) arctxt 
  in
  let env_arities =
    Array.fold_left
      (fun env_ar ind ->
        let ar_ctxt = ind.mind_arity_ctxt in
        let _ = check_ctxt env ar_ctxt in
        conv_ctxt_prefix env params ar_ctxt;
        (* Arities (with params) are typed-checked here *)
        let arity = check_arity ar_ctxt ind.mind_arity in
        (* mind_nrealargs *)
	let nrealargs = rel_context_nhyps ar_ctxt - nparamargs in
        if ind.mind_nrealargs <> nrealargs then
             failwith "bad number of real inductive arguments";
	let nrealargs_ctxt = rel_context_length ar_ctxt - nparamdecls in
        if ind.mind_nrealdecls <> nrealargs_ctxt then
             failwith "bad length of real inductive arguments signature";
	(* We do not need to generate the universe of full_arity; if
	   later, after the validation of the inductive definition,
	   full_arity is used as argument or subject to cast, an
	   upper universe will be generated *)
	let id = ind.mind_typename in
	let env_ar' = push_rel (LocalAssum (Name id, arity)) env_ar in
        env_ar')
      env
      inds in
  env_arities

(* Allowed eliminations *)

let check_predicativity env s small level =
  match s, engagement env with
      Type u, _ ->
        (* let u' = fresh_local_univ () in *)
        (* let cst = *)
        (*   merge_constraints (enforce_leq u u' empty_constraint) *)
        (*     (universes env) in *)
        if not (Univ.check_leq (universes env) level u) then
          failwith "impredicative Type inductive type"
    | Set, ImpredicativeSet -> ()
    | Set, _ ->
        if not small then failwith "impredicative Set inductive type"
    | Prop,_ -> ()


let sort_of_ind = function
  | RegularArity mar -> mar.mind_sort
  | TemplateArity par -> Type par.template_level

let all_sorts = [InProp;InSet;InType]
let small_sorts = [InProp;InSet]
let logical_sorts = [InProp]

let allowed_sorts issmall isunit s =
  match family_of_sort s with
  (* Type: all elimination allowed *)
  | InType -> all_sorts

  (* Small Set is predicative: all elimination allowed *)
  | InSet when issmall -> all_sorts

  (* Large Set is necessarily impredicative: forbids large elimination *)
  | InSet -> small_sorts

  (* Unitary/empty Prop: elimination to all sorts are realizable *)
  (* unless the type is large. If it is large, forbids large elimination *)
  (* which otherwise allows simulating the inconsistent system Type:Type *)
  | InProp when isunit -> if issmall then all_sorts else small_sorts

  (* Other propositions: elimination only to Prop *)
  | InProp -> logical_sorts



let compute_elim_sorts env_ar params arity lc =
  let inst = extended_rel_list 0 params in
  let env_params = push_rel_context params env_ar in
  let lc = Array.map
    (fun c ->
      hnf_prod_applist env_params (lift (rel_context_length params) c) inst)
    lc in
  let s = sort_of_ind arity in
  let infos = Array.map (sorts_of_constr_args env_params) lc in
  let (small,unit) = small_unit infos in
  (* We accept recursive unit types... *)
  (* compute the max of the sorts of the products of the constructor type *)
  let level = max_inductive_sort
    (Array.concat (Array.to_list (Array.map Array.of_list infos))) in
  check_predicativity env_ar s small level;
  allowed_sorts small unit s


let typecheck_one_inductive env params mip =
  (* mind_typename and mind_consnames not checked *)
  (* mind_reloc_tbl, mind_nb_constant, mind_nb_args not checked (VM) *)
  (* mind_arity_ctxt, mind_arity, mind_nrealargs DONE (typecheck_arity) *)
  (* mind_user_lc *)
  let _ = Array.map (infer_type env) mip.mind_user_lc in
  (* mind_nf_lc *)
  let _ = Array.map (infer_type env) mip.mind_nf_lc in
  Array.iter2 (conv env) mip.mind_nf_lc mip.mind_user_lc;
  (* mind_consnrealdecls *)
  let check_cons_args c n =
    let ctx,_ = decompose_prod_assum c in
    if n <> rel_context_length ctx - rel_context_length params then
      failwith "bad number of real constructor arguments" in
  Array.iter2 check_cons_args mip.mind_nf_lc mip.mind_consnrealdecls;
  (* mind_kelim: checked by positivity criterion ? *)
  let sorts =
    compute_elim_sorts env params mip.mind_arity mip.mind_nf_lc in
  let reject_sort s = not (List.mem_f family_equal s sorts) in
  if List.exists reject_sort mip.mind_kelim then
    failwith "elimination not allowed";
  (* mind_recargs: checked by positivity criterion *)
  ()

(************************************************************************)
(************************************************************************)
(* Positivity *)

type ill_formed_ind =
  | LocalNonPos of int
  | LocalNotEnoughArgs of int
  | LocalNotConstructor
  | LocalNonPar of int * int * int

exception IllFormedInd of ill_formed_ind

(* [mind_extract_params mie] extracts the params from an inductive types
   declaration, and checks that they are all present (and all the same)
   for all the given types. *)

let mind_extract_params = decompose_prod_n_assum

let explain_ind_err ntyp env0 nbpar c err =
  let (lpar,c') = mind_extract_params nbpar c in
  let env = push_rel_context lpar env0 in
  match err with
    | LocalNonPos kt ->
	raise (InductiveError (NonPos (env,c',Rel (kt+nbpar))))
    | LocalNotEnoughArgs kt ->
	raise (InductiveError
		 (NotEnoughArgs (env,c',Rel (kt+nbpar))))
    | LocalNotConstructor ->
	raise (InductiveError
		 (NotConstructor (env,c',Rel (ntyp+nbpar))))
    | LocalNonPar (n,i,l) ->
	raise (InductiveError
		 (NonPar (env,c',n,Rel i,Rel (l+nbpar))))

let failwith_non_pos n ntypes c =
  for k = n to n + ntypes - 1 do
    if not (noccurn k c) then raise (IllFormedInd (LocalNonPos (k-n+1)))
  done

let failwith_non_pos_vect n ntypes v =
  Array.iter (failwith_non_pos n ntypes) v;
  anomaly ~label:"failwith_non_pos_vect" (Pp.str "some k in [n;n+ntypes-1] should occur.")

let failwith_non_pos_list n ntypes l =
  List.iter (failwith_non_pos n ntypes) l;
  anomaly ~label:"failwith_non_pos_list" (Pp.str "some k in [n;n+ntypes-1] should occur.")

(* Conclusion of constructors: check the inductive type is called with
   the expected parameters *)
let check_correct_par (env,n,ntypes,_) hyps l largs =
  let nparams = rel_context_nhyps hyps in
  let largs = Array.of_list largs in
  if Array.length largs < nparams then
    raise (IllFormedInd (LocalNotEnoughArgs l));
  let (lpar,largs') = Array.chop nparams largs in
  let nhyps = List.length hyps in
  let rec check k index = function
    | [] -> ()
    | LocalDef _ :: hyps -> check k (index+1) hyps
    | _::hyps ->
        match whd_all env lpar.(k) with
	  | Rel w when w = index -> check (k-1) (index+1) hyps
	  | _ -> raise (IllFormedInd (LocalNonPar (k+1,index,l)))
  in check (nparams-1) (n-nhyps) hyps;
  if not (Array.for_all (noccur_between n ntypes) largs') then
    failwith_non_pos_vect n ntypes largs'

(* Arguments of constructor: check the number of recursive parameters nrecp.
    the first parameters which are constant in recursive arguments
    n is the current depth, nmr is the maximum number of possible
    recursive parameters *)

let check_rec_par (env,n,_,_) hyps nrecp largs =
  let (lpar,_) = List.chop nrecp largs in
  let rec find index =
    function
      | ([],_) -> ()
      | (_,[]) ->
          failwith "number of recursive parameters cannot be greater than the number of parameters."
      | (lp,LocalDef _ :: hyps) -> find (index-1) (lp,hyps)
      | (p::lp,_::hyps) ->
          (match whd_all env p with
	    | Rel w when w = index -> find (index-1) (lp,hyps)
            | _ -> failwith "bad number of recursive parameters")
  in find (n-1) (lpar,List.rev hyps)

let lambda_implicit_lift n a =
  let lambda_implicit a = Lambda(Anonymous,Evar(0,[||]),a) in
  iterate lambda_implicit n (lift n a)

(* This removes global parameters of the inductive types in lc (for
   nested inductive types only ) *)
let abstract_mind_lc ntyps npars lc =
  if npars = 0 then
    lc
  else
    let make_abs =
      List.init ntyps
	(function i -> lambda_implicit_lift npars (Rel (i+1)))
    in
    Array.map (substl make_abs) lc

(* [env] is the typing environment
   [n] is the dB of the last inductive type
   [ntypes] is the number of inductive types in the definition
     (i.e. range of inductives is [n; n+ntypes-1])
   [lra] is the list of recursive tree of each variable
 *)
let ienv_push_var (env, n, ntypes, lra) (x,a,ra) =
 (push_rel (LocalAssum (x,a)) env, n+1, ntypes, (Norec,ra)::lra)

let ienv_push_inductive (env, n, ntypes, ra_env) ((mi,u),lpar) =
  let auxntyp = 1 in
  let specif = lookup_mind_specif env mi in
  let env' =
    let decl = LocalAssum (Anonymous,
                           hnf_prod_applist env (type_of_inductive env (specif,u)) lpar) in
    push_rel decl env in
  let ra_env' =
    (Imbr mi,(Rtree.mk_rec_calls 1).(0)) ::
    List.map (fun (r,t) -> (r,Rtree.lift 1 t)) ra_env in
  (* New index of the inductive types *)
  let newidx = n + auxntyp in
  (env', newidx, ntypes, ra_env')

let rec ienv_decompose_prod (env,_,_,_ as ienv) n c =
  if n=0 then (ienv,c) else
    let c' = whd_all env c in
    match c' with
	Prod(na,a,b) ->
	  let ienv' = ienv_push_var ienv (na,a,mk_norec) in
	  ienv_decompose_prod ienv' (n-1) b
      | _ -> assert false

(* The recursive function that checks positivity and builds the list
   of recursive arguments *)
let check_positivity_one (env, _,ntypes,_ as ienv) hyps nrecp (_,i as ind) indlc =
  let lparams = rel_context_length hyps in
  (* check the inductive types occur positively in [c] *)
  let rec check_pos (env, n, ntypes, ra_env as ienv) c =
    let x,largs = decompose_app (whd_all env c) in
      match x with
	| Prod (na,b,d) ->
	    assert (List.is_empty largs);
            (match weaker_noccur_between env n ntypes b with
		None -> failwith_non_pos_list n ntypes [b]
              | Some b ->
	          check_pos (ienv_push_var ienv (na, b, mk_norec)) d)
	| Rel k ->
            (try
              let (ra,rarg) = List.nth ra_env (k-1) in
	      (match ra with
                  Mrec _ -> check_rec_par ienv hyps nrecp largs
		|  _ -> ());
	      if not (List.for_all (noccur_between n ntypes) largs)
	      then failwith_non_pos_list n ntypes largs
	      else rarg
            with Failure _ | Invalid_argument _ -> mk_norec)
	| Ind ind_kn ->
            (* If the inductive type being defined appears in a
               parameter, then we have an imbricated type *)
            if List.for_all (noccur_between n ntypes) largs then mk_norec
            else check_positive_imbr ienv (ind_kn, largs)
	| err ->
	    if noccur_between n ntypes x &&
              List.for_all (noccur_between n ntypes) largs
	    then mk_norec
	    else failwith_non_pos_list n ntypes (x::largs)

  (* accesses to the environment are not factorised, but is it worth it? *)
  and check_positive_imbr (env,n,ntypes,ra_env as ienv) ((mi,u), largs) =
    let (mib,mip) = lookup_mind_specif env mi in
    let auxnpar = mib.mind_nparams_rec in
    let nonrecpar = mib.mind_nparams - auxnpar in
    let (lpar,auxlargs) =
      try List.chop auxnpar largs
      with Failure _ -> raise (IllFormedInd (LocalNonPos n)) in
      (* If the inductive appears in the args (non params) then the
	 definition is not positive. *)
      if not (List.for_all (noccur_between n ntypes) auxlargs) then
	raise (IllFormedInd (LocalNonPos n));
      (* We do not deal with imbricated mutual inductive types *)
      let auxntyp = mib.mind_ntypes in
	if auxntyp <> 1 then raise (IllFormedInd (LocalNonPos n));
	(* The nested inductive type with parameters removed *)
        let auxlcvect = abstract_mind_lc auxntyp auxnpar mip.mind_nf_lc in
	  (* Extends the environment with a variable corresponding to
	     the inductive def *)
	let (env',_,_,_ as ienv') = ienv_push_inductive ienv ((mi,u),lpar) in
	  (* Parameters expressed in env' *)
	let lpar' = List.map (lift auxntyp) lpar in
	let irecargs =
	  (* fails if the inductive type occurs non positively *)
	  (* with recursive parameters substituted *)
	  Array.map
	    (function c ->
	      let c' = hnf_prod_applist env' c lpar' in
	      (* skip non-recursive parameters *)
	      let (ienv',c') = ienv_decompose_prod ienv' nonrecpar c' in
		check_constructors ienv' false c')
	    auxlcvect in
	(Rtree.mk_rec [|mk_paths (Imbr mi) irecargs|]).(0)

  (* check the inductive types occur positively in the products of C, if
     check_head=true, also check the head corresponds to a constructor of
     the ith type *)

  and check_constructors ienv check_head c =
    let rec check_constr_rec (env,n,ntypes,ra_env as ienv) lrec c =
      let x,largs = decompose_app (whd_all env c) in
	match x with
          | Prod (na,b,d) ->
	      assert (List.is_empty largs);
              let recarg = check_pos ienv b in
              let ienv' = ienv_push_var ienv (na,b,mk_norec) in
		check_constr_rec ienv' (recarg::lrec) d

	  | hd ->
	      if check_head then
                match hd with
		| Rel j when j = (n + ntypes - i - 1) ->
		  check_correct_par ienv hyps (ntypes-i) largs
		| _ ->
		  raise (IllFormedInd LocalNotConstructor)
	      else
		if not (List.for_all (noccur_between n ntypes) largs)
              then raise (IllFormedInd (LocalNonPos n));
	      List.rev lrec
    in check_constr_rec ienv [] c
  in
  let irecargs =
    Array.map
      (fun c ->
        let _,rawc = mind_extract_params lparams c in
          try
	    check_constructors ienv true rawc
          with IllFormedInd err ->
            explain_ind_err (ntypes-i) env lparams c err)
      indlc
  in mk_paths (Mrec ind) irecargs

let prrecarg = function
  | Norec -> str "Norec"
  | Mrec (mind,i) ->
     str "Mrec[" ++ MutInd.debug_print mind ++ pr_comma () ++ int i ++ str "]"
  | Imbr (mind,i) ->
     str "Imbr[" ++ MutInd.debug_print mind ++ pr_comma () ++ int i ++ str "]"

let check_subtree t1 t2 =
  let cmp_labels l1 l2 = l1 == Norec || eq_recarg l1 l2 in
  if not (Rtree.equiv eq_recarg cmp_labels t1 t2)
  then user_err Pp.(str "Bad recursive tree: found " ++ fnl ()
    ++ Rtree.pp_tree prrecarg t1 ++ fnl () ++ str " when expected " ++ fnl ()
    ++ Rtree.pp_tree prrecarg t2)
(* if t1=t2 then () else msg_warning (str"TODO: check recursive positions")*)

let check_positivity env_ar mind params nrecp inds =
  let ntypes = Array.length inds in
  let rc =
    Array.mapi (fun j t -> (Mrec(mind,j),t)) (Rtree.mk_rec_calls ntypes) in
  let lra_ind = List.rev (Array.to_list rc) in
  let lparams = rel_context_length params in
  let ra_env =
    List.init lparams (fun _ -> (Norec,mk_norec)) @ lra_ind in
  let env_ar_par = push_rel_context params env_ar in
  let check_one i mip =
    let ienv = (env_ar_par, 1+lparams, ntypes, ra_env) in
      check_positivity_one ienv params nrecp (mind,i) mip.mind_nf_lc
  in
  let irecargs = Array.mapi check_one inds in
  let wfp = Rtree.mk_rec irecargs in
  Array.iter2 (fun ind wfpi -> check_subtree ind.mind_recargs wfpi) inds wfp

(* Check arities and constructors *)
let check_subtyping_arity_constructor env (subst : Univ.Instance.t) (arcn : constr) numparams is_arity =
  let numchecked = ref 0 in
  let basic_check ev tp =
    if !numchecked < numparams then () else conv_leq ev tp (Term.subst_instance_constr subst tp);
    numchecked := !numchecked + 1
  in
  let check_typ typ typ_env =
    match typ with
    | LocalAssum (_, typ') ->
      begin
       try
          basic_check typ_env typ'; Environ.push_rel typ typ_env
        with NotConvertible -> 
          anomaly ~label:"bad inductive subtyping relation" (Pp.str "Invalid subtyping relation")
      end
    | _ -> anomaly (Pp.str "")
  in
  let typs, codom = dest_prod env arcn in
  let last_env = fold_rel_context_outside check_typ typs ~init:env in
  if not is_arity then basic_check last_env codom else ()

(* Check that the subtyping information inferred for inductive types in the block is correct. *)
(* This check produces a value of the unit type if successful or raises an anomaly if check fails. *)
let check_subtyping cumi paramsctxt env inds =
  let open Univ in
  let numparams = rel_context_nhyps paramsctxt in
  (** In [env] we already have [ Var(0) ... Var(n-1) |- cst ] available.
      We must produce the substitution σ : [ Var(i) -> Var (i + n) | 0 <= i < n]
      and push the constraints [ Var(n) ... Var(2n - 1) |- cst{σ} ], together
      with the cumulativity constraints [ cumul_cst ]. *)
  let uctx = ACumulativityInfo.univ_context cumi in
  let len = AUContext.size uctx in
  let inst = Instance.of_array @@ Array.init len (fun i -> Level.var (i + len)) in

  let other_context = ACumulativityInfo.univ_context cumi in
  let uctx_other = UContext.make (inst, AUContext.instantiate inst other_context) in
  let cumul_cst =
    Array.fold_left_i (fun i csts var ->
        match var with
        | Variance.Irrelevant -> csts
        | Variance.Covariant -> Constraint.add (Level.var i,Le,Level.var (i+len)) csts
        | Variance.Invariant -> Constraint.add (Level.var i,Eq,Level.var (i+len)) csts)
      Constraint.empty (ACumulativityInfo.variance cumi)
  in
  let env = Environ.push_context uctx_other env in
  let env = Environ.add_constraints cumul_cst env in

  (* process individual inductive types: *)
  Array.iter (fun { mind_user_lc = lc; mind_arity = arity } ->
      match arity with
      | RegularArity { mind_user_arity = full_arity} ->
        check_subtyping_arity_constructor env inst full_arity numparams true;
        Array.iter (fun cnt -> check_subtyping_arity_constructor env inst cnt numparams false) lc
      | TemplateArity _ -> ()
    ) inds
    
(************************************************************************)
(************************************************************************)

let print_mutind ind =
  let kn = MutInd.user ind in
  str (ModPath.to_string (KerName.modpath kn) ^ "." ^ Label.to_string (KerName.label kn))

let check_inductive env kn mib =
  Flags.if_verbose Feedback.msg_notice (str "  checking mutind block: " ++ print_mutind kn);
  (* check mind_constraints: should be consistent with env *)
  let env0 =
    match mib.mind_universes with
    | Monomorphic_ind _ -> env
    | Polymorphic_ind auctx ->
      let uctx = Univ.AUContext.repr auctx in
      Environ.push_context uctx env
    | Cumulative_ind cumi -> 
      let uctx = Univ.AUContext.repr (Univ.ACumulativityInfo.univ_context cumi) in
      Environ.push_context uctx env
  in
  (** Locally set the oracle for further typechecking *)
  let env0 = Environ.set_oracle env0 mib.mind_typing_flags.conv_oracle in
  (* check mind_record : TODO ? check #constructor = 1 ? *)
  (* check mind_finite : always OK *)
  (* check mind_ntypes *)
  if Array.length mib.mind_packets <> mib.mind_ntypes then
    user_err Pp.(str "not the right number of packets");
  (* check mind_params_ctxt *)
  let params = mib.mind_params_ctxt in
  let _ = check_ctxt env0 params in
  (* check mind_nparams *)
  if rel_context_nhyps params <> mib.mind_nparams then
    user_err Pp.(str "number the right number of parameters");
  (* mind_packets *)
  (*  - check arities *)
  let env_ar = typecheck_arity env0 params mib.mind_packets in
  (*  - check constructor types *)
  Array.iter (typecheck_one_inductive env_ar params) mib.mind_packets;
  (* check the inferred subtyping relation *)
  let () = 
    match mib.mind_universes with
    | Monomorphic_ind _ | Polymorphic_ind _ -> ()
    | Cumulative_ind acumi ->
      check_subtyping acumi params env_ar mib.mind_packets
  in
  (* check mind_nparams_rec: positivity condition *)
  check_positivity env_ar kn params mib.mind_nparams_rec mib.mind_packets;
  (* check mind_equiv... *)
  (* Now we can add the inductive *)
  add_mind kn mib env


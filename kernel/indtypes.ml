(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Univ
open Term
open Declarations
open Inductive
open Sign
open Environ
open Reduction
open Typeops
open Entries

(* Same as noccur_between but may perform reductions.
   Could be refined more...  *)
let weaker_noccur_between env x nvars t =
  if noccur_between x nvars t then Some t
  else
   let t' = whd_betadeltaiota env t in
   if noccur_between x nvars t' then Some t'
   else None

(************************************************************************)
(* Various well-formedness check for inductive declarations            *)

(* Errors related to inductive constructions *)
type inductive_error =
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * constr * constr
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier * identifier
  | SameNamesOverlap of identifier list
  | NotAnArity of identifier
  | BadEntry

exception InductiveError of inductive_error

(* [check_constructors_names id s cl] checks that all the constructors names
   appearing in [l] are not present in the set [s], and returns the new set
   of names. The name [id] is the name of the current inductive type, used
   when reporting the error. *)

let check_constructors_names id =
  let rec check idset = function
    | [] -> idset
    | c::cl -> 
	if Idset.mem c idset then 
	  raise (InductiveError (SameNamesConstructors (id,c)))
	else
	  check (Idset.add c idset) cl
  in
  check

(* [mind_check_names mie] checks the names of an inductive types declaration,
   and raises the corresponding exceptions when two types or two constructors
   have the same name. *)

let mind_check_names mie =
  let rec check indset cstset = function
    | [] -> ()
    | ind::inds -> 
	let id = ind.mind_entry_typename in
	let cl = ind.mind_entry_consnames in
	if Idset.mem id indset then
	  raise (InductiveError (SameNamesTypes id))
	else
	  let cstset' = check_constructors_names id cstset cl in
	  check (Idset.add id indset) cstset' inds
  in
  check Idset.empty Idset.empty mie.mind_entry_inds
(* The above verification is not necessary from the kernel point of
  vue since inductive and constructors are not referred to by their
  name, but only by the name of the inductive packet and an index. *)

let mind_check_arities env mie =
  let check_arity id c =
    if not (is_arity env c) then 
      raise (InductiveError (NotAnArity id))
  in
  List.iter
    (fun {mind_entry_typename=id; mind_entry_arity=ar} -> check_arity id ar)
    mie.mind_entry_inds

(************************************************************************)
(************************************************************************)

(* Typing the arities and constructor types *)

let is_info_arity env c =
  match dest_arity env c with
    | (_,Prop Null) -> false 
    | (_,Prop Pos)  -> true 
    | (_,Type _)    -> true

let is_info_type env t =
  let s = t.utj_type in
  if s = mk_Set then true
  else if s = mk_Prop then false
  else
    try is_info_arity env t.utj_val
    with UserError _ -> true

(* [infos] is a sequence of pair [islogic,issmall] for each type in
   the product of a constructor or arity *)

let is_small infos = List.for_all (fun (logic,small) -> small) infos
let is_logic_constr infos = List.for_all (fun (logic,small) -> logic) infos

(* An inductive definition is a "unit" if it has only one constructor
   and that all arguments expected by this constructor are 
   logical, this is the case for equality, conjunction of logical properties 
*)
let is_unit constrsinfos =
  match constrsinfos with  (* One info = One constructor *)
   | [constrinfos] -> is_logic_constr constrinfos 
   | [] -> (* type without constructors *) true
   | _ -> false

let rec infos_and_sort env t =
  match kind_of_term t with
    | Prod (name,c1,c2) ->
        let (varj,_) = infer_type env c1 in
	let env1 = Environ.push_rel (name,None,varj.utj_val) env in
	let logic = not (is_info_type env varj) in
	let small = Term.is_small varj.utj_type in
	(logic,small) :: (infos_and_sort env1 c2)
    | Cast (c,_,_) -> infos_and_sort env c
    | _ -> []

let small_unit constrsinfos =
  let issmall = List.for_all is_small constrsinfos 
  and isunit = is_unit constrsinfos in
  issmall, isunit

(* Computing the levels of polymorphic inductive types

   For each inductive type of a block that is of level u_i, we have
   the constraints that u_i >= v_i where v_i is the type level of the
   types of the constructors of this inductive type. Each v_i depends
   of some of the u_i and of an extra (maybe non variable) universe,
   say w_i that summarize all the other constraints. Typically, for
   three inductive types, we could have

   u1,u2,u3,w1 <= u1
   u1       w2 <= u2
      u2,u3,w3 <= u3

   From this system of inequations, we shall deduce

   w1,w2,w3 <= u1
   w1,w2 <= u2
   w1,w2,w3 <= u3
*)   

let extract_level (_,_,_,lc,lev) =
  (* Enforce that the level is not in Prop if more than two constructors *)
  if Array.length lc >= 2 then sup base_univ lev else lev

let inductive_levels arities inds =
  let levels = Array.map pi3 arities in
  let cstrs_levels = Array.map extract_level inds in
  (* Take the transitive closure of the system of constructors *)
  (* level constraints and remove the recursive dependencies *)
  solve_constraints_system levels cstrs_levels

(* This (re)computes informations relevant to extraction and the sort of an
   arity or type constructor; we do not to recompute universes constraints *)

let constraint_list_union =
  List.fold_left Constraint.union Constraint.empty

let infer_constructor_packet env_ar params lc =
  (* builds the typing context "Gamma, I1:A1, ... In:An, params" *)
  let env_ar_par = push_rel_context params env_ar in
  (* type-check the constructors *)
  let jlc,cstl = List.split (List.map (infer_type env_ar_par) lc) in
  let cst = constraint_list_union cstl in
  let jlc = Array.of_list jlc in
  (* generalize the constructor over the parameters *)
  let lc'' = Array.map (fun j -> it_mkProd_or_LetIn j.utj_val params) jlc in
  (* compute the max of the sorts of the products of the constructor type *)
  let level = max_inductive_sort (Array.map (fun j -> j.utj_type) jlc) in
  (* compute *)
  let info = small_unit (List.map (infos_and_sort env_ar_par) lc) in

  (info,lc'',level,cst)

(* Type-check an inductive definition. Does not check positivity
   conditions. *)
let typecheck_inductive env mie =
  if mie.mind_entry_inds = [] then anomaly "empty inductive types declaration";
  (* Check unicity of names *)
  mind_check_names mie;
  mind_check_arities env mie;
  (* Params are typed-checked here *)
  let env_params, params, cst1 = infer_local_decls env mie.mind_entry_params in
  (* We first type arity of each inductive definition *)
  (* This allows to build the environment of arities and to share *)
  (* the set of constraints *)
  let cst, env_arities, rev_arity_list =
    List.fold_left
      (fun (cst,env_ar,l) ind ->
         (* Arities (without params) are typed-checked here *)
	 let arity, cst2 = infer_type env_params ind.mind_entry_arity in
	 (* We do not need to generate the universe of full_arity; if
	    later, after the validation of the inductive definition,
	    full_arity is used as argument or subject to cast, an
	    upper universe will be generated *)
	 let full_arity = it_mkProd_or_LetIn arity.utj_val params in
	 let cst = Constraint.union cst cst2 in
	 let id = ind.mind_entry_typename in
	 let env_ar' = push_rel (Name id, None, full_arity) env_ar in
	 let lev =
	   (* Decide that if the conclusion is not explicitly Type *)
	   (* then the inductive type is not polymorphic *)
	   match kind_of_term (snd (decompose_prod_assum arity.utj_val)) with
	   | Sort (Type u) -> Some u
	   | _ -> None in
         (cst,env_ar',(id,full_arity,lev)::l))
      (cst1,env,[])
      mie.mind_entry_inds in

  let arity_list = List.rev rev_arity_list in

  (* Now, we type the constructors (without params) *)
  let inds,cst =
    List.fold_right2
      (fun ind arity_data (inds,cst) ->
	 let (info,lc',cstrs_univ,cst') =
	   infer_constructor_packet env_arities params ind.mind_entry_lc in
	 let consnames = ind.mind_entry_consnames in
	 let ind' = (arity_data,consnames,info,lc',cstrs_univ) in
	 (ind'::inds, Constraint.union cst cst'))
      mie.mind_entry_inds
      arity_list
      ([],cst) in

  let inds = Array.of_list inds in
  let arities = Array.of_list arity_list in
  let param_ccls = List.fold_left (fun l (_,b,p) ->
    if b = None then 
      let _,c = dest_prod_assum env p in
      let u = match kind_of_term c with Sort (Type u) -> Some u | _ -> None in
      u::l
    else 
      l) [] params in

  (* Compute/check the sorts of the inductive types *)
  let ind_min_levels = inductive_levels arities inds in
  let inds, cst =
    array_fold_map2' (fun ((id,full_arity,ar_level),cn,info,lc,_) lev cst ->
      let sign, s = dest_arity env full_arity in
      let status,cst = match s with
      | Type _ when ar_level <> None (* Explicitly polymorphic *) ->
	  (* The polymorphic level is a function of the level of the *)
	  (* conclusions of the parameters *)
	  Inr (param_ccls, lev), cst
      | Type u (* Not an explicit occurrence of Type *) ->
	  Inl (info,full_arity,s), enforce_geq u lev cst
      | Prop Pos when engagement env <> Some ImpredicativeSet ->
	  (* Predicative set: check that the content is indeed predicative *)
	  if not (is_empty_univ lev) & not (is_base_univ lev) then
	    error "Large non-propositional inductive types must be in Type";
	  Inl (info,full_arity,s), cst
      | Prop _ ->
	  Inl (info,full_arity,s), cst in
      (id,cn,lc,(sign,status)),cst)
      inds ind_min_levels cst in

  (env_arities, params, inds, cst)

(************************************************************************)
(************************************************************************)
(* Positivity *)

type ill_formed_ind =
  | LocalNonPos of int
  | LocalNotEnoughArgs of int
  | LocalNotConstructor
  | LocalNonPar of int * int

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
	raise (InductiveError (NonPos (env,c',mkRel (kt+nbpar))))
    | LocalNotEnoughArgs kt -> 
	raise (InductiveError 
		 (NotEnoughArgs (env,c',mkRel (kt+nbpar))))
    | LocalNotConstructor ->
	raise (InductiveError 
		 (NotConstructor (env,c',mkRel (ntyp+nbpar))))
    | LocalNonPar (n,l) ->
	raise (InductiveError 
		 (NonPar (env,c',n,mkRel (nbpar-n+1), mkRel (l+nbpar))))

let failwith_non_pos n ntypes c =
  for k = n to n + ntypes - 1 do
    if not (noccurn k c) then raise (IllFormedInd (LocalNonPos (k-n+1)))
  done

let failwith_non_pos_vect n ntypes v =
  Array.iter (failwith_non_pos n ntypes) v;
  anomaly "failwith_non_pos_vect: some k in [n;n+ntypes-1] should occur"

let failwith_non_pos_list n ntypes l =
  List.iter (failwith_non_pos n ntypes) l;
  anomaly "failwith_non_pos_list: some k in [n;n+ntypes-1] should occur"

(* Check the inductive type is called with the expected parameters *)
let check_correct_par (env,n,ntypes,_) hyps l largs =
  let nparams = rel_context_nhyps hyps in
  let largs = Array.of_list largs in
  if Array.length largs < nparams then 
    raise (IllFormedInd (LocalNotEnoughArgs l));
  let (lpar,largs') = array_chop nparams largs in
  let nhyps = List.length hyps in
  let rec check k index = function
    | [] -> ()
    | (_,Some _,_)::hyps -> check k (index+1) hyps
    | _::hyps ->
        match kind_of_term (whd_betadeltaiota env lpar.(k)) with
	  | Rel w when w = index -> check (k-1) (index+1) hyps
	  | _ -> raise (IllFormedInd (LocalNonPar (k+1,l)))
  in check (nparams-1) (n-nhyps) hyps;
  if not (array_for_all (noccur_between n ntypes) largs') then 
    failwith_non_pos_vect n ntypes largs'

(* Computes the maximum number of recursive parameters : 
    the first parameters which are constant in recursive arguments 
    n is the current depth, nmr is the maximum number of possible 
    recursive parameters *)

let compute_rec_par (env,n,_,_) hyps nmr largs = 
if nmr = 0 then 0 else
(* start from 0, hyps will be in reverse order *)
  let (lpar,_) = list_chop nmr largs in
  let rec find k index = 
      function 
	  ([],_) -> nmr
	| (_,[]) -> assert false (* |hyps|>=nmr *)
	| (lp,(_,Some _,_)::hyps) -> find k (index-1) (lp,hyps)
	| (p::lp,_::hyps) ->
       ( match kind_of_term (whd_betadeltaiota env p) with
	  | Rel w when w = index -> find (k+1) (index-1) (lp,hyps)
          | _ -> k)
  in find 0 (n-1) (lpar,List.rev hyps)

(* This removes global parameters of the inductive types in lc (for
   nested inductive types only ) *)
let abstract_mind_lc env ntyps npars lc = 
  if npars = 0 then 
    lc
  else 
    let make_abs = 
      list_tabulate
	(function i -> lambda_implicit_lift npars (mkRel (i+1))) ntyps 
    in 
    Array.map (substl make_abs) lc

(* [env] is the typing environment
   [n] is the dB of the last inductive type
   [ntypes] is the number of inductive types in the definition
     (i.e. range of inductives is [n; n+ntypes-1])
   [lra] is the list of recursive tree of each variable
 *) 
let ienv_push_var (env, n, ntypes, lra) (x,a,ra) =
 (push_rel (x,None,a) env, n+1, ntypes, (Norec,ra)::lra)

let ienv_push_inductive (env, n, ntypes, ra_env) (mi,lpar) =
  let auxntyp = 1 in
  let specif = lookup_mind_specif env mi in
  let env' =
    push_rel (Anonymous,None,
              hnf_prod_applist env (type_of_inductive env specif) lpar) env in
  let ra_env' = 
    (Imbr mi,Rtree.mk_param 0) ::
    List.map (fun (r,t) -> (r,Rtree.lift 1 t)) ra_env in
  (* New index of the inductive types *)
  let newidx = n + auxntyp in
  (env', newidx, ntypes, ra_env')

let array_min nmr a = if nmr = 0 then 0 else
  Array.fold_left (fun k (nmri,_) -> min k nmri) nmr a

(* The recursive function that checks positivity and builds the list
   of recursive arguments *)
let check_positivity_one (env, _,ntypes,_ as ienv) hyps i indlc =
  let lparams = rel_context_length hyps in
  let nmr = rel_context_nhyps hyps in
  (* check the inductive types occur positively in [c] *)
  let rec check_pos (env, n, ntypes, ra_env as ienv) nmr c = 
    let x,largs = decompose_app (whd_betadeltaiota env c) in
    match kind_of_term x with
      | Prod (na,b,d) ->
	  assert (largs = []);
          (match weaker_noccur_between env n ntypes b with
              None -> failwith_non_pos_list n ntypes [b]
            | Some b ->
	        check_pos (ienv_push_var ienv (na, b, mk_norec)) nmr d)
      | Rel k ->
           (try let (ra,rarg) = List.nth ra_env (k-1) in 
		let nmr1 =
	       (match ra with
                 Mrec _ -> compute_rec_par ienv hyps nmr largs
		  |  _ -> nmr)
		in 
		  if not (List.for_all (noccur_between n ntypes) largs)
	          then failwith_non_pos_list n ntypes largs
		  else (nmr1,rarg)
            with Failure _ | Invalid_argument _ -> (nmr,mk_norec))
      | Ind ind_kn ->
          (* If the inductive type being defined appears in a
             parameter, then we have an imbricated type *)
          if List.for_all (noccur_between n ntypes) largs then (nmr,mk_norec)
          else check_positive_imbr ienv nmr (ind_kn, largs)
      | err -> 
	  if noccur_between n ntypes x &&
             List.for_all (noccur_between n ntypes) largs 
	  then (nmr,mk_norec)
	  else failwith_non_pos_list n ntypes (x::largs)

  (* accesses to the environment are not factorised, but is it worth? *)
  and check_positive_imbr (env,n,ntypes,ra_env as ienv) nmr (mi, largs) =
    let (mib,mip) = lookup_mind_specif env mi in
    let auxnpar = mib.mind_nparams_rec in
    let (lpar,auxlargs) =
      try list_chop auxnpar largs 
      with Failure _ -> raise (IllFormedInd (LocalNonPos n)) in 
    (* If the inductive appears in the args (non params) then the
       definition is not positive. *)
    if not (List.for_all (noccur_between n ntypes) auxlargs) then
      raise (IllFormedInd (LocalNonPos n));
    (* We do not deal with imbricated mutual inductive types *)
    let auxntyp = mib.mind_ntypes in 
    if auxntyp <> 1 then raise (IllFormedInd (LocalNonPos n));
    (* The nested inductive type with parameters removed *)
    let auxlcvect = abstract_mind_lc env auxntyp auxnpar mip.mind_nf_lc in
    (* Extends the environment with a variable corresponding to
       the inductive def *)
    let (env',_,_,_ as ienv') = ienv_push_inductive ienv (mi,lpar) in
    (* Parameters expressed in env' *)
    let lpar' = List.map (lift auxntyp) lpar in
    let irecargs_nmr = 
      (* fails if the inductive type occurs non positively *)
      (* when substituted *) 
      Array.map 
	(function c -> 
	  let c' = hnf_prod_applist env' c lpar' in 
	  check_constructors ienv' false nmr c') 
	auxlcvect
    in
    let irecargs = Array.map snd irecargs_nmr
    and nmr' = array_min nmr irecargs_nmr
    in 
    (nmr',(Rtree.mk_rec [|mk_paths (Imbr mi) irecargs|]).(0))
  
  (* check the inductive types occur positively in the products of C, if
     check_head=true, also check the head corresponds to a constructor of
     the ith type *) 

  and check_constructors ienv check_head nmr c = 
    let rec check_constr_rec (env,n,ntypes,ra_env as ienv) nmr lrec c = 
      let x,largs = decompose_app (whd_betadeltaiota env c) in
      match kind_of_term x with

        | Prod (na,b,d) -> 
	    assert (largs = []);
            let nmr',recarg = check_pos ienv nmr b in 
            let ienv' = ienv_push_var ienv (na,b,mk_norec) in
	    check_constr_rec ienv' nmr' (recarg::lrec) d

	| hd ->
	    if check_head then
	      if hd = Rel (n+ntypes-i-1) then
		check_correct_par ienv hyps (ntypes-i) largs
	      else
		raise (IllFormedInd LocalNotConstructor)
	    else
	      if not (List.for_all (noccur_between n ntypes) largs)
              then raise (IllFormedInd (LocalNonPos n));
	    (nmr,List.rev lrec)
    in check_constr_rec ienv nmr [] c
  in
  let irecargs_nmr =
     Array.map
      (fun c ->
        let _,rawc = mind_extract_params lparams c in
        try
	  check_constructors ienv true nmr rawc
        with IllFormedInd err -> 
	  explain_ind_err (ntypes-i) env lparams c err)
      indlc
  in
  let irecargs = Array.map snd irecargs_nmr
  and nmr' = array_min nmr irecargs_nmr
  in (nmr', mk_paths (Mrec i) irecargs)

let check_positivity env_ar params inds =
  let ntypes = Array.length inds in
  let lra_ind =
    List.rev (list_tabulate (fun j -> (Mrec j, Rtree.mk_param j)) ntypes) in
  let lparams = rel_context_length params in
  let nmr = rel_context_nhyps params in
  let check_one i (_,_,lc,_) =
    let ra_env =
      list_tabulate (fun _ -> (Norec,mk_norec)) lparams @ lra_ind in
    let ienv = (env_ar, 1+lparams, ntypes, ra_env) in
    check_positivity_one ienv params i lc 
  in
  let irecargs_nmr = Array.mapi check_one inds in 
  let irecargs = Array.map snd irecargs_nmr
  and nmr' = array_min nmr irecargs_nmr
  in (nmr',Rtree.mk_rec irecargs)


(************************************************************************)
(************************************************************************)
(* Build the inductive packet *)
    
(* Elimination sorts *)
let is_recursive = Rtree.is_infinite
(*  let rec one_is_rec rvec = 
    List.exists (function Mrec(i) -> List.mem i listind 
                   | Imbr(_,lvec) -> array_exists one_is_rec lvec
                   | Norec -> false) rvec
  in 
  array_exists one_is_rec
*)

(* Allowed eliminations *)

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
  (* which otherwise allows to simulate the inconsistent system Type:Type *)
  | InProp when isunit -> if issmall then all_sorts else small_sorts

  (* Other propositions: elimination only to Prop *)
  | InProp -> logical_sorts

let fold_inductive_blocks f =
  Array.fold_left (fun acc (_,_,lc,(arsign,_)) ->
    f (Array.fold_left f acc lc) (it_mkProd_or_LetIn (* dummy *) mkSet arsign))

let used_section_variables env inds =
  let ids = fold_inductive_blocks
    (fun l c -> Idset.union (Environ.global_vars_set env c) l)
      Idset.empty inds in
  keep_hyps env ids

let build_inductive env env_ar params isrecord isfinite inds nmr recargs cst =
  let ntypes = Array.length inds in
  (* Compute the set of used section variables *)
  let hyps =  used_section_variables env inds in
  let nparamargs = rel_context_nhyps params in
  (* Check one inductive *)
  let build_one_packet (id,cnames,lc,(ar_sign,ar_kind)) recarg =
    (* Type of constructors in normal form *)
    let splayed_lc = Array.map (dest_prod_assum env_ar) lc in
    let nf_lc = Array.map (fun (d,b) -> it_mkProd_or_LetIn b d) splayed_lc in
    let nf_lc = if nf_lc = lc then lc else nf_lc in
    let consnrealargs =
      Array.map (fun (d,_) -> rel_context_length d - rel_context_length params)
	splayed_lc in
    (* Elimination sorts *)
    let arkind,kelim = match ar_kind with
    | Inr (param_levels,lev) ->
	Polymorphic {
	  poly_param_levels = param_levels;
	  poly_level = lev; 
	}, all_sorts
    | Inl ((issmall,isunit),ar,s) ->
	let isunit = isunit && ntypes = 1 && not (is_recursive recargs.(0)) in
	let kelim = allowed_sorts issmall isunit s in
	Monomorphic {
	  mind_user_arity = ar;
	  mind_sort = s; 
	}, kelim in
    let nconst, nblock = ref 0, ref 0 in 
    let transf num =
      let arity = List.length (dest_subterms recarg).(num) in
      if arity = 0 then 
	let p  = (!nconst, 0) in
	incr nconst; p
      else 
	let p = (!nblock + 1, arity) in
	incr nblock; p
     (* les tag des constructeur constant commence a 0,
	les tag des constructeur non constant a 1 (0 => accumulator) *)
    in 
    let rtbl = Array.init (List.length cnames) transf in
    (* Build the inductive packet *)
    { mind_typename = id;
      mind_arity = arkind;
      mind_arity_ctxt = ar_sign;
      mind_nrealargs = rel_context_nhyps ar_sign - nparamargs;
      mind_kelim = kelim;
      mind_consnames = Array.of_list cnames;
      mind_consnrealdecls = consnrealargs;
      mind_user_lc = lc;
      mind_nf_lc = nf_lc;
      mind_recargs = recarg;
      mind_nb_constant = !nconst;
      mind_nb_args = !nblock;
      mind_reloc_tbl = rtbl;
    } in
  let packets = array_map2 build_one_packet inds recargs in
  (* Build the mutual inductive *)
  { mind_record = isrecord;
    mind_ntypes = ntypes;
    mind_finite = isfinite;
    mind_hyps = hyps;
    mind_nparams = nparamargs;
    mind_nparams_rec = nmr;  
    mind_params_ctxt = params;
    mind_packets = packets;
    mind_constraints = cst;
    mind_equiv = None;
  }

(************************************************************************)
(************************************************************************)

let check_inductive env mie =
  (* First type-check the inductive definition *)
  let (env_ar, params, inds, cst) = typecheck_inductive env mie in
  (* Then check positivity conditions *)
  let (nmr,recargs) = check_positivity env_ar params inds in
  (* Build the inductive packets *)
  build_inductive env env_ar params mie.mind_entry_record mie.mind_entry_finite
    inds nmr recargs cst

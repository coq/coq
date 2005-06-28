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

(* [check_constructors_names id s cl] checks that all the constructors names
   appearing in [l] are not present in the set [s], and returns the new set
   of names. The name [id] is the name of the current inductive type, used
   when reporting the error. *)

(************************************************************************)
(* Various well-formedness check for inductive declarations            *)

type inductive_error =
  (* These are errors related to inductive constructions in this module *)
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * constr * constr
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier * identifier
  | SameNamesOverlap of identifier list
  | NotAnArity of identifier
  | BadEntry
  (* These are errors related to recursors building in Indrec *)
  | NotAllowedCaseAnalysis of bool * sorts * inductive
  | BadInduction of bool * identifier * sorts
  | NotMutualInScheme

exception InductiveError of inductive_error

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
let is_logic_arity infos =
  List.for_all (fun (logic,small) -> logic || small) infos

(* An inductive definition is a "unit" if it has only one constructor
   and that all arguments expected by this constructor are 
   logical, this is the case for equality, conjonction of logical properties 
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
    | Cast (c,_) -> infos_and_sort env c
    | _ -> []

let small_unit constrsinfos =
  let issmall = List.for_all is_small constrsinfos 
  and isunit = is_unit constrsinfos in
  issmall, isunit

(* This (re)computes informations relevant to extraction and the sort of an
   arity or type constructor; we do not to recompute universes constraints *)

(* [smax] is the max of the sorts of the products of the constructor type *)

let enforce_type_constructor env arsort smax cst =
  match smax, arsort with
    | Type uc, Type ua -> enforce_geq ua uc cst
    | Type uc, Prop Pos when engagement env <> Some ImpredicativeSet ->
        error "Large non-propositional inductive types must be in Type"
    | _,_ -> cst

let type_one_constructor env_ar_par params arsort c =
  let infos = infos_and_sort env_ar_par c in

  (* Each constructor is typed-checked here *)
  let (j,cst) = infer_type env_ar_par c in
  let full_cstr_type = it_mkProd_or_LetIn j.utj_val params in

  (* If the arity is at some level Type arsort, then the sort of the
     constructor must be below arsort; here we consider constructors with the
     global parameters (which add a priori more constraints on their sort) *)
  let cst2 = enforce_type_constructor env_ar_par arsort j.utj_type cst in

  (infos, full_cstr_type, cst2)

let infer_constructor_packet env_ar params arsort vc =
  let env_ar_par = push_rel_context params env_ar in
  let (constrsinfos,jlc,cst) = 
    List.fold_right
      (fun c (infosl,l,cst) ->
	 let (infos,ct,cst') =
	   type_one_constructor env_ar_par params arsort c in
	 (infos::infosl,ct::l, Constraint.union cst cst'))
      vc
      ([],[],Constraint.empty) in
  let vc' = Array.of_list jlc in
  let issmall,isunit = small_unit constrsinfos in
  (issmall,isunit,vc', cst)

(* Type-check an inductive definition. Does not check positivity
   conditions. *)
let typecheck_inductive env mie =
  if mie.mind_entry_inds = [] then anomaly "empty inductive types declaration";
  (* Check unicity of names *)
  mind_check_names mie;
  mind_check_arities env mie;
  (* We first type params and arity of each inductive definition *)
  (* This allows to build the environment of arities and to share *)
  (* the set of constraints *)
  let cst, arities, rev_params_arity_list =
    List.fold_left
      (fun (cst,arities,l) ind ->
         (* Params are typed-checked here *)
	 let params = ind.mind_entry_params in
	 let env_params, params, cst1 =
           infer_local_decls env params in
         (* Arities (without params) are typed-checked here *)
	 let arity, cst2 =
           infer_type env_params ind.mind_entry_arity in
	 (* We do not need to generate the universe of full_arity; if
	    later, after the validation of the inductive definition,
	    full_arity is used as argument or subject to cast, an
	    upper universe will be generated *)
	 let id = ind.mind_entry_typename in
	 let full_arity = it_mkProd_or_LetIn arity.utj_val params in
	 Constraint.union cst (Constraint.union cst1 cst2),
	 Sign.add_rel_decl (Name id, None, full_arity) arities,
         (params, id, full_arity, arity.utj_val)::l)
      (Constraint.empty,empty_rel_context,[])
      mie.mind_entry_inds in

  let env_arities = push_rel_context arities env in

  let params_arity_list = List.rev rev_params_arity_list in

  (* Now, we type the constructors (without params) *)
  let inds,cst =
    List.fold_right2
      (fun ind (params,id,full_arity,short_arity) (inds,cst) ->
	 let (_,arsort) = dest_arity env full_arity in
	 let lc = ind.mind_entry_lc in
	 let (issmall,isunit,lc',cst') =
	   infer_constructor_packet env_arities params arsort lc in
	 let consnames = ind.mind_entry_consnames in
	 let ind' = (params,id,full_arity,consnames,issmall,isunit,lc')
	 in
	 (ind'::inds, Constraint.union cst cst'))
      mie.mind_entry_inds
      params_arity_list
      ([],cst) in
  (env_arities, Array.of_list inds, cst)

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

let failwith_non_pos_vect n ntypes v =
  for i = 0 to Array.length v - 1 do
    for k = n to n + ntypes - 1 do
      if not (noccurn k v.(i)) then raise (IllFormedInd (LocalNonPos (k-n+1)))
    done
  done;
  anomaly "failwith_non_pos_vect: some k in [n;n+ntypes-1] should occur in v"

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
  let env' =
    push_rel (Anonymous,None,
              hnf_prod_applist env (type_of_inductive env mi) lpar) env in
  let ra_env' = 
    (Imbr mi,Rtree.mk_param 0) ::
    List.map (fun (r,t) -> (r,Rtree.lift 1 t)) ra_env in
  (* New index of the inductive types *)
  let newidx = n + auxntyp in
  (env', newidx, ntypes, ra_env')

(* The recursive function that checks positivity and builds the list
   of recursive arguments *)
let check_positivity_one (env, _,ntypes,_ as ienv) hyps i indlc =
  let nparams = rel_context_length hyps in
  (* check the inductive types occur positively in [c] *)
  let rec check_pos (env, n, ntypes, ra_env as ienv) c = 
    let x,largs = decompose_app (whd_betadeltaiota env c) in
    match kind_of_term x with
      | Prod (na,b,d) ->
	  assert (largs = []);
          let b = whd_betadeltaiota env b in
          if not (noccur_between n ntypes b) then
	    raise (IllFormedInd (LocalNonPos n));
	  check_pos (ienv_push_var ienv (na, b, mk_norec)) d
      | Rel k ->
          let (ra,rarg) =
            try List.nth ra_env (k-1)
            with Failure _ | Invalid_argument _ -> (Norec,mk_norec) in
          (match ra with
              Mrec _ -> check_correct_par ienv hyps (k-n+1) largs
            | _ ->
                if not (List.for_all (noccur_between n ntypes) largs)
	        then raise (IllFormedInd (LocalNonPos n)));
          rarg
      | Ind ind_kn ->
          (* If the inductive type being defined appears in a
             parameter, then we have an imbricated type *)
          if List.for_all (noccur_between n ntypes) largs then mk_norec
          else check_positive_imbr ienv (ind_kn, largs)
      | err -> 
	  if noccur_between n ntypes x &&
             List.for_all (noccur_between n ntypes) largs 
	  then mk_norec
	  else raise (IllFormedInd (LocalNonPos n))

  (* accesses to the environment are not factorised, but does it worth
     it? *)
  and check_positive_imbr (env,n,ntypes,ra_env as ienv) (mi, largs) =
    let (mib,mip) = lookup_mind_specif env mi in
    let auxnpar = mip.mind_nparams in
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
    let irecargs = 
      (* fails if the inductive type occurs non positively *)
      (* when substituted *) 
      Array.map 
	(function c -> 
	  let c' = hnf_prod_applist env' c lpar' in 
	  check_constructors ienv' false c') 
	auxlcvect
    in 
    (Rtree.mk_rec [|mk_paths (Imbr mi) irecargs|]).(0)
  
  (* check the inductive types occur positively in the products of C, if
     check_head=true, also check the head corresponds to a constructor of
     the ith type *) 

  and check_constructors ienv check_head c = 
    let rec check_constr_rec (env,n,ntypes,ra_env as ienv) lrec c = 
      let x,largs = decompose_app (whd_betadeltaiota env c) in
      match kind_of_term x with

        | Prod (na,b,d) -> 
	    assert (largs = []);
            let recarg = check_pos ienv b in 
            let ienv' = ienv_push_var ienv (na,b,mk_norec) in
	    check_constr_rec ienv' (recarg::lrec) d

	| hd ->
	    if check_head then
	      if hd = Rel (n+ntypes-i-1) then
		check_correct_par ienv hyps (ntypes-i) largs
	      else
		raise (IllFormedInd LocalNotConstructor)
	    else
	      if not (List.for_all (noccur_between n ntypes) largs)
              then raise (IllFormedInd (LocalNonPos n));
	    List.rev lrec
    in check_constr_rec ienv [] c
  in
  mk_paths (Mrec i)
    (Array.map
      (fun c ->
        let c = body_of_type c in
        let sign, rawc = mind_extract_params nparams c in
        let env' = push_rel_context sign env in
        try
	  check_constructors ienv true rawc
        with IllFormedInd err -> 
	  explain_ind_err (ntypes-i) env nparams c err)
      indlc)

let check_positivity env_ar inds =
  let ntypes = Array.length inds in
  let lra_ind =
    List.rev (list_tabulate (fun j -> (Mrec j, Rtree.mk_param j)) ntypes) in
  let check_one i (params,_,_,_,_,_,lc) =
    let nparams = rel_context_length params in
    let ra_env =
      list_tabulate (fun _ -> (Norec,mk_norec)) nparams @ lra_ind in
    let ienv = (env_ar, 1+nparams, ntypes, ra_env) in
    check_positivity_one ienv params i lc in
  Rtree.mk_rec (Array.mapi check_one inds)


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

let all_sorts = [InProp;InSet;InType]
let impredicative_sorts = [InProp;InSet]
let logical_sorts = [InProp]

let allowed_sorts env issmall isunit = function
  | Type _ -> all_sorts
  | Prop Pos -> 
      if issmall then all_sorts
      else impredicative_sorts
  | Prop Null -> 
(* Added InType which is derivable :when the type is unit and small *)
(* unit+small types have all elimination 
   In predicative system, the 
   other inductive definitions have only Prop elimination.
   In impredicative system, large unit type have also Set elimination
*)   if isunit then 
	if issmall then all_sorts
	else if Environ.engagement env = None 
        then logical_sorts else impredicative_sorts
      else logical_sorts

let build_inductive env env_ar finite inds recargs cst =
  let ntypes = Array.length inds in
  (* Compute the set of used section variables *)
  let ids = 
    Array.fold_left 
      (fun acc (_,_,ar,_,_,_,lc) -> 
	 Idset.union (Environ.global_vars_set env (body_of_type ar))
	   (Array.fold_left
	      (fun acc c ->
                Idset.union (global_vars_set env (body_of_type c)) acc)
	      acc
	      lc))
      Idset.empty inds in
  let hyps = keep_hyps env ids in
  (* Check one inductive *)
  let build_one_packet (params,id,ar,cnames,issmall,isunit,lc) recarg =
    (* Arity in normal form *)
    let nparamargs = rel_context_nhyps params in
    let (ar_sign,ar_sort) = dest_arity env ar in
    let nf_ar =
      if isArity (body_of_type ar) then ar
      else it_mkProd_or_LetIn (mkSort ar_sort) ar_sign in
    (* Type of constructors in normal form *)
    let splayed_lc = Array.map (dest_prod_assum env_ar) lc in
    let nf_lc =
      array_map2 (fun (d,b) c -> it_mkProd_or_LetIn b d) splayed_lc lc in
    let nf_lc = if nf_lc = lc then lc else nf_lc in
    (* Elimination sorts *)
    let isunit = isunit && ntypes = 1 && (not (is_recursive recargs.(0))) in
    let kelim = allowed_sorts env issmall isunit ar_sort in
    (* Build the inductive packet *)
    { mind_typename = id;
      mind_nparams = nparamargs;
      mind_params_ctxt = params;
      mind_user_arity  = ar;
      mind_nf_arity = nf_ar;
      mind_nrealargs = rel_context_nhyps ar_sign - nparamargs;
      mind_sort = ar_sort;
      mind_kelim = kelim;
      mind_consnames = Array.of_list cnames;
      mind_user_lc = lc;
      mind_nf_lc = nf_lc;
      mind_recargs = recarg;
    } in
  let packets = array_map2 build_one_packet inds recargs in
  (* Build the mutual inductive *)
  { mind_ntypes = ntypes;
    mind_finite = finite;
    mind_hyps = hyps;
    mind_packets = packets;
    mind_constraints = cst;
    mind_equiv = None;
  }

(************************************************************************)
(************************************************************************)

let check_inductive env mie =
  (* First type-check the inductive definition *)
  let (env_arities, inds, cst) = typecheck_inductive env mie in
  (* Then check positivity conditions *)
  let recargs = check_positivity env_arities inds in
  (* Build the inductive packets *)
  build_inductive env env_arities mie.mind_entry_finite inds recargs cst


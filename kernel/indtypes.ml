(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

(* [check_constructors_names id s cl] checks that all the constructors names
   appearing in [l] are not present in the set [s], and returns the new set
   of names. The name [id] is the name of the current inductive type, used
   when reporting the error. *)

(*s Declaration. *)

type one_inductive_entry = {
  mind_entry_nparams : int;
  mind_entry_params : (identifier * local_entry) list;
  mind_entry_typename : identifier;
  mind_entry_arity : constr;
  mind_entry_consnames : identifier list;
  mind_entry_lc : constr list }

type mutual_inductive_entry = {
  mind_entry_finite : bool;
  mind_entry_inds : one_inductive_entry list }

(***********************************************************************)
(* Various well-formedness check for inductive declarations            *)

type inductive_error =
  (* These are errors related to inductive constructions in this module *)
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * constr * constr
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier * identifier
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

(* [mind_extract_params mie] extracts the params from an inductive types
   declaration, and checks that they are all present (and all the same)
   for all the given types. *)

let mind_extract_params = decompose_prod_n_assum

let mind_check_arities env mie =
  let check_arity id c =
    if not (is_arity env c) then 
      raise (InductiveError (NotAnArity id))
  in
  List.iter
    (fun {mind_entry_typename=id; mind_entry_arity=ar} -> check_arity id ar)
    mie.mind_entry_inds

(***********************************************************************)
(***********************************************************************)

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
  (* CP : relax this constraint which was related 
          to extraction 
          && is_logic_arity arinfos *)
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

let enforce_type_constructor arsort smax cst =
  match smax, arsort with
    | Type uc, Type ua -> enforce_geq ua uc cst
    | _,_ -> cst

let type_one_constructor env_ar_par params arsort c =
  let infos = infos_and_sort env_ar_par c in

  (* Each constructor is typed-checked here *)
  let (j,cst) = infer_type env_ar_par c in
  let full_cstr_type = it_mkProd_or_LetIn j.utj_val params in

  (* If the arity is at some level Type arsort, then the sort of the
     constructor must be below arsort; here we consider constructors with the
     global parameters (which add a priori more constraints on their sort) *)
  let cst2 = enforce_type_constructor arsort j.utj_type cst in

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
let type_inductive env mie =
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
	   infer_constructor_packet env_arities params arsort lc
	 in
	 let nparams = ind.mind_entry_nparams in
	 let consnames = ind.mind_entry_consnames in
	 let ind' = (params,nparams,id,full_arity,consnames,issmall,isunit,lc')
	 in
	 (ind'::inds, Constraint.union cst cst'))
      mie.mind_entry_inds
      params_arity_list
      ([],cst) in
  (env_arities, inds, cst)

(***********************************************************************)
(***********************************************************************)
let all_sorts = [InProp;InSet;InType]
let impredicative_sorts = [InProp;InSet]
let logical_sorts = [InProp]

let allowed_sorts issmall isunit = function
  | Type _ -> all_sorts
  | Prop Pos -> 
      if issmall then all_sorts
      else impredicative_sorts
  | Prop Null -> 
(* Added InType which is derivable :when the type is unit and small *)
      if isunit then 
	if issmall then all_sorts
	else impredicative_sorts
      else logical_sorts

type ill_formed_ind =
  | LocalNonPos of int
  | LocalNotEnoughArgs of int
  | LocalNotConstructor
  | LocalNonPar of int * int

exception IllFormedInd of ill_formed_ind

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
let check_correct_par env hyps nparams ntypes n l largs =
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

(* This removes global parameters of the inductive types in lc *)
let abstract_mind_lc env ntyps npars lc = 
  if npars = 0 then 
    lc
  else 
    let make_abs = 
      list_tabulate
	(function i -> lambda_implicit_lift npars (mkRel (i+1))) ntyps 
    in 
    Array.map (substl make_abs) lc

(* The recursive function that checks positivity and builds the list
   of recursive arguments *)
let check_positivity env ntypes hyps nparams i indlc =
  let nhyps = List.length hyps in
  (* check the inductive types occur positively in [c] *)
  let rec check_pos env n c = 
    let x,largs = decompose_app (whd_betadeltaiota env c) in
    match kind_of_term x with
      | Prod (na,b,d) ->
	  assert (largs = []);
          if not (noccur_between n ntypes b) then
	    raise (IllFormedInd (LocalNonPos n));
	  check_pos (push_rel (na, None, b) env) (n+1) d
      | Rel k ->
          if k >= n && k<n+ntypes then begin
	    check_correct_par env hyps nparams ntypes n (k-n+1) largs;
	    Mrec(n+ntypes-k-1)
          end else if List.for_all (noccur_between n ntypes) largs then 
	    if (n-nhyps) <= k & k <= (n-1) 
	    then Param(n-1-k)
            else Norec
	  else
	    raise (IllFormedInd (LocalNonPos n))
      | Ind ind_sp ->
          (* If the inductive type being defined or a parameter appears as
             parameter, then we have an imbricated type *)
          if List.for_all (noccur_between n ntypes) largs then
            (* If parameters are passed but occur negatively, then
               the argument is considered non recursive *)
            if List.for_all (noccur_between (n-nhyps) nhyps) largs 
            then Norec
            else
              try check_positive_imbr env n ind_sp largs
              with IllFormedInd _ -> Norec
          else check_positive_imbr env n ind_sp largs
      | err -> 
	  if noccur_between n ntypes x &&
             List.for_all (noccur_between n ntypes) largs 
	  then Norec
	  else raise (IllFormedInd (LocalNonPos n))

  (* accesses to the environment are not factorised, but does it worth
     it? *)
  and check_positive_imbr env n mi largs =
    let (mib,mip) = lookup_mind_specif env mi in
    let auxnpar = mip.mind_nparams in
    let (lpar,auxlargs) =
      try list_chop auxnpar largs 
      with Failure _ -> raise (IllFormedInd (LocalNonPos n)) in 
    (* If the inductive appears in the args (non params) then the
       definition is not positive. *)
    if not (List.for_all (noccur_between n ntypes) auxlargs) then
      raise (IllFormedInd (LocalNonPos n));
    (* If the inductive type appears non positively in the
       parameters then the def is not positive *)
    let lrecargs = List.map (check_weak_pos env n) lpar in
    let auxlc = mip.mind_nf_lc in
    let auxntyp = mib.mind_ntypes in 
    (* We do not deal with imbricated mutual inductive types *)
    if auxntyp <> 1 then raise (IllFormedInd (LocalNonPos n));
    (* The abstract imbricated inductive type with parameters substituted *)
    let auxlcvect = abstract_mind_lc env auxntyp auxnpar auxlc in
    (* Extends the environment with a variable corresponding to
       the inductive def *)
    let env' = push_rel (Anonymous,None,type_of_inductive env mi) env in
    let newidx = n + auxntyp in
    let _ = 
      (* fails if the inductive type occurs non positively *)
      (* when substituted *) 
      Array.map 
	(function c -> 
	  let c' = hnf_prod_applist env c (List.map (lift auxntyp) lpar) in 
	  check_construct env' false newidx c') 
	auxlcvect
    in 
    Imbr(mi,lrecargs)

  (* The function check_weak_pos is exactly the same as check_pos, but
     with an extra case for traversing abstractions, like in Marseille's
     contribution about bisimulations:
     
     CoInductive strong_eq:process->process->Prop:=
       str_eq:(p,q:process)((a:action)(p':process)(transition p a p')->
          (Ex [q':process] (transition q a q')/\(strong_eq p' q')))->
             ((a:action)(q':process)(transition q a q')->
          (Ex [p':process] (transition p a p')/\(strong_eq p' q')))->
          (strong_eq p q).

     Abstractions may occur in imbricated recursive ocurrences, but I am
     not sure if they make sense in a form of constructor. This is why I
     chose to duplicated the code.  Eduardo 13/7/99. *)
  (* Since Lambda can no longer occur after a product or a Ind,
     I have branched the remaining cases on check_pos. HH 28/1/00 *)

  and check_weak_pos env n c =
    let x = whd_betadeltaiota env c in
    match kind_of_term x with 
      (* The extra case *)
      | Lambda (na,b,d) -> 
          if noccur_between n ntypes b
          then check_weak_pos (push_rel (na,None,b) env) (n+1) d
          else raise (IllFormedInd (LocalNonPos n))
      (******************)
      | _ -> check_pos env n x
  
  (* check the inductive types occur positively in the products of C, if
     check_head=true, also check the head corresponds to a constructor of
     the ith type *) 

  and check_construct env check_head n c = 
    let rec check_constr_rec env lrec n c = 
      let x,largs = decompose_app (whd_betadeltaiota env c) in
      match kind_of_term x with

        | Prod (na,b,d) -> 
	    assert (largs = []);
            let recarg = check_pos env n b in 
	    check_constr_rec (push_rel (na, None, b) env)
	      (recarg::lrec) (n+1) d

	| hd ->
	    if check_head then
	      if hd = Rel (n+ntypes-i) then
		check_correct_par env hyps nparams ntypes n (ntypes-i+1) largs
	      else
		raise (IllFormedInd LocalNotConstructor)
	    else
	      if not (List.for_all (noccur_between n ntypes) largs)
              then raise (IllFormedInd (LocalNonPos n));
	    List.rev lrec
    in check_constr_rec env [] n c
  in
  Array.map
    (fun c ->
       let c = body_of_type c in
       let sign, rawc = mind_extract_params nhyps c in
       let env' = push_rel_context sign env in
       try
	 check_construct env' true (1+nhyps) rawc
       with IllFormedInd err -> 
	 explain_ind_err (ntypes-i+1) env nhyps c err)
    indlc
    
let is_recursive listind =
  let rec one_is_rec rvec = 
    List.exists (function Mrec(i) -> List.mem i listind 
                   | Imbr(_,lvec) -> one_is_rec lvec
                   | Norec -> false
                   | Param _ -> false) rvec
  in 
  array_exists one_is_rec

(* Check positivity of an inductive definition *)
let cci_inductive env env_ar finite inds cst =
  let ntypes = List.length inds in
  (* Compute the set of used section variables *)
  let ids = 
    List.fold_left 
      (fun acc (_,_,_,ar,_,_,_,lc) -> 
	 Idset.union (Environ.global_vars_set env (body_of_type ar))
	   (Array.fold_left
	      (fun acc c ->
                Idset.union (global_vars_set env (body_of_type c)) acc)
	      acc
	      lc))
      Idset.empty inds in
  let hyps = keep_hyps env ids in
  (* Check one inductive *)
  let one_packet i (params,nparams,id,ar,cnames,issmall,isunit,lc) =
    (* Check positivity *)
    let recargs = check_positivity env_ar ntypes params nparams i lc in
    (* Arity in normal form *)
    let (ar_sign,ar_sort) = dest_arity env ar in
    let nf_ar =
      if isArity (body_of_type ar) then ar
      else it_mkProd_or_LetIn (mkSort ar_sort) ar_sign in
    (* Elimination sorts *)
    let isunit = isunit && ntypes = 1 && (not (is_recursive [0] recargs)) in
    let kelim = allowed_sorts issmall isunit ar_sort in
    (* Type of constructors in normal form *)
    let splayed_lc = Array.map (dest_prod_assum env_ar) lc in
    let nf_lc =
      array_map2 (fun (d,b) c -> it_mkProd_or_LetIn b d) splayed_lc lc in
    let nf_lc = if nf_lc = lc then lc else nf_lc in
    (* Build the inductive *)
    { mind_consnames = Array.of_list cnames;
      mind_typename = id;
      mind_user_lc = lc;
      mind_nf_lc = nf_lc;
      mind_user_arity  = ar;
      mind_nf_arity = nf_ar;
      mind_nrealargs = rel_context_length ar_sign - nparams;
      mind_sort = ar_sort;
      mind_kelim = kelim;
      mind_listrec = recargs;
      mind_nparams = nparams;
      mind_params_ctxt = params }
  in
  let packets = Array.of_list (list_map_i one_packet 1 inds) in
  { mind_ntypes = ntypes;
    mind_finite = finite;
    mind_hyps = hyps;
    mind_packets = packets;
    mind_constraints = cst;
    mind_singl = None }

(***********************************************************************)
(***********************************************************************)

let check_inductive env mie =
  (* First type the inductive definition *)
  let (env_arities, inds, cst) = type_inductive env mie in
  (* Then check positivity *)
  cci_inductive env env_arities mie.mind_entry_finite inds cst

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
open Sign
open Declarations
open Environ
open Reduction
open Type_errors

exception Induc

(* raise Induc if not an inductive type *)
let lookup_mind_specif env (sp,tyi) =
  let mib =
    try Environ.lookup_mind sp env
    with Not_found -> raise Induc in
  if tyi >= Array.length mib.mind_packets then
    error "Inductive.lookup_mind_specif: invalid inductive index";
  (mib, mib.mind_packets.(tyi))

let lookup_recargs env ind =
  let (mib,mip) = lookup_mind_specif env ind in
  Array.map (fun mip -> mip.mind_listrec) mib.mind_packets

let lookup_subterms env (_,i as ind) =
  (lookup_recargs env ind).(i)

let find_rectype env c =
  let (t, l) = decompose_app (whd_betadeltaiota env c) in
  match kind_of_term t with
    | Ind ind -> (ind, l)
    | _ -> raise Induc

let find_inductive env c =
  let (t, l) = decompose_app (whd_betadeltaiota env c) in
  match kind_of_term t with
    | Ind ind
        when (fst (lookup_mind_specif env ind)).mind_finite -> (ind, l)
    | _ -> raise Induc

let find_coinductive env c =
  let (t, l) = decompose_app (whd_betadeltaiota env c) in
  match kind_of_term t with
    | Ind ind
        when not (fst (lookup_mind_specif env ind)).mind_finite -> (ind, l)
    | _ -> raise Induc

(***********************************************************************)

type inductive_instance = {
  mis_sp : section_path;
  mis_mib : mutual_inductive_body;
  mis_tyi : int;
  mis_mip : one_inductive_body }

let mis_nconstr mis = Array.length (mis.mis_mip.mind_consnames)
let mis_inductive mis = (mis.mis_sp,mis.mis_tyi)

let lookup_mind_instance (sp,tyi) env =
  let (mib,mip) = lookup_mind_specif env (sp,tyi) in
  { mis_sp = sp; mis_mib = mib; mis_tyi = tyi; mis_mip = mip }

(* Build the substitution that replaces Rels by the appropriate *)
(* inductives *)
let ind_subst mispec =
  let ntypes = mispec.mis_mib.mind_ntypes in
  let make_Ik k = mkInd (mispec.mis_sp,ntypes-k-1) in 
  list_tabulate make_Ik ntypes

(* Instantiate both section variables and inductives *)
let constructor_instantiate mispec c =
  let s = ind_subst mispec in
  type_app (substl s) c

(* Instantiate the parameters of the inductive type *)
(* TODO: verify the arg of LetIn correspond to the value in the
   signature ? *)
let instantiate_params t args sign =
  let fail () =
    anomaly "instantiate_params: type, ctxt and args mismatch" in
  let (rem_args, subs, ty) =
    Sign.fold_rel_context
      (fun (_,copt,_) (largs,subs,ty) ->
        match (copt, largs, kind_of_term ty) with
          | (None, a::args, Prod(_,_,t)) -> (args, a::subs, t)
          | (Some b,_,LetIn(_,_,_,t))    -> (largs, (substl subs b)::subs, t)
	  | _                            -> fail())
      sign
      ~init:(args,[],t) 
  in
  if rem_args <> [] then fail();
  type_app (substl subs) ty

let full_inductive_instantiate (mispec,params) t =
  instantiate_params t params mispec.mis_mip.mind_params_ctxt

let full_constructor_instantiate (mispec,params) =
  let inst_ind = constructor_instantiate mispec in
  (fun t ->
    instantiate_params (inst_ind t) params mispec.mis_mip.mind_params_ctxt)

(***********************************************************************)
(***********************************************************************)

(* Functions to build standard types related to inductive *)

(* Type of an inductive type *)

let type_of_inductive env i =
  let mis = lookup_mind_instance i env in
  let hyps = mis.mis_mib.mind_hyps in
  mis.mis_mip.mind_user_arity

(* The same, with parameters instantiated *)
let get_arity (mispec,params as indf) =
  let arity = mispec.mis_mip.mind_nf_arity in
  destArity (full_inductive_instantiate indf arity)

(***********************************************************************)
(* Type of a constructor *)

let type_of_constructor env cstr =
  let ind = inductive_of_constructor cstr in
  let mispec = lookup_mind_instance ind env in
  let specif = mispec.mis_mip.mind_user_lc in
  let i = index_of_constructor cstr in
  let nconstr = mis_nconstr mispec in
  if i > nconstr then error "Not enough constructors in the type";
  constructor_instantiate mispec specif.(i-1)

let arities_of_constructors env ind = 
  let mispec = lookup_mind_instance ind env in
  let specif = mispec.mis_mip.mind_user_lc in
  Array.map (constructor_instantiate mispec) specif



(* gives the vector of constructors and of 
   types of constructors of an inductive definition 
   correctly instanciated *)

let mis_nf_constructor_type i mispec =
  let nconstr = mis_nconstr mispec in
  if i > nconstr then error "Not enough constructors in the type";
  constructor_instantiate mispec mispec.mis_mip.mind_nf_lc.(i-1)
   
(*s Useful functions *)

type constructor_summary = {
  cs_cstr : constructor;
  cs_params : constr list;
  cs_nargs : int;
  cs_args : rel_context;
  cs_concl_realargs : constr array
}

let process_constructor ((mispec,params) as indf) j typi =
  let typi = full_constructor_instantiate indf typi in
  let (args,ccl) = decompose_prod_assum typi in
  let (_,allargs) = decompose_app ccl in
  let (_,vargs) = list_chop mispec.mis_mip.mind_nparams allargs in
  { cs_cstr = ith_constructor_of_inductive (mis_inductive mispec) (j+1);
    cs_params = params;
    cs_nargs = rel_context_length args;
    cs_args = args;
    cs_concl_realargs = Array.of_list vargs }

let get_constructors ((mispec,params) as indf) =
  let constr_tys = mispec.mis_mip.mind_nf_lc in
  Array.mapi (process_constructor indf) constr_tys

(***********************************************************************)

(* Type of case branches *)

let local_rels ctxt =
  let (rels,_) =
    Sign.fold_rel_context_reverse
      (fun (rels,n) (_,copt,_) ->
        match copt with
            None   -> (mkRel n :: rels, n+1)
          | Some _ -> (rels, n+1))
      ~init:([],1)
      ctxt 
  in
  rels

let build_dependent_constructor cs =
  applist
    (mkConstruct cs.cs_cstr,
     (List.map (lift cs.cs_nargs) cs.cs_params)@(local_rels cs.cs_args))

let build_dependent_inductive ((mis, params) as indf) =
  let arsign,_ = get_arity indf in
  let nrealargs = mis.mis_mip.mind_nrealargs in
  applist 
    (mkInd (mis_inductive mis),
     (List.map (lift nrealargs) params)@(local_rels arsign))

(* [p] is the predicate and [cs] a constructor summary *)
let build_branch_type dep p cs =
  let args =
    if dep then
      Array.append cs.cs_concl_realargs [|build_dependent_constructor cs|]
    else
      cs.cs_concl_realargs in
  let base = beta_appvect (lift cs.cs_nargs p) args in
  it_mkProd_or_LetIn base cs.cs_args


let is_info_arity env c =
  match dest_arity env c with
    | (_,Prop Null) -> false 
    | (_,Prop Pos)  -> true 
    | (_,Type _)    -> true

let error_elim_expln env kp ki =
  if is_info_arity env kp && not (is_info_arity env ki) then
    NonInformativeToInformative
  else 
    match (kind_of_term kp,kind_of_term ki) with 
      | Sort (Type _), Sort (Prop _) -> StrongEliminationOnNonSmallType
      | _ -> WrongArity

exception Arity of (constr * constr * arity_error) option


let is_correct_arity env kelim (c,pj) indf t = 
  let rec srec (pt,t) u =
    let pt' = whd_betadeltaiota env pt in
    let t' = whd_betadeltaiota env t in
    match kind_of_term pt', kind_of_term t' with
      | Prod (_,a1,a2), Prod (_,a1',a2') ->
          let univ =
            try conv env a1 a1'
            with NotConvertible -> raise (Arity None) in
          srec (a2,a2') (Constraint.union u univ)
      | Prod (_,a1,a2), _ -> 
          let k = whd_betadeltaiota env a2 in 
          let ksort = match kind_of_term k with
            | Sort s -> family_of_sort s 
	    | _ -> raise (Arity None) in
	  let ind = build_dependent_inductive indf in
          let univ =
            try conv env a1 ind
            with NotConvertible -> raise (Arity None) in
          if List.exists ((=) ksort) kelim then
	    ((true,k), Constraint.union u univ)
          else 
	    raise (Arity (Some(k,t',error_elim_expln env k t')))
      | k, Prod (_,_,_) ->
	  raise (Arity None)
      | k, ki -> 
	  let ksort = match k with
            | Sort s -> family_of_sort s 
            | _ ->  raise (Arity None) in
          if List.exists ((=) ksort) kelim then 
	    (false, pt'), u
          else 
	    raise (Arity (Some(pt',t',error_elim_expln env pt' t')))
  in 
  try srec (pj.uj_type,t) Constraint.empty
  with Arity kinds ->
    let create_sort = function 
      | InProp -> mkProp
      | InSet -> mkSet
      | InType -> mkSort type_0 in
    let listarity = List.map create_sort kelim
(*    let listarity =
      (List.map (fun s -> make_arity env true indf (create_sort s)) kelim)
      @(List.map (fun s -> make_arity env false indf (create_sort s)) kelim)*)
    in 
    let ind = mis_inductive (fst indf) in
    error_elim_arity env ind listarity c pj kinds


let find_case_dep_nparams env (c,pj) (ind,params) =
  let indf = lookup_mind_instance ind env in
  let kelim = indf.mis_mip.mind_kelim in
  let arsign,s = get_arity (indf,params) in
  let glob_t = it_mkProd_or_LetIn (mkSort s) arsign in
  let ((dep,_),univ) =
    is_correct_arity env kelim (c,pj) (indf,params) glob_t in
  (dep,univ)


let type_case_branches env (mind,largs) pj c =
  let mispec = lookup_mind_instance mind env in 
  let nparams = mispec.mis_mip.mind_nparams in
  let (params,realargs) = list_chop nparams largs in
  let indf = (mispec,params) in
  let p = pj.uj_val in
  let (dep,univ) = find_case_dep_nparams env (c,pj) (mind,params) in
  let constructs = get_constructors indf in
  let lc = Array.map (build_branch_type dep p) constructs in
  let args = if dep then realargs@[c] else realargs in
  (lc, beta_appvect p (Array.of_list args), univ)


let check_case_info env indsp ci =
  let (mib,mip) = lookup_mind_specif env indsp in
  if
    (indsp <> ci.ci_ind) or
    (mip.mind_nparams <> ci.ci_npar)
  then raise (TypeError(env,WrongCaseInfo(indsp,ci)))

(***********************************************************************)
(***********************************************************************)

(* Guard conditions for fix and cofix-points *)

exception FixGuardError of guard_error

(* Check if t is a subterm of Rel n, and gives its specification, 
   assuming lst already gives index of
   subterms with corresponding specifications of recursive arguments *)

(* A powerful notion of subterm *)

(* To each inductive definition corresponds an array describing the
   structure of recursive arguments for each constructor, we call it
   the recursive spec of the type (it has type recargs vect).  For
   checking the guard, we start from the decreasing argument (Rel n)
   with its recursive spec.  During checking the guardness condition,
   we collect patterns variables corresponding to subterms of n, each
   of them with its recursive spec.  They are organised in a list lst
   of type (int * recargs) list which is sorted with respect to the
   first argument.
*)

(*************************)
(* Environment annotated with marks on recursive arguments:
   it is a triple (env,lst,n) where
   - env is the typing environment
   - lst is a mapping from de Bruijn indices to list of recargs
     (tells which subterms of that variable are recursive)
   - n is the de Bruijn index of the fixpoint for which we are
     checking the guard condition.

   Below are functions to handle such environment.
 *)
type size = Large | Strict
type guard_env =
  { env     : env;
    (* dB of last fixpoint *)
    rel_min : int;
    (* inductive of recarg of each fixpoint *)
    inds    : inductive array;
    (* the recarg information of inductive family *)
    recvec  : recarg list array array;
    (* dB of variables denoting subterms *)
    lst     : (int * (size * recarg list array)) list;
  }

let make_renv env minds recarg (_,tyi as ind) =
  let mind_recvec = lookup_recargs env ind in 
  let lcx = mind_recvec.(tyi)  in
  { env = env;
    rel_min = recarg+2;
    inds = minds;
    recvec = mind_recvec;
    lst = [(1,(Large,mind_recvec.(tyi)))] }

let map_lift_fst_n m = List.map (function (n,t)->(n+m,t))

let push_var_renv renv (x,ty) =
  { renv with 
    env = push_rel (x,None,ty) renv.env;
    rel_min = renv.rel_min+1;
    lst = map_lift_fst_n 1 renv.lst }

let push_ctxt_renv renv ctxt =
  let n = rel_context_length ctxt in
  { renv with 
    env = push_rel_context ctxt renv.env;
    rel_min = renv.rel_min+n;
    lst = map_lift_fst_n n renv.lst }

let push_fix_renv renv (_,v,_ as recdef) =
  let n = Array.length v in
  { renv with
    env = push_rec_types recdef renv.env;
    rel_min = renv.rel_min+n;
    lst = map_lift_fst_n n renv.lst }

(* Add a variable and mark it as strictly smaller with information [spec]. *)
let add_recarg renv (x,a,spec) =
  let renv' = push_var_renv renv (x,a) in
  { renv' with lst = (1,(Strict,spec))::renv'.lst }

(* Fetch recursive information about a variable *)
let subterm_var p renv = 
  let rec findrec = function 
    | (a,ta)::l -> 
        if a < p then findrec l else if a = p then Some ta else None
    | _ -> None in
  findrec renv.lst


(******************************)
(* Computing the recursive subterms of a term (propagation of size
   information through Cases). *)

(*
   c is a branch of an inductive definition corresponding to the spec
   lrec.  mind_recvec is the recursive spec of the inductive
   definition of the decreasing argument n.

   case_branches_specif renv lrec lc will pass the lambdas
   of c corresponding to pattern variables and collect possibly new
   subterms variables and returns the bodies of the branches with the
   correct envs and decreasing args.
*)


let imbr_recarg_expand env (sp,i as ind_sp) lrc =
  let recargs = lookup_subterms env ind_sp in
  let rec imbr_recarg ra = 
    match ra with 
      | Mrec(j)        -> Imbr((sp,j),lrc)
      | Imbr(ind_sp,l) -> Imbr(ind_sp, List.map imbr_recarg l)
      | Norec          -> Norec
      | Param(k)       -> List.nth lrc k in
  Array.map (List.map imbr_recarg) recargs


let case_branches_specif renv = 
  let rec crec renv lrec c = 
    let c' = strip_outer_cast c in 
    match lrec, kind_of_term c' with 
      |	(ra::lr,Lambda (x,a,b)) ->
          let renv' =
            match ra with 
	        Mrec(i) -> add_recarg renv (x,a,renv.recvec.(i))
              | Imbr(ind_sp,lrc) ->
                  let lc = imbr_recarg_expand renv.env ind_sp lrc in
                  add_recarg renv (x,a,lc)
	      | _ -> push_var_renv renv (x,a) in
          crec renv' lr b
      | (_,LetIn (x,c,a,b)) -> crec renv lrec (subst1 c b)
      (* Rq: if branch is not eta-long, then the recursive information
         is not propagated: *)
      | (_,_) -> (renv,c')
  in array_map2 (crec renv) 

(*********************************)

(* finds the inductive type of the recursive argument of a fixpoint *)
let inductive_of_fix env recarg body =
  let (ctxt,b) = decompose_lam_n_assum recarg body in
  let env' = push_rel_context ctxt env in
  let (_,ty,_) = destLambda(whd_betadeltaiota env' b) in
  let (i,_) = decompose_app (whd_betadeltaiota env' ty) in 
  destInd i

(* 
   subterm_specif env c ind 

   subterm_specif should test if [c] (building objects of inductive
   type [ind], not necassarily the same as that of the recursive
   argument) is a subterm of the recursive argument of the fixpoint we
   are checking and fails with Not_found if not. In case it is, it
   should send its recursive specification (i.e. on which arguments we
   are allowed to make recursive calls). This recursive spec should be
   the same size as the number of constructors of the type of c.

   Returns:
   - [Some lc] if [c] is a strict subterm of the rec. arg. (or a Meta) 
   - [None] otherwise
*)
let subterm_specif renv c ind = 
  let rec crec renv c ind = 
    let f,l = decompose_app (whd_betadeltaiota renv.env c) in
    match kind_of_term f with 
      | Rel k -> subterm_var k renv

      | Case (ci,_,c,lbr) ->
          if Array.length lbr = 0
            (* New: if it is built by contadiction, it is OK *)
          then Some (Strict,[||])
          else
            let def = Array.create (Array.length lbr) [] in
            let lcv =
              match crec renv c ci.ci_ind with
                Some (_,lr) -> lr
              | None -> def in 
            let lbr' = case_branches_specif renv lcv lbr in
            let stl  =
              Array.map (fun (renv',br') -> crec renv' br' ind) lbr' in
            let stl0 = stl.(0) in
	    if array_for_all (fun st -> st=stl0) stl then stl0 
            (* branches do not return objects with same spec *)
            else None
	       
      | Fix ((recindxs,i),(_,typarray,bodies as recdef)) ->
(* when proving that the fixpoint f(x)=e is less than n, it is enough
   to prove that e is less than n assuming f is less than n
   furthermore when f is applied to a term which is strictly less than
   n, one may assume that x itself is strictly less than n
*)
          let nbfix = Array.length typarray in
          let recargs = lookup_subterms renv.env ind in
          (* pushing the fixpoints *)
          let renv' = push_fix_renv renv recdef in
          let renv' =
            { renv' with lst=(nbfix-i,(Strict,recargs))::renv'.lst } in
          let decrArg = recindxs.(i) in 
          let theBody = bodies.(i)   in
          let nbOfAbst = decrArg+1 in
          let sign,strippedBody = decompose_lam_n_assum nbOfAbst theBody in
          (* pushing the fix parameters *)
          let renv'' = push_ctxt_renv renv' sign in
          let renv'' =
            { renv'' with
              lst =
              if List.length l < nbOfAbst then renv''.lst
              else
                let decrarg_ind =
                  inductive_of_fix renv''.env decrArg theBody in
                let theDecrArg  = List.nth l decrArg in
	        try 
	          match crec renv theDecrArg decrarg_ind with 
		    (Some recArgsDecrArg) ->
                      (1,recArgsDecrArg) :: renv''.lst 
                  | None -> renv''.lst
	        with Not_found -> renv''.lst } in
	  crec renv'' strippedBody ind
	    
      | Lambda (x,a,b) -> 
          assert (l=[]);
          crec (push_var_renv renv (x,a)) b ind

      (* A term with metas is considered OK *)
      | Meta _ -> Some (Strict,lookup_subterms renv.env ind)
      (* Other terms are not subterms *)
      | _ -> None
  in 
  crec renv c ind

(* Propagation of size information through Cases: if the matched
   object is a recursive subterm then compute the information
   associated to its own subterms. *)
let spec_subterm_large renv c ind = 
  match subterm_specif renv c ind with
    Some (_,lr) -> lr
  | None ->
      let nb = Array.length (lookup_subterms renv.env ind) in
      Array.create nb []

(* Check term c can be applied to one of the mutual fixpoints. *)
let check_is_subterm renv c ind = 
  match subterm_specif renv c ind with
    Some (Strict,_) -> ()
  |  _ -> raise (FixGuardError RecursionOnIllegalTerm)

(***********************************************************************)

(* Check if [def] is a guarded fixpoint body with decreasing arg.
   given [recpos], the decreasing arguments of each mutually defined
   fixpoint. *)
let check_one_fix renv recpos def =
  let nfi = Array.length recpos in 
  let rec check_rec_call renv t = 
    (* if [t] does not make recursive calls, it is guarded: *)
    noccur_with_meta renv.rel_min nfi t or 
    (* Rq: why not try and expand some definitions ? *)
    let f,l = decompose_app (whd_betaiotazeta renv.env t) in
    match kind_of_term f with
      | Rel p -> 
          (* Test if it is a recursive call: *) 
	  if renv.rel_min <= p & p < renv.rel_min+nfi then
            (* the position of the invoked fixpoint: *) 
	    let glob = renv.rel_min+nfi-1-p in
            (* the decreasing arg of the rec call: *)
	    let np = recpos.(glob) in
	    if List.length l > np then 
	      (match list_chop np l with
		  (la,(z::lrest)) -> 
                    (* Check the decreasing arg is smaller *)
	            check_is_subterm renv z renv.inds.(glob);
                    List.for_all (check_rec_call renv) (la@lrest)
		| _ -> assert false)
	    else raise (FixGuardError NotEnoughArgumentsForFixCall)
          (* otherwise check the arguments are guarded: *)
	  else List.for_all (check_rec_call renv) l        

      | Case (ci,p,c_0,lrest) ->
            (* compute the recarg information for the arguments of
               each branch *)
            let lc  = spec_subterm_large renv c_0 ci.ci_ind in
            let lbr = case_branches_specif renv lc lrest in
            array_for_all (fun (renv',br') -> check_rec_call renv' br') lbr
	    && List.for_all (check_rec_call renv) (c_0::p::l)

  (* Enables to traverse Fixpoint definitions in a more intelligent
     way, ie, the rule :

     if - g = Fix g/1 := [y1:T1]...[yp:Tp]e &
        - f is guarded with respect to the set of pattern variables S 
          in a1 ... am        &
        - f is guarded with respect to the set of pattern variables S 
          in T1 ... Tp        &
        - ap is a sub-term of the formal argument of f &
        - f is guarded with respect to the set of pattern variables S+{yp}
          in e
     then f is guarded with respect to S in (g a1 ... am).

     Eduardo 7/9/98 *)

      | Fix ((recindxs,i),(_,typarray,bodies as recdef)) ->
          List.for_all (check_rec_call renv) l &&
          array_for_all (check_rec_call renv) typarray && 
	  let nbfix = Array.length typarray in
          let decrArg = recindxs.(i) in
	  let theBody = bodies.(i)   in
          let renv' = push_fix_renv renv recdef in 
          if (List.length l < (decrArg+1)) then
	    array_for_all (check_rec_call renv') bodies
          else 
            let decrarg_ind = inductive_of_fix renv'.env decrArg theBody in
            let theDecrArg  = List.nth l decrArg in
	    (try 
	      match subterm_specif renv theDecrArg decrarg_ind with
                  Some recArgsDecrArg -> 
		    check_nested_fix_body renv'
                      (decrArg+1) recArgsDecrArg theBody
		| None -> array_for_all (check_rec_call renv') bodies
	     with Not_found -> array_for_all (check_rec_call renv') bodies)

      | Const sp as c -> 
          (try List.for_all (check_rec_call renv) l
           with (FixGuardError _ ) as e ->
             if evaluable_constant renv.env sp then 
	       check_rec_call renv (whd_betadeltaiota renv.env t)
	     else raise e)

      (* The cases below simply check recursively the condition on the
         subterms *)
      | Cast (a,b) -> 
          List.for_all (check_rec_call renv) (a::b::l)

      | Lambda (x,a,b) ->
          check_rec_call (push_var_renv renv (x,a)) b &&
          List.for_all (check_rec_call renv) (a::l)

      | Prod (x,a,b) -> 
          check_rec_call (push_var_renv renv (x,a)) b &&
          List.for_all (check_rec_call renv) (a::l)

      | CoFix (i,(_,typarray,bodies as recdef)) ->
	  array_for_all (check_rec_call renv) typarray &&
          List.for_all (check_rec_call renv) l &&
	  let renv' = push_fix_renv renv recdef in
	  array_for_all (check_rec_call renv') bodies

      | Evar (_,la) -> 
	  array_for_all (check_rec_call renv) la &&
          List.for_all (check_rec_call renv) l

      | Meta _ -> true

      | (App _ | LetIn _) -> 
	  anomaly "check_rec_call: should have been reduced"

      | (Ind _ | Construct _ | Var _ | Sort _) ->
          List.for_all (check_rec_call renv) l

  and check_nested_fix_body renv decr recArgsDecrArg body =
    if decr = 0 then
      check_rec_call
        { renv with lst=(1,recArgsDecrArg)::renv.lst } body
    else
      match kind_of_term body with
	| Lambda (x,a,b) ->
	    check_rec_call renv a &&
	    check_nested_fix_body (push_var_renv renv (x,a))
              (decr-1) recArgsDecrArg b
	| _ -> anomaly "Not enough abstractions in fix body"
    
  in
  check_rec_call renv def


let inductive_of_mutfix env ((nvect,bodynum),(names,types,bodies as recdef)) =
  let nbfix = Array.length bodies in 
  if nbfix = 0
    or Array.length nvect <> nbfix 
    or Array.length types <> nbfix
    or Array.length names <> nbfix
    or bodynum < 0
    or bodynum >= nbfix
  then anomaly "Ill-formed fix term";
  let fixenv = push_rec_types recdef env in
  let raise_err i err =
    error_ill_formed_rec_body fixenv err names i bodies in
  (* Check the i-th definition with recarg k *)
  let find_ind i k def = 
    if k < 0 then anomaly "negative recarg position";
    (* check fi does not appear in the k+1 first abstractions, 
       gives the type of the k+1-eme abstraction (must be an inductive)  *)
    let rec check_occur env n def = 
      match kind_of_term (whd_betadeltaiota env def) with
        | Lambda (x,a,b) -> 
	    if noccur_with_meta n nbfix a then
	      let env' = push_rel (x, None, a) env in
              if n = k+1 then
                (* get the inductive type of the fixpoint *)
                let (mind, _) = 
                  try find_inductive env a 
                  with Induc -> raise_err i RecursionNotOnInductiveType in
                (mind, (env', b))
	      else check_occur env' (n+1) b
            else anomaly "check_one_fix: Bad occurrence of recursive call"
        | _ -> raise_err i NotEnoughAbstractionInFixBody in
    check_occur env 1 def in
  (* Do it on every fixpoint *)
  let rv = array_map2_i find_ind nvect bodies in
  (Array.map fst rv, Array.map snd rv)


let check_fix env ((nvect,_),(names,_,bodies as recdef) as fix) =
  let (minds, rdef) = inductive_of_mutfix env fix in
  for i = 0 to Array.length bodies - 1 do
    let (fenv,body) = rdef.(i) in
    let renv = make_renv fenv minds nvect.(i) minds.(i) in
    try
      let _ = check_one_fix renv nvect body in ()
    with FixGuardError err ->
      let fixenv = push_rec_types recdef env in
      error_ill_formed_rec_body fixenv err names i bodies
  done

(*
let cfkey = Profile.declare_profile "check_fix";;
let check_fix env fix = Profile.profile3 cfkey check_fix env fix;;
*)

(***********************************************************************)
(* Co-fixpoints. *)

exception CoFixGuardError of guard_error

let anomaly_ill_typed () =
  anomaly "check_one_cofix: too many arguments applied to constructor"


let check_one_cofix env nbfix def deftype = 
  let rec codomain_is_coind env c =
    let b = whd_betadeltaiota env c in
    match kind_of_term b with
      | Prod (x,a,b) ->
	  codomain_is_coind (push_rel (x, None, a) env) b 
      | _ -> 
	  try
	    find_coinductive env b
          with Induc ->
	    raise (CoFixGuardError (CodomainNotInductiveType b))
  in
  let (mind, _) = codomain_is_coind env deftype in
  let (sp,tyi) = mind in
  let lvlra = lookup_recargs env (sp,tyi) in
  let vlra = lvlra.(tyi) in  
  let rec check_rec_call env alreadygrd n vlra  t =
    if noccur_with_meta n nbfix t then
      true 
    else
      let c,args = decompose_app (whd_betadeltaiota env t) in
      match kind_of_term c with 
	| Meta _ -> true
	      
	| Rel p -> 
             if n <= p && p < n+nbfix then
	       (* recursive call *)
               if alreadygrd then
		 if List.for_all (noccur_with_meta n nbfix) args then
		   true
		 else 
		   raise (CoFixGuardError NestedRecursiveOccurrences)
               else 
		 raise (CoFixGuardError (UnguardedRecursiveCall t))
             else  
	       error "check_one_cofix: ???"  (* ??? *)
		 
	| Construct (_,i as cstr_sp)  ->
            let lra =vlra.(i-1) in 
            let mI = inductive_of_constructor cstr_sp in
	    let (mib,mip) = lookup_mind_specif env mI in
            let _,realargs = list_chop mip.mind_nparams args in
            let rec process_args_of_constr l lra =
              match l with
                | [] -> true 
                | t::lr ->
		    (match lra  with 
                       | [] -> anomaly_ill_typed () 
                       |  (Mrec i)::lrar -> 
                            let newvlra = lvlra.(i) in
                            (check_rec_call env true n newvlra t) &&
                            (process_args_of_constr lr lrar)
			    
                       |  (Imbr((sp,i) as ind_sp,lrc)::lrar)  ->
                            let lc = imbr_recarg_expand env ind_sp lrc in
                            check_rec_call env true n lc t &
                            process_args_of_constr lr lrar
				 
                       |  _::lrar  -> 
                            if (noccur_with_meta n nbfix t) 
                            then (process_args_of_constr lr lrar)
                            else raise (CoFixGuardError
					  (RecCallInNonRecArgOfConstructor t)))
            in (process_args_of_constr realargs lra)
		 
		 
	| Lambda (x,a,b) ->
	     assert (args = []);
            if (noccur_with_meta n nbfix a) then
              check_rec_call (push_rel (x, None, a) env)
		alreadygrd (n+1)  vlra b
            else 
	      raise (CoFixGuardError (RecCallInTypeOfAbstraction t))
	      
	| CoFix (j,(_,varit,vdefs as recdef)) ->
            if (List.for_all (noccur_with_meta n nbfix) args)
            then 
              let nbfix = Array.length vdefs in
	      if (array_for_all (noccur_with_meta n nbfix) varit) then
		let env' = push_rec_types recdef env in
		(array_for_all
		   (check_rec_call env' alreadygrd (n+1) vlra) vdefs)
		&&
		(List.for_all (check_rec_call env alreadygrd (n+1) vlra) args) 
              else 
		raise (CoFixGuardError (RecCallInTypeOfDef c))
	    else
	      raise (CoFixGuardError (UnguardedRecursiveCall c))

	| Case (_,p,tm,vrest) ->
            if (noccur_with_meta n nbfix p) then
              if (noccur_with_meta n nbfix tm) then
		if (List.for_all (noccur_with_meta n nbfix) args) then
		  (array_for_all (check_rec_call env alreadygrd n vlra) vrest)
		else 
		  raise (CoFixGuardError (RecCallInCaseFun c))
              else 
		raise (CoFixGuardError (RecCallInCaseArg c))
            else 
	      raise (CoFixGuardError (RecCallInCasePred c))
              
	| _    -> raise (CoFixGuardError NotGuardedForm)
	      
  in 
  check_rec_call env false 1 vlra def

(* The  function which checks that the whole block of definitions 
   satisfies the guarded condition *)

let check_cofix env (bodynum,(names,types,bodies as recdef)) = 
  let nbfix = Array.length bodies in 
  for i = 0 to nbfix-1 do
    let fixenv = push_rec_types recdef env in
    try 
      let _ = check_one_cofix fixenv nbfix bodies.(i) types.(i)
      in ()
    with CoFixGuardError err -> 
      error_ill_formed_rec_body fixenv err names i bodies
  done

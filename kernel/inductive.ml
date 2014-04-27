(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Names
open Univ
open Term
open Vars
open Context
open Declarations
open Declareops
open Environ
open Reduction
open Type_errors

type mind_specif = mutual_inductive_body * one_inductive_body

(* raise Not_found if not an inductive type *)
let lookup_mind_specif env (kn,tyi) =
  let mib = Environ.lookup_mind kn env in
  if tyi >= Array.length mib.mind_packets then
    error "Inductive.lookup_mind_specif: invalid inductive index";
  (mib, mib.mind_packets.(tyi))

let find_rectype env c =
  let (t, l) = decompose_app (whd_betadeltaiota env c) in
  match kind_of_term t with
  | Ind ind -> (ind, l)
  | _ -> raise Not_found

let find_inductive env c =
  let (t, l) = decompose_app (whd_betadeltaiota env c) in
  match kind_of_term t with
    | Ind ind
        when (fst (lookup_mind_specif env ind)).mind_finite -> (ind, l)
    | _ -> raise Not_found

let find_coinductive env c =
  let (t, l) = decompose_app (whd_betadeltaiota env c) in
  match kind_of_term t with
    | Ind ind
        when not (fst (lookup_mind_specif env ind)).mind_finite -> (ind, l)
    | _ -> raise Not_found

let inductive_params (mib,_) = mib.mind_nparams

(************************************************************************)

(* Build the substitution that replaces Rels by the appropriate *)
(* inductives *)
let ind_subst mind mib =
  let ntypes = mib.mind_ntypes in
  let make_Ik k = mkInd (mind,ntypes-k-1) in
  List.init ntypes make_Ik

(* Instantiate inductives in constructor type *)
let constructor_instantiate mind mib c =
  let s = ind_subst mind mib in
  substl s c

let instantiate_params full t args sign =
  let fail () =
    anomaly ~label:"instantiate_params" (Pp.str "type, ctxt and args mismatch") in
  let (rem_args, subs, ty) =
    Context.fold_rel_context
      (fun (_,copt,_) (largs,subs,ty) ->
        match (copt, largs, kind_of_term ty) with
          | (None, a::args, Prod(_,_,t)) -> (args, a::subs, t)
          | (Some b,_,LetIn(_,_,_,t))    -> (largs, (substl subs b)::subs, t)
	  | (_,[],_)                -> if full then fail() else ([], subs, ty)
	  | _                       -> fail ())
      sign
      ~init:(args,[],t)
  in
  let () = if not (List.is_empty rem_args) then fail () in
  substl subs ty

let full_inductive_instantiate mib params sign =
  let dummy = prop_sort in
  let t = mkArity (sign,dummy) in
  fst (destArity (instantiate_params true t params mib.mind_params_ctxt))

let full_constructor_instantiate ((mind,_),(mib,_),params) =
  let inst_ind = constructor_instantiate mind mib in
  (fun t ->
    instantiate_params true (inst_ind t) params mib.mind_params_ctxt)

(************************************************************************)
(************************************************************************)

(* Functions to build standard types related to inductive *)

(*
Computing the actual sort of an applied or partially applied inductive type:

I_i: forall uniformparams:utyps, forall otherparams:otyps, Type(a)
uniformargs : utyps
otherargs : otyps
I_1:forall ...,s_1;...I_n:forall ...,s_n |- sort(C_kj(uniformargs)) = s_kj
s'_k = max(..s_kj..)
merge(..s'_k..) = ..s''_k..
--------------------------------------------------------------------
Gamma |- I_i uniformargs otherargs : phi(s''_i)

where

- if p=0, phi() = Prop
- if p=1, phi(s) = s
- if p<>1, phi(s) = sup(Set,s)

Remark: Set (predicative) is encoded as Type(0)
*)

let sort_as_univ = function
| Type u -> u
| Prop Null -> type0m_univ
| Prop Pos -> type0_univ

let cons_subst u su subst =
  try
    (u, sup su (List.assoc_f Universe.equal u subst)) ::
      List.remove_assoc_f Universe.equal u subst
  with Not_found -> (u, su) :: subst

let actualize_decl_level env lev t =
  let sign,s = dest_arity env t in
  mkArity (sign,lev)

let polymorphism_on_non_applied_parameters = false

(* Bind expected levels of parameters to actual levels *)
(* Propagate the new levels in the signature *)
let rec make_subst env = function
  | (_,Some _,_ as t)::sign, exp, args ->
      let ctx,subst = make_subst env (sign, exp, args) in
      t::ctx, subst
  | d::sign, None::exp, args ->
      let args = match args with _::args -> args | [] -> [] in
      let ctx,subst = make_subst env (sign, exp, args) in
      d::ctx, subst
  | d::sign, Some u::exp, a::args ->
      (* We recover the level of the argument, but we don't change the *)
      (* level in the corresponding type in the arity; this level in the *)
      (* arity is a global level which, at typing time, will be enforce *)
      (* to be greater than the level of the argument; this is probably *)
      (* a useless extra constraint *)
      let s = sort_as_univ (snd (dest_arity env (Lazy.force a))) in
      let ctx,subst = make_subst env (sign, exp, args) in
      d::ctx, cons_subst u s subst
  | (na,None,t as d)::sign, Some u::exp, [] ->
      (* No more argument here: we instantiate the type with a fresh level *)
      (* which is first propagated to the corresponding premise in the arity *)
      (* (actualize_decl_level), then to the conclusion of the arity (via *)
      (* the substitution) *)
      let ctx,subst = make_subst env (sign, exp, []) in
      if polymorphism_on_non_applied_parameters then
	let s = fresh_local_univ () in
	let t = actualize_decl_level env (Type s) t in
	(na,None,t)::ctx, cons_subst u s subst
      else
	d::ctx, subst
  | sign, [], _ ->
      (* Uniform parameters are exhausted *)
      sign,[]
  | [], _, _ ->
      assert false

let instantiate_universes env ctx ar argsorts =
  let args = Array.to_list argsorts in
  let ctx,subst = make_subst env (ctx,ar.poly_param_levels,args) in
  let level = subst_large_constraints subst ar.poly_level in
  ctx,
  (* Singleton type not containing types are interpretable in Prop *)
  if is_type0m_univ level then prop_sort
  (* Non singleton type not containing types are interpretable in Set *)
  else if is_type0_univ level then set_sort
  (* This is a Type with constraints *)
 else Type level

exception SingletonInductiveBecomesProp of Id.t

let type_of_inductive_knowing_parameters ?(polyprop=true) env mip paramtyps =
  match mip.mind_arity with
  | Monomorphic s ->
      s.mind_user_arity
  | Polymorphic ar ->
      let ctx = List.rev mip.mind_arity_ctxt in
      let ctx,s = instantiate_universes env ctx ar paramtyps in
      (* The Ocaml extraction cannot handle (yet?) "Prop-polymorphism", i.e.
         the situation where a non-Prop singleton inductive becomes Prop
         when applied to Prop params *)
      if not polyprop && not (is_type0m_univ ar.poly_level) && is_prop_sort s
      then raise (SingletonInductiveBecomesProp mip.mind_typename);
      mkArity (List.rev ctx,s)

(* Type of a (non applied) inductive type *)

let type_of_inductive env (_,mip) =
  type_of_inductive_knowing_parameters env mip [||]

(* The max of an array of universes *)

let cumulate_constructor_univ u = function
  | Prop Null -> u
  | Prop Pos -> sup type0_univ u
  | Type u' -> sup u u'

let max_inductive_sort =
  Array.fold_left cumulate_constructor_univ type0m_univ

(************************************************************************)
(* Type of a constructor *)

let type_of_constructor cstr (mib,mip) =
  let ind = inductive_of_constructor cstr in
  let specif = mip.mind_user_lc in
  let i = index_of_constructor cstr in
  let nconstr = Array.length mip.mind_consnames in
  if i > nconstr then error "Not enough constructors in the type.";
  constructor_instantiate (fst ind) mib specif.(i-1)

let arities_of_specif kn (mib,mip) =
  let specif = mip.mind_nf_lc in
  Array.map (constructor_instantiate kn mib) specif

let arities_of_constructors ind specif =
  arities_of_specif (fst ind) specif

let type_of_constructors ind (mib,mip) =
  let specif = mip.mind_user_lc in
  Array.map (constructor_instantiate (fst ind) mib) specif

(************************************************************************)

(* Type of case predicates *)

let local_rels ctxt =
  let (rels,_) =
    Context.fold_rel_context_reverse
      (fun (rels,n) (_,copt,_) ->
        match copt with
            None   -> (mkRel n :: rels, n+1)
          | Some _ -> (rels, n+1))
      ~init:([],1)
      ctxt
  in
  rels

(* Get type of inductive, with parameters instantiated *)

let inductive_sort_family mip =
  match mip.mind_arity with
   | Monomorphic s -> family_of_sort s.mind_sort
   | Polymorphic _ -> InType

let mind_arity mip =
  mip.mind_arity_ctxt, inductive_sort_family mip

let get_instantiated_arity (mib,mip) params =
  let sign, s = mind_arity mip in
  full_inductive_instantiate mib params sign, s

let elim_sorts (_,mip) = mip.mind_kelim

let extended_rel_list n hyps =
  let rec reln l p = function
    | (_,None,_) :: hyps -> reln (mkRel (n+p) :: l) (p+1) hyps
    | (_,Some _,_) :: hyps -> reln l (p+1) hyps
    | [] -> l
  in
  reln [] 1 hyps

let build_dependent_inductive ind (_,mip) params =
  let realargs,_ = List.chop mip.mind_nrealargs_ctxt mip.mind_arity_ctxt in
  applist
    (mkInd ind,
       List.map (lift mip.mind_nrealargs_ctxt) params
       @ extended_rel_list 0 realargs)

(* This exception is local *)
exception LocalArity of (sorts_family * sorts_family * arity_error) option

let check_allowed_sort ksort specif =
  let eq_ksort s = match ksort, s with
  | InProp, InProp | InSet, InSet | InType, InType -> true
  | _ -> false in
  if not (List.exists eq_ksort (elim_sorts specif)) then
    let s = inductive_sort_family (snd specif) in
    raise (LocalArity (Some(ksort,s,error_elim_explain ksort s)))

let is_correct_arity env c pj ind specif params =
  let arsign,_ = get_instantiated_arity specif params in
  let rec srec env pt ar u =
    let pt' = whd_betadeltaiota env pt in
    match kind_of_term pt', ar with
      | Prod (na1,a1,t), (_,None,a1')::ar' ->
          let univ =
            try conv env a1 a1'
            with NotConvertible -> raise (LocalArity None) in
          srec (push_rel (na1,None,a1) env) t ar' (union_constraints u univ)
      (* The last Prod domain is the type of the scrutinee *)
      | Prod (na1,a1,a2), [] -> (* whnf of t was not needed here! *)
	 let env' = push_rel (na1,None,a1) env in
	 let ksort = match kind_of_term (whd_betadeltaiota env' a2) with
       | Sort s -> family_of_sort s
       | _ -> raise (LocalArity None) in
	 let dep_ind = build_dependent_inductive ind specif params in
	 let univ =
           try conv env a1 dep_ind
           with NotConvertible -> raise (LocalArity None) in
	 check_allowed_sort ksort specif;
	 union_constraints u univ
      | _, (_,Some _,_ as d)::ar' ->
	 srec (push_rel d env) (lift 1 pt') ar' u
      | _ ->
	  raise (LocalArity None)
  in
  try srec env pj.uj_type (List.rev arsign) empty_constraint
  with LocalArity kinds ->
    error_elim_arity env ind (elim_sorts specif) c pj kinds


(************************************************************************)
(* Type of case branches *)

(* [p] is the predicate, [i] is the constructor number (starting from 0),
   and [cty] is the type of the constructor (params not instantiated) *)
let build_branches_type ind (_,mip as specif) params p =
  let build_one_branch i cty =
    let typi = full_constructor_instantiate (ind,specif,params) cty in
    let (args,ccl) = decompose_prod_assum typi in
    let nargs = rel_context_length args in
    let (_,allargs) = decompose_app ccl in
    let (lparams,vargs) = List.chop (inductive_params specif) allargs in
    let cargs =
      let cstr = ith_constructor_of_inductive ind (i+1) in
      let dep_cstr = applist (mkConstruct cstr,lparams@(local_rels args)) in
      vargs @ [dep_cstr] in
    let base = beta_appvect (lift nargs p) (Array.of_list cargs) in
    it_mkProd_or_LetIn base args in
  Array.mapi build_one_branch mip.mind_nf_lc

(* [p] is the predicate, [c] is the match object, [realargs] is the
   list of real args of the inductive type *)
let build_case_type n p c realargs =
  whd_betaiota (betazeta_appvect (n+1) p (Array.of_list (realargs@[c])))

let type_case_branches env (ind,largs) pj c =
  let specif = lookup_mind_specif env ind in
  let nparams = inductive_params specif in
  let (params,realargs) = List.chop nparams largs in
  let p = pj.uj_val in
  let univ = is_correct_arity env c pj ind specif params in
  let lc = build_branches_type ind specif params p in
  let ty = build_case_type (snd specif).mind_nrealargs_ctxt p c realargs in
  (lc, ty, univ)


(************************************************************************)
(* Checking the case annotation is relevent *)

let check_case_info env indsp ci =
  let (mib,mip) = lookup_mind_specif env indsp in
  if
    not (eq_ind indsp ci.ci_ind) ||
    not (Int.equal mib.mind_nparams ci.ci_npar) ||
    not (Array.equal Int.equal mip.mind_consnrealdecls ci.ci_cstr_ndecls) ||
    not (Array.equal Int.equal mip.mind_consnrealargs ci.ci_cstr_nargs)
  then raise (TypeError(env,WrongCaseInfo(indsp,ci)))

(************************************************************************)
(************************************************************************)

(* Guard conditions for fix and cofix-points *)

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

(*************************************************************)
(* Environment annotated with marks on recursive arguments *)

(* tells whether it is a strict or loose subterm *)
type size = Large | Strict

(* merging information *)
let size_glb s1 s2 =
  match s1,s2 with
      Strict, Strict -> Strict
    | _ -> Large

(* possible specifications for a term:
   - Not_subterm: when the size of a term is not related to the
     recursive argument of the fixpoint
   - Subterm: when the term is a subterm of the recursive argument
       the wf_paths argument specifies which subterms are recursive
   - Dead_code: when the term has been built by elimination over an
       empty type
 *)

type subterm_spec =
    Subterm of (size * wf_paths)
  | Dead_code
  | Not_subterm

let eq_wf_paths = Rtree.equal Declareops.eq_recarg

let spec_of_tree t =
  if eq_wf_paths t mk_norec
  then Not_subterm
  else Subterm (Strict, t)

let subterm_spec_glb =
  let glb2 s1 s2 = 
    match s1, s2 with
        s1, Dead_code -> s1
      | Dead_code, s2 -> s2
      | Not_subterm, _ -> Not_subterm
      | _, Not_subterm -> Not_subterm
      | Subterm (a1,t1), Subterm (a2,t2) ->
          if eq_wf_paths t1 t2 then Subterm (size_glb a1 a2, t1)
          (* branches do not return objects with same spec *)
          else Not_subterm in
  Array.fold_left glb2 Dead_code

type guard_env =
  { env     : env;
    (* dB of last fixpoint *)
    rel_min : int;
    (* dB of variables denoting subterms *)
    genv    : subterm_spec Lazy.t list;
  }

let make_renv env recarg (kn,tyi) =
  let mib = Environ.lookup_mind kn env in
  let mind_recvec =
    Array.map (fun mip -> mip.mind_recargs) mib.mind_packets in
  { env = env;
    rel_min = recarg+2;
    genv = [Lazy.lazy_from_val(Subterm(Large,mind_recvec.(tyi)))] }

let push_var renv (x,ty,spec) =
  { env = push_rel (x,None,ty) renv.env;
    rel_min = renv.rel_min+1;
    genv = spec:: renv.genv }

let assign_var_spec renv (i,spec) =
  { renv with genv = List.assign renv.genv (i-1) spec }

let push_var_renv renv (x,ty) =
  push_var renv (x,ty,lazy Not_subterm)

(* Fetch recursive information about a variable p *)
let subterm_var p renv =
  try Lazy.force (List.nth renv.genv (p-1))
  with Failure _ | Invalid_argument _ -> Not_subterm

let push_ctxt_renv renv ctxt =
  let n = rel_context_length ctxt in
  { env = push_rel_context ctxt renv.env;
    rel_min = renv.rel_min+n;
    genv = iterate (fun ge -> lazy Not_subterm::ge) n renv.genv }

let push_fix_renv renv (_,v,_ as recdef) =
  let n = Array.length v in
  { env = push_rec_types recdef renv.env;
    rel_min = renv.rel_min+n;
    genv = iterate (fun ge -> lazy Not_subterm::ge) n renv.genv }

(* Definition and manipulation of the stack *)
type stack_element = |SClosure of guard_env*constr |SArg of subterm_spec Lazy.t

let push_stack_closures renv l stack = 
  List.fold_right (fun h b -> (SClosure (renv,h))::b) l stack

let push_stack_args l stack = 
  List.fold_right (fun h b -> (SArg h)::b) l stack

(******************************)
(* {6 Computing the recursive subterms of a term (propagation of size
   information through Cases).} *)

let lookup_subterms env ind =
  let (_,mip) = lookup_mind_specif env ind in
  mip.mind_recargs


let match_inductive ind ra =
  match ra with
    | (Mrec i | Imbr i) -> eq_ind ind i
    | Norec -> false

(* In {match c as z in ci y_s return P with |C_i x_s => t end}
   [branches_specif renv c_spec ci] returns an array of x_s specs knowing
   c_spec. *)
let branches_specif renv c_spec ci =
  let car = 
    (* We fetch the regular tree associated to the inductive of the match.
       This is just to get the number of constructors (and constructor
       arities) that fit the match branches without forcing c_spec.
       Note that c_spec might be more precise than [v] below, because of
       nested inductive types. *)
    let (_,mip) = lookup_mind_specif renv.env ci.ci_ind in
    let v = dest_subterms mip.mind_recargs in
      Array.map List.length v in
    Array.mapi
      (fun i nca -> (* i+1-th cstructor has arity nca *)
	 let lvra = lazy 
	   (match Lazy.force c_spec with
		Subterm (_,t) when match_inductive ci.ci_ind (dest_recarg t) ->
		  let vra = Array.of_list (dest_subterms t).(i) in
		  assert (Int.equal nca (Array.length vra));
		  Array.map spec_of_tree vra
	      | Dead_code -> Array.make nca Dead_code
	      | _ -> Array.make nca Not_subterm) in
	 List.init nca (fun j -> lazy (Lazy.force lvra).(j)))
      car 

let check_inductive_codomain env p =
  let absctx, ar = dest_lam_assum env p in
  let arctx, s = dest_prod_assum env ar in
  let i,l' = decompose_app (whd_betadeltaiota env s) in
    isInd i

(* [subterm_specif renv t] computes the recursive structure of [t] and
   compare its size with the size of the initial recursive argument of
   the fixpoint we are checking. [renv] collects such information
   about variables.
*)

let rec subterm_specif renv stack t =
  (* maybe reduction is not always necessary! *)
  let f,l = decompose_app (whd_betadeltaiota renv.env t) in
    match kind_of_term f with
    | Rel k -> subterm_var k renv

    | Case (ci,p,c,lbr) ->
    let stack' = push_stack_closures renv l stack in
      if not (check_inductive_codomain renv.env p) then Not_subterm
      else
        let cases_spec = branches_specif renv 
	  (lazy_subterm_specif renv [] c) ci in
        let stl  =
	  Array.mapi (fun i br' ->
	  let stack_br = push_stack_args (cases_spec.(i)) stack' in
	    subterm_specif renv stack_br br')
	  lbr in
	  subterm_spec_glb stl

    | Fix ((recindxs,i),(_,typarray,bodies as recdef)) ->
      (* when proving that the fixpoint f(x)=e is less than n, it is enough
	 to prove that e is less than n assuming f is less than n
	 furthermore when f is applied to a term which is strictly less than
	 n, one may assume that x itself is strictly less than n
      *)
    if not (check_inductive_codomain renv.env typarray.(i)) then Not_subterm
    else 
      let (ctxt,clfix) = dest_prod renv.env typarray.(i) in	    
      let oind =
        let env' = push_rel_context ctxt renv.env in
          try Some(fst(find_inductive env' clfix))
          with Not_found -> None in
        (match oind with
      None -> Not_subterm (* happens if fix is polymorphic *)
        | Some ind ->
	let nbfix = Array.length typarray in
	let recargs = lookup_subterms renv.env ind in
		   (* pushing the fixpoints *)
	let renv' = push_fix_renv renv recdef in
	let renv' =
                     (* Why Strict here ? To be general, it could also be
			Large... *)
          assign_var_spec renv'
	  (nbfix-i, lazy (Subterm(Strict,recargs))) in
	let decrArg = recindxs.(i) in
	let theBody = bodies.(i)   in
	let nbOfAbst = decrArg+1 in
	let sign,strippedBody = decompose_lam_n_assum nbOfAbst theBody in
		   (* pushing the fix parameters *)
	let stack' = push_stack_closures renv l stack in
	let renv'' = push_ctxt_renv renv' sign in
	let renv'' =
          if List.length stack' < nbOfAbst then renv''
          else
	    let decrArg = List.nth stack' decrArg in
            let arg_spec = stack_element_specif decrArg in
	      assign_var_spec renv'' (1, arg_spec) in
	  subterm_specif renv'' [] strippedBody)

    | Lambda (x,a,b) ->
      let () = assert (List.is_empty l) in
      let spec,stack' = extract_stack renv a stack in
	subterm_specif (push_var renv (x,a,spec)) stack' b

      (* Metas and evars are considered OK *)
    | (Meta _|Evar _) -> Dead_code

      (* Other terms are not subterms *)
    | _ -> Not_subterm

and lazy_subterm_specif renv stack t =
  lazy (subterm_specif renv stack t)

and stack_element_specif = function
  |SClosure (h_renv,h) -> lazy_subterm_specif h_renv [] h
  |SArg x -> x

and extract_stack renv a = function
  | [] -> Lazy.lazy_from_val Not_subterm , []
  | h::t -> stack_element_specif h, t

(* Check term c can be applied to one of the mutual fixpoints. *)
let check_is_subterm x =
  match Lazy.force x with
    Subterm (Strict,_) | Dead_code -> true
  |  _ -> false

(************************************************************************)

exception FixGuardError of env * guard_error

let error_illegal_rec_call renv fx (arg_renv,arg) =
  let (_,le_vars,lt_vars) =
    List.fold_left
      (fun (i,le,lt) sbt ->
        match Lazy.force sbt with
            (Subterm(Strict,_) | Dead_code) -> (i+1, le, i::lt)
          | (Subterm(Large,_)) -> (i+1, i::le, lt)
          | _ -> (i+1, le ,lt))
      (1,[],[]) renv.genv in
  raise (FixGuardError (renv.env,
                        RecursionOnIllegalTerm(fx,(arg_renv.env, arg),
					       le_vars,lt_vars)))

let error_partial_apply renv fx =
  raise (FixGuardError (renv.env,NotEnoughArgumentsForFixCall fx))

(* Check if [def] is a guarded fixpoint body with decreasing arg.
   given [recpos], the decreasing arguments of each mutually defined
   fixpoint. *)
let check_one_fix renv recpos def =
  let nfi = Array.length recpos in

  (* Checks if [t] only make valid recursive calls 
     [stack] is the list of constructor's argument specification and 
     arguments than will be applied after reduction.
     example u in t where we have (match .. with |.. => t end) u *)
  let rec check_rec_call renv stack t =
    (* if [t] does not make recursive calls, it is guarded: *)
    if noccur_with_meta renv.rel_min nfi t then ()
    else
      let (f,l) = decompose_app (whd_betaiotazeta t) in
      match kind_of_term f with
        | Rel p ->
            (* Test if [p] is a fixpoint (recursive call) *)
	    if renv.rel_min <= p && p < renv.rel_min+nfi then
              begin
                List.iter (check_rec_call renv []) l;
                (* the position of the invoked fixpoint: *)
	        let glob = renv.rel_min+nfi-1-p in
                (* the decreasing arg of the rec call: *)
	        let np = recpos.(glob) in
		let stack' = push_stack_closures renv l stack in
                if List.length stack' <= np then error_partial_apply renv glob
                else
                  (* Check the decreasing arg is smaller *)
                  let z = List.nth stack' np in
	          if not (check_is_subterm (stack_element_specif z)) then
                    begin match z with
		      |SClosure (z,z') -> error_illegal_rec_call renv glob (z,z') 
		      |SArg _ -> error_partial_apply renv glob
		    end
              end
            else
              begin
                match pi2 (lookup_rel p renv.env) with
                | None ->
                    List.iter (check_rec_call renv []) l
                | Some c ->
                    try List.iter (check_rec_call renv []) l
                    with FixGuardError _ ->
                      check_rec_call renv stack (applist(lift p c,l))
              end
		
        | Case (ci,p,c_0,lrest) ->
            List.iter (check_rec_call renv []) (c_0::p::l);
            (* compute the recarg information for the arguments of
               each branch *)
            let case_spec = branches_specif renv 
	      (lazy_subterm_specif renv [] c_0) ci in
	    let stack' = push_stack_closures renv l stack in
              Array.iteri (fun k br' -> 
			     let stack_br = push_stack_args case_spec.(k) stack' in
			     check_rec_call renv stack_br br') lrest

        (* Enables to traverse Fixpoint definitions in a more intelligent
           way, ie, the rule :
           if - g = fix g (y1:T1)...(yp:Tp) {struct yp} := e &
              - f is guarded with respect to the set of pattern variables S
                in a1 ... am        &
              - f is guarded with respect to the set of pattern variables S
                in T1 ... Tp        &
              - ap is a sub-term of the formal argument of f &
              - f is guarded with respect to the set of pattern variables
                S+{yp} in e
           then f is guarded with respect to S in (g a1 ... am).
           Eduardo 7/9/98 *)
        | Fix ((recindxs,i),(_,typarray,bodies as recdef)) ->
            List.iter (check_rec_call renv []) l;
            Array.iter (check_rec_call renv []) typarray;
            let decrArg = recindxs.(i) in
            let renv' = push_fix_renv renv recdef in
	    let stack' = push_stack_closures renv l stack in
              Array.iteri
                (fun j body ->
                   if Int.equal i j && (List.length stack' > decrArg) then
		     let recArg = List.nth stack' decrArg in
	             let arg_sp = stack_element_specif recArg in
	             check_nested_fix_body renv' (decrArg+1) arg_sp body
                   else check_rec_call renv' [] body)
                bodies

        | Const kn ->
            if evaluable_constant kn renv.env then
              try List.iter (check_rec_call renv []) l
              with (FixGuardError _ ) ->
		let value = (applist(constant_value renv.env kn, l)) in
	        check_rec_call renv stack value
	    else List.iter (check_rec_call renv []) l

        | Lambda (x,a,b) ->
            let () = assert (List.is_empty l) in
	    check_rec_call renv [] a ;
	    let spec, stack' = extract_stack renv a stack in
	    check_rec_call (push_var renv (x,a,spec)) stack' b

        | Prod (x,a,b) ->
            let () = assert (List.is_empty l && List.is_empty stack) in
            check_rec_call renv [] a;
            check_rec_call (push_var_renv renv (x,a)) [] b

        | CoFix (i,(_,typarray,bodies as recdef)) ->
            List.iter (check_rec_call renv []) l;
	    Array.iter (check_rec_call renv []) typarray;
	    let renv' = push_fix_renv renv recdef in
	    Array.iter (check_rec_call renv' []) bodies

        | (Ind _ | Construct _) ->
            List.iter (check_rec_call renv []) l

        | Var id ->
            begin
              match pi2 (lookup_named id renv.env) with
              | None ->
                  List.iter (check_rec_call renv []) l
              | Some c ->
                  try List.iter (check_rec_call renv []) l
                  with (FixGuardError _) -> 
		    check_rec_call renv stack (applist(c,l))
            end

	| Sort _ ->
          assert (List.is_empty l)

        (* l is not checked because it is considered as the meta's context *)
        | (Evar _ | Meta _) -> ()

        | (App _ | LetIn _ | Cast _) -> assert false (* beta zeta reduction *)

  and check_nested_fix_body renv decr recArgsDecrArg body =
    if Int.equal decr 0 then
      check_rec_call (assign_var_spec renv (1,recArgsDecrArg)) [] body
    else
      match kind_of_term body with
	| Lambda (x,a,b) ->
	    check_rec_call renv [] a;
            let renv' = push_var_renv renv (x,a) in
	      check_nested_fix_body renv' (decr-1) recArgsDecrArg b
	| _ -> anomaly (Pp.str "Not enough abstractions in fix body")
	    
  in
  check_rec_call renv [] def

let judgment_of_fixpoint (_, types, bodies) =
  Array.map2 (fun typ body -> { uj_val = body ; uj_type = typ }) types bodies

let inductive_of_mutfix env ((nvect,bodynum),(names,types,bodies as recdef)) =
  let nbfix = Array.length bodies in
  if Int.equal nbfix 0
    || not (Int.equal (Array.length nvect) nbfix)
    || not (Int.equal (Array.length types) nbfix)
    || not (Int.equal (Array.length names) nbfix)
    || bodynum < 0
    || bodynum >= nbfix
  then anomaly (Pp.str "Ill-formed fix term");
  let fixenv = push_rec_types recdef env in
  let vdefj = judgment_of_fixpoint recdef in
  let raise_err env i err =
    error_ill_formed_rec_body env err names i fixenv vdefj in
  (* Check the i-th definition with recarg k *)
  let find_ind i k def =
    (* check fi does not appear in the k+1 first abstractions,
       gives the type of the k+1-eme abstraction (must be an inductive)  *)
    let rec check_occur env n def =
      match kind_of_term (whd_betadeltaiota env def) with
        | Lambda (x,a,b) ->
	    if noccur_with_meta n nbfix a then
	      let env' = push_rel (x, None, a) env in
              if Int.equal n (k + 1) then
                (* get the inductive type of the fixpoint *)
                let (mind, _) =
                  try find_inductive env a
                  with Not_found ->
		    raise_err env i (RecursionNotOnInductiveType a) in
                (mind, (env', b))
	      else check_occur env' (n+1) b
            else anomaly ~label:"check_one_fix" (Pp.str "Bad occurrence of recursive call")
        | _ -> raise_err env i NotEnoughAbstractionInFixBody in
    check_occur fixenv 1 def in
  (* Do it on every fixpoint *)
  let rv = Array.map2_i find_ind nvect bodies in
  (Array.map fst rv, Array.map snd rv)


let check_fix env ((nvect,_),(names,_,bodies as recdef) as fix) =
  let (minds, rdef) = inductive_of_mutfix env fix in
  for i = 0 to Array.length bodies - 1 do
    let (fenv,body) = rdef.(i) in
    let renv = make_renv fenv nvect.(i) minds.(i) in
    try check_one_fix renv nvect body
    with FixGuardError (fixenv,err) ->
      error_ill_formed_rec_body fixenv err names i
	(push_rec_types recdef env) (judgment_of_fixpoint recdef)
  done

(*
let cfkey = Profile.declare_profile "check_fix";;
let check_fix env fix = Profile.profile3 cfkey check_fix env fix;;
*)

(************************************************************************)
(* Co-fixpoints. *)

exception CoFixGuardError of env * guard_error

let anomaly_ill_typed () =
  anomaly ~label:"check_one_cofix" (Pp.str "too many arguments applied to constructor")

let rec codomain_is_coind env c =
  let b = whd_betadeltaiota env c in
  match kind_of_term b with
    | Prod (x,a,b) ->
	codomain_is_coind (push_rel (x, None, a) env) b
    | _ ->
	(try find_coinductive env b
        with Not_found ->
	  raise (CoFixGuardError (env, CodomainNotInductiveType b)))

let check_one_cofix env nbfix def deftype =
  let rec check_rec_call env alreadygrd n vlra  t =
    if not (noccur_with_meta n nbfix t) then
      let c,args = decompose_app (whd_betadeltaiota env t) in
      match kind_of_term c with
	| Rel p when  n <= p && p < n+nbfix ->
	    (* recursive call: must be guarded and no nested recursive
               call allowed *)
            if not alreadygrd then
	      raise (CoFixGuardError (env,UnguardedRecursiveCall t))
            else if not(List.for_all (noccur_with_meta n nbfix) args) then
	      raise (CoFixGuardError (env,NestedRecursiveOccurrences))

	| Construct (_,i as cstr_kn)  ->
            let lra = vlra.(i-1) in
            let mI = inductive_of_constructor cstr_kn in
	    let (mib,mip) = lookup_mind_specif env mI in
            let realargs = List.skipn mib.mind_nparams args in
            let rec process_args_of_constr = function
              | (t::lr), (rar::lrar) ->
                  if eq_wf_paths rar mk_norec then
                    if noccur_with_meta n nbfix t
                    then process_args_of_constr (lr, lrar)
                    else raise (CoFixGuardError
		                 (env,RecCallInNonRecArgOfConstructor t))
                  else
                    let spec = dest_subterms rar in
                    check_rec_call env true n spec t;
                    process_args_of_constr (lr, lrar)
              | [],_ -> ()
              | _ -> anomaly_ill_typed ()
            in process_args_of_constr (realargs, lra)

	| Lambda (x,a,b) ->
	    let () = assert (List.is_empty args) in
            if noccur_with_meta n nbfix a then
              let env' = push_rel (x, None, a) env in
              check_rec_call env' alreadygrd (n+1)  vlra b
            else
	      raise (CoFixGuardError (env,RecCallInTypeOfAbstraction a))

	| CoFix (j,(_,varit,vdefs as recdef)) ->
            if List.for_all (noccur_with_meta n nbfix) args
            then
	      if Array.for_all (noccur_with_meta n nbfix) varit then
		let nbfix = Array.length vdefs in
		let env' = push_rec_types recdef env in
		(Array.iter (check_rec_call env' alreadygrd (n+nbfix) vlra) vdefs;
		 List.iter (check_rec_call env alreadygrd n vlra) args)
              else
		raise (CoFixGuardError (env,RecCallInTypeOfDef c))
	    else
	      raise (CoFixGuardError (env,UnguardedRecursiveCall c))

	| Case (_,p,tm,vrest) ->
            if (noccur_with_meta n nbfix p) then
              if (noccur_with_meta n nbfix tm) then
		if (List.for_all (noccur_with_meta n nbfix) args) then
		  Array.iter (check_rec_call env alreadygrd n vlra) vrest
		else
		  raise (CoFixGuardError (env,RecCallInCaseFun c))
              else
		raise (CoFixGuardError (env,RecCallInCaseArg c))
            else
	      raise (CoFixGuardError (env,RecCallInCasePred c))

	| Meta _ -> ()
        | Evar _ ->
	    List.iter (check_rec_call env alreadygrd n vlra) args

	| _    -> raise (CoFixGuardError (env,NotGuardedForm t)) in

  let (mind, _) = codomain_is_coind env deftype in
  let vlra = lookup_subterms env mind in
  check_rec_call env false 1 (dest_subterms vlra) def

(* The  function which checks that the whole block of definitions
   satisfies the guarded condition *)

let check_cofix env (bodynum,(names,types,bodies as recdef)) =
  let nbfix = Array.length bodies in
  for i = 0 to nbfix-1 do
    let fixenv = push_rec_types recdef env in
    try check_one_cofix fixenv nbfix bodies.(i) types.(i)
    with CoFixGuardError (errenv,err) ->
      error_ill_formed_rec_body errenv err names i
	fixenv (judgment_of_fixpoint recdef)
  done

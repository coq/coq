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
open Univ
open Constr
open Vars
open Declarations
open Declareops
open Environ
open Reduction
open Type_errors
open Context.Rel.Declaration

type mind_specif = mutual_inductive_body * one_inductive_body

(* raise Not_found if not an inductive type *)
let lookup_mind_specif env (kn,tyi) =
  let mib = Environ.lookup_mind kn env in
  if tyi >= Array.length mib.mind_packets then
    user_err Pp.(str "Inductive.lookup_mind_specif: invalid inductive index");
  (mib, mib.mind_packets.(tyi))

let find_rectype env c =
  let (t, l) = decompose_app (whd_all env c) in
  match kind t with
  | Ind ind -> (ind, l)
  | _ -> raise Not_found

let find_inductive env c =
  let (t, l) = decompose_app (whd_all env c) in
  match kind t with
    | Ind ind
        when (fst (lookup_mind_specif env (out_punivs ind))).mind_finite <> CoFinite -> (ind, l)
    | _ -> raise Not_found

let find_coinductive env c =
  let (t, l) = decompose_app (whd_all env c) in
  match kind t with
    | Ind ind
        when (fst (lookup_mind_specif env (out_punivs ind))).mind_finite == CoFinite -> (ind, l)
    | _ -> raise Not_found

let inductive_params (mib,_) = mib.mind_nparams

let inductive_paramdecls (mib,u) = 
  Vars.subst_instance_context u mib.mind_params_ctxt

let instantiate_inductive_constraints mib u =
  let process auctx =  Univ.AUContext.instantiate u auctx in
  match mib.mind_universes with
  | Monomorphic_ind _ -> Univ.Constraint.empty
  | Polymorphic_ind auctx -> process auctx
  | Cumulative_ind cumi -> process (Univ.ACumulativityInfo.univ_context cumi)


(************************************************************************)

(* Build the substitution that replaces Rels by the appropriate *)
(* inductives *)
let ind_subst mind mib u =
  let ntypes = mib.mind_ntypes in
  let make_Ik k = mkIndU ((mind,ntypes-k-1),u) in
  List.init ntypes make_Ik

(* Instantiate inductives in constructor type *)
let constructor_instantiate mind u mib c =
  let s = ind_subst mind mib u in
    substl s (subst_instance_constr u c)

let instantiate_params full t u args sign =
  let fail () =
    anomaly ~label:"instantiate_params" (Pp.str "type, ctxt and args mismatch.") in
  let (rem_args, subs, ty) =
    Context.Rel.fold_outside
      (fun decl (largs,subs,ty) ->
        match (decl, largs, kind ty) with
          | (LocalAssum _, a::args, Prod(_,_,t)) -> (args, a::subs, t)
          | (LocalDef (_,b,_), _, LetIn(_,_,_,t))    ->
	     (largs, (substl subs (subst_instance_constr u b))::subs, t)
	  | (_,[],_)                -> if full then fail() else ([], subs, ty)
	  | _                       -> fail ())
      sign
      ~init:(args,[],t)
  in
  let () = if not (List.is_empty rem_args) then fail () in
  substl subs ty

let full_inductive_instantiate mib u params sign =
  let dummy = Sorts.prop in
  let t = Term.mkArity (Vars.subst_instance_context u sign,dummy) in
    fst (Term.destArity (instantiate_params true t u params mib.mind_params_ctxt))

let full_constructor_instantiate ((mind,_),u,(mib,_),params) t =
  let inst_ind = constructor_instantiate mind u mib t in
   instantiate_params true inst_ind u params mib.mind_params_ctxt
		      
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

(* Template polymorphism *)

(* cons_subst add the mapping [u |-> su] in subst if [u] is not *)
(* in the domain or add [u |-> sup x su] if [u] is already mapped *)
(* to [x]. *)
let cons_subst u su subst =
  try
    Univ.LMap.add u (Univ.sup (Univ.LMap.find u subst) su) subst
  with Not_found -> Univ.LMap.add u su subst

(* remember_subst updates the mapping [u |-> x] by [u |-> sup x u] *)
(* if it is presents and returns the substitution unchanged if not.*)
let remember_subst u subst =
  try
    let su = Universe.make u in
    Univ.LMap.add u (Univ.sup (Univ.LMap.find u subst) su) subst
  with Not_found -> subst

(* Bind expected levels of parameters to actual levels *)
(* Propagate the new levels in the signature *)
let make_subst env =
  let rec make subst = function
    | LocalDef _ :: sign, exp, args ->
        make subst (sign, exp, args)
    | _d::sign, None::exp, args ->
        let args = match args with _::args -> args | [] -> [] in
        make subst (sign, exp, args)
    | _d::sign, Some u::exp, a::args ->
        (* We recover the level of the argument, but we don't change the *)
        (* level in the corresponding type in the arity; this level in the *)
        (* arity is a global level which, at typing time, will be enforce *)
        (* to be greater than the level of the argument; this is probably *)
        (* a useless extra constraint *)
        let s = Sorts.univ_of_sort (snd (dest_arity env (Lazy.force a))) in
          make (cons_subst u s subst) (sign, exp, args)
    | LocalAssum (_na,_t) :: sign, Some u::exp, [] ->
        (* No more argument here: we add the remaining universes to the *)
        (* substitution (when [u] is distinct from all other universes in the *)
        (* template, it is identity substitution  otherwise (ie. when u is *)
        (* already in the domain of the substitution) [remember_subst] will *)
        (* update its image [x] by [sup x u] in order not to forget the *)
        (* dependency in [u] that remains to be fullfilled. *)
        make (remember_subst u subst) (sign, exp, [])
    | _sign, [], _ ->
        (* Uniform parameters are exhausted *)
        subst
    | [], _, _ ->
        assert false
  in
  make Univ.LMap.empty

exception SingletonInductiveBecomesProp of Id.t

let instantiate_universes env ctx ar argsorts =
  let args = Array.to_list argsorts in
  let subst = make_subst env (ctx,ar.template_param_levels,args) in
  let level = Univ.subst_univs_universe (Univ.make_subst subst) ar.template_level in
  let ty =
    (* Singleton type not containing types are interpretable in Prop *)
    if is_type0m_univ level then Sorts.prop
    (* Non singleton type not containing types are interpretable in Set *)
    else if is_type0_univ level then Sorts.set
    (* This is a Type with constraints *)
    else Sorts.Type level
  in
    (ctx, ty)

(* Type of an inductive type *)

let type_of_inductive_gen ?(polyprop=true) env ((_mib,mip),u) paramtyps =
  match mip.mind_arity with
  | RegularArity a -> subst_instance_constr u a.mind_user_arity
  | TemplateArity ar ->
    let ctx = List.rev mip.mind_arity_ctxt in
    let ctx,s = instantiate_universes env ctx ar paramtyps in
      (* The Ocaml extraction cannot handle (yet?) "Prop-polymorphism", i.e.
         the situation where a non-Prop singleton inductive becomes Prop
         when applied to Prop params *)
      if not polyprop && not (is_type0m_univ ar.template_level) && Sorts.is_prop s
      then raise (SingletonInductiveBecomesProp mip.mind_typename);
      Term.mkArity (List.rev ctx,s)

let type_of_inductive env pind = 
  type_of_inductive_gen env pind [||]

let constrained_type_of_inductive env ((mib,_mip),u as pind) =
  let ty = type_of_inductive env pind in
  let cst = instantiate_inductive_constraints mib u in
    (ty, cst)

let constrained_type_of_inductive_knowing_parameters env ((mib,_mip),u as pind) args =
  let ty = type_of_inductive_gen env pind args in
  let cst = instantiate_inductive_constraints mib u in
    (ty, cst)

let type_of_inductive_knowing_parameters env ?(polyprop=true) mip args =
  type_of_inductive_gen ~polyprop env mip args

(* The max of an array of universes *)

let cumulate_constructor_univ u = let open Sorts in function
  | Prop -> u
  | Set -> Universe.sup Universe.type0 u
  | Type u' -> Universe.sup u u'

let max_inductive_sort =
  Array.fold_left cumulate_constructor_univ Universe.type0m

(************************************************************************)
(* Type of a constructor *)

let type_of_constructor (cstr, u) (mib,mip) =
  let ind = inductive_of_constructor cstr in
  let specif = mip.mind_user_lc in
  let i = index_of_constructor cstr in
  let nconstr = Array.length mip.mind_consnames in
  if i > nconstr then user_err Pp.(str "Not enough constructors in the type.");
  constructor_instantiate (fst ind) u mib specif.(i-1)

let constrained_type_of_constructor (_cstr,u as cstru) (mib,_mip as ind) =
  let ty = type_of_constructor cstru ind in
  let cst = instantiate_inductive_constraints mib u in
    (ty, cst)

let arities_of_specif (kn,u) (mib,mip) =
  let specif = mip.mind_nf_lc in
    Array.map (constructor_instantiate kn u mib) specif

let arities_of_constructors ind specif =
  arities_of_specif (fst (fst ind), snd ind) specif

let type_of_constructors (ind,u) (mib,mip) =
  let specif = mip.mind_user_lc in
    Array.map (constructor_instantiate (fst ind) u mib) specif

(************************************************************************)

(* Type of case predicates *)

(* Get type of inductive, with parameters instantiated *)

let inductive_sort_family mip =
  match mip.mind_arity with
  | RegularArity s -> Sorts.family s.mind_sort
  | TemplateArity _ -> Sorts.InType

let mind_arity mip =
  mip.mind_arity_ctxt, inductive_sort_family mip

let get_instantiated_arity (_ind,u) (mib,mip) params =
  let sign, s = mind_arity mip in
  full_inductive_instantiate mib u params sign, s

let elim_sorts (_,mip) = mip.mind_kelim

let is_private (mib,_) = mib.mind_private = Some true
let is_primitive_record (mib,_) = 
  match mib.mind_record with
  | PrimRecord _ -> true
  | NotRecord | FakeRecord -> false

let build_dependent_inductive ind (_,mip) params =
  let realargs,_ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
  Term.applist
    (mkIndU ind,
       List.map (lift mip.mind_nrealdecls) params
       @ Context.Rel.to_extended_list mkRel 0 realargs)

(* This exception is local *)
exception LocalArity of (Sorts.family * Sorts.family * arity_error) option

let check_allowed_sort ksort specif =
  let open Sorts in
  let eq_ksort s = match ksort, s with
  | InProp, InProp | InSet, InSet | InType, InType -> true
  | _ -> false in
  if not (CList.exists eq_ksort (elim_sorts specif)) then
    let s = inductive_sort_family (snd specif) in
    raise (LocalArity (Some(ksort,s,error_elim_explain ksort s)))

let is_correct_arity env c pj ind specif params =
  let arsign,_ = get_instantiated_arity ind specif params in
  let rec srec env pt ar =
    let pt' = whd_all env pt in
    match kind pt', ar with
      | Prod (na1,a1,t), (LocalAssum (_,a1'))::ar' ->
          let () =
            try conv env a1 a1'
            with NotConvertible -> raise (LocalArity None) in
          srec (push_rel (LocalAssum (na1,a1)) env) t ar'
      (* The last Prod domain is the type of the scrutinee *)
      | Prod (na1,a1,a2), [] -> (* whnf of t was not needed here! *)
	 let env' = push_rel (LocalAssum (na1,a1)) env in
	 let ksort = match kind (whd_all env' a2) with
	 | Sort s -> Sorts.family s
	 | _ -> raise (LocalArity None) in
	 let dep_ind = build_dependent_inductive ind specif params in
	 let _ =
           try conv env a1 dep_ind
           with NotConvertible -> raise (LocalArity None) in
	   check_allowed_sort ksort specif
      | _, (LocalDef _ as d)::ar' ->
	  srec (push_rel d env) (lift 1 pt') ar'
      | _ ->
	  raise (LocalArity None)
  in
  try srec env pj.uj_type (List.rev arsign) 
  with LocalArity kinds ->
    error_elim_arity env ind (elim_sorts specif) c pj kinds


(************************************************************************)
(* Type of case branches *)

(* [p] is the predicate, [i] is the constructor number (starting from 0),
   and [cty] is the type of the constructor (params not instantiated) *)
let build_branches_type (ind,u) (_,mip as specif) params p =
  let build_one_branch i cty =
    let typi = full_constructor_instantiate (ind,u,specif,params) cty in
    let (cstrsign,ccl) = Term.decompose_prod_assum typi in
    let nargs = Context.Rel.length cstrsign in
    let (_,allargs) = decompose_app ccl in
    let (lparams,vargs) = List.chop (inductive_params specif) allargs in
    let cargs =
      let cstr = ith_constructor_of_inductive ind (i+1) in
      let dep_cstr = Term.applist (mkConstructU (cstr,u),lparams@(Context.Rel.to_extended_list mkRel 0 cstrsign)) in
      vargs @ [dep_cstr] in
    let base = Term.lambda_appvect_assum (mip.mind_nrealdecls+1) (lift nargs p) (Array.of_list cargs) in
    Term.it_mkProd_or_LetIn base cstrsign in
  Array.mapi build_one_branch mip.mind_nf_lc

(* [p] is the predicate, [c] is the match object, [realargs] is the
   list of real args of the inductive type *)
let build_case_type env n p c realargs =
  whd_betaiota env (Term.lambda_appvect_assum (n+1) p (Array.of_list (realargs@[c])))

let type_case_branches env (pind,largs) pj c =
  let specif = lookup_mind_specif env (fst pind) in
  let nparams = inductive_params specif in
  let (params,realargs) = List.chop nparams largs in
  let p = pj.uj_val in
  let () = is_correct_arity env c pj pind specif params in
  let lc = build_branches_type pind specif params p in
  let ty = build_case_type env (snd specif).mind_nrealdecls p c realargs in
  (lc, ty)


(************************************************************************)
(* Checking the case annotation is relevant *)

let check_case_info env (indsp,u) ci =
  let (mib,mip as spec) = lookup_mind_specif env indsp in
  if
    not (eq_ind indsp ci.ci_ind) ||
    not (Int.equal mib.mind_nparams ci.ci_npar) ||
    not (Array.equal Int.equal mip.mind_consnrealdecls ci.ci_cstr_ndecls) ||
    not (Array.equal Int.equal mip.mind_consnrealargs ci.ci_cstr_nargs) ||
    is_primitive_record spec
  then raise (TypeError(env,WrongCaseInfo((indsp,u),ci)))

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

let inter_recarg r1 r2 = match r1, r2 with
| Norec, Norec -> Some r1
| Mrec i1, Mrec i2
| Imbr i1, Imbr i2
| Mrec i1, Imbr i2 -> if Names.eq_ind i1 i2 then Some r1 else None
| Imbr i1, Mrec i2 -> if Names.eq_ind i1 i2 then Some r2 else None
| _ -> None

let inter_wf_paths = Rtree.inter Declareops.eq_recarg inter_recarg Norec

let incl_wf_paths = Rtree.incl Declareops.eq_recarg inter_recarg Norec

let spec_of_tree t =
  if eq_wf_paths t mk_norec
  then Not_subterm
  else Subterm (Strict, t)

let inter_spec s1 s2 =
  match s1, s2 with
  | _, Dead_code -> s1
  | Dead_code, _ -> s2
  | Not_subterm, _ -> s1
  | _, Not_subterm -> s2
  | Subterm (a1,t1), Subterm (a2,t2) ->
     Subterm (size_glb a1 a2, inter_wf_paths t1 t2)

let subterm_spec_glb =
  Array.fold_left inter_spec Dead_code

type guard_env =
  { env     : env;
    (* dB of last fixpoint *)
    rel_min : int;
    (* dB of variables denoting subterms *)
    genv    : subterm_spec Lazy.t list;
  }

let make_renv env recarg tree =
  { env = env;
    rel_min = recarg+2; (* recarg = 0 ==> Rel 1 -> recarg; Rel 2 -> fix *)
    genv = [Lazy.from_val(Subterm(Large,tree))] }

let push_var renv (x,ty,spec) =
  { env = push_rel (LocalAssum (x,ty)) renv.env;
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
  let n = Context.Rel.length ctxt in
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
  let env = push_rel_context absctx env in
  let arctx, s = dest_prod_assum env ar in
  let env = push_rel_context arctx env in
  let i,_l' = decompose_app (whd_all env s) in
  isInd i

(* The following functions are almost duplicated from indtypes.ml, except
that they carry here a poorer environment (containing less information). *)
let ienv_push_var (env, lra) (x,a,ra) =
  (push_rel (LocalAssum (x,a)) env, (Norec,ra)::lra)

let ienv_push_inductive (env, ra_env) ((mind,u),lpar) =
  let mib = Environ.lookup_mind mind env in
  let ntypes = mib.mind_ntypes in
  let push_ind specif env =
    let decl = LocalAssum (Anonymous, hnf_prod_applist env (type_of_inductive env ((mib,specif),u)) lpar) in
    push_rel decl env
  in
  let env = Array.fold_right push_ind mib.mind_packets env in
  let rc = Array.mapi (fun j t -> (Imbr (mind,j),t)) (Rtree.mk_rec_calls ntypes) in
  let lra_ind = Array.rev_to_list rc in
  let ra_env = List.map (fun (r,t) -> (r,Rtree.lift ntypes t)) ra_env in
  (env, lra_ind @ ra_env)

let rec ienv_decompose_prod (env,_ as ienv) n c =
 if Int.equal n 0 then (ienv,c) else
   let c' = whd_all env c in
   match kind c' with
   Prod(na,a,b) ->
     let ienv' = ienv_push_var ienv (na,a,mk_norec) in
     ienv_decompose_prod ienv' (n-1) b
     | _ -> assert false

let dummy_univ = Level.(make (UGlobal.make (DirPath.make [Id.of_string "implicit"]) 0))
let dummy_implicit_sort = mkType (Universe.make dummy_univ)
let lambda_implicit_lift n a =
  let lambda_implicit a = mkLambda (Anonymous, dummy_implicit_sort, a) in
  iterate lambda_implicit n (lift n a)

(* This removes global parameters of the inductive types in lc (for
   nested inductive types only ) *)
let abstract_mind_lc ntyps npars lc =
  if Int.equal npars 0 then
    lc
  else
    let make_abs =
      List.init ntyps
	(function i -> lambda_implicit_lift npars (mkRel (i+1)))
    in
    Array.map (substl make_abs) lc

(* [get_recargs_approx env tree ind args] builds an approximation of the recargs
tree for ind, knowing args. The argument tree is used to know when candidate
nested types should be traversed, pruning the tree otherwise. This code is very
close to check_positive in indtypes.ml, but does no positivity check and does not
compute the number of recursive arguments. *)
let get_recargs_approx env tree ind args =
  let rec build_recargs (env, ra_env as ienv) tree c =
    let x,largs = decompose_app (whd_all env c) in
    match kind x with
    | Prod (na,b,d) ->
       assert (List.is_empty largs);
       build_recargs (ienv_push_var ienv (na, b, mk_norec)) tree d
    | Rel k ->
       (* Free variables are allowed and assigned Norec *)
       (try snd (List.nth ra_env (k-1))
        with Failure _ | Invalid_argument _ -> mk_norec)
    | Ind ind_kn ->
       (* When the inferred tree allows it, we consider that we have a potential
       nested inductive type *)
       begin match dest_recarg tree with
	     | Imbr kn' | Mrec kn' when eq_ind (fst ind_kn) kn' ->
			   build_recargs_nested ienv tree (ind_kn, largs)
	     | _ -> mk_norec
       end
    | _err ->
       mk_norec

  and build_recargs_nested (env,_ra_env as ienv) tree (((mind,i),u), largs) =
    (* If the inferred tree already disallows recursion, no need to go further *)
    if eq_wf_paths tree mk_norec then tree
    else
    let mib = Environ.lookup_mind mind env in
    let auxnpar = mib.mind_nparams_rec in
    let nonrecpar = mib.mind_nparams - auxnpar in
    let (lpar,_) = List.chop auxnpar largs in
    let auxntyp = mib.mind_ntypes in
    (* Extends the environment with a variable corresponding to
	     the inductive def *)
    let (env',_ as ienv') = ienv_push_inductive ienv ((mind,u),lpar) in
    (* Parameters expressed in env' *)
    let lpar' = List.map (lift auxntyp) lpar in
    (* In case of mutual inductive types, we use the recargs tree which was
    computed statically. This is fine because nested inductive types with
    mutually recursive containers are not supported. *)
    let trees =
      if Int.equal auxntyp 1 then [|dest_subterms tree|]
      else Array.map (fun mip -> dest_subterms mip.mind_recargs) mib.mind_packets
    in
    let mk_irecargs j specif =
      (* The nested inductive type with parameters removed *)
      let auxlcvect = abstract_mind_lc auxntyp auxnpar specif.mind_nf_lc in
      let paths = Array.mapi
        (fun k c ->
	 let c' = hnf_prod_applist env' c lpar' in
	 (* skip non-recursive parameters *)
	 let (ienv',c') = ienv_decompose_prod ienv' nonrecpar c' in
	 build_recargs_constructors ienv' trees.(j).(k) c')
	auxlcvect
      in
      mk_paths (Imbr (mind,j)) paths
    in
    let irecargs = Array.mapi mk_irecargs mib.mind_packets in
    (Rtree.mk_rec irecargs).(i)

  and build_recargs_constructors ienv trees c =
    let rec recargs_constr_rec (env,_ra_env as ienv) trees lrec c =
      let x,largs = decompose_app (whd_all env c) in
	match kind x with

          | Prod (na,b,d) ->
	     let () = assert (List.is_empty largs) in
             let recarg = build_recargs ienv (List.hd trees) b in
             let ienv' = ienv_push_var ienv (na,b,mk_norec) in
             recargs_constr_rec ienv' (List.tl trees) (recarg::lrec) d
          | _hd ->
             List.rev lrec
    in
    recargs_constr_rec ienv trees [] c
  in
  (* starting with ra_env = [] seems safe because any unbounded Rel will be
  assigned Norec *)
  build_recargs_nested (env,[]) tree (ind, args)

(* [restrict_spec env spec p] restricts the size information in spec to what is
   allowed to flow through a match with predicate p in environment env. *)
let restrict_spec env spec p =
  if spec = Not_subterm then spec
  else let absctx, ar = dest_lam_assum env p in
  (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if noccur_with_meta 1 (Context.Rel.length absctx) ar then spec
  else
  let env = push_rel_context absctx env in
  let arctx, s = dest_prod_assum env ar in
  let env = push_rel_context arctx env in
  let i,args = decompose_app (whd_all env s) in
  match kind i with
  | Ind i ->
     begin match spec with
	   | Dead_code -> spec
	   | Subterm(st,tree) ->
	      let recargs = get_recargs_approx env tree i args in
	      let recargs = inter_wf_paths tree recargs in
	      Subterm(st,recargs)
	   | _ -> assert false
     end
  | _ -> Not_subterm

(* [subterm_specif renv t] computes the recursive structure of [t] and
   compare its size with the size of the initial recursive argument of
   the fixpoint we are checking. [renv] collects such information
   about variables.
*)

let rec subterm_specif renv stack t =
  (* maybe reduction is not always necessary! *)
  let f,l = decompose_app (whd_all renv.env t) in
    match kind f with
    | Rel k -> subterm_var k renv
    | Case (ci,p,c,lbr) ->
       let stack' = push_stack_closures renv l stack in
       let cases_spec =
	 branches_specif renv (lazy_subterm_specif renv [] c) ci
       in
       let stl =
	 Array.mapi (fun i br' ->
		     let stack_br = push_stack_args (cases_spec.(i)) stack' in
		     subterm_specif renv stack_br br')
		    lbr in
       let spec = subterm_spec_glb stl in
       restrict_spec renv.env spec p

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
        | Some (ind, _) ->
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
	let sign,strippedBody = Term.decompose_lam_n_assum nbOfAbst theBody in
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
      let spec,stack' = extract_stack stack in
	subterm_specif (push_var renv (x,a,spec)) stack' b

      (* Metas and evars are considered OK *)
    | (Meta _|Evar _) -> Dead_code

    | Proj (p, c) -> 
      let subt = subterm_specif renv stack c in
      (match subt with
       | Subterm (_s, wf) ->
         (* We take the subterm specs of the constructor of the record *)
         let wf_args = (dest_subterms wf).(0) in
         (* We extract the tree of the projected argument *)
         let n = Projection.arg p in
         spec_of_tree (List.nth wf_args n)
       | Dead_code -> Dead_code
       | Not_subterm -> Not_subterm)

    | Var _ | Sort _ | Cast _ | Prod _ | LetIn _ | App _ | Const _ | Ind _
      | Construct _ | CoFix _ | Int _ -> Not_subterm


      (* Other terms are not subterms *)

and lazy_subterm_specif renv stack t =
  lazy (subterm_specif renv stack t)

and stack_element_specif = function
  |SClosure (h_renv,h) -> lazy_subterm_specif h_renv [] h
  |SArg x -> x

and extract_stack = function
   | [] -> Lazy.from_val Not_subterm , []
   | h::t -> stack_element_specif h, t

(* Check term c can be applied to one of the mutual fixpoints. *)
let check_is_subterm x tree =
  match Lazy.force x with
  | Subterm (Strict,tree') -> incl_wf_paths tree tree'
  | Dead_code -> true
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

let filter_stack_domain env p stack =
  let absctx, ar = dest_lam_assum env p in
  (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if noccur_with_meta 1 (Context.Rel.length absctx) ar then stack
  else let env = push_rel_context absctx env in
  let rec filter_stack env ar stack =
    let t = whd_all env ar in
    match stack, kind t with
    | elt :: stack', Prod (n,a,c0) ->
      let d = LocalAssum (n,a) in
      let ctx, a = dest_prod_assum env a in
      let env = push_rel_context ctx env in
      let ty, args = decompose_app (whd_all env a) in
      let elt = match kind ty with
      | Ind ind -> 
        let spec' = stack_element_specif elt in
        (match (Lazy.force spec') with
        | Not_subterm | Dead_code -> elt
        | Subterm(s,path) ->
            let recargs = get_recargs_approx env path ind args in
            let path = inter_wf_paths path recargs in
            SArg (lazy (Subterm(s,path))))
      | _ -> (SArg (lazy Not_subterm))
      in
      elt :: filter_stack (push_rel d env) c0 stack'
    | _,_ -> List.fold_right (fun _ l -> SArg (lazy Not_subterm) :: l) stack []
  in
  filter_stack env ar stack

(* Check if [def] is a guarded fixpoint body with decreasing arg.
   given [recpos], the decreasing arguments of each mutually defined
   fixpoint. *)
let check_one_fix renv recpos trees def =
  let nfi = Array.length recpos in

  (* Checks if [t] only make valid recursive calls 
     [stack] is the list of constructor's argument specification and 
     arguments that will be applied after reduction.
     example u in t where we have (match .. with |.. => t end) u *)
  let rec check_rec_call renv stack t =
    (* if [t] does not make recursive calls, it is guarded: *)
    if noccur_with_meta renv.rel_min nfi t then ()
    else
      let (f,l) = decompose_app (whd_betaiotazeta renv.env t) in
      match kind f with
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
		  (* Retrieve the expected tree for the argument *)
                  (* Check the decreasing arg is smaller *)
                  let z = List.nth stack' np in
	          if not (check_is_subterm (stack_element_specif z) trees.(glob)) then
                    begin match z with
		      |SClosure (z,z') -> error_illegal_rec_call renv glob (z,z') 
		      |SArg _ -> error_partial_apply renv glob
		    end
              end
            else
              begin
                match lookup_rel p renv.env with
                | LocalAssum _ ->
                    List.iter (check_rec_call renv []) l
                | LocalDef (_,c,_) ->
                    try List.iter (check_rec_call renv []) l
                    with FixGuardError _ ->
                      check_rec_call renv stack (Term.applist(lift p c,l))
              end
		
        | Case (ci,p,c_0,lrest) ->
            List.iter (check_rec_call renv []) (c_0::p::l);
            (* compute the recarg information for the arguments of
               each branch *)
            let case_spec = branches_specif renv 
	      (lazy_subterm_specif renv [] c_0) ci in
	    let stack' = push_stack_closures renv l stack in
            let stack' = filter_stack_domain renv.env p stack' in
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

        | Const (kn,_u as cu) ->
            if evaluable_constant kn renv.env then
              try List.iter (check_rec_call renv []) l
              with (FixGuardError _ ) ->
		let value = (Term.applist(constant_value_in renv.env cu, l)) in
	        check_rec_call renv stack value
	    else List.iter (check_rec_call renv []) l

        | Lambda (x,a,b) ->
            let () = assert (List.is_empty l) in
	    check_rec_call renv [] a ;
            let spec, stack' = extract_stack stack in
	    check_rec_call (push_var renv (x,a,spec)) stack' b

        | Prod (x,a,b) ->
            let () = assert (List.is_empty l && List.is_empty stack) in
            check_rec_call renv [] a;
            check_rec_call (push_var_renv renv (x,a)) [] b

        | CoFix (_i,(_,typarray,bodies as recdef)) ->
            List.iter (check_rec_call renv []) l;
	    Array.iter (check_rec_call renv []) typarray;
	    let renv' = push_fix_renv renv recdef in
	    Array.iter (check_rec_call renv' []) bodies

        | (Ind _ | Construct _) ->
            List.iter (check_rec_call renv []) l

        | Proj (_p, c) ->
           List.iter (check_rec_call renv []) l;
           check_rec_call renv [] c

        | Var id ->
            begin
              let open! Context.Named.Declaration in
              match lookup_named id renv.env with
              | LocalAssum _ ->
                  List.iter (check_rec_call renv []) l
              | LocalDef (_,c,_) ->
                  try List.iter (check_rec_call renv []) l
                  with (FixGuardError _) -> 
		    check_rec_call renv stack (Term.applist(c,l))
            end

        | Sort _ | Int _ ->
          assert (List.is_empty l)

        (* l is not checked because it is considered as the meta's context *)
        | (Evar _ | Meta _) -> ()

        | (App _ | LetIn _ | Cast _) -> assert false (* beta zeta reduction *)

  and check_nested_fix_body renv decr recArgsDecrArg body =
    if Int.equal decr 0 then
      check_rec_call (assign_var_spec renv (1,recArgsDecrArg)) [] body
    else
      match kind body with
	| Lambda (x,a,b) ->
	    check_rec_call renv [] a;
            let renv' = push_var_renv renv (x,a) in
	      check_nested_fix_body renv' (decr-1) recArgsDecrArg b
	| _ -> anomaly (Pp.str "Not enough abstractions in fix body.")
	    
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
  then anomaly (Pp.str "Ill-formed fix term.");
  let fixenv = push_rec_types recdef env in
  let vdefj = judgment_of_fixpoint recdef in
  let raise_err env i err =
    error_ill_formed_rec_body env err names i fixenv vdefj in
  (* Check the i-th definition with recarg k *)
  let find_ind i k def =
    (* check fi does not appear in the k+1 first abstractions,
       gives the type of the k+1-eme abstraction (must be an inductive)  *)
    let rec check_occur env n def =
      match kind (whd_all env def) with
        | Lambda (x,a,b) ->
	    if noccur_with_meta n nbfix a then
	      let env' = push_rel (LocalAssum (x,a)) env in
              if Int.equal n (k + 1) then
                (* get the inductive type of the fixpoint *)
                let (mind, _) =
                  try find_inductive env a
                  with Not_found ->
		    raise_err env i (RecursionNotOnInductiveType a) in
                let mib,_ = lookup_mind_specif env (out_punivs mind) in
                if mib.mind_finite != Finite then
                  raise_err env i (RecursionNotOnInductiveType a);
                (mind, (env', b))
	      else check_occur env' (n+1) b
            else anomaly ~label:"check_one_fix" (Pp.str "Bad occurrence of recursive call.")
        | _ -> raise_err env i NotEnoughAbstractionInFixBody in
    check_occur fixenv 1 def in
  (* Do it on every fixpoint *)
  let rv = Array.map2_i find_ind nvect bodies in
  (Array.map fst rv, Array.map snd rv)


let check_fix env ((nvect,_),(names,_,bodies as recdef) as fix) =
  let flags = Environ.typing_flags env in
  if flags.check_guarded then
    let (minds, rdef) = inductive_of_mutfix env fix in
    let get_tree (kn,i) =
      let mib = Environ.lookup_mind kn env in
      mib.mind_packets.(i).mind_recargs
    in
    let trees = Array.map (fun (mind,_) -> get_tree mind) minds in
    for i = 0 to Array.length bodies - 1 do
      let (fenv,body) = rdef.(i) in
      let renv = make_renv fenv nvect.(i) trees.(i) in
      try check_one_fix renv nvect trees body
      with FixGuardError (fixenv,err) ->
        error_ill_formed_rec_body fixenv err names i
	  (push_rec_types recdef env) (judgment_of_fixpoint recdef)
    done
  else
    ()

(*
let cfkey = CProfile.declare_profile "check_fix";;
let check_fix env fix = CProfile.profile3 cfkey check_fix env fix;;
*)

(************************************************************************)
(* Co-fixpoints. *)

exception CoFixGuardError of env * guard_error

let anomaly_ill_typed () =
  anomaly ~label:"check_one_cofix" (Pp.str "too many arguments applied to constructor.")

let rec codomain_is_coind env c =
  let b = whd_all env c in
  match kind b with
    | Prod (x,a,b) ->
	codomain_is_coind (push_rel (LocalAssum (x,a)) env) b
    | _ ->
	(try find_coinductive env b
        with Not_found ->
	  raise (CoFixGuardError (env, CodomainNotInductiveType b)))

let check_one_cofix env nbfix def deftype =
  let rec check_rec_call env alreadygrd n tree vlra  t =
    if not (noccur_with_meta n nbfix t) then
      let c,args = decompose_app (whd_all env t) in
      match kind c with
	| Rel p when  n <= p && p < n+nbfix ->
	    (* recursive call: must be guarded and no nested recursive
               call allowed *)
            if not alreadygrd then
	      raise (CoFixGuardError (env,UnguardedRecursiveCall t))
            else if not(List.for_all (noccur_with_meta n nbfix) args) then
	      raise (CoFixGuardError (env,NestedRecursiveOccurrences))
        | Construct ((_,i as cstr_kn),_u)  ->
            let lra = vlra.(i-1) in
            let mI = inductive_of_constructor cstr_kn in
            let (mib,_mip) = lookup_mind_specif env mI in
            let realargs = List.skipn mib.mind_nparams args in
            let rec process_args_of_constr = function
              | (t::lr), (rar::lrar) ->
                  if eq_wf_paths rar mk_norec then
                    if noccur_with_meta n nbfix t
                    then process_args_of_constr (lr, lrar)
                    else raise (CoFixGuardError
		                 (env,RecCallInNonRecArgOfConstructor t))
                  else begin
                      check_rec_call env true n rar (dest_subterms rar) t;
                      process_args_of_constr (lr, lrar)
		    end
              | [],_ -> ()
              | _ -> anomaly_ill_typed ()
            in process_args_of_constr (realargs, lra)

	| Lambda (x,a,b) ->
	    let () = assert (List.is_empty args) in
            if noccur_with_meta n nbfix a then
              let env' = push_rel (LocalAssum (x,a)) env in
              check_rec_call env' alreadygrd (n+1) tree vlra b
            else
	      raise (CoFixGuardError (env,RecCallInTypeOfAbstraction a))

        | CoFix (_j,(_,varit,vdefs as recdef)) ->
            if List.for_all (noccur_with_meta n nbfix) args
            then
	      if Array.for_all (noccur_with_meta n nbfix) varit then
		let nbfix = Array.length vdefs in
		let env' = push_rec_types recdef env in
		(Array.iter (check_rec_call env' alreadygrd (n+nbfix) tree vlra) vdefs;
		 List.iter (check_rec_call env alreadygrd n tree vlra) args)
              else
		raise (CoFixGuardError (env,RecCallInTypeOfDef c))
	    else
	      raise (CoFixGuardError (env,UnguardedRecursiveCall c))

	| Case (_,p,tm,vrest) ->
	   begin
	     let tree = match restrict_spec env (Subterm (Strict, tree)) p with
	     | Dead_code -> assert false
	     | Subterm (_, tree') -> tree'
	     | _ -> raise (CoFixGuardError (env, ReturnPredicateNotCoInductive c))
	     in
               if (noccur_with_meta n nbfix p) then
		 if (noccur_with_meta n nbfix tm) then
		   if (List.for_all (noccur_with_meta n nbfix) args) then
		     let vlra = dest_subterms tree in
		     Array.iter (check_rec_call env alreadygrd n tree vlra) vrest
		   else
		     raise (CoFixGuardError (env,RecCallInCaseFun c))
		 else
		   raise (CoFixGuardError (env,RecCallInCaseArg c))
               else
		 raise (CoFixGuardError (env,RecCallInCasePred c))
	   end

	| Meta _ -> ()
        | Evar _ ->
	    List.iter (check_rec_call env alreadygrd n tree vlra) args
        | Rel _ | Var _ | Sort _ | Cast _ | Prod _ | LetIn _ | App _ | Const _
          | Ind _ | Fix _ | Proj _ | Int _ ->
           raise (CoFixGuardError (env,NotGuardedForm t)) in

  let ((mind, _),_) = codomain_is_coind env deftype in
  let vlra = lookup_subterms env mind in
  check_rec_call env false 1 vlra (dest_subterms vlra) def

(* The  function which checks that the whole block of definitions
   satisfies the guarded condition *)

let check_cofix env (_bodynum,(names,types,bodies as recdef)) =
  let flags = Environ.typing_flags env in
  if flags.check_guarded then
    let nbfix = Array.length bodies in
    for i = 0 to nbfix-1 do
      let fixenv = push_rec_types recdef env in
      try check_one_cofix fixenv nbfix bodies.(i) types.(i)
      with CoFixGuardError (errenv,err) ->
        error_ill_formed_rec_body errenv err names i
	  fixenv (judgment_of_fixpoint recdef)
    done
  else
    ()

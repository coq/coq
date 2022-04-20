(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

(* raises an anomaly if not an inductive type *)
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

let inductive_nonrec_rec_paramdecls (mib,u) =
  let nnonrecparamdecls = mib.mind_nparams - mib.mind_nparams_rec in
  let paramdecls = inductive_paramdecls (mib,u) in
  Context.Rel.chop_nhyps nnonrecparamdecls paramdecls

let instantiate_inductive_constraints mib u =
  Univ.AbstractContext.instantiate u (Declareops.inductive_polymorphic_context mib)

(************************************************************************)

let instantiate_params t u args sign =
  let fail () =
    anomaly ~label:"instantiate_params" (Pp.str "type, ctxt and args mismatch.") in
  let (rem_args, subs, ty) =
    Context.Rel.fold_outside
      (fun decl (largs,subs,ty) ->
        match (decl, largs, kind ty) with
          | (LocalAssum _, a::args, Prod(_,_,t)) -> (args, a::subs, t)
          | (LocalDef (_,b,_), _, LetIn(_,_,_,t))    ->
            (largs, (substl subs (subst_instance_constr u b))::subs, t)
          | _                       -> fail ())
      sign
      ~init:(args,[],t)
  in
  let () = if not (List.is_empty rem_args) then fail () in
  substl subs ty

let full_inductive_instantiate mib u params sign =
  let dummy = Sorts.prop in
  let t = Term.mkArity (Vars.subst_instance_context u sign,dummy) in
    fst (Term.destArity (instantiate_params t u params mib.mind_params_ctxt))

let full_constructor_instantiate (_,u,(mib,_),params) t =
  let inst_ind = subst_instance_constr u t in
   instantiate_params inst_ind u params mib.mind_params_ctxt

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

let max_template_universe u v = u @ v

(* cons_subst add the mapping [u |-> su] in subst if [u] is not *)
(* in the domain or add [u |-> sup x su] if [u] is already mapped *)
(* to [x]. *)
let cons_subst u su subst =
  let su = match su with
  | Sorts.SProp -> assert false (* No template on SProp *)
  | Sorts.Prop -> []
  | Sorts.Set -> [Universe.type0]
  | Sorts.Type u -> [u]
  in
  try
    Univ.Level.Map.add u (max_template_universe su (Univ.Level.Map.find u subst)) subst
  with Not_found -> Univ.Level.Map.add u su subst

(* remember_subst updates the mapping [u |-> x] by [u |-> sup x u] *)
(* if it is presents and returns the substitution unchanged if not.*)
let remember_subst u subst =
  try
    let su = [Universe.make u] in
    Univ.Level.Map.add u (max_template_universe su (Univ.Level.Map.find u subst)) subst
  with Not_found -> subst

type param_univs = (unit -> Sorts.t) list

let make_param_univs env argtys =
  Array.map_to_list (fun arg () -> (snd (Reduction.dest_arity env arg))) argtys

(* Bind expected levels of parameters to actual levels *)
(* Propagate the new levels in the signature *)
let make_subst =
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
        let s = a () in
        make (cons_subst u s subst) (sign, exp, args)
    | LocalAssum (_na,_t) :: sign, Some u::exp, [] ->
        (* No more argument here: we add the remaining universes to the *)
        (* substitution (when [u] is distinct from all other universes in the *)
        (* template, it is identity substitution  otherwise (ie. when u is *)
        (* already in the domain of the substitution) [remember_subst] will *)
        (* update its image [x] by [sup x u] in order not to forget the *)
        (* dependency in [u] that remains to be fulfilled. *)
        make (remember_subst u subst) (sign, exp, [])
    | _sign, [], _ ->
        (* Uniform parameters are exhausted *)
        subst
    | [], _, _ ->
        assert false
  in
  make Univ.Level.Map.empty

exception SingletonInductiveBecomesProp of Id.t

let subst_univs_sort subs = function
| Sorts.Prop | Sorts.Set | Sorts.SProp as s -> s
| Sorts.Type u ->
  (* We implement by hand a max on universes that handles Prop *)
  let u = Universe.repr u in
  let supern u n = iterate Universe.super n u in
  let map (u, n) =
    if Level.is_set u then [Universe.type0, n]
    else match Level.Map.find u subs with
    | [] ->
      if Int.equal n 0 then
        (* This is an instantiation of a template universe by Prop, ignore it *)
        []
      else
        (* Prop + S n actually means Set + S n *)
        [Universe.type0, n]
    | _ :: _ as vs ->
      List.map (fun v -> (v, n)) vs
    | exception Not_found ->
      (* Either an unbound template universe due to missing arguments, or a
         global one appearing in the inductive arity. *)
      [Universe.make u, n]
  in
  let u = List.map_append map u in
  match u with
  | [] ->
    (* No constraints, fall in Prop *)
    Sorts.prop
  | (u,n) :: rest ->
    let fold accu (u, n) = Universe.sup accu (supern u n) in
    Sorts.sort_of_univ (List.fold_left fold (supern u n) rest)

let instantiate_universes ctx (templ, ar) args =
  let subst = make_subst (ctx,templ.template_param_levels,args) in
  let ty = subst_univs_sort subst ar.template_level in
  (ctx, ty)

(* Type of an inductive type *)

let relevance_of_inductive env ind =
  let _, mip = lookup_mind_specif env ind in
  mip.mind_relevance

let check_instance mib u =
  if not (match mib.mind_universes with
      | Monomorphic -> Instance.is_empty u
      | Polymorphic uctx -> Instance.length u = AbstractContext.size uctx)
  then CErrors.anomaly Pp.(str "bad instance length on mutind.")

let type_of_inductive_gen ?(polyprop=true) ((mib,mip),u) paramtyps =
  check_instance mib u;
  match mip.mind_arity with
  | RegularArity a -> subst_instance_constr u a.mind_user_arity
  | TemplateArity ar ->
    let templ = match mib.mind_template with
    | None -> assert false
    | Some t -> t
    in
    let ctx = List.rev mip.mind_arity_ctxt in
    let ctx,s = instantiate_universes ctx (templ, ar) paramtyps in
      (* The Ocaml extraction cannot handle (yet?) "Prop-polymorphism", i.e.
         the situation where a non-Prop singleton inductive becomes Prop
         when applied to Prop params *)
      if not polyprop && not (Sorts.is_prop ar.template_level) && Sorts.is_prop s
      then raise (SingletonInductiveBecomesProp mip.mind_typename);
      Term.mkArity (List.rev ctx,s)

let type_of_inductive pind =
  type_of_inductive_gen pind []

let constrained_type_of_inductive ((mib,_mip),u as pind) =
  let ty = type_of_inductive pind in
  let cst = instantiate_inductive_constraints mib u in
    (ty, cst)

let constrained_type_of_inductive_knowing_parameters ((mib,_mip),u as pind) args =
  let ty = type_of_inductive_gen pind args in
  let cst = instantiate_inductive_constraints mib u in
    (ty, cst)

let type_of_inductive_knowing_parameters ?(polyprop=true) mip args =
  type_of_inductive_gen ~polyprop mip args

(************************************************************************)
(* Type of a constructor *)

let type_of_constructor (cstr, u) (mib,mip) =
  check_instance mib u;
  let i = index_of_constructor cstr in
  let nconstr = Array.length mip.mind_consnames in
  if i > nconstr then user_err Pp.(str "Not enough constructors in the type.");
  subst_instance_constr u mip.mind_user_lc.(i-1)

let constrained_type_of_constructor (_cstr,u as cstru) (mib,_mip as ind) =
  let ty = type_of_constructor cstru ind in
  let cst = instantiate_inductive_constraints mib u in
    (ty, cst)

let arities_of_constructors (_,u) (_,mip) =
  let map (ctx, c) =
    let cty = Term.it_mkProd_or_LetIn c ctx in
    subst_instance_constr u cty
  in
  Array.map map mip.mind_nf_lc

let type_of_constructors (_,u) (_,mip) =
  Array.map (subst_instance_constr u) mip.mind_user_lc

let abstract_constructor_type_relatively_to_inductive_types_context ntyps mind t =
  let rec replace_ind k c =
    let hd, args = decompose_appvect c in
    match kind hd with
    | Ind ((mind',i),_) when MutInd.CanOrd.equal mind mind' ->
       mkApp (mkRel (ntyps+k-i), Array.map (replace_ind k) args)
    | _ -> map_with_binders succ replace_ind k c
  in
  replace_ind 0 t

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

let elim_sort (_,mip) = mip.mind_kelim

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
       @ Context.Rel.instance_list mkRel 0 realargs)

(* This exception is local *)
exception LocalArity of (Sorts.family * Sorts.family * Sorts.family * arity_error) option

let check_allowed_sort ksort specif =
  if not (Sorts.family_leq ksort (elim_sort specif)) then
    let s = inductive_sort_family (snd specif) in
    raise (LocalArity (Some(elim_sort specif, ksort,s,error_elim_explain ksort s)))

let check_correct_arity env c pj ind specif params =
  (* We use l2r:true for compat with old versions which used CONV
     instead of CUMUL called with arguments flipped. It is relevant
     for performance eg in bedrock / Kami. *)
  let arsign,_ = get_instantiated_arity ind specif params in
  let rec srec env ar pt =
    let pt' = whd_all env pt in
    match ar, kind pt' with
    | (LocalAssum (_,a1))::ar', Prod (na1,a1',t) ->
      let () =
        try conv_leq ~l2r:true env a1 a1'
        with NotConvertible -> raise (LocalArity None) in
      srec (push_rel (LocalAssum (na1,a1)) env) ar' t
    (* The last Prod domain is the type of the scrutinee *)
    | [], Prod (na1,a1',a2) ->
      let env' = push_rel (LocalAssum (na1,a1')) env in
      let ksort = match kind (whd_all env' a2) with
      | Sort s -> Sorts.family s
      | _ -> raise (LocalArity None)
      in
      let dep_ind = build_dependent_inductive ind specif params in
      let () =
        (* This ensures that the type of the scrutinee is <= the
           inductive type declared in the predicate. *)
        try conv_leq ~l2r:true env dep_ind a1'
        with NotConvertible -> raise (LocalArity None)
      in
      let () = check_allowed_sort ksort specif in
      (* We return the "higher" inductive universe instance from the predicate,
         the branches must be typeable using these universes.
         The find_rectype call cannot fail due to the cumulativity check above. *)
      let (pind, _args) = find_rectype env a1' in
      pind
    | (LocalDef _ as d)::ar', _ ->
      srec (push_rel d env) ar' (lift 1 pt')
    | _ ->
      raise (LocalArity None)
  in
  try srec env (List.rev arsign) pj.uj_type
  with LocalArity kinds ->
    error_elim_arity env ind c pj kinds

(** {6 Changes of representation of Case nodes} *)

(** Provided:
    - a universe instance [u]
    - a term substitution [subst]
    - name replacements [nas]
    [instantiate_context u subst nas ctx] applies both [u] and [subst] to [ctx]
    while replacing names using [nas] (order reversed)
*)
let instantiate_context u subst nas ctx =
  let rec instantiate i ctx = match ctx with
  | [] -> assert (Int.equal i (-1)); []
  | LocalAssum (_, ty) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    LocalAssum (nas.(i), ty) :: ctx
  | LocalDef (_, ty, bdy) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    let bdy = substnl subst i (subst_instance_constr u bdy) in
    LocalDef (nas.(i), ty, bdy) :: ctx
  in
  instantiate (Array.length nas - 1) ctx

let expand_case_specif mib (ci, u, params, p, iv, c, br) =
  (* Γ ⊢ c : I@{u} params args *)
  (* Γ, indices, self : I@{u} params indices ⊢ p : Type *)
  let mip = mib.mind_packets.(snd ci.ci_ind) in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in
  (* Expand the return clause *)
  let ep =
    let (nas, p) = p in
    let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
    let self =
      let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
      let inst = Instance.of_array (Array.init (Instance.length u) Level.var) in
      mkApp (mkIndU (ci.ci_ind, inst), args)
    in
    let realdecls = LocalAssum (Context.anonR, self) :: realdecls in
    let realdecls = instantiate_context u paramsubst nas realdecls in
    Term.it_mkLambda_or_LetIn p realdecls
  in
  (* Expand the branches *)
  let ebr =
    let build_one_branch i (nas, br) (ctx, _) =
      let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
      let ctx = instantiate_context u paramsubst nas ctx in
      Term.it_mkLambda_or_LetIn br ctx
    in
    Array.map2_i build_one_branch br mip.mind_nf_lc
  in
  (ci, ep, iv, c, ebr)

let expand_case env (ci, _, _, _, _, _, _ as case) =
  let specif = Environ.lookup_mind (fst ci.ci_ind) env in
  expand_case_specif specif case

let contract_case env (ci, p, iv, c, br) =
  let (mib, mip) = lookup_mind_specif env ci.ci_ind in
  let (arity, p) = Term.decompose_lam_n_decls (mip.mind_nrealdecls + 1) p in
  let (u, pms) = match arity with
  | LocalAssum (_, ty) :: _ ->
    (** Last binder is the self binder for the term being eliminated *)
    let (ind, args) = decompose_appvect ty in
    let (ind, u) = destInd ind in
    let () = assert (Ind.CanOrd.equal ind ci.ci_ind) in
    let pms = Array.sub args 0 mib.mind_nparams in
    (** Unlift the parameters from under the index binders *)
    let dummy = List.make mip.mind_nrealdecls mkProp in
    let pms = Array.map (fun c -> Vars.substl dummy c) pms in
    (u, pms)
  | _ -> assert false
  in
  let p =
    let nas = Array.of_list (List.rev_map get_annot arity) in
    (nas, p)
  in
  let map i br =
    let (ctx, br) = Term.decompose_lam_n_decls mip.mind_consnrealdecls.(i) br in
    let nas = Array.of_list (List.rev_map get_annot ctx) in
    (nas, br)
  in
  (ci, u, pms, p, iv, c, Array.mapi map br)

(************************************************************************)
(* Type of case branches *)

(* [p] is the predicate, [i] is the constructor number (starting from 0),
   and [cty] is the type of the constructor (params not instantiated) *)
let build_branches_type (ind,u) (_,mip as specif) params p =
  let build_one_branch i (ctx, c) =
    let cty = Term.it_mkProd_or_LetIn c ctx in
    let typi = full_constructor_instantiate (ind,u,specif,params) cty in
    let (cstrsign,ccl) = Term.decompose_prod_assum typi in
    let nargs = Context.Rel.length cstrsign in
    let (_,allargs) = decompose_app ccl in
    let (lparams,vargs) = List.chop (inductive_params specif) allargs in
    let cargs =
      let cstr = ith_constructor_of_inductive ind (i+1) in
      let dep_cstr = Term.applist (mkConstructU (cstr,u),lparams@(Context.Rel.instance_list mkRel 0 cstrsign)) in
      vargs @ [dep_cstr] in
    let base = Term.lambda_appvect_assum (mip.mind_nrealdecls+1) (lift nargs p) (Array.of_list cargs) in
    Term.it_mkProd_or_LetIn base cstrsign in
  Array.mapi build_one_branch mip.mind_nf_lc

(* [p] is the predicate, [c] is the match object, [realargs] is the
   list of real args of the inductive type *)
let build_case_type env n p c realargs =
  whd_betaiota env (Term.lambda_appvect_assum (n+1) p (Array.of_list (realargs@[c])))

let type_case_branches env ((ind, _ as pind),largs) pj c =
  let specif = lookup_mind_specif env ind in
  let nparams = inductive_params specif in
  let (params,realargs) = List.chop nparams largs in
  let p = pj.uj_val in
  let pind = check_correct_arity env c pj pind specif params in
  let lc = build_branches_type pind specif params p in
  let ty = build_case_type env (snd specif).mind_nrealdecls p c realargs in
  (lc, ty)

(************************************************************************)
(* Checking the case annotation is relevant *)

let check_case_info env (indsp,u) r ci =
  let (mib,mip as spec) = lookup_mind_specif env indsp in
  if
    not (Ind.CanOrd.equal indsp ci.ci_ind) ||
    not (Int.equal mib.mind_nparams ci.ci_npar) ||
    not (Array.equal Int.equal mip.mind_consnrealdecls ci.ci_cstr_ndecls) ||
    not (Array.equal Int.equal mip.mind_consnrealargs ci.ci_cstr_nargs) ||
    not (ci.ci_relevance == r) ||
    is_primitive_record spec
  then raise (TypeError(env,WrongCaseInfo((indsp,u),ci)))


(************************************************************************)
(************************************************************************)

let apply_branch ((_, i), _u) args ci lf =
  let args = List.skipn ci.ci_npar args in
  let br = lf.(i - 1) in
  let ctx, br = Term.decompose_lam_n_decls ci.ci_cstr_ndecls.(i - 1) br in
  let subst = subst_of_rel_context_instance_list ctx args in
  Vars.substl subst br

let contract_fix ((recindices,bodynum),(_,_,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let ind = nbodies-j-1 in
    mkFix ((recindices,ind),typedbodies)
  in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

let contract_cofix (bodynum,(_,_,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let coind = nbodies-j-1 in
    mkCoFix (coind,typedbodies)
  in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

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
   - Internally_bound_subterm: when the recursive call is in a subterm
     of a redex and the recursive argument is bound to a variable
     which will be instantiated by reducing the redex; the integers
     refer to the number of redexes stacked, with 1 counting for the
     variables bound at head in the body of the fix (as e.g. [x] in
     [fix f n := fun x => f x]); there may be several such indices
     because [match] subterms may have combine several results;
   - Subterm: when the term is a subterm of the recursive argument
       the wf_paths argument specifies which subterms are recursive;
     the [int list] is used in the [match] case where one branch of
     the [match] might be a subterm but (an arbitrary number of)
     others are calls to bound variables
   - Dead_code: when the term has been built by elimination over an
       empty type
 *)

type subterm_spec =
    Subterm of (Int.Set.t * size * wf_paths)
  | Dead_code
  | Not_subterm
  | Internally_bound_subterm of Int.Set.t

let eq_wf_paths = Rtree.equal Declareops.eq_recarg

let inter_recarg r1 r2 = match r1, r2 with
| Norec, Norec -> Some r1
| Norec, _ -> None
| Mrec i1, Mrec i2
| Nested (NestedInd i1), Nested (NestedInd i2)
| Mrec i1, (Nested (NestedInd i2)) -> if Names.Ind.CanOrd.equal i1 i2 then Some r1 else None
| Mrec _, _ -> None
| Nested (NestedInd i1), Mrec i2 -> if Names.Ind.CanOrd.equal i1 i2 then Some r2 else None
| Nested (NestedInd _), _ -> None
| Nested (NestedPrimitive c1), Nested (NestedPrimitive c2) ->
  if Names.Constant.CanOrd.equal c1 c2 then Some r1 else None
| Nested (NestedPrimitive _), _ -> None

let inter_wf_paths = Rtree.inter Declareops.eq_recarg inter_recarg Norec

let incl_wf_paths = Rtree.incl Declareops.eq_recarg inter_recarg Norec

let spec_of_tree t =
  if eq_wf_paths t mk_norec
  then Not_subterm
  else Subterm (Int.Set.empty, Strict, t)

let merge_internal_subterms l1 l2 =
  Int.Set.union l1 l2

let inter_spec s1 s2 =
  match s1, s2 with
  | _, Dead_code -> s1
  | Dead_code, _ -> s2
  | Not_subterm, _ -> s1
  | _, Not_subterm -> s2
  | Internally_bound_subterm l1, Internally_bound_subterm l2 -> Internally_bound_subterm (merge_internal_subterms l1 l2)
  | Subterm (l1,a1,t1), Internally_bound_subterm l2 -> Subterm (merge_internal_subterms l1 l2,a1,t1)
  | Internally_bound_subterm l1, Subterm (l2,a2,t2) -> Subterm (merge_internal_subterms l1 l2,a2,t2)
  | Subterm (l1,a1,t1), Subterm (l2,a2,t2) ->
     Subterm (merge_internal_subterms l1 l2, size_glb a1 a2, inter_wf_paths t1 t2)

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
    genv = [Lazy.from_val(Subterm(Int.Set.empty, Large,tree))] }

let push_var renv (x,ty,spec) =
  { env = push_rel (LocalAssum (x,ty)) renv.env;
    rel_min = renv.rel_min+1;
    genv = spec:: renv.genv }

let push_let renv (x,c,ty,spec) =
  { env = push_rel (LocalDef (x,c,ty)) renv.env;
    rel_min = renv.rel_min+1;
    genv = spec:: renv.genv }

let assign_var_spec renv (i,spec) =
  { renv with genv = List.assign renv.genv (i-1) spec }

let push_var_renv renv n (x,ty) =
  let spec = Lazy.from_val (if n >= 1 then Internally_bound_subterm (Int.Set.singleton n) else Not_subterm) in
  push_var renv (x,ty,spec)

(* Fetch recursive information about a variable p *)
let subterm_var p renv =
  try Lazy.force (List.nth renv.genv (p-1))
  with Failure _ | Invalid_argument _ -> (* outside context of the fixpoint *) Not_subterm

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

type fix_check_result =
  | NeedReduce of env * fix_guard_error
  | NoNeedReduce

(* Definition and manipulation of the stack *)
type stack_element =
  (* arguments in the evaluation stack *)
  (* [constr] is typed in [guard_env] and [int] is the number of
     binders added in the current env on top of [guard_env.env] *)
  | SClosure of fix_check_result * guard_env * int * constr
  (* arguments applied to a "match": only their spec traverse the match *)
  | SArg of subterm_spec Lazy.t

let needreduce_of_stack = function
  | [] | SArg _ :: _ -> NoNeedReduce
  | SClosure (needreduce,_,_,_) :: _ -> needreduce

let (|||) x y = match x with
  | NeedReduce _ -> x
  | NoNeedReduce -> y

let redex_level rs = List.length rs

let push_stack_closure renv needreduce c stack =
  (* In (f a b), if b requires reduction, than a has to require too *)
  let needreduce' = needreduce ||| needreduce_of_stack stack in
  (SClosure (needreduce', renv, 0, c)) :: stack

let push_stack_closures renv l stack =
  List.fold_right (push_stack_closure renv NoNeedReduce) l stack

let push_stack_args l stack =
  List.fold_right (fun spec stack -> SArg spec :: stack) l stack

let lift_stack =
   List.map (function
       | SClosure (needreduce,s,n,c) -> SClosure (needreduce,s,n+1,c)
       | x -> x)

(******************************)
(* {6 Computing the recursive subterms of a term (propagation of size
   information through Cases).} *)

let lookup_subterms env ind =
  let (_,mip) = lookup_mind_specif env ind in
  mip.mind_recargs

let match_inductive ind ra =
  match ra with
    | Mrec i | Nested (NestedInd i) -> Ind.CanOrd.equal ind i
    | Norec | Nested (NestedPrimitive _) -> false

(* In {match c as z in ci y_s return P with | C_i x_s => t end}
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
                Subterm (_,_,t) when match_inductive ci.ci_ind (dest_recarg t) ->
                  let vra = Array.of_list (dest_subterms t).(i) in
                  assert (Int.equal nca (Array.length vra));
                  Array.map spec_of_tree vra
              | Dead_code -> Array.make nca Dead_code
              | Internally_bound_subterm _ as x -> Array.make nca x
              | Subterm _ | Not_subterm -> Array.make nca Not_subterm) in
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
  let push_ind mip env =
    let r = mip.mind_relevance in
    let anon = Context.make_annot Anonymous r in
    let decl = LocalAssum (anon, hnf_prod_applist env (type_of_inductive ((mib,mip),u)) lpar) in
    push_rel decl env
  in
  let env = Array.fold_right push_ind mib.mind_packets env in
  let rc = Array.mapi (fun j t -> (Nested (NestedInd (mind,j)),t)) (Rtree.mk_rec_calls ntypes) in
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

(* This removes global parameters of the inductive types in lc (for
   nested inductive types only ) *)
let dummy_univ = Level.(make (UGlobal.make (DirPath.make [Id.of_string "implicit"]) "" 0))
let dummy_implicit_sort = mkType (Universe.make dummy_univ)
let lambda_implicit n a =
  let anon = Context.make_annot Anonymous Sorts.Relevant in
  let lambda_implicit a = mkLambda (anon, dummy_implicit_sort, a) in
  iterate lambda_implicit n a

let abstract_mind_lc ntyps npars mind lc =
  let lc = Array.map (fun (ctx, c) -> Term.it_mkProd_or_LetIn c ctx) lc in
  let rec replace_ind k c =
    let hd, args = decompose_app c in
    match kind hd with
    | Ind ((mind',i),_) when MutInd.CanOrd.equal mind mind' ->
      let rec drop_params n = function
        | _ :: args when n > 0 -> drop_params (n-1) args
        | args -> lambda_implicit n (Term.applist (mkRel (ntyps+n+k-i), List.Smart.map (replace_ind (n+k)) args))
      in
      drop_params npars args
    | _ -> map_with_binders succ replace_ind k c
  in
  Array.map (replace_ind 0) lc

let is_primitive_positive_container env c =
  match env.retroknowledge.Retroknowledge.retro_array with
  | Some c' when QConstant.equal env c c' -> true
  | _ -> false

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
             | Nested (NestedInd kn') | Mrec kn' when Ind.CanOrd.equal (fst ind_kn) kn' ->
               build_recargs_nested ienv tree (ind_kn, largs)
             | _ -> mk_norec
       end
    | Const (c,_) when is_primitive_positive_container env c ->
       begin match dest_recarg tree with
             | Nested (NestedPrimitive c') when QConstant.equal env c c' ->
               build_recargs_nested_primitive ienv tree (c, largs)
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
    let mk_irecargs j mip =
      (* The nested inductive type with parameters removed *)
      let auxlcvect = abstract_mind_lc auxntyp auxnpar mind mip.mind_nf_lc in
      let paths = Array.mapi
        (fun k c ->
         let c' = hnf_prod_applist env' c lpar' in
         (* skip non-recursive parameters *)
         let (ienv',c') = ienv_decompose_prod ienv' nonrecpar c' in
         build_recargs_constructors ienv' trees.(j).(k) c')
        auxlcvect
      in
      mk_paths (Nested (NestedInd (mind,j))) paths
    in
    let irecargs = Array.mapi mk_irecargs mib.mind_packets in
    (Rtree.mk_rec irecargs).(i)

  and build_recargs_nested_primitive (env, ra_env) tree (c, largs) =
    if eq_wf_paths tree mk_norec then tree
    else
    let ntypes = 1 in (* Primitive types are modelled by non-mutual inductive types *)
    let ra_env = List.map (fun (r,t) -> (r,Rtree.lift ntypes t)) ra_env in
    let ienv = (env, ra_env) in
    let paths = List.map2 (build_recargs ienv) (dest_subterms tree).(0) largs in
    let recargs = [| mk_paths (Nested (NestedPrimitive c)) [| paths |] |] in
    (Rtree.mk_rec recargs).(0)

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
  match spec with
  | Not_subterm | Internally_bound_subterm _ -> spec
  | _ ->
  let absctx, ar = dest_lam_assum env p in
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
           | Subterm(l,st,tree) ->
              let recargs = get_recargs_approx env tree i args in
              let recargs = inter_wf_paths tree recargs in
              Subterm(l,st,recargs)
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
    | Case (ci, u, pms, p, iv, c, lbr) -> (* iv ignored: it's just a cache *)
      let (ci, p, _iv, c, lbr) = expand_case renv.env (ci, u, pms, p, iv, c, lbr) in
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
          (nbfix-i, lazy (Subterm(Int.Set.empty,Strict,recargs))) in
        let decrArg = recindxs.(i) in
        let theBody = bodies.(i)   in
        let nbOfAbst = decrArg+1 in
        let sign,strippedBody = dest_lam_n_assum renv.env nbOfAbst theBody in
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
       | Subterm (_, _s, wf) ->
         (* We take the subterm specs of the constructor of the record *)
         let wf_args = (dest_subterms wf).(0) in
         (* We extract the tree of the projected argument *)
         let n = Projection.arg p in
         spec_of_tree (List.nth wf_args n)
       | Dead_code -> Dead_code
       | Not_subterm -> Not_subterm
       | Internally_bound_subterm n -> Internally_bound_subterm n)

    | Const c ->
      begin try
        let _ = Environ.constant_value_in renv.env c in Not_subterm
      with
        | NotEvaluableConst (IsPrimitive (_u,op)) when List.length l >= CPrimitives.arity op ->
          primitive_specif renv op l
        | NotEvaluableConst _ -> Not_subterm
      end

    | Var _ | Sort _ | Cast _ | Prod _ | LetIn _ | App _ | Ind _
      | Construct _ | CoFix _ | Int _ | Float _ | Array _ -> Not_subterm


      (* Other terms are not subterms *)

and lazy_subterm_specif renv stack t =
  lazy (subterm_specif renv stack t)

and stack_element_specif = function
  | SClosure (_, h_renv, _, h) -> lazy_subterm_specif h_renv [] h
  | SArg x -> x

and extract_stack = function
   | [] -> Lazy.from_val Not_subterm, []
   | elt :: l -> stack_element_specif elt, l

and primitive_specif renv op args =
  let open CPrimitives in
  match op with
  | Arrayget | Arraydefault ->
    (* t.[i] and default t can be seen as strict subterms of t, with a
       potentially nested rectree. *)
    let arg = List.nth args 1 in (* the result is a strict subterm of the second argument *)
    let subt = subterm_specif renv [] arg in
    begin match subt with
    | Subterm (_, _s, wf) ->
      let wf_args = (dest_subterms wf).(0) in
      spec_of_tree (List.nth wf_args 0) (* first and only parameter of `array` *)
    | Dead_code -> Dead_code
    | Not_subterm -> Not_subterm
    | Internally_bound_subterm n -> Internally_bound_subterm n
    end
  | _ -> Not_subterm

let set_iota_specif nr spec =
  lazy (match Lazy.force spec with
        | Not_subterm -> if nr >= 1 then Internally_bound_subterm (Int.Set.singleton nr) else Not_subterm
        | spec -> spec)

(************************************************************************)

exception FixGuardError of env * fix_guard_error

let illegal_rec_call renv fx = function
  | SClosure (_,arg_renv,_,arg) ->
    let le_lt_vars =
    lazy (let (_,le_vars,lt_vars) =
      List.fold_left
        (fun (i,le,lt) sbt ->
          match Lazy.force sbt with
              (Subterm(_,Strict,_) | Dead_code) -> (i+1, le, i::lt)
            | (Subterm(_,Large,_)) -> (i+1, i::le, lt)
            | _ -> (i+1, le ,lt))
        (1,[],[]) renv.genv in
          (le_vars,lt_vars)) in
    RecursionOnIllegalTerm(fx,(arg_renv.env, arg),le_lt_vars)
  | SArg _ ->
    (* Typically the case of a recursive call encapsulated under a
       rewriting before been applied to the parameter of a constructor *)
    NotEnoughArgumentsForFixCall fx

let set_need_reduce_one env nr err rs =
  let mr = List.length rs in
  let rs1, rs2 = List.chop (mr-nr) rs in
  let _, rs2 = List.sep_first rs2 in
  rs1 @ NeedReduce (env, err) :: rs2

let set_need_reduce env l err rs =
  Int.Set.fold (fun n -> set_need_reduce_one env n err) l rs

let set_need_reduce_top env err rs =
  set_need_reduce_one env (List.length rs) err rs

type check_subterm_result =
  | InvalidSubterm
  | NeedReduceSubterm of Int.Set.t (* empty = NoNeedReduce *)

(* Check term c can be applied to one of the mutual fixpoints. *)
let check_is_subterm x tree =
  match Lazy.force x with
  | Subterm (need_reduce,Strict,tree') ->
    if incl_wf_paths tree tree' then NeedReduceSubterm need_reduce
    else InvalidSubterm
  | Dead_code -> NeedReduceSubterm Int.Set.empty
  | Not_subterm | Subterm (_,Large,_) -> InvalidSubterm
  | Internally_bound_subterm l -> NeedReduceSubterm l

let filter_stack_domain env nr p stack =
  let absctx, ar = Term.decompose_lam_assum p in
  (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if noccur_with_meta 1 (Context.Rel.length absctx) ar then stack
  else let env = push_rel_context absctx env in
  let rec filter_stack env ar stack =
    match stack with
    | [] -> []
    | elt :: stack' ->
    let t = whd_all env ar in
    match kind t with
    | Prod (n,a,c0) ->
      let d = LocalAssum (n,a) in
      let ctx, a = dest_prod_assum env a in
      let env = push_rel_context ctx env in
      let ty, args = decompose_app (whd_all env a) in
      let elt = match kind ty with
      | Ind ind ->
        let spec = stack_element_specif elt in
        (match Lazy.force spec with
        | Not_subterm | Dead_code | Internally_bound_subterm _ -> SArg spec
        | Subterm(l,s,path) ->
            let recargs = get_recargs_approx env path ind args in
            let path = inter_wf_paths path recargs in
            SArg (lazy (Subterm(l,s,path))))
      | _ -> SArg (set_iota_specif nr (lazy Not_subterm))
      in
      elt :: filter_stack (push_rel d env) c0 stack'
    | _ -> List.fold_right (fun _ l -> SArg (set_iota_specif nr (lazy Not_subterm)) :: l) stack []
  in
  filter_stack env ar stack

let judgment_of_fixpoint (_, types, bodies) =
  Array.map2 (fun typ body -> { uj_val = body ; uj_type = typ }) types bodies

(* Check if [def] is a guarded fixpoint body with decreasing arg.
   given [recpos], the decreasing arguments of each mutually defined
   fixpoint. *)
let check_one_fix renv recpos trees def =
  let nfi = Array.length recpos in

  (* Checks if [t] only make valid recursive calls
     [stack] is the list of constructor's argument specification and
     arguments that will be applied after reduction.
     example u in t where we have (match .. with |.. => t end) u;
     [rs] is the stack of redexes traversed w/o having been triggered *)
  let rec check_rec_call_stack renv stack rs t =
      match kind t with
        | App (f,args) ->
            begin
              let rs, stack =
                Array.fold_right (fun a (rs,stack) ->
                    let needreduce,rs = check_rec_call renv rs a in
                    let stack = push_stack_closure renv needreduce a stack in
                    (rs,stack)) args (rs,stack)
              in
              check_rec_call_stack renv stack rs f
            end

        | Rel p ->
            begin
              (* Test if [p] is a fixpoint (recursive call) *)
              if renv.rel_min <= p && p < renv.rel_min+nfi then
                (* the position of the invoked fixpoint: *)
                let glob = renv.rel_min+nfi-1-p in
                (* the decreasing arg of the rec call: *)
                let np = recpos.(glob) in
                if List.length stack <= np then
                  set_need_reduce_top renv.env (NotEnoughArgumentsForFixCall glob) rs
                else
                  (* Retrieve the expected tree for the argument *)
                  (* Check the decreasing arg is smaller *)
                  let z = List.nth stack np in
                  match check_is_subterm (stack_element_specif z) trees.(glob) with
                  | NeedReduceSubterm l -> set_need_reduce renv.env l (illegal_rec_call renv glob z) rs
                  | InvalidSubterm -> raise (FixGuardError (renv.env, illegal_rec_call renv glob z))
              else
                check_rec_call_state renv NoNeedReduce stack rs (fun () ->
                    match lookup_rel p renv.env with
                    | LocalAssum _ -> None
                    | LocalDef (_,c,_) -> Some (lift p c))
            end

        | Case (ci, u, pms, ret, iv, c_0, br) -> (* iv ignored: it's just a cache *)
            let (ci, p, _iv, c_0, brs) = expand_case renv.env (ci, u, pms, ret, iv, c_0, br) in
            let needreduce_c_0, rs = check_rec_call renv rs c_0 in
            let rs = check_inert_subterm_rec_call renv rs p in
            (* compute the recarg info for the arguments of each branch *)
            let rs' = NoNeedReduce::rs in
            let nr = redex_level rs' in
            let case_spec =
              branches_specif renv (set_iota_specif nr (lazy_subterm_specif renv [] c_0)) ci in
            let stack' = filter_stack_domain renv.env nr p stack in
            let rs' =
              Array.fold_left_i (fun k rs' br' ->
                  let stack_br = push_stack_args case_spec.(k) stack' in
                  check_rec_call_stack renv stack_br rs' br') rs' brs in
            let needreduce_br, rs = List.sep_first rs' in
            check_rec_call_state renv (needreduce_br ||| needreduce_c_0) stack rs (fun () ->
              (* we try hard to reduce the match away by looking for a
                 constructor in c_0 (we unfold definitions too) *)
              let c_0 = whd_all renv.env c_0 in
              let hd, args = decompose_app c_0 in
              let hd, args = match kind hd with
              | CoFix cofix ->
                  decompose_app (whd_all renv.env (Term.applist (contract_cofix cofix, args)))
              | _ -> hd, args in
              match kind hd with
              | Construct cstr -> Some (apply_branch cstr args ci brs)
              | CoFix _ | Ind _ | Lambda _ | Prod _ | LetIn _
              | Sort _ | Int _ | Float _ | Array _ -> assert false
              | Rel _ | Var _ | Const _ | App _ | Case _ | Fix _
              | Proj _ | Cast _ | Meta _ | Evar _ -> None)

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
        | Fix ((recindxs,i),(_,typarray,bodies as recdef) as fix) ->
            let decrArg = recindxs.(i) in
            let rs' = Array.fold_left (check_inert_subterm_rec_call renv) (NoNeedReduce::rs) typarray in
            let renv' = push_fix_renv renv recdef in
            let rs' = Array.fold_left_i (fun j rs' body ->
              if Int.equal i j && (List.length stack > decrArg) then
                let recArg = List.nth stack decrArg in
                let arg_spec = set_iota_specif (redex_level rs') (stack_element_specif recArg) in
                let illformed () =
                  error_ill_formed_rec_body renv.env (Type_errors.FixGuardError NotEnoughAbstractionInFixBody)
                    (pi1 recdef) i (push_rec_types recdef renv.env)
                    (judgment_of_fixpoint recdef)
                in
                check_nested_fix_body illformed renv' (decrArg+1) arg_spec rs' body
              else
                let needreduce, rs' = check_rec_call renv' rs' body in
                (needreduce ||| List.hd rs') :: List.tl rs') rs' bodies in
            let needreduce_fix, rs = List.sep_first rs' in
            check_rec_call_state renv needreduce_fix stack rs (fun () ->
              (* we try hard to reduce the fix away by looking for a
                 constructor in l[decrArg] (we unfold definitions too) *)
              if List.length stack <= decrArg then None else
              match List.nth stack decrArg with
              | SArg _ -> (* A match on the way *) None
              | SClosure (_,_,n,recArg) ->
              let c = whd_all renv.env (lift n recArg) in
              let hd, _ = decompose_app c in
              match kind hd with
              | Construct _ -> Some (contract_fix fix)
              | CoFix _ | Ind _ | Lambda _ | Prod _ | LetIn _
              | Sort _ | Int _ | Float _ | Array _ -> assert false
              | Rel _ | Var _ | Const _ | App _ | Case _ | Fix _
              | Proj _ | Cast _ | Meta _ | Evar _ -> None)

        | Const (kn,_u as cu) ->
            check_rec_call_state renv NoNeedReduce stack rs (fun () ->
                if evaluable_constant kn renv.env then Some (constant_value_in renv.env cu)
                else None)

        | Lambda (x,a,b) ->
            begin
              let needreduce, rs = check_rec_call renv rs a in
              match needreduce, stack with
              | NoNeedReduce, (SClosure (NoNeedReduce, _, n, c) as elt :: stack) ->
                  (* Neither function nor args have rec calls on internally bound variables *)
                  let spec = stack_element_specif elt in
                  let stack = lift_stack stack in
                  (* Thus, args do not a priori require to be rechecked, so we push a let *)
                  (* maybe the body of the let will have to be locally expanded though, see Rel case *)
                  check_rec_call_stack (push_let renv (x,lift n c,a,spec)) stack rs b
              | _, SClosure (_, _, n, c) :: stack ->
                  (* Either function or args have rec call on internally bound variables *)
                  check_rec_call_stack renv stack rs (subst1 (lift n c) b)
              | _, SArg spec :: stack ->
                  (* Going down a case branch *)
                  let stack = lift_stack stack in
                  check_rec_call_stack (push_var renv (x,a,spec)) stack rs b
              | _, [] ->
                  check_rec_call_stack (push_var_renv renv (redex_level rs) (x,a)) [] rs b
            end

        | Prod (x,a,u) ->
            let () = assert (List.is_empty stack) in
            let rs = check_inert_subterm_rec_call renv rs a in
            (* Note: can recursive calls on [x] be else than inert "dead code"? *)
            check_rec_call_stack (push_var_renv renv (redex_level rs) (x,a)) [] rs u

        | CoFix (_i,(_,typarray,bodies as recdef)) ->
            let rs = Array.fold_left (check_inert_subterm_rec_call renv) rs typarray in
            let renv' = push_fix_renv renv recdef in
            Array.fold_left (fun rs body ->
                let needreduce', rs = check_rec_call renv' rs body in
                check_rec_call_state renv needreduce' stack rs (fun _ -> None))
              rs bodies

        | Ind _ | Construct _ ->
            check_rec_call_state renv NoNeedReduce stack rs (fun () -> None)

        | Proj (p, c) ->
            begin
              let needreduce', rs = check_rec_call renv rs c in
              check_rec_call_state renv needreduce' stack rs (fun () ->
              (* we try hard to reduce the proj away by looking for a
                 constructor in c (we unfold definitions too) *)
              let c = whd_all renv.env c in
              let hd, args = decompose_appvect c in
              let hd, args = match kind hd with
              | CoFix cofix ->
                  decompose_appvect (whd_all renv.env (mkApp (contract_cofix cofix, args)))
              | _ -> hd, args in
              match kind hd with
              | Construct _ -> Some args.(Projection.npars p + Projection.arg p)
              | CoFix _ | Ind _ | Lambda _ | Prod _ | LetIn _
              | Sort _ | Int _ | Float _ | Array _ -> assert false
              | Rel _ | Var _ | Const _ | App _ | Case _ | Fix _
              | Proj _ | Cast _ | Meta _ | Evar _ -> None)
            end

        | Var id ->
            check_rec_call_state renv NoNeedReduce stack rs (fun () ->
              let open! Context.Named.Declaration in
              match lookup_named id renv.env with
              | LocalAssum _ -> None
              | LocalDef (_,c,_) -> Some c)

        | LetIn (x,c,t,b) ->
            let needreduce_c, rs = check_rec_call renv rs c in
            let needreduce_t, rs = check_rec_call renv rs t in
            begin
              match needreduce_of_stack stack ||| needreduce_c ||| needreduce_t with
              | NoNeedReduce ->
                  (* Stack do not require to beta-reduce; let's look if the body of the let needs *)
                  let spec = lazy_subterm_specif renv [] c in
                  let stack = lift_stack stack in
                  check_rec_call_stack (push_let renv (x,c,t,spec)) stack rs b
              | NeedReduce _ -> check_rec_call_stack renv stack rs (subst1 c b)
            end

        | Cast (c,_,t) ->
            let rs = check_inert_subterm_rec_call renv rs t in
            let rs = check_rec_call_stack renv stack rs c in
            rs

        | Sort _ | Int _ | Float _ ->
            assert (List.is_empty stack); rs

        | Array (_u,t,def,ty) ->
            assert (List.is_empty stack);
            let rs = Array.fold_left (check_inert_subterm_rec_call renv) rs t in
            let rs = check_inert_subterm_rec_call renv rs def in
            let rs = check_inert_subterm_rec_call renv rs ty in
            rs

        (* l is not checked because it is considered as the meta's context *)
        | (Evar _ | Meta _) ->
            rs

  and check_nested_fix_body illformed renv decr recArgsDecrArg rs body =
    if Int.equal decr 0 then
      check_inert_subterm_rec_call (assign_var_spec renv (1,recArgsDecrArg)) rs body
    else
      match kind (whd_all renv.env body) with
        | Lambda (x,a,body) ->
            let rs = check_inert_subterm_rec_call renv rs a in
            let renv' = push_var_renv renv (redex_level rs) (x,a) in
              check_nested_fix_body illformed renv' (decr-1) recArgsDecrArg rs body
        | _ -> illformed ()

  and check_rec_call_state renv needreduce_of_head stack rs expand_head =
    (* Test if either the head or the stack of a state
       needs the state to be reduced before continuing checking *)
    match needreduce_of_head ||| needreduce_of_stack stack with
    | NoNeedReduce -> rs
    | NeedReduce _ as e ->
        (* Expand if possible, otherwise, last chance, propagate need
           for expansion, in the hope to be eventually erased *)
        match expand_head () with
        | None -> e :: List.tl rs
        | Some c -> check_rec_call_stack renv stack rs c

  and check_inert_subterm_rec_call renv rs c =
    (* Check rec calls of a term which does not interact with its
       immediate context and which can be possibly erased at higher
       level of the redex stack *)
    let need_reduce, rs = check_rec_call renv rs c in
    check_rec_call_state renv need_reduce [] rs (fun () -> None)

  and check_rec_call renv rs c =
    (* either fails if a non guarded call occurs or tells if there is
       rec call on a variable bound at the top of [c] and update the
       need for reduction in the redex stack with rec calls on
       variables bound at higher levels of the redex stack *)
    List.sep_first (check_rec_call_stack renv [] (NoNeedReduce::rs) c)

  in
  let need_reduce, rs = check_rec_call renv [] def in
  assert (List.is_empty rs);
  match need_reduce with
  | NeedReduce (env,err) -> raise (FixGuardError (env,err))
  | NoNeedReduce -> ()

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
    error_ill_formed_rec_body env (Type_errors.FixGuardError err) names i fixenv vdefj in
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
        | _ -> raise_err env i NotEnoughAbstractionInFixBody
    in
    let ((ind, _), _) as res = check_occur fixenv 1 def in
    let _, mip = lookup_mind_specif env ind in
    (* recursive sprop means non record with projections -> squashed *)
    if mip.mind_relevance == Sorts.Irrelevant &&
       not (Environ.is_type_in_type env (GlobRef.IndRef ind))
    then
      begin
        if names.(i).Context.binder_relevance == Sorts.Relevant
        then raise_err env i FixpointOnIrrelevantInductive
      end;
    res
  in
  (* Do it on every fixpoint *)
  let rv = Array.map2_i find_ind nvect bodies in
  (Array.map fst rv, Array.map snd rv)


let check_fix env ((nvect,_),(names,_,bodies as recdef) as fix) =
  let (minds, rdef) = inductive_of_mutfix env fix in
  let flags = Environ.typing_flags env in
  if flags.check_guarded then
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
        error_ill_formed_rec_body fixenv (Type_errors.FixGuardError err) names i
          (push_rec_types recdef env) (judgment_of_fixpoint recdef)
    done
  else
    ()

(************************************************************************)
(* Co-fixpoints. *)

exception CoFixGuardError of env * cofix_guard_error

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

        | Case (ci, u, pms, p, iv, tm, br) -> (* iv ignored: just a cache *)
          begin
            let (_, p, _iv, tm, vrest) = expand_case env (ci, u, pms, p, iv, tm, br) in
            let tree = match restrict_spec env (Subterm (Int.Set.empty, Strict, tree)) p with
            | Dead_code -> assert false
            | Subterm (_, _, tree') -> tree'
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
          | Ind _ | Fix _ | Proj _ | Int _ | Float _ | Array _ ->
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
        error_ill_formed_rec_body errenv (Type_errors.CoFixGuardError err) names i
          fixenv (judgment_of_fixpoint recdef)
    done
  else
    ()

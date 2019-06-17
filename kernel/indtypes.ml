(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Term
open Constr
open Vars
open Declarations
open Declareops
open Inductive
open Environ
open Reduction
open Entries
open Context.Rel.Declaration

(* Terminology:
paramdecls (ou paramsctxt?)
args = params + realargs (called vargs when an array, largs when a list)
params = recparams + nonrecparams
nonrecargs = nonrecparams + realargs
env_ar = initial env + declaration of inductive types
env_ar_par = env_ar + declaration of parameters
nmr = ongoing computation of recursive parameters
*)

(* [weaker_noccur_between env n nvars t] (defined above), checks that
   no de Bruijn indices between [n] and [n+nvars] occur in [t]. If
   some such occurrences are found, then reduction is performed
   (lazily for efficiency purposes) in order to determine whether
   these occurrences are occurrences in the normal form. If the
   occurrences are eliminated a witness reduct [Some t'] of [t] is
   returned otherwise [None] is returned. *)
let weaker_noccur_between env x nvars t =
  if noccur_between x nvars t then Some t
  else
   let t' = whd_all env t in
   if noccur_between x nvars t' then Some t'
   else None

(************************************************************************)
(* Various well-formedness check for inductive declarations            *)

exception InductiveError = Type_errors.InductiveError

(************************************************************************)
(************************************************************************)
(* Positivity *)

type ill_formed_ind =
  | LocalNonPos of int
  | LocalNotEnoughArgs of int
  | LocalNotConstructor of Constr.rel_context * int
  | LocalNonPar of int * int * int

exception IllFormedInd of ill_formed_ind

(* [mind_extract_params mie] extracts the params from an inductive types
   declaration, and checks that they are all present (and all the same)
   for all the given types. *)

let mind_extract_params = decompose_prod_n_assum

let explain_ind_err id ntyp env nparamsctxt c err =
  let open Type_errors in
  let (_lparams,c') = mind_extract_params nparamsctxt c in
  match err with
    | LocalNonPos kt ->
	raise (InductiveError (NonPos (env,c',mkRel (kt+nparamsctxt))))
    | LocalNotEnoughArgs kt ->
	raise (InductiveError
		 (NotEnoughArgs (env,c',mkRel (kt+nparamsctxt))))
    | LocalNotConstructor (paramsctxt,nargs)->
        let nparams = Context.Rel.nhyps paramsctxt in
	raise (InductiveError
		 (NotConstructor (env,id,c',mkRel (ntyp+nparamsctxt),
                                  nparams,nargs)))
    | LocalNonPar (n,i,l) ->
	raise (InductiveError
		 (NonPar (env,c',n,mkRel i,mkRel (l+nparamsctxt))))

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

(* Check the inductive type is called with the expected parameters *)
(* [n] is the index of the last inductive type in [env] *)
let check_correct_par (env,n,ntypes,_) paramdecls ind_index args =
  let nparams = Context.Rel.nhyps paramdecls in
  let args = Array.of_list args in
  if Array.length args < nparams then
    raise (IllFormedInd (LocalNotEnoughArgs ind_index));
  let (params,realargs) = Array.chop nparams args in
  let nparamdecls = List.length paramdecls in
  let rec check param_index paramdecl_index = function
    | [] -> ()
    | LocalDef _ :: paramdecls ->
      check param_index (paramdecl_index+1) paramdecls
    | _::paramdecls ->
        match kind (whd_all env params.(param_index)) with
	  | Rel w when Int.equal w paramdecl_index ->
            check (param_index-1) (paramdecl_index+1) paramdecls
	  | _ ->
            let paramdecl_index_in_env = paramdecl_index-n+nparamdecls+1 in
            let err =
              LocalNonPar (param_index+1, paramdecl_index_in_env, ind_index) in
            raise (IllFormedInd err)
  in check (nparams-1) (n-nparamdecls) paramdecls;
  if not (Array.for_all (noccur_between n ntypes) realargs) then
    failwith_non_pos_vect n ntypes realargs

(* Computes the maximum number of recursive parameters:
   the first parameters which are constant in recursive arguments
   [n] is the current depth, [nmr] is the maximum number of possible
   recursive parameters *)

let compute_rec_par (env,n,_,_) paramsctxt nmr largs =
if Int.equal nmr 0 then 0 else
(* start from 0, params will be in reverse order *)
  let (lpar,_) = List.chop nmr largs in
  let rec find k index =
      function
	  ([],_) -> nmr
	| (_,[]) -> assert false (* |paramsctxt|>=nmr *)
	| (lp, LocalDef _ :: paramsctxt) -> find k (index-1) (lp,paramsctxt)
	| (p::lp,_::paramsctxt) ->
       ( match kind (whd_all env p) with
	  | Rel w when Int.equal w index -> find (k+1) (index-1) (lp,paramsctxt)
          | _ -> k)
  in find 0 (n-1) (lpar,List.rev paramsctxt)

(* [env] is the typing environment
   [n] is the dB of the last inductive type
   [ntypes] is the number of inductive types in the definition
     (i.e. range of inductives is [n; n+ntypes-1])
   [lra] is the list of recursive tree of each variable
 *)
let ienv_push_var (env, n, ntypes, lra) (x,a,ra) =
  (push_rel (LocalAssum (x,a)) env, n+1, ntypes, (Norec,ra)::lra)

let ienv_push_inductive (env, n, ntypes, ra_env) ((mi,u),lrecparams) =
  let auxntyp = 1 in
  let specif = (lookup_mind_specif env mi, u) in
  let ty = type_of_inductive env specif in
  let env' =
    let r = (snd (fst specif)).mind_relevance in
    let anon = Context.make_annot Anonymous r in
    let decl = LocalAssum (anon, hnf_prod_applist env ty lrecparams) in
    push_rel decl env in
  let ra_env' =
    (Imbr mi,(Rtree.mk_rec_calls 1).(0)) ::
    List.map (fun (r,t) -> (r,Rtree.lift 1 t)) ra_env in
  (* New index of the inductive types *)
  let newidx = n + auxntyp in
  (env', newidx, ntypes, ra_env')

let rec ienv_decompose_prod (env,_,_,_ as ienv) n c =
  if Int.equal n 0 then (ienv,c) else
    let c' = whd_all env c in
    match kind c' with
        Prod(na,a,b) ->
          let ienv' = ienv_push_var ienv (na,a,mk_norec) in
	  ienv_decompose_prod ienv' (n-1) b
      | _ -> assert false

let array_min nmr a = if Int.equal nmr 0 then 0 else
  Array.fold_left (fun k (nmri,_) -> min k nmri) nmr a

(** [check_positivity_one ienv paramsctxt (mind,i) nnonrecargs lcnames indlc]
    checks the positivity of the [i]-th member of the mutually
    inductive definition [mind]. It returns an [Rtree.t] which
    represents the position of the recursive calls of inductive in [i]
    for use by the guard condition (terms at these positions are
    considered sub-terms) as well as the number of of non-uniform
    arguments (used to generate induction schemes, so a priori less
    relevant to the kernel).

    If [chkpos] is [false] then positivity is assumed, and
    [check_positivity_one] computes the subterms occurrences in a
    best-effort fashion. *)
let check_positivity_one ~chkpos recursive (env,_,ntypes,_ as ienv) paramsctxt (_,i as ind) nnonrecargs lcnames indlc =
  let nparamsctxt = Context.Rel.length paramsctxt in
  let nmr = Context.Rel.nhyps paramsctxt in
  (** Positivity of one argument [c] of a constructor (i.e. the
      constructor [cn] has a type of the shape [… -> c … -> P], where,
      more generally, the arrows may be dependent). *)
  let rec check_pos (env, n, ntypes, ra_env as ienv) nmr c =
    let x,largs = decompose_app (whd_all env c) in
      match kind x with
        | Prod (na,b,d) ->
	    let () = assert (List.is_empty largs) in
            (** If one of the inductives of the mutually inductive
                block occurs in the left-hand side of a product, then
                such an occurrence is a non-strictly-positive
                recursive call. Occurrences in the right-hand side of
                the product must be strictly positive.*)
            (match weaker_noccur_between env n ntypes b with
	      | None when chkpos ->
                  failwith_non_pos_list n ntypes [b]
              | None ->
                  check_pos (ienv_push_var ienv (na, b, mk_norec)) nmr d
              | Some b ->
                  check_pos (ienv_push_var ienv (na, b, mk_norec)) nmr d)
	| Rel k ->
            (try let (ra,rarg) = List.nth ra_env (k-1) in
            let largs = List.map (whd_all env) largs in
	    let nmr1 =
	      (match ra with
                  Mrec _ -> compute_rec_par ienv paramsctxt nmr largs
		|  _ -> nmr)
	    in
              (** The case where one of the inductives of the mutually
                  inductive block occurs as an argument of another is not
                  known to be safe. So Coq rejects it. *)
	      if chkpos &&
                 not (List.for_all (noccur_between n ntypes) largs)
	      then failwith_non_pos_list n ntypes largs
	      else (nmr1,rarg)
              with Failure _ | Invalid_argument _ -> (nmr,mk_norec))
	| Ind ind_kn ->
            (** If one of the inductives of the mutually inductive
                block being defined appears in a parameter, then we
                have a nested inductive type. The positivity is then
                discharged to the [check_positive_nested] function. *)
            if List.for_all (noccur_between n ntypes) largs then (nmr,mk_norec)
            else check_positive_nested ienv nmr (ind_kn, largs)
        | _err ->
            (** If an inductive of the mutually inductive block
                appears in any other way, then the positivy check gives
                up. *)
	    if not chkpos ||
              (noccur_between n ntypes x &&
               List.for_all (noccur_between n ntypes) largs)
	    then (nmr,mk_norec)
	    else failwith_non_pos_list n ntypes (x::largs)

  (** [check_positive_nested] handles the case of nested inductive
      calls, that is, when an inductive types from the mutually
      inductive block is called as an argument of an inductive types
      (for the moment, this inductive type must be a previously
      defined types, not one of the types of the mutually inductive
      block being defined). *)
  (* accesses to the environment are not factorised, but is it worth? *)
  and check_positive_nested (env,n,ntypes,_ra_env as ienv) nmr ((mi,u), largs) =
    let (mib,mip) = lookup_mind_specif env mi in
    let auxnrecpar = mib.mind_nparams_rec in
    let auxnnonrecpar = mib.mind_nparams - auxnrecpar in
    let (auxrecparams,auxnonrecargs) =
      try List.chop auxnrecpar largs
      with Failure _ -> raise (IllFormedInd (LocalNonPos n)) in

      (** Inductives of the inductive block being defined are only
          allowed to appear nested in the parameters of another inductive
          type. Not in the proper indices. *)
      if chkpos && not (List.for_all (noccur_between n ntypes) auxnonrecargs) then
	failwith_non_pos_list n ntypes auxnonrecargs;
      (* Nested mutual inductive types are not supported *)
      let auxntyp = mib.mind_ntypes in
	if not (Int.equal auxntyp 1) then raise (IllFormedInd (LocalNonPos n));
	(* The nested inductive type with parameters removed *)
	let auxlcvect = abstract_mind_lc auxntyp auxnrecpar mip.mind_nf_lc in
	  (* Extends the environment with a variable corresponding to
	     the inductive def *)
	let (env',_,_,_ as ienv') = ienv_push_inductive ienv ((mi,u),auxrecparams) in
	  (* Parameters expressed in env' *)
	let auxrecparams' = List.map (lift auxntyp) auxrecparams in
	let irecargs_nmr =
	  (** Checks that the "nesting" inductive type is covariant in
	      the relevant parameters. In other words, that the
	      (nested) parameters which are instantiated with
	      inductives of the mutually inductive block occur
	      positively in the types of the nested constructors. *)
	  Array.map
	    (function c ->
	      let c' = hnf_prod_applist env' c auxrecparams' in
	      (* skip non-recursive parameters *)
	      let (ienv',c') = ienv_decompose_prod ienv' auxnnonrecpar c' in
		check_constructors ienv' false nmr c')
	    auxlcvect
	in
	let irecargs = Array.map snd irecargs_nmr
	and nmr' = array_min nmr irecargs_nmr
	in
	  (nmr',(Rtree.mk_rec [|mk_paths (Imbr mi) irecargs|]).(0))

  (** [check_constructors ienv check_head nmr c] checks the positivity
      condition in the type [c] of a constructor (i.e. that recursive
      calls to the inductives of the mutually inductive definition
      appear strictly positively in each of the arguments of the
      constructor, see also [check_pos]). If [check_head] is [true],
      then the type of the fully applied constructor (the "head" of
      the type [c]) is checked to be the right (properly applied)
      inductive type. *)
  and check_constructors ienv check_head nmr c =
    let rec check_constr_rec (env,n,ntypes,_ra_env as ienv) nmr lrec c =
      let x,largs = decompose_app (whd_all env c) in
	match kind x with

          | Prod (na,b,d) ->
	      let () = assert (List.is_empty largs) in
	      if not recursive && not (noccur_between n ntypes b) then
                raise (InductiveError Type_errors.BadEntry);
              let nmr',recarg = check_pos ienv nmr b in
              let ienv' = ienv_push_var ienv (na,b,mk_norec) in
                check_constr_rec ienv' nmr' (recarg::lrec) d
          | hd ->
            let () =
              if check_head then
                begin match hd with
                | Rel j when Int.equal j (n + ntypes - i - 1) ->
                  check_correct_par ienv paramsctxt (ntypes - i) largs
                | _ -> raise (IllFormedInd (LocalNotConstructor(paramsctxt,nnonrecargs)))
                end
              else
                if chkpos &&
                   not (List.for_all (noccur_between n ntypes) largs)
                then failwith_non_pos_list n ntypes largs
            in
            (nmr, List.rev lrec)
    in check_constr_rec ienv nmr [] c
  in
  let irecargs_nmr =
    Array.map2
      (fun id c ->
        let _,rawc = mind_extract_params nparamsctxt c in
          try
	    check_constructors ienv true nmr rawc
          with IllFormedInd err ->
	    explain_ind_err id (ntypes-i) env nparamsctxt c err)
      (Array.of_list lcnames) indlc
  in
  let irecargs = Array.map snd irecargs_nmr
  and nmr' = array_min nmr irecargs_nmr
  in (nmr', mk_paths (Mrec ind) irecargs)

(** [check_positivity ~chkpos kn env_ar paramsctxt inds] checks that the mutually
    inductive block [inds] is strictly positive.

    If [chkpos] is [false] then positivity is assumed, and
    [check_positivity_one] computes the subterms occurrences in a
    best-effort fashion. *)
let check_positivity ~chkpos kn names env_ar_par paramsctxt finite inds =
  let ntypes = Array.length inds in
  let recursive = finite != BiFinite in
  let rc = Array.mapi (fun j t -> (Mrec (kn,j),t)) (Rtree.mk_rec_calls ntypes) in
  let ra_env_ar = Array.rev_to_list rc in
  let nparamsctxt = Context.Rel.length paramsctxt in
  let nmr = Context.Rel.nhyps paramsctxt in
  let check_one i (_,lcnames) (nindices,lc) =
    let ra_env_ar_par =
      List.init nparamsctxt (fun _ -> (Norec,mk_norec)) @ ra_env_ar in
    let ienv = (env_ar_par, 1+nparamsctxt, ntypes, ra_env_ar_par) in
    check_positivity_one ~chkpos recursive ienv paramsctxt (kn,i) nindices lcnames lc
  in
  let irecargs_nmr = Array.map2_i check_one names inds in
  let irecargs = Array.map snd irecargs_nmr
  and nmr' = array_min nmr irecargs_nmr
  in (nmr',Rtree.mk_rec irecargs)


(************************************************************************)
(************************************************************************)
(* Build the inductive packet *)

let repair_arity indices = function
  | RegularArity ar -> ar.mind_user_arity
  | TemplateArity ar -> mkArity (indices,Sorts.sort_of_univ ar.template_level)

let fold_inductive_blocks f =
  Array.fold_left (fun acc ((arity,lc),(indices,_),_) ->
    f (Array.fold_left f acc lc) (repair_arity indices arity))

let used_section_variables env inds =
  let fold l c = Id.Set.union (Environ.global_vars_set env c) l in
  let ids = fold_inductive_blocks fold Id.Set.empty inds in
  keep_hyps env ids

let rel_vect n m = Array.init m (fun i -> mkRel(n+m-i))
let rel_list n m = Array.to_list (rel_vect n m)

(** From a rel context describing the constructor arguments,
    build an expansion function.
    The term built is expecting to be substituted first by 
    a substitution of the form [params, x : ind params] *)
let compute_projections (kn, i as ind) mib =
  let pkt = mib.mind_packets.(i) in
  let u = Univ.make_abstract_instance (Declareops.inductive_polymorphic_context mib) in
  let subst = List.init mib.mind_ntypes (fun i -> mkIndU ((kn, mib.mind_ntypes - i - 1), u)) in
  let (ctx, cty) = pkt.mind_nf_lc.(0) in
  let cty = it_mkProd_or_LetIn cty ctx in
  let rctx, _ = decompose_prod_assum (substl subst cty) in
  let ctx, paramslet = List.chop pkt.mind_consnrealdecls.(0) rctx in
  (** We build a substitution smashing the lets in the record parameters so
      that typechecking projections requires just a substitution and not
      matching with a parameter context. *)
  let paramsletsubst =
    (* [Ind inst] is typed in context [params-wo-let] *)
    let inst' = rel_list 0 mib.mind_nparams in
    (* {params-wo-let |- subst:params] *)
    let subst = subst_of_rel_context_instance paramslet inst' in
    (* {params-wo-let, x:Ind inst' |- subst':(params,x:Ind inst)] *)
    let subst = (* For the record parameter: *)
      mkRel 1 :: List.map (lift 1) subst in
    subst
  in
  let projections decl (i, j, labs, rs, pbs, letsubst) =
    match decl with
    | LocalDef (_na,c,_t) ->
        (* From [params, field1,..,fieldj |- c(params,field1,..,fieldj)]
           to [params, x:I, field1,..,fieldj |- c(params,field1,..,fieldj)] *)
        let c = liftn 1 j c in
        (* From [params, x:I, field1,..,fieldj |- c(params,field1,..,fieldj)]
           to [params-wo-let, x:I |- c(params,proj1 x,..,projj x)] *)
        let c2 = substl letsubst c in
        (* From [params-wo-let, x:I |- subst:(params, x:I, field1,..,fieldj)]
           to [params-wo-let, x:I |- subst:(params, x:I, field1,..,fieldj+1)] *)
        let letsubst = c2 :: letsubst in
        (i, j+1, labs, rs, pbs, letsubst)
    | LocalAssum (na,t) ->
      match na.Context.binder_name with
      | Name id ->
        let r = na.Context.binder_relevance in
        let lab = Label.of_id id in
        let kn = Projection.Repr.make ind ~proj_npars:mib.mind_nparams ~proj_arg:i lab in
        (* from [params, field1,..,fieldj |- t(params,field1,..,fieldj)]
           to [params, x:I, field1,..,fieldj |- t(params,field1,..,fieldj] *)
        let t = liftn 1 j t in
        (* from [params, x:I, field1,..,fieldj |- t(params,field1,..,fieldj)]
           to [params-wo-let, x:I |- t(params,proj1 x,..,projj x)] *)
	let projty = substl letsubst t in
        (* from [params, x:I, field1,..,fieldj |- t(field1,..,fieldj)]
           to [params, x:I |- t(proj1 x,..,projj x)] *)
	let fterm = mkProj (Projection.make kn false, mkRel 1) in
        (i + 1, j + 1, lab :: labs, r :: rs, projty :: pbs, fterm :: letsubst)
      | Anonymous -> assert false (* checked by indTyping *)
  in
  let (_, _, labs, rs, pbs, _letsubst) =
    List.fold_right projections ctx (0, 1, [], [], [], paramsletsubst)
  in
  Array.of_list (List.rev labs),
  Array.of_list (List.rev rs),
  Array.of_list (List.rev pbs)

let build_inductive env names prv univs variance paramsctxt kn isrecord isfinite inds nmr recargs =
  let ntypes = Array.length inds in
  (* Compute the set of used section variables *)
  let hyps = used_section_variables env inds in
  let nparamargs = Context.Rel.nhyps paramsctxt in
  (* Check one inductive *)
  let build_one_packet (id,cnames) ((arity,lc),(indices,splayed_lc),kelim) recarg =
    (* Type of constructors in normal form *)
    let nf_lc = Array.map (fun (d, b) -> (d@paramsctxt, b)) splayed_lc in
    let consnrealdecls =
      Array.map (fun (d,_) -> Context.Rel.length d)
	splayed_lc in
    let consnrealargs =
      Array.map (fun (d,_) -> Context.Rel.nhyps d)
        splayed_lc in
    let mind_relevance = match arity with
      | RegularArity { mind_sort;_ } -> Sorts.relevance_of_sort mind_sort
      | TemplateArity _ -> Sorts.Relevant
    in
    (* Assigning VM tags to constructors *)
    let nconst, nblock = ref 0, ref 0 in
    let transf num =
      let arity = List.length (dest_subterms recarg).(num) in
	if Int.equal arity 0 then
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
        mind_arity = arity;
        mind_arity_ctxt = indices @ paramsctxt;
        mind_nrealargs = Context.Rel.nhyps indices;
        mind_nrealdecls = Context.Rel.length indices;
	mind_kelim = kelim;
	mind_consnames = Array.of_list cnames;
	mind_consnrealdecls = consnrealdecls;
	mind_consnrealargs = consnrealargs;
	mind_user_lc = lc;
	mind_nf_lc = nf_lc;
        mind_recargs = recarg;
        mind_relevance;
        mind_nb_constant = !nconst;
	mind_nb_args = !nblock;
	mind_reloc_tbl = rtbl;
      } in
  let packets = Array.map3 build_one_packet names inds recargs in
  let mib =
      (* Build the mutual inductive *)
    { mind_record = NotRecord;
      mind_ntypes = ntypes;
      mind_finite = isfinite;
      mind_hyps = hyps;
      mind_nparams = nparamargs;
      mind_nparams_rec = nmr;
      mind_params_ctxt = paramsctxt;
      mind_packets = packets;
      mind_universes = univs;
      mind_variance = variance;
      mind_private = prv;
      mind_typing_flags = Environ.typing_flags env;
    }
  in
  let record_info = match isrecord with
  | Some (Some rid) ->
    (** The elimination criterion ensures that all projections can be defined. *)
    let map i id =
      let labs, rs, projs = compute_projections (kn, i) mib in
      (id, labs, rs, projs)
    in
    PrimRecord (Array.mapi map rid)
  | Some None -> FakeRecord
  | None -> NotRecord
  in
  { mib with mind_record = record_info }

(************************************************************************)
(************************************************************************)

let check_inductive env kn mie =
  (* First type-check the inductive definition *)
  let (env_ar_par, univs, variance, record, paramsctxt, inds) = IndTyping.typecheck_inductive env mie in
  (* Then check positivity conditions *)
  let chkpos = (Environ.typing_flags env).check_guarded in
  let names = Array.map_of_list (fun entry -> entry.mind_entry_typename, entry.mind_entry_consnames)
      mie.mind_entry_inds
  in
  let (nmr,recargs) = check_positivity ~chkpos kn names
      env_ar_par paramsctxt mie.mind_entry_finite
      (Array.map (fun ((_,lc),(indices,_),_) -> Context.Rel.nhyps indices,lc) inds)
  in
  (* Build the inductive packets *)
    build_inductive env names mie.mind_entry_private univs variance
      paramsctxt kn record mie.mind_entry_finite
      inds nmr recargs

(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open UVars
open Constr
open Vars
open Declarations
open Declareops
open Environ
open Reduction
open Type_errors
open Context.Rel.Declaration

(* raises an anomaly if not an inductive type *)
let lookup_mind_specif env (kn,tyi) =
  let mib = Environ.lookup_mind kn env in
  if tyi >= Array.length mib.mind_packets then
    user_err Pp.(str "Inductive.lookup_mind_specif: invalid inductive index");
  (mib, mib.mind_packets.(tyi))

let find_rectype ?evars env c =
  let (t, l) = decompose_app_list (whd_all ?evars env c) in
  match kind t with
  | Ind ind -> (ind, l)
  | _ -> raise Not_found

let find_inductive ?evars env c =
  let (t, l) = decompose_app_list (whd_all ?evars env c) in
  match kind t with
    | Ind ind
        when (fst (lookup_mind_specif env (out_punivs ind))).mind_finite <> CoFinite -> (ind, l)
    | _ -> raise Not_found

let find_coinductive ?evars env c =
  let (t, l) = decompose_app_list (whd_all ?evars env c) in
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
  UVars.AbstractContext.instantiate u (Declareops.inductive_polymorphic_context mib)

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

type template_univ =
  | TemplateProp
  | TemplateAboveProp of Sorts.QVar.t * Universe.t
  | TemplateUniv of Universe.t

type template_subst = Sorts.Quality.t Int.Map.t * Universe.t Int.Map.t

let template_univ_quality = function
  | TemplateProp -> Sorts.Quality.qprop
  | TemplateUniv _ -> Sorts.Quality.qtype
  | TemplateAboveProp (q,_) -> Sorts.Quality.QVar q

(* this requires TemplateAboveProp to really be above prop *)
let max_template_quality a b =
  let open Sorts.Quality in
  match a, b with
  | QConstant QSProp, _ | _, QConstant QSProp -> assert false
  | QConstant QProp, q | q, QConstant QProp -> q
  | (QConstant QType as q), _ | _, (QConstant QType as q) -> q
  | QVar a', QVar b' ->
    if Sorts.QVar.equal a' b' then a
    else qtype

let template_univ_universe = function
  | TemplateProp -> Universe.type0
  | TemplateAboveProp (_,u) | TemplateUniv u -> u

let univ_bind_kind u =
  match Universe.level u with
  | None -> None
  | Some l -> Level.var_index l

let bind_kind = let open Sorts in function
  | SProp | Prop | Set -> assert false
  | Type u ->
    let u = univ_bind_kind u in
    assert (Option.has_some u);
    None, u
  | QSort (q,u) ->
    let q = Sorts.QVar.var_index q in
    let u = univ_bind_kind u in
    assert (Option.has_some q || Option.has_some u);
    q, u

(* Add a binding for a parameter binding qbind and ubind to su. *)
let cons_subst bind su (qsubst,usubst) =
  let qbind, ubind = bind_kind bind in
  let qsubst = match qbind with
    | None -> qsubst
    | Some qbind ->
      let sq = template_univ_quality su in
      Int.Map.update qbind (function
          | None -> Some sq
          | Some q0 -> Some (max_template_quality q0 sq))
        qsubst
  in
  let usubst = match ubind with
    | None -> usubst
    | Some ubind ->
      let u = template_univ_universe su in
      Int.Map.update ubind (function
          | None -> Some u
          | Some _ -> CErrors.anomaly Pp.(str "cons_subst found non linear template level."))
        usubst
  in
  qsubst, usubst

(* cons_default_subst adds the binding to the default universe to the substitution. *)
let cons_default_subst bind defaults (qsubst,usubst) =
  let qbind, ubind = bind_kind bind in
  let qsubst = match qbind with
    | None -> qsubst
    | Some qbind -> Int.Map.add qbind Sorts.Quality.qtype qsubst
  in
  let usubst = match ubind with
    | None -> usubst
    | Some ubind ->
      let u = UVars.subst_instance_universe defaults (Universe.make (Level.var ubind)) in
      Int.Map.update ubind (function
          | None -> Some u
          | Some _ -> CErrors.anomaly Pp.(str "cons_default_subst found non linear template level."))
        usubst
  in
  qsubst, usubst

type param_univs = (default:Sorts.t -> template_univ) list

(* Bind expected levels of parameters to actual levels *)
(* Propagate the new levels in the signature *)
let make_subst defaults =
  let rec make subst = function
    | LocalDef _ :: sign, exp, args ->
        make subst (sign, exp, args)
    | _d::sign, None::exp, args ->
        let args = match args with _::args -> args | [] -> [] in
        make subst (sign, exp, args)
    | LocalAssum (_,t)::sign, Some bind::exp, a::args ->
        (* [default] is used in error messages (e.g. when the user gave SProp) *)
        let _, default = Term.destArity t in
        let s = a ~default in
        make (cons_subst bind s subst) (sign, exp, args)
    | LocalAssum _ :: sign, Some bind::exp, [] ->
      make (cons_default_subst bind defaults subst) (sign, exp, [])
    | _sign, [], _ ->
        (* Uniform parameters are exhausted *)
        subst
    | [], _, _ ->
        assert false
  in
  make (Int.Map.empty,Int.Map.empty)

let template_subst_universe (_,usubst) u =
  let supern u n = iterate Universe.super n u in
  let map (u,n) =
    match Level.var_index u with
    | None -> Universe.maken u n
    | Some u ->
      let u = Int.Map.get u usubst in
      supern u n
  in
  match List.map map (Universe.repr u) with
  | [] -> assert false
  | u :: rest ->
    List.fold_left Universe.sup u rest

let template_subst_sort (subst : template_subst) = function
| Sorts.Prop | Sorts.Set | Sorts.SProp as s -> s
| Sorts.Type u ->
  Sorts.sort_of_univ (template_subst_universe subst u)
| Sorts.QSort (q,u) ->
  let q = match Sorts.QVar.var_index q with
    | None -> Sorts.Quality.QVar q
    | Some q -> Int.Map.get q (fst subst)
  in
  (* shortcut for impredicative quality *)
  if Sorts.Quality.(equal qprop q) then Sorts.prop
  else Sorts.make q (template_subst_universe subst u)

let rec template_subst_ctx accu subs ctx params = match ctx, params with
| [], [] -> accu
| (LocalDef _ as decl) :: ctx, params ->
  template_subst_ctx (decl :: accu) subs ctx params
| (LocalAssum _ as decl) :: ctx, None :: params ->
  template_subst_ctx (decl :: accu) subs ctx params
| LocalAssum (na, t) :: ctx, Some s :: params ->
  let (decls, _) = Term.destArity t in
  let s = template_subst_sort subs s in
  let decl = LocalAssum (na, Term.it_mkProd_or_LetIn (mkSort s) decls) in
  template_subst_ctx (decl :: accu) subs ctx params
| _, [] | [], _ -> assert false

let template_subst_ctx subst ctx params = template_subst_ctx [] subst ctx params

let instantiate_template_constraints subst templ =
  let cstrs = UVars.UContext.constraints (UVars.AbstractContext.repr templ.template_context) in
  let fold (u, cst, v) accu =
    (* v is not a local universe by the unbounded from below property *)
    let u = match Level.var_index u with
      | None -> Universe.make u
      | Some u -> Int.Map.get u (snd subst)
    in
    (* if qsort, it is above prop *)
    let fold accu (u, n) = match n, cst with
      | 0, _ -> Constraints.add (u, cst, v) accu
      | 1, Le -> Constraints.add (u, Lt, v) accu
      | 1, (Eq | Lt) -> assert false (* FIXME? *)
      | _ -> assert false
    in
    List.fold_left fold accu (Univ.Universe.repr u)
  in
  Constraints.fold fold cstrs Constraints.empty

let instantiate_template_universes (mib, _mip) args =
  let templ = match mib.mind_template with
  | None -> assert false
  | Some t -> t
  in
  let ctx = List.rev mib.mind_params_ctxt in
  let subst = make_subst templ.template_defaults (ctx,templ.template_param_arguments,args) in
  let ctx = template_subst_ctx subst ctx templ.template_param_arguments in
  let cstrs = instantiate_template_constraints subst templ in
  (cstrs, ctx, subst)

(* Type of an inductive type *)

let relevance_of_ind_body mip u =
  UVars.subst_instance_relevance u mip.mind_relevance

let relevance_of_inductive env (ind,u) =
  let _, mip = lookup_mind_specif env ind in
  relevance_of_ind_body mip u

let check_instance mib u =
  if not (match mib.mind_universes with
      | Monomorphic -> Instance.is_empty u
      | Polymorphic uctx -> Instance.length u = AbstractContext.size uctx)
  then CErrors.anomaly Pp.(str "bad instance length on mutind.")

let type_of_inductive_gen ((mib,mip),u) paramtyps =
  check_instance mib u;
  match mib.mind_template with
  | None ->
    let cst = instantiate_inductive_constraints mib u in
    subst_instance_constr u mip.mind_user_arity, cst
  | Some templ ->
    let cst, params, subst = instantiate_template_universes (mib, mip) paramtyps in
    let ctx = (List.firstn mip.mind_nrealdecls mip.mind_arity_ctxt) @ params in
    let s = template_subst_sort subst templ.template_concl in
    Term.mkArity (ctx, s), cst

let type_of_inductive pind =
  let (ty, _cst) = type_of_inductive_gen pind [] in
  ty

let constrained_type_of_inductive pind =
  type_of_inductive_gen pind []

let type_of_inductive_knowing_parameters mip args =
  type_of_inductive_gen mip args

(************************************************************************)
(* Type of a constructor *)

let type_of_constructor_gen (cstr, u) (mib,mip) paramtyps =
  check_instance mib u;
  let i = index_of_constructor cstr in
  let nconstr = Array.length mip.mind_consnames in
  if i > nconstr then user_err Pp.(str "Not enough constructors in the type.");
  match mib.mind_template with
  | None ->
    let cst = instantiate_inductive_constraints mib u in
    subst_instance_constr u mip.mind_user_lc.(i-1), cst
  | Some _ ->
    let cst, params, _ = instantiate_template_universes (mib, mip) paramtyps in
    let _, typ = Term.decompose_prod_n_decls (List.length mib.mind_params_ctxt) mip.mind_user_lc.(i - 1) in
    let typ = Term.it_mkProd_or_LetIn typ params in
    typ, cst

let type_of_constructor pcstr ind =
  let (ty, _cst) = type_of_constructor_gen pcstr ind [] in
  ty

let constrained_type_of_constructor cstru ind =
  type_of_constructor_gen cstru ind []

let type_of_constructor_knowing_parameters cstr specif args =
  type_of_constructor_gen cstr specif args

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
    let hd, args = decompose_app c in
    match kind hd with
    | Ind ((mind',i),_) when MutInd.CanOrd.equal mind mind' ->
       mkApp (mkRel (ntyps+k-i), Array.map (replace_ind k) args)
    | _ -> map_with_binders succ replace_ind k c
  in
  replace_ind 0 t

(************************************************************************)

(* Type of case predicates *)

(* Get type of inductive, with parameters instantiated *)

let quality_leq q q' =
  let open Sorts.Quality in
  match q, q' with
  | QVar q, QVar q' -> Sorts.QVar.equal q q'
  | QConstant q, QConstant q' ->
    begin match q, q' with
    | QSProp, _
    | _, QType
    | QProp, QProp
      -> true
    | (QProp|QType), _ -> false
    end
  | QVar _, QConstant QType -> true
  | (QVar _|QConstant _), _ -> false

type squash = SquashToSet | SquashToQuality of Sorts.Quality.t

let is_squashed ((_,mip),u) =
  let s = mip.mind_sort in
  match mip.mind_squashed with
  | None -> None
  | Some squash ->
    let indq = Sorts.quality (UVars.subst_instance_sort u s) in
    match squash with
    | AlwaysSquashed -> begin match s with
        | Sorts.Set -> Some SquashToSet
        | _ -> Some (SquashToQuality indq)
      end
    | SometimesSquashed squash ->
      (* impredicative set squashes are always AlwaysSquashed,
         so here if inds=Set it is a sort poly squash (see "foo6" in test sort_poly.v) *)
      if Sorts.Quality.Set.for_all (fun q ->
          let q = UVars.subst_instance_quality u q in
          quality_leq q indq)
          squash
      then None
      else Some (SquashToQuality indq)

let is_allowed_elimination specifu s =
  let open Sorts in
  match is_squashed specifu with
  | None -> true
  | Some SquashToSet ->
    begin match s with
      | SProp|Prop|Set -> true
      | QSort _ | Type _ ->
        (* XXX in [Type u] case, should we check [u == set] in the ugraph? *)
        false
    end
  | Some (SquashToQuality indq) -> quality_leq (Sorts.quality s) indq

let is_private (mib,_) = mib.mind_private = Some true
let is_primitive_record (mib,_) =
  match mib.mind_record with
  | PrimRecord _ -> true
  | NotRecord | FakeRecord -> false

(** {6 Changes of representation of Case nodes} *)

(** Provided:
    - a universe instance [u]
    - a term substitution [subst]
    - name replacements [nas]
    [instantiate_context u subst nas ctx] applies both [u] and [subst] to [ctx]
    while replacing names using [nas] (order reversed)
*)
let instantiate_context = Environ.instantiate_context

let expand_arity = Environ.expand_arity

let expand_branch_contexts = Environ.expand_branch_contexts

type ('constr,'types,'r) pexpanded_case =
  (case_info * ('constr * 'r) * 'constr pcase_invert * 'constr * 'constr array)

type expanded_case = (constr,types,Sorts.relevance) pexpanded_case

let expand_case_specif mib (ci, u, params, (p,rp), iv, c, br) =
  (* Γ ⊢ c : I@{u} params args *)
  (* Γ, indices, self : I@{u} params indices ⊢ p : Type *)
  let mip = mib.mind_packets.(snd ci.ci_ind) in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in
  (* Expand the return clause *)
  let ep =
    let (nas, p) = p in
    let realdecls = expand_arity (mib, mip) (ci.ci_ind, u) params nas in
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
  (ci, (ep,rp), iv, c, ebr)

let expand_case env (ci, _, _, _, _, _, _ as case) =
  let specif = Environ.lookup_mind (fst ci.ci_ind) env in
  expand_case_specif specif case

let contract_case env (ci, (p,rp), iv, c, br) =
  let (mib, mip) = lookup_mind_specif env ci.ci_ind in
  let (arity, p) = Term.decompose_lambda_n_decls (mip.mind_nrealdecls + 1) p in
  let (u, pms) = match arity with
  | LocalAssum (_, ty) :: _ ->
    (** Last binder is the self binder for the term being eliminated *)
    let (ind, args) = decompose_app ty in
    let (ind, u) = destInd ind in
    let () = assert (QInd.equal env ind ci.ci_ind) in
    let pms = Array.sub args 0 mib.mind_nparams in
    (** Unlift the parameters from under the index binders *)
    let dummy = List.make mip.mind_nrealdecls mkProp in
    let pms = Array.map (fun c -> Vars.substl dummy c) pms in
    (u, pms)
  | _ -> assert false
  in
  let p =
    let nas = Array.of_list (List.rev_map get_annot arity) in
    ((nas, p),rp)
  in
  let map i br =
    let (ctx, br) = Term.decompose_lambda_n_decls mip.mind_consnrealdecls.(i) br in
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
    let (cstrsign,ccl) = Term.decompose_prod_decls typi in
    let nargs = Context.Rel.length cstrsign in
    let (_,allargs) = decompose_app_list ccl in
    let (lparams,vargs) = List.chop (inductive_params specif) allargs in
    let cargs =
      let cstr = ith_constructor_of_inductive ind (i+1) in
      let dep_cstr = Term.applist (mkConstructU (cstr,u),lparams@(Context.Rel.instance_list mkRel 0 cstrsign)) in
      vargs @ [dep_cstr] in
    let base = Term.lambda_appvect_decls (mip.mind_nrealdecls+1) (lift nargs p) (Array.of_list cargs) in
    Term.it_mkProd_or_LetIn base cstrsign in
  Array.mapi build_one_branch mip.mind_nf_lc

(************************************************************************)
(* Checking the case annotation is relevant *)

let check_case_info env (indsp,u) ci =
  let (mib,mip as spec) = lookup_mind_specif env indsp in
  if
    not (QInd.equal env indsp ci.ci_ind) ||
    not (Int.equal mib.mind_nparams ci.ci_npar) ||
    not (Array.equal Int.equal mip.mind_consnrealdecls ci.ci_cstr_ndecls) ||
    not (Array.equal Int.equal mip.mind_consnrealargs ci.ci_cstr_nargs) ||
    is_primitive_record spec
  then raise (TypeError(env,WrongCaseInfo((indsp,u),ci)))


(************************************************************************)
(************************************************************************)

let apply_branch ((_, i), _u) args ci lf =
  let args = List.skipn ci.ci_npar args in
  let br = lf.(i - 1) in
  let ctx, br = Term.decompose_lambda_n_decls ci.ci_cstr_ndecls.(i - 1) br in
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

let is_norec_path t = match Rtree.dest_head t with
| Norec -> true
| Mrec _ -> false
| exception (Failure _) -> false

let inter_recarg r1 r2 = if eq_recarg r1 r2 then Some r1 else None

let inter_wf_paths = Rtree.inter Declareops.eq_recarg inter_recarg Norec

let incl_wf_paths = Rtree.incl Declareops.eq_recarg inter_recarg Norec

let spec_of_tree t =
  if is_norec_path t
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

let (|||) x y = match x with
  | NeedReduce _ -> x
  | NoNeedReduce -> y

let rec needreduce_of_stack = function
  | [] -> NoNeedReduce
  | SArg _ :: l -> needreduce_of_stack l
  | SClosure (needreduce,_,_,_) :: l -> needreduce ||| needreduce_of_stack l

let redex_level rs = List.length rs

let push_stack_closure renv needreduce c stack =
  (SClosure (needreduce, renv, 0, c)) :: stack

let push_stack_closures renv l stack =
  List.fold_right (push_stack_closure renv NoNeedReduce) l stack

let push_stack_args l stack =
  List.fold_right (fun spec stack -> SArg spec :: stack) l stack

let lift_stack k =
   List.map (function
       | SClosure (needreduce,s,n,c) -> SClosure (needreduce,s,n+k,c)
       | x -> x)

let lift1_stack = lift_stack 1

(******************************)
(* {6 Computing the recursive subterms of a term (propagation of size
   information through Cases).} *)

let lookup_subterms env ind =
  let (_,mip) = lookup_mind_specif env ind in
  mip.mind_recargs

let match_inductive ind ra =
  match ra with
    | Mrec (RecArgInd i) -> Ind.CanOrd.equal ind i
    | Norec | Mrec (RecArgPrim _) -> false

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
    let tree = Rtree.Kind.make mip.mind_recargs in
    match Rtree.Kind.kind tree with
    | Rtree.Kind.Node (_, v) -> Array.map Array.length v
    | Rtree.Kind.Var _ -> assert false
  in
  let subterms = lazy begin match Lazy.force c_spec with
  | Subterm (_, _, t) -> dest_subterms t
  | Dead_code | Internally_bound_subterm _ | Not_subterm -> assert false
  end in
  Array.mapi
      (fun i nca -> (* i+1-th cstructor has arity nca *)
         let lvra = lazy
           (match Lazy.force c_spec with
                Subterm (_,_,t) when match_inductive ci.ci_ind (dest_recarg t) ->
                  let vra = Array.of_list (Lazy.force subterms).(i) in
                  assert (Int.equal nca (Array.length vra));
                  Array.map spec_of_tree vra
              | Dead_code -> Array.make nca Dead_code
              | Internally_bound_subterm _ as x -> Array.make nca x
              | Subterm _ | Not_subterm -> Array.make nca Not_subterm) in
         List.init nca (fun j -> lazy (Lazy.force lvra).(j)))
      car

let check_inductive_codomain ?evars env p =
  let absctx, ar = whd_decompose_lambda_decls ?evars env p in
  let env = push_rel_context absctx env in
  let arctx, s = whd_decompose_prod_decls ?evars env ar in
  let env = push_rel_context arctx env in
  let i,_l' = decompose_app (whd_all ?evars env s) in
  isInd i

(* The following functions are almost duplicated from indtypes.ml, except
that they carry here a poorer environment (containing less information). *)
let ienv_push_var (env, lra) (x,a,ra) =
  (push_rel (LocalAssum (x,a)) env, (Norec,ra)::lra)

let ienv_push_inductive ?evars (env, ra_env) ((mind,u),lpar) =
  let mib = Environ.lookup_mind mind env in
  let ntypes = mib.mind_ntypes in
  let push_ind mip env =
    let r = relevance_of_ind_body mip u in
    let anon = Context.make_annot Anonymous r in
    let decl = LocalAssum (anon, hnf_prod_applist ?evars env (type_of_inductive ((mib,mip),u)) lpar) in
    push_rel decl env
  in
  let env = Array.fold_right push_ind mib.mind_packets env in
  let rc = Array.mapi (fun j t -> Mrec (RecArgInd (mind,j)),t) (Rtree.mk_rec_calls ntypes) in
  let lra_ind = Array.rev_to_list rc in
  let ra_env = List.map (fun (r,t) -> (r,Rtree.lift ntypes t)) ra_env in
  (env, lra_ind @ ra_env)

let rec ienv_decompose_prod ?evars (env,_ as ienv) n c =
 if Int.equal n 0 then (ienv,c) else
   let c' = whd_all ?evars env c in
   match kind c' with
   Prod(na,a,b) ->
     let ienv' = ienv_push_var ienv (na,a,mk_norec) in
     ienv_decompose_prod ?evars ienv' (n-1) b
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
    let hd, args = decompose_app_list c in
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
  match (Environ.retroknowledge env).Retroknowledge.retro_array with
  | Some c' when QConstant.equal env c c' -> true
  | _ -> false

(* [get_recargs_approx env tree ind args] builds an approximation of the recargs
tree for ind, knowing args. The argument tree is used to know when candidate
nested types should be traversed, pruning the tree otherwise. This code is very
close to check_positive in indtypes.ml, but does no positivity check and does not
compute the number of recursive arguments. *)
let get_recargs_approx ?evars env tree ind args =
  let rec build_recargs (env, ra_env as ienv) tree c =
    let x,largs = decompose_app_list (whd_all ?evars env c) in
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
             | Mrec (RecArgInd ind') when QInd.equal env (fst ind_kn) ind' ->
               build_recargs_nested ienv tree (ind_kn, largs)
             | Norec | Mrec _ -> mk_norec
       end
    | Const (c,_) when is_primitive_positive_container env c ->
       begin match dest_recarg tree with
             | Mrec (RecArgPrim c') when QConstant.equal env c c' ->
               build_recargs_nested_primitive ienv tree (c, largs)
             | Norec | Mrec _ -> mk_norec
       end
    | _err ->
       mk_norec

  and build_recargs_nested (env,_ra_env as ienv) tree (((mind,i),u), largs) =
    (* If the inferred tree already disallows recursion, no need to go further *)
    if is_norec_path tree then tree
    else
    let mib = Environ.lookup_mind mind env in
    let auxnpar = mib.mind_nparams_rec in
    let nonrecpar = mib.mind_nparams - auxnpar in
    let (lpar,_) = List.chop auxnpar largs in
    let auxntyp = mib.mind_ntypes in
    (* Extends the environment with a variable corresponding to
             the inductive def *)
    let (env',_ as ienv') = ienv_push_inductive ?evars ienv ((mind,u),lpar) in
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
         let c' = hnf_prod_applist ?evars env' c lpar' in
         (* skip non-recursive parameters *)
         let (ienv',c') = ienv_decompose_prod ?evars ienv' nonrecpar c' in
         build_recargs_constructors ienv' trees.(j).(k) c')
        auxlcvect
      in
      mk_paths (Mrec (RecArgInd (mind,j))) paths
    in
    let irecargs = Array.mapi mk_irecargs mib.mind_packets in
    (Rtree.mk_rec irecargs).(i)

  and build_recargs_nested_primitive (env, ra_env) tree (c, largs) =
    if is_norec_path tree then tree
    else
    let ntypes = 1 in (* Primitive types are modelled by non-mutual inductive types *)
    let ra_env = List.map (fun (r,t) -> (r,Rtree.lift ntypes t)) ra_env in
    let ienv = (env, ra_env) in
    let paths = List.map2 (build_recargs ienv) (dest_subterms tree).(0) largs in
    let recargs = [| mk_paths (Mrec (RecArgPrim c)) [| paths |] |] in
    (Rtree.mk_rec recargs).(0)

  and build_recargs_constructors ienv trees c =
    let rec recargs_constr_rec (env,_ra_env as ienv) trees lrec c =
      let x,largs = decompose_app_list (whd_all ?evars env c) in
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
let restrict_spec ?evars env spec p =
  match spec with
  | Not_subterm | Internally_bound_subterm _ -> spec
  | _ ->
  let absctx, ar = whd_decompose_lambda_decls ?evars env p in
  (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if noccur_with_meta 1 (Context.Rel.length absctx) ar then spec
  else
  let env = push_rel_context absctx env in
  let arctx, s = whd_decompose_prod_decls ?evars env ar in
  let env = push_rel_context arctx env in
  let i,args = decompose_app_list (whd_all ?evars env s) in
  match kind i with
  | Ind i ->
     begin match spec with
           | Dead_code -> spec
           | Subterm(l,st,tree) ->
              let recargs = get_recargs_approx ?evars env tree i args in
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

let rec subterm_specif ?evars renv stack t =
  (* maybe reduction is not always necessary! *)
  let f,l = decompose_app_list (whd_all ?evars renv.env t) in
    match kind f with
    | Rel k -> subterm_var k renv
    | Case (ci, u, pms, p, iv, c, lbr) -> (* iv ignored: it's just a cache *)
      let (ci, (p,_), _iv, c, lbr) = expand_case renv.env (ci, u, pms, p, iv, c, lbr) in
       let stack' = push_stack_closures renv l stack in
       let cases_spec =
         branches_specif renv (lazy_subterm_specif ?evars renv [] c) ci
       in
       let stl =
         Array.mapi (fun i br' ->
                     let stack_br = push_stack_args (cases_spec.(i)) stack' in
                     subterm_specif ?evars renv stack_br br')
                    lbr in
       let spec = subterm_spec_glb stl in
       restrict_spec ?evars renv.env spec p

    | Fix ((recindxs,i),(_,typarray,bodies as recdef)) ->
      (* when proving that the fixpoint f(x)=e is less than n, it is enough
         to prove that e is less than n assuming f is less than n
         furthermore when f is applied to a term which is strictly less than
         n, one may assume that x itself is strictly less than n
      *)
    if not (check_inductive_codomain ?evars renv.env typarray.(i)) then Not_subterm
    else
      let (ctxt,clfix) = whd_decompose_prod ?evars renv.env typarray.(i) in
      let oind =
        let env' = push_rel_context ctxt renv.env in
          try Some(fst (find_inductive ?evars env' clfix))
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
        let sign,strippedBody = whd_decompose_lambda_n_assum ?evars renv.env nbOfAbst theBody in
                   (* pushing the fix parameters *)
        let stack' = push_stack_closures renv l stack in
        let renv'' = push_ctxt_renv renv' sign in
        let renv'' =
          if List.length stack' < nbOfAbst then renv''
          else
            let decrArg = List.nth stack' decrArg in
            let arg_spec = stack_element_specif ?evars decrArg in
              assign_var_spec renv'' (1, arg_spec) in
          subterm_specif ?evars renv'' [] strippedBody)

    | Lambda (x,a,b) ->
      let () = assert (List.is_empty l) in
      let spec,stack' = extract_stack ?evars stack in
        subterm_specif ?evars (push_var renv (x,a,spec)) stack' b

      (* Metas and evars are considered OK *)
    | (Meta _|Evar _) -> Dead_code

    | Proj (p, _, c) ->
      let subt = subterm_specif ?evars renv stack c in
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
          primitive_specif ?evars renv op l
        | NotEvaluableConst _ -> Not_subterm
      end

    | Var _ | Sort _ | Cast _ | Prod _ | LetIn _ | App _ | Ind _
      | Construct _ | CoFix _ | Int _ | Float _ | String _
      | Array _ -> Not_subterm


      (* Other terms are not subterms *)

and lazy_subterm_specif ?evars renv stack t =
  lazy (subterm_specif ?evars renv stack t)

and stack_element_specif ?evars = function
  | SClosure (_, h_renv, _, h) -> lazy_subterm_specif ?evars h_renv [] h
  | SArg x -> x

and extract_stack ?evars = function
   | [] -> Lazy.from_val Not_subterm, []
   | elt :: l -> stack_element_specif ?evars elt, l

and primitive_specif ?evars renv op args =
  let open CPrimitives in
  match op with
  | Arrayget | Arraydefault ->
    (* t.[i] and default t can be seen as strict subterms of t, with a
       potentially nested rectree. *)
    let arg = List.nth args 1 in (* the result is a strict subterm of the second argument *)
    let subt = subterm_specif ?evars renv [] arg in
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

let filter_stack_domain ?evars env nr p stack =
  let absctx, ar = Term.decompose_lambda_decls p in
  (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if noccur_with_meta 1 (Context.Rel.length absctx) ar then stack
  else let env = push_rel_context absctx env in
  let rec filter_stack env ar stack =
    match stack with
    | [] -> []
    | elt :: stack' ->
    let t = whd_all ?evars env ar in
    match kind t with
    | Prod (n,a,c0) ->
      let d = LocalAssum (n,a) in
      let ctx, a = whd_decompose_prod_decls ?evars env a in
      let env = push_rel_context ctx env in
      let ty, args = decompose_app_list (whd_all ?evars env a) in
      let elt = match kind ty with
      | Ind ind ->
        let spec = stack_element_specif ?evars elt in
        let sarg =
        lazy (match Lazy.force spec with
        | Not_subterm | Dead_code | Internally_bound_subterm _ as spec -> spec
        | Subterm(l,s,path) ->
            let recargs = get_recargs_approx ?evars env path ind args in
            let path = inter_wf_paths path recargs in
            Subterm(l,s,path))
        in
        SArg sarg
      | _ -> SArg (set_iota_specif nr (lazy Not_subterm))
      in
      elt :: filter_stack (push_rel d env) c0 stack'
    | _ -> List.fold_right (fun _ l -> SArg (set_iota_specif nr (lazy Not_subterm)) :: l) stack []
  in
  filter_stack env ar stack

let find_uniform_parameters recindx nargs bodies =
  let nbodies = Array.length bodies in
  let min_indx = Array.fold_left min nargs recindx in
  (* We work only on the i-th body but are in the context of n bodies *)
  let rec aux i k nuniformparams c =
    let f, l = decompose_app_list c in
    match kind f with
    | Rel n ->
      (* A recursive reference to the i-th body *)
      if Int.equal n (nbodies + k - i) then
        List.fold_left_i (fun j nuniformparams a ->
            match kind a with
            | Rel m when Int.equal m (k - j) ->
              (* a reference to the j-th parameter *)
              nuniformparams
            | _ ->
              (* not a parameter: this puts a bound on the size of an extrudable prefix of uniform arguments *)
              min j nuniformparams) 0 nuniformparams l
      else
        nuniformparams
    | _ -> fold_constr_with_binders succ (aux i) k nuniformparams c
  in
  Array.fold_left_i (fun i -> aux i 0) min_indx bodies

(** Given a fixpoint [fix f x y z n {struct n} := phi(f x y u t, ..., f x y u' t')]
    with [z] not uniform we build in context [x:A, y:B(x), z:C(x,y)] a term
    [fix f z n := phi(f u t, ..., f u' t')], say [psi], of some type
    [forall (z:C(x,y)) (n:I(x,y,z)), T(x,y,z,n)], so that
    [fun x y z => psi z] is of same type as the original term *)

let drop_uniform_parameters nuniformparams bodies =
  let nbodies = Array.length bodies in
  let rec aux i k c =
    let f, l = decompose_app_list c in
    match kind f with
    | Rel n ->
      (* A recursive reference to the i-th body *)
      if Int.equal n (nbodies + k - i) then
        let new_args = List.skipn_at_best nuniformparams l in
        Term.applist (f, new_args)
      else
        c
    | _ -> map_with_binders succ (aux i) k c
  in
  Array.mapi (fun i -> aux i 0) bodies

let filter_fix_stack_domain nr decrarg stack nuniformparams =
  let rec aux i nuniformparams stack =
    match stack with
    | [] -> []
    | a :: stack ->
      let uniform, nuniformparams = if nuniformparams = 0 then false, 0 else true, nuniformparams -1 in
      let a =
        if uniform || Int.equal i decrarg then a
        else
          (* deactivate the status of non-uniform parameters since we
             cannot guarantee that they are preserve in the recursive
             calls *)
          SArg (set_iota_specif nr (lazy Not_subterm)) in
      a :: aux (i+1) nuniformparams stack
  in aux 0 nuniformparams stack

let pop_argument ?evars needreduce renv elt stack x a b =
  match needreduce, elt with
  | NoNeedReduce, SClosure (NoNeedReduce, _, n, c) ->
    (* Neither function nor args have rec calls on internally bound variables *)
    let spec = stack_element_specif ?evars elt in
    (* Thus, args do not a priori require to be rechecked, so we push a let *)
    (* maybe the body of the let will have to be locally expanded though, see Rel case *)
    push_let renv (x,lift n c,a,spec), lift1_stack stack, b
  | _, SClosure (_, _, n, c) ->
    (* Either function or args have rec call on internally bound variables *)
    renv, stack, subst1 (lift n c) b
  | _, SArg spec ->
    (* Going down a case branch *)
    push_var renv (x,a,spec), lift1_stack stack, b

let judgment_of_fixpoint (_, types, bodies) =
  Array.map2 (fun typ body -> { uj_val = body ; uj_type = typ }) types bodies

(* Check if [def] is a guarded fixpoint body with decreasing arg.
   given [recpos], the decreasing arguments of each mutually defined
   fixpoint. *)
let check_one_fix ?evars renv recpos trees def =
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
                  match check_is_subterm (stack_element_specif ?evars z) trees.(glob) with
                  | NeedReduceSubterm l -> set_need_reduce renv.env l (illegal_rec_call renv glob z) rs
                  | InvalidSubterm -> raise (FixGuardError (renv.env, illegal_rec_call renv glob z))
              else
                check_rec_call_state renv NoNeedReduce stack rs (fun () ->
                    match lookup_rel p renv.env with
                    | LocalAssum _ -> None
                    | LocalDef (_,c,_) -> Some (lift p c, []))
            end

        | Case (ci, u, pms, ret, iv, c_0, br) -> (* iv ignored: it's just a cache *)
            let (ci, (p,_), _iv, c_0, brs) = expand_case renv.env (ci, u, pms, ret, iv, c_0, br) in
            let needreduce_c_0, rs = check_rec_call renv rs c_0 in
            let rs = check_inert_subterm_rec_call renv rs p in
            (* compute the recarg info for the arguments of each branch *)
            let rs' = NoNeedReduce::rs in
            let nr = redex_level rs' in
            let case_spec =
              branches_specif renv (set_iota_specif nr (lazy_subterm_specif ?evars renv [] c_0)) ci in
            let stack' = filter_stack_domain ?evars renv.env nr p stack in
            let rs' =
              Array.fold_left_i (fun k rs' br' ->
                  let stack_br = push_stack_args case_spec.(k) stack' in
                  check_rec_call_stack renv stack_br rs' br') rs' brs in
            let needreduce_br, rs = List.sep_first rs' in
            check_rec_call_state renv (needreduce_br ||| needreduce_c_0) stack rs (fun () ->
              (* we try hard to reduce the match away by looking for a
                 constructor in c_0 (we unfold definitions too) *)
              let c_0 = whd_all ?evars renv.env c_0 in
              let hd, args = decompose_app_list c_0 in
              let hd, args = match kind hd with
              | CoFix cofix ->
                  decompose_app_list (whd_all ?evars renv.env (Term.applist (contract_cofix cofix, args)))
              | _ -> hd, args in
              match kind hd with
              | Construct cstr -> Some (apply_branch cstr args ci brs, [])
              | CoFix _ | Ind _ | Lambda _ | Prod _ | LetIn _
              | Sort _ | Int _ | Float _ | String _ | Array _ -> assert false
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
            let nbodies = Array.length bodies in
            let rs' = Array.fold_left (check_inert_subterm_rec_call renv) (NoNeedReduce::rs) typarray in
            let renv' = push_fix_renv renv recdef in
            let nuniformparams = find_uniform_parameters recindxs (List.length stack) bodies in
            let bodies = drop_uniform_parameters nuniformparams bodies in
            let fix_stack = filter_fix_stack_domain (redex_level rs) decrArg stack nuniformparams in
            let fix_stack = if List.length stack > decrArg then List.firstn (decrArg+1) fix_stack else fix_stack in
            let stack_this = lift_stack nbodies fix_stack in
            let stack_others = lift_stack nbodies (List.firstn nuniformparams fix_stack) in
            (* Check guard in the expanded fix *)
            let illformed () =
              error_ill_formed_rec_body renv.env (Type_errors.FixGuardError NotEnoughAbstractionInFixBody)
                (pi1 recdef) i (push_rec_types recdef renv.env)
                (judgment_of_fixpoint recdef) in
            let rs' = Array.fold_left2_i (fun j rs' recindx body ->
                let fix_stack = if Int.equal i j then stack_this else stack_others in
                check_nested_fix_body illformed renv' (recindx+1) fix_stack rs' body) rs' recindxs bodies in
            let needreduce_fix, rs = List.sep_first rs' in
            let absorbed_stack, non_absorbed_stack = List.chop nuniformparams stack in
            check_rec_call_state renv needreduce_fix non_absorbed_stack rs (fun () ->
              (* we try hard to reduce the fix away by looking for a
                 constructor in [decrArg] (we unfold definitions too) *)
              if List.length stack <= decrArg then None else
              match List.nth stack decrArg with
              | SArg _ -> (* A match on the way *) None
              | SClosure (_,_,n,recArg) ->
              let c = whd_all ?evars renv.env (lift n recArg) in
              let hd, _ = decompose_app_list c in
              match kind hd with
              | Construct _ -> Some (contract_fix fix, absorbed_stack)
              | CoFix _ | Ind _ | Lambda _ | Prod _ | LetIn _
              | Sort _ | Int _ | Float _ | String _
              | Array _ -> assert false
              | Rel _ | Var _ | Const _ | App _ | Case _ | Fix _
              | Proj _ | Cast _ | Meta _ | Evar _ -> None)

        | Const (kn,_u as cu) ->
            check_rec_call_state renv NoNeedReduce stack rs (fun () ->
                if evaluable_constant kn renv.env then Some (constant_value_in renv.env cu, [])
                else None)

        | Lambda (x,a,b) ->
            begin
              let needreduce, rs = check_rec_call renv rs a in
              match stack with
              | elt :: stack ->
                let renv, stack, b = pop_argument ?evars needreduce renv elt stack x a b in
                check_rec_call_stack renv stack rs b
              | [] ->
                check_rec_call_stack (push_var_renv renv (redex_level rs) (x,a)) [] rs b
            end

        | Prod (x,a,u) ->
            (* Note: we cannot ensure that the stack is empty because
               non-accessible branches of "match" expressions can have
               arbitrary types (see #17073) *)
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

        | Proj (p, _, c) ->
            begin
              let needreduce', rs = check_rec_call renv rs c in
              check_rec_call_state renv needreduce' stack rs (fun () ->
              (* we try hard to reduce the proj away by looking for a
                 constructor in c (we unfold definitions too) *)
              let c = whd_all ?evars renv.env c in
              let hd, args = decompose_app c in
              let hd, args = match kind hd with
              | CoFix cofix ->
                  decompose_app (whd_all ?evars renv.env (mkApp (contract_cofix cofix, args)))
              | _ -> hd, args in
              match kind hd with
              | Construct _ -> Some (args.(Projection.npars p + Projection.arg p), [])
              | CoFix _ | Ind _ | Lambda _ | Prod _ | LetIn _
              | Sort _ | Int _ | Float _ | String _ | Array _ -> assert false
              | Rel _ | Var _ | Const _ | App _ | Case _ | Fix _
              | Proj _ | Cast _ | Meta _ | Evar _ -> None)
            end

        | Var id ->
            check_rec_call_state renv NoNeedReduce stack rs (fun () ->
              let open! Context.Named.Declaration in
              match lookup_named id renv.env with
              | LocalAssum _ -> None
              | LocalDef (_,c,_) -> Some (c, []))

        | LetIn (x,c,t,b) ->
            let needreduce_c, rs = check_rec_call renv rs c in
            let needreduce_t, rs = check_rec_call renv rs t in
            begin
              match needreduce_of_stack stack ||| needreduce_c ||| needreduce_t with
              | NoNeedReduce ->
                  (* Stack do not require to beta-reduce; let's look if the body of the let needs *)
                  let spec = lazy_subterm_specif ?evars renv [] c in
                  let stack = lift1_stack stack in
                  check_rec_call_stack (push_let renv (x,c,t,spec)) stack rs b
              | NeedReduce _ -> check_rec_call_stack renv stack rs (subst1 c b)
            end

        | Cast (c,_,t) ->
            let rs = check_inert_subterm_rec_call renv rs t in
            let rs = check_rec_call_stack renv stack rs c in
            rs

        | Sort _ | Int _ | Float _ | String _ ->
            (* See [Prod]: we cannot ensure that the stack is empty *)
            rs

        | Array (_u,t,def,ty) ->
            (* See [Prod]: we cannot ensure that the stack is empty *)
            let rs = Array.fold_left (check_inert_subterm_rec_call renv) rs t in
            let rs = check_inert_subterm_rec_call renv rs def in
            let rs = check_inert_subterm_rec_call renv rs ty in
            rs

        (* l is not checked because it is considered as the meta's context *)
        | (Evar _ | Meta _) ->
            rs

  and check_nested_fix_body illformed renv decr stack rs body =
    if Int.equal decr 0 then
      check_inert_subterm_rec_call renv rs body
    else
      match kind (whd_all ?evars renv.env body) with
        | Lambda (x,a,body) ->
          begin
            match stack with
            | elt :: stack ->
              let rs = check_inert_subterm_rec_call renv rs a in
              let renv', stack', body' = pop_argument NoNeedReduce renv elt stack x a body in
              check_nested_fix_body illformed renv' (decr-1) stack' rs body'
            | [] ->
              let renv' = push_var_renv renv (redex_level rs) (x,a) in
              check_nested_fix_body illformed renv' (decr-1) [] rs body
          end
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
        | Some (c, stack') -> check_rec_call_stack renv (stack'@stack) rs c

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

let inductive_of_mutfix ?evars env ((nvect,bodynum),(names,types,bodies as recdef)) =
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
      match kind (whd_all ?evars env def) with
        | Lambda (x,a,b) ->
            if noccur_with_meta n nbfix a then
              let env' = push_rel (LocalAssum (x,a)) env in
              if Int.equal n (k + 1) then
                (* get the inductive type of the fixpoint *)
                let (mind, _) =
                  try find_inductive ?evars env a
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
    let ((ind, u), _) as res = check_occur fixenv 1 def in
    let _, mip = lookup_mind_specif env ind in
    (* recursive sprop means non record with projections -> squashed *)
    let () =
      if Environ.is_type_in_type env (GlobRef.IndRef ind) then ()
      else match relevance_of_ind_body mip u with
        | Sorts.Irrelevant | Sorts.RelevanceVar _ as rind ->
          if not (Sorts.relevance_equal names.(i).Context.binder_relevance rind)
          then raise_err env i FixpointOnIrrelevantInductive
        | Sorts.Relevant -> ()
    in
    res
  in
  (* Do it on every fixpoint *)
  let rv = Array.map2_i find_ind nvect bodies in
  (Array.map fst rv, Array.map snd rv)


let check_fix ?evars env ((nvect,_),(names,_,bodies as recdef) as fix) =
  let (minds, rdef) = inductive_of_mutfix ?evars env fix in
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
      try check_one_fix ?evars renv nvect trees body
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

let rec codomain_is_coind ?evars env c =
  let b = whd_all ?evars env c in
  match kind b with
    | Prod (x,a,b) ->
        codomain_is_coind ?evars (push_rel (LocalAssum (x,a)) env) b
    | _ ->
        (try find_coinductive ?evars env b
        with Not_found ->
          raise (CoFixGuardError (env, CodomainNotInductiveType b)))

let check_one_cofix ?evars env nbfix def deftype =
  let rec check_rec_call env alreadygrd n tree vlra t =
    if not (noccur_with_meta n nbfix t) then
      let c,args = decompose_app_list (whd_all ?evars env t) in
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
                  if is_norec_path rar then
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
            let (_, (p,_), _iv, tm, vrest) = expand_case env (ci, u, pms, p, iv, tm, br) in
            let tree = match restrict_spec ?evars env (Subterm (Int.Set.empty, Strict, tree)) p with
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
          | Ind _ | Fix _ | Proj _ | Int _ | Float _ | String _
          | Array _ ->
           raise (CoFixGuardError (env,NotGuardedForm t)) in

  let ((mind, _),_) = codomain_is_coind ?evars env deftype in
  let vlra = lookup_subterms env mind in
  check_rec_call env false 1 vlra (dest_subterms vlra) def

(* The  function which checks that the whole block of definitions
   satisfies the guarded condition *)

let check_cofix ?evars env (_bodynum,(names,types,bodies as recdef)) =
  let flags = Environ.typing_flags env in
  if flags.check_guarded then
    let nbfix = Array.length bodies in
    for i = 0 to nbfix-1 do
      let fixenv = push_rec_types recdef env in
      try check_one_cofix ?evars fixenv nbfix bodies.(i) types.(i)
      with CoFixGuardError (errenv,err) ->
        error_ill_formed_rec_body errenv (Type_errors.CoFixGuardError err) names i
          fixenv (judgment_of_fixpoint recdef)
    done
  else
    ()

module Template = struct
  let bind_kind = bind_kind
  let template_subst_sort = template_subst_sort
  let max_template_quality = max_template_quality
end

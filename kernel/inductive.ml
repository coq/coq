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
open Sorts

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

let get_template_instance mib u = match mib.mind_template with
| None -> u
| Some templ ->
  let () = assert (UVars.Instance.is_empty u) in
  templ.template_defaults

let inductive_paramdecls (mib,u) =
  let u = get_template_instance mib u in
  Vars.subst_instance_context u mib.mind_params_ctxt

let inductive_nnonrecparams mib = mib.mind_nparams - mib.mind_nparams_rec

let inductive_nonrec_rec_paramdecls (mib,u) =
  let nnonrecparamdecls = inductive_nnonrecparams mib in
  let paramdecls = inductive_paramdecls (mib,u) in
  Context.Rel.chop_nhyps nnonrecparamdecls paramdecls

let instantiate_inductive_constraints mib u =
  UVars.AbstractContext.instantiate u (Declareops.inductive_polymorphic_context mib)

(** Splits a fixpoint body between the context until the [recindx+1]-th
    assumption, and the rest of the body. Inlines local definitions,
    which is necessary for the computation of uniform arguments,
    and incidentally allows local definitions in the prefix to circumvent
    restrictions if their inlining passes them. *)
let split_struct_arg ?evars env recindx =
  let rec decrec env n ctx c =
    if Int.equal n 0 then ctx, c
    else
    let rc = whd_all ?evars env c in
    match kind rc with
    | Lambda (na, ty, bd) ->
        let d = LocalAssum (na, ty) in
        decrec (push_rel d env) (n-1) (Context.Rel.add d ctx) bd
    | _ -> invalid_arg "split_struct_arg"
  in
  decrec env (recindx + 1) Context.Rel.empty

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
  let u = get_template_instance mib u in
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
  | QConstant QSProp, _ | _, QConstant QSProp
  | QGlobal _, _ | _, QGlobal _ ->
    assert false
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
  | Type u | GSort (_, u) ->
    let u = univ_bind_kind u in
    assert (Option.has_some u);
    None, u
  | VSort (q,u) ->
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
| Sorts.Type u | Sorts.GSort (_, u) as s ->
  Sorts.make (Sorts.quality s) (template_subst_universe subst u)
| Sorts.VSort (q,u) ->
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
  let foldq (q, cst, q') accq =
    let substq q = match q with
      | Quality.QConstant _ | Quality.QGlobal _ -> q
      | Quality.QVar q' ->
         begin
           match QVar.var_index q' with
           | None -> q
           | Some q' -> Int.Map.get q' (fst subst)
         end in
    ElimConstraints.add (substq q, cst, substq q') accq in
  let foldu (u, cst, v) accu =
    (* v is not a local universe by the unbounded from below property *)
    let u = match Level.var_index u with
      | None -> Universe.make u
      | Some u -> Int.Map.get u (snd subst)
    in
    (* if qsort, it is above prop *)
    let fold accu (u, n) = match n, cst with
      | 0, _ -> UnivConstraints.add (u, cst, v) accu
      | 1, UnivConstraint.Le -> UnivConstraints.add (u, UnivConstraint.Lt, v) accu
      | 1, (UnivConstraint.Eq | UnivConstraint.Lt) -> assert false (* FIXME? *)
      | _ -> assert false
    in
    List.fold_left fold accu (Univ.Universe.repr u)
  in
  PConstraints.fold (foldq, foldu) cstrs PConstraints.empty

let instantiate_template_universes mib args =
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
    let cst, params, subst = instantiate_template_universes mib paramtyps in
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
    let cst, params, _ = instantiate_template_universes mib paramtyps in
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

let arities_of_constructors (_, u) (mib, mip) =
  let u = get_template_instance mib u in
  let map (ctx, c) =
    let cty = Term.it_mkProd_or_LetIn c ctx in
    subst_instance_constr u cty
  in
  Array.map map mip.mind_nf_lc

let type_of_constructors (_, u) (mib, mip) =
  let u = get_template_instance mib u in
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

(** Elimination functions *)

let raw_eliminates_to = QGraph.ElimTable.eliminates_to

let eliminates_to g = QGraph.eliminates_to g

let sort_eliminates_to g s s' = eliminates_to g (Sorts.quality s) (Sorts.quality s')

type squash = SquashToSet | SquashToQuality of Quality.t

type 'a allow_elimination_actions =
  { not_squashed : 'a
  ; squashed_to_set_below : 'a
  ; squashed_to_set_above : 'a
  ; squashed_to_quality : Quality.t -> 'a }

let is_squashed_gen g nf_quality ((_,mip),u) =
  let s = mip.mind_sort in
  match mip.mind_squashed with
  | None -> None
  | Some squash ->
    let indq = nf_quality (UVars.subst_instance_quality u @@ Sorts.quality s) in
    match squash with
    | AlwaysSquashed ->
      begin match s with
      | Set -> Some SquashToSet
      | _ -> Some (SquashToQuality indq)
      end
    | SometimesSquashed squash ->
      (* impredicative set squashes are always quashed,
         so here if inds=Set it is a sort poly squash (see "foo6" in test sort_poly.v) *)
      if Quality.Set.for_all
          (fun q -> eliminates_to g indq (nf_quality (UVars.subst_instance_quality u q)))
          squash && not @@ Quality.is_qvar indq
      then None
      else Some (SquashToQuality indq)

let allowed_elimination_gen g nf_quality actions specifu s =
  match is_squashed_gen g nf_quality specifu with
  | None -> actions.not_squashed
  | Some SquashToSet ->
    begin match s with
      | SProp|Prop|Set -> actions.squashed_to_set_below
      | GSort _ | VSort _ | Type _ -> actions.squashed_to_set_above
    end
  | Some (SquashToQuality indq) -> actions.squashed_to_quality indq

let is_squashed env specif =
  is_squashed_gen (Environ.qualities env) Fun.id specif

let is_allowed_elimination_actions g s =
  { not_squashed = true
  ; squashed_to_set_below = true
  (* XXX in [Type u] case, should we check [u == set] in the ugraph? *)
  ; squashed_to_set_above = false
  ; squashed_to_quality
    = fun indq -> eliminates_to g indq (Sorts.quality s)}

let is_allowed_elimination env specifu s =
  let g = Environ.qualities env in
  allowed_elimination_gen g
    Fun.id
    (is_allowed_elimination_actions g s)
    specifu s

(* We always allow fixpoints on values in Prop (for the accessibility predicate for instance). *)
let is_allowed_fixpoint elim_to sind star =
  elim_to (Sorts.quality sind) Quality.qprop ||
    elim_to (Sorts.quality sind) (Sorts.quality star)

(************************************************************************)

let is_private (mib,_) = mib.mind_private = Some true
let is_primitive_record (_,mip) =
  match mip.mind_record with
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
  let (arity, p) = match Term.decompose_lambda_n_decls_opt (mip.mind_nrealdecls + 1) p with
    | Some v -> v
    | None -> CErrors.anomaly Pp.(str "contract_case: not enough abstractions in return predicate.")
  in
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
    let (ctx, br) = match Term.decompose_lambda_n_decls_opt mip.mind_consnrealdecls.(i) br with
      | Some v -> v
      | None ->
        CErrors.anomaly Pp.(fmt "contract_case: not enough abstractions in branch %d." i)
    in
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

let apply_branch ((_, i), _u) args ci brctxs brs =
  let args = List.skipn ci.ci_npar args in
  let brctx = brctxs.(i - 1) in
  let _, br = brs.(i - 1) in
  let subst = subst_of_rel_context_instance_list brctx args in
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


(************************************************************************)
(* Subterm information *)

module WfPaths :
sig
type t
val lookup_subterms : env -> inductive -> t
val lookup_mutual_subterms : env -> MutInd.t -> t array
val inter : t -> t -> t
val restrict : t -> wf_paths -> t
val dest_subterm : t -> int -> int -> t
val dest_subterms : t -> t array array
val is_norec : t -> bool
val is_inductive : env -> inductive -> t -> bool
val is_primitive_positive_container : env -> Constant.t -> t -> bool
val incl : t -> t -> bool

end =
struct

module Atm = Rtree.Automaton

type t = recarg Atm.t

let lookup_subterms env ind =
  let _, mip = lookup_mind_specif env ind in
  mip.mind_automaton

let lookup_mutual_subterms env mind =
  let mib = Environ.lookup_mind mind env in
  Array.map (fun mip -> mip.mind_automaton) mib.mind_packets

let meet_recarg r1 r2 = match r1, r2 with
| Mrec _, Mrec _ ->
  let () = assert (eq_recarg r1 r2) in
  r1
| Norec, Norec -> Norec
| (Norec, Mrec _) | (Mrec _, Norec) -> Norec

let inter t1 t2 =
  let automaton = Atm.inter meet_recarg t1 t2 in
  if automaton == t1 then t1 else Atm.compact compare_recarg automaton

let restrict t p =
  let p = Atm.make p in
  let p = Atm.compact compare_recarg p in
  let automaton = Atm.inter meet_recarg t p in
  Atm.compact compare_recarg automaton

let dest_subterm t i j =
  let trans = Atm.transitions t (Atm.initial t) in
  Atm.move t trans.(i).(j)

let dest_subterms t =
  let trans = Atm.transitions t (Atm.initial t) in
  let map v = Array.map (fun tgt -> Atm.move t tgt) v in
  Array.map map trans

let dest_recarg t =
  Atm.data t (Atm.initial t)

let is_norec t = match dest_recarg t with
| Norec -> true
| Mrec _ -> false
| exception Failure _ ->
  anomaly ~label:"rtree" Pp.(str "Non-closed recursive tree during guard checking.")

let is_inductive env ind t = match dest_recarg t with
| Mrec (RecArgInd i) -> QInd.equal env ind i
| Norec | Mrec (RecArgPrim _) -> false

let is_primitive_positive_container env cst t = match dest_recarg t with
| Mrec (RecArgPrim c) -> QConstant.equal env cst c
| Norec | Mrec _ -> false

let equal t1 t2 =
  Atm.equal eq_recarg t1 t2

let incl t1 t2 =
  equal t1 t2 ||
  let t12 = inter t1 t2 in
  equal t1 t12

end

(*************************************)
(* Exported utilities for positivity *)

let is_primitive_positive_container env c =
  match (Environ.retroknowledge env).Retroknowledge.retro_array with
  | Some c' when QConstant.equal env c c' -> true
  | _ -> false

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


(*****************************************************************************)
(* Subterm specification *)
module Subterm : sig

type size = Large | Strict

(**
  Possible specifications for a term, from most to least acceptable:
  - DeadCode: the term has been built by elimination over an empty type;
  - Vars l: the term is as much of a subterm as the worst of these variables;
    variables are levels pointing to the redex stack;
  - Subterm: the term is a [strict|large] subterm of the structural argument;
    the argument itself is a large subterm, becomes strict after a [match];
    the wf_paths argument specifies which constructor arguments are recursive,
    it can never be empty or this downgrades the specification to [NotSubterm];
    the [int set] is the same as in [Vars l];
  - NotSubterm: the term is not a subterm in any kind **)
type t = private
  | DeadCode
  | Vars of Int.Set.t
  | Subterm of size * WfPaths.t * Int.Set.t
  | NotSubterm

val structural : WfPaths.t -> t
val strict_subterm : WfPaths.t -> t

val dead_code : t
val not_subterm : t

val internal : int -> t
val make_internal : int -> t lazy_t -> t lazy_t

type check_result =
  | InvalidSubterm
  | NeedReduce of Int.Set.t

val check : t -> WfPaths.t -> check_result

val inter_spec : t array -> t

val on_branches : env -> inductive -> t lazy_t -> int -> t lazy_t list

val on_projection : t -> int -> t
val on_array : t -> t

val prune_path : ?evars:CClosure.evar_handler ->
  env -> t -> pinductive -> types list -> t

val prune_path_tree : ?evars:CClosure.evar_handler ->
  env -> WfPaths.t -> pinductive -> types list -> WfPaths.t option

end = struct

type size = Large | Strict

(* merging information *)
let inter_size s1 s2 =
  match s1 with
  | Strict -> s2
  | Large -> Large


(**
  Possible specifications for a term, from most to least acceptable:
  - DeadCode: the term has been built by elimination over an empty type;
  - Vars l: the term is as much of a subterm as the worst of these variables;
    variables are levels pointing to the redex stack;
  - Subterm: the term is a [strict|large] subterm of the structural argument;
    the argument itself is a large subterm, becomes strict after a [match];
    the wf_paths argument specifies which constructor arguments are recursive,
    it can never be empty or this downgrades the specification to [NotSubterm];
    the [int set] is the same as in [Vars l];
  - NotSubterm: the term is not a subterm in any kind **)

type t =
  | DeadCode
  | Vars of Int.Set.t
  | Subterm of size * WfPaths.t * Int.Set.t
  | NotSubterm

(** Constructor for Subterm, which possibly downgrades to NotSubterm *)
let spec_of_tree size vars tree =
  if WfPaths.is_norec tree then
    NotSubterm
  else
    Subterm (size, tree, vars)

let structural tree =
  spec_of_tree Large Int.Set.empty tree

let strict_subterm tree =
  spec_of_tree Strict Int.Set.empty tree

let internal n =
  assert (n >= 1);
  Vars (Int.Set.singleton n)

let dead_code = DeadCode
let not_subterm = NotSubterm

let make_internal n spec =
  lazy begin match Lazy.force spec with
  | NotSubterm -> internal n
  | spec -> spec
  end

type check_result =
  | InvalidSubterm
  | NeedReduce of Int.Set.t (* empty = NoNeedReduce *)

let check t tree =
  match t with
  | DeadCode -> NeedReduce Int.Set.empty
  | Vars l ->   NeedReduce l
  | Subterm (Strict, tree', l) ->
    if WfPaths.incl tree tree' then
      NeedReduce l
    else
      InvalidSubterm
  | NotSubterm | Subterm (Large, _, _) -> InvalidSubterm

let inter_spec s1 s2 =
  match s1, s2 with
  | s, DeadCode | DeadCode, s -> s
  | NotSubterm, _ | _, NotSubterm -> NotSubterm
  | Vars l1, Vars l2 ->
    Vars (Int.Set.union l1 l2)
  | Subterm (s, tree, l1), Vars l2
  | Vars l1, Subterm (s, tree, l2) ->
    Subterm (s, tree, Int.Set.union l1 l2)
  | Subterm (s1, tree1, l1), Subterm (s2, tree2, l2) ->
    spec_of_tree (inter_size s1 s2) (Int.Set.union l1 l2) (WfPaths.inter tree1 tree2)

let inter_spec =
  Array.fold_left inter_spec DeadCode


let on_constructors discr i j =
  lazy begin match Lazy.force discr with
  | DeadCode | Vars _ | NotSubterm as spec -> spec
  | Subterm (_, tree, vars) ->
    let subtree = WfPaths.dest_subterm tree i j in
    spec_of_tree Strict vars subtree
  end

let on_branches env ind discr =
  let _, mip = lookup_mind_specif env ind in
  let sizes = mip.mind_consnrealargs in
  let subterms = on_constructors discr in
  fun i -> List.init sizes.(i) (subterms i)

let on_projection discr n =
  Lazy.force (on_constructors (lazy discr) 0 n)

let on_array discr =
  Lazy.force (on_constructors (lazy discr) 0 0)





(* The following functions are almost duplicated from indtypes.ml, except
that they carry here a poorer environment (containing less information). *)
let ienv_push_var (env, lra) (x,a,ra) =
  (push_rel (LocalAssum (x,a)) env, (Norec,ra)::lra)

let ienv_push_inductive ?evars (env, ra_env) ((mind,u),lpar) =
  let mib = Environ.lookup_mind mind env in
  let ntypes = Declareops.mind_ntypes mib in
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
      if WfPaths.is_inductive env (fst ind_kn) tree then
        build_recargs_nested ienv tree (ind_kn, largs)
      else mk_norec
    | Const (c, _) ->
      if WfPaths.is_primitive_positive_container env c tree then
        build_recargs_nested_primitive ienv tree (c, largs)
      else mk_norec
    | _err ->
       mk_norec

  and build_recargs_nested (env,_ra_env as ienv) tree (((mind,i),u), largs) =
    (* If the inferred tree already disallows recursion, no need to go further *)
    if WfPaths.is_norec tree then mk_norec
    else
    let mib = Environ.lookup_mind mind env in
    let nonrecpar = mib.mind_nparams - mib.mind_nparams_rec in
    let (lpar,_) = List.chop mib.mind_nparams_rec largs in
    let auxntyp = Declareops.mind_ntypes mib in
    (* Extends the environment with a variable corresponding to
             the inductive def *)
    let (env',_ as ienv') = ienv_push_inductive ?evars ienv ((mind,u),lpar) in
    (* Parameters expressed in env' *)
    let lpar' = List.map (lift auxntyp) lpar in
    (* In case of mutual inductive types, we use the recargs tree which was
    computed statically. This is fine because nested inductive types with
    mutually recursive containers are not supported. *)
    let trees =
      if Int.equal auxntyp 1 then [|tree|]
      else WfPaths.lookup_mutual_subterms env mind
    in
    let mk_irecargs j mip =
      (* The nested inductive type with parameters removed *)
      let auxlcvect = abstract_mind_lc auxntyp mib.mind_nparams_rec mind mip.mind_nf_lc in
      let paths = Array.mapi
        (fun k c ->
         let c' = hnf_prod_applist ?evars env' c lpar' in
         (* skip non-recursive parameters *)
         let (ienv',c') = ienv_decompose_prod ?evars ienv' nonrecpar c' in
         build_recargs_constructors ienv' trees.(j) k c')
        auxlcvect
      in
      mk_paths (Mrec (RecArgInd (mind,j))) paths
    in
    let irecargs = Array.mapi mk_irecargs mib.mind_packets in
    (Rtree.mk_rec irecargs).(i)

  and build_recargs_nested_primitive (env, ra_env) tree (c, largs) =
    if WfPaths.is_norec tree then mk_norec
    else
    let ntypes = 1 in (* Primitive types are modelled by non-mutual inductive types *)
    let ra_env = List.map (fun (r,t) -> (r,Rtree.lift ntypes t)) ra_env in
    let ienv = (env, ra_env) in
    let paths = List.map2 (build_recargs ienv) (Array.to_list (WfPaths.dest_subterms tree).(0)) largs in
    let recargs = [| mk_paths (Mrec (RecArgPrim c)) [| paths |] |] in
    (Rtree.mk_rec recargs).(0)

  and build_recargs_constructors ienv trees k c =
    let rec recargs_constr_rec (env,_ra_env as ienv) i lrec c =
      let x,largs = decompose_app_list (whd_all ?evars env c) in
        match kind x with

          | Prod (na,b,d) ->
             let () = assert (List.is_empty largs) in
             let recarg = build_recargs ienv (WfPaths.dest_subterm trees k i) b in
             let ienv' = ienv_push_var ienv (na,b,mk_norec) in
             recargs_constr_rec ienv' (i+1) (recarg::lrec) d
          | _hd ->
             List.rev lrec
    in
    recargs_constr_rec ienv 0 [] c
  in
  (* starting with ra_env = [] seems safe because any unbounded Rel will be
  assigned Norec *)
  build_recargs_nested (env,[]) tree (ind, args)

let prune_path_tree ?evars env tree ind args =
  let recargs = get_recargs_approx ?evars env tree ind args in
  let tree = WfPaths.restrict tree recargs in
  if WfPaths.is_norec tree then
    None
  else
    Some tree

let prune_path ?evars env spec ind args =
  match spec with
  | DeadCode | Vars _ | NotSubterm as spec -> spec
  | Subterm (size, tree, vars) ->
    let recargs = get_recargs_approx ?evars env tree ind args in
    let tree = WfPaths.restrict tree recargs in
    spec_of_tree size vars tree

end

(*************************************************************)
(* Environment annotated with marks on recursive arguments *)

type guard_env =
  { env     : env;
    (* dB of last fixpoint *)
    rel_min : int;
    (* dB of variables denoting subterms *)
    genv    : Subterm.t Lazy.t list;
  }

let make_renv env recarg tree =
  { env = env;
    rel_min = recarg+2; (* recarg = 0 ==> Rel 1 -> recarg; Rel 2 -> fix *)
    genv = [Lazy.from_val (Subterm.structural tree)] }

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
  let spec = Lazy.from_val (Subterm.internal n) in
  push_var renv (x,ty,spec)

(* Fetch recursive information about a variable p *)
let subterm_var p renv =
  try Lazy.force (List.nth renv.genv (p-1))
  with Failure _ | Invalid_argument _ ->
    (* Check still that the variable is well scoped *)
    if 1 <= p && p <= Environ.nb_rel renv.env then
      Subterm.not_subterm
    else
      anomaly ~label:"fixpoint" Pp.(str "Index not found in current environment.")

let push_ctxt_renv renv ctxt =
  let n = Context.Rel.length ctxt in
  { env = push_rel_context ctxt renv.env;
    rel_min = renv.rel_min+n;
    genv = iterate (fun ge -> lazy Subterm.not_subterm::ge) n renv.genv }

let push_branch_renv lazy_subterm_specif renv ctxt specs =
  let rec push renv tele specs = match tele, specs with
    | [], [] -> renv
    | LocalDef (na, def, ty) :: tele, specs ->
      let spec = lazy_subterm_specif renv def in
      let renv = push_let renv (na, def, ty, spec) in
      push renv tele specs
    | LocalAssum (na, ty) :: tele, spec :: specs ->
      let renv = push_var renv (na, ty, spec) in
      push renv tele specs
    | LocalAssum _ :: _, [] | [], _ :: _ -> assert false
  in
  push renv (List.rev ctxt) specs

let push_fix_renv renv (_,v,_ as recdef) =
  let n = Array.length v in
  { env = push_rec_types recdef renv.env;
    rel_min = renv.rel_min+n;
    genv = iterate (fun ge -> lazy Subterm.not_subterm::ge) n renv.genv }

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
  | SArg of Subterm.t Lazy.t

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

let lift_stack k =
   List.map (function
       | SClosure (needreduce,s,n,c) -> SClosure (needreduce,s,n+k,c)
       | x -> x)

let lift1_stack = lift_stack 1

(******************************)
(* {6 Computing the recursive subterms of a term (propagation of size
   information through Cases).} *)

let check_inductive_codomain ?evars env p =
  let absctx, ar = whd_decompose_lambda_decls ?evars env p in
  let env = push_rel_context absctx env in
  let arctx, s = whd_decompose_prod_decls ?evars env ar in
  let env = push_rel_context arctx env in
  let i,_l' = decompose_app (whd_all ?evars env s) in
  isInd i

(* Check that the parameter arguments of an inductive type do not mention some
   variable range. This is used as a fast-path when casting recursive trees
   against a commutative cut: indices are irrelevant for the tree
   computation in {!get_recargs_approx}. *)
let has_constant_parameters env nvars k ((mind, _), _) args =
  let mib = Environ.lookup_mind mind env in
  let auxnpar = mib.mind_nparams_rec in
  let (lpar, _) = List.chop auxnpar args in
  List.for_all (fun c -> noccur_with_meta (1 + k) nvars c) lpar

let find_rectype_codom ?evars env ty =
  let ctx, ret = whd_decompose_prod ?evars env ty in
  let env = push_rel_context ctx env in
  let ty, args = decompose_app_list (whd_all ?evars env ret) in
  match kind ty with
  | Ind ind -> ctx, ind, args
  | _ -> raise Not_found

type filter = Pass | Block | Prune of env * pinductive * types list
type codomain_filter = Pass' | Test of env * int * types

let apply_filter_stack_one stack_element_specif not_subterm ?evars elt = function
  | Pass -> SArg (stack_element_specif ?evars elt)
  | Block -> SArg not_subterm
  | Prune (env, ind, args) ->
    SArg (lazy (
      let lazy spec = stack_element_specif ?evars elt in
      Subterm.prune_path ?evars env spec ind args))

let apply_filter_spec not_subterm ?evars spec = function
  | Pass -> spec
  | Block -> not_subterm
  | Prune (env, ind, args) ->
    Subterm.prune_path ?evars env spec ind args

let apply_filter_tree ?evars tree = function
  | Pass -> Some tree
  | Block -> None
  | Prune (env, ind, args) ->
    Subterm.prune_path_tree ?evars env tree ind args

(** In context [env = pctx, Δ], with [|pctx| = pctxlen] and [|Δ| = k],
    returns what filter needs to be applied to [elt] from [t] *)
let filter_type apply_filter ?evars pctxlen env k t elt =
  match find_rectype_codom ?evars env t with
  | ctx, ind, args ->
    if has_constant_parameters env pctxlen (k + List.length ctx) ind args then
      apply_filter ?evars elt Pass
    else
      apply_filter ?evars elt (Prune (Environ.push_rel_context ctx env, ind, args))
  | exception Not_found ->
      apply_filter ?evars elt Block

let filter_predicate_stack stack_element_specif not_subterm ?evars pctxlen env p stack =
  (* Optimization: if the predicate is not dependent, no restriction is needed
     and we avoid building the recargs tree. *)
  if noccur_with_meta 1 pctxlen p then
    List.map (fun elt -> SArg (stack_element_specif ?evars elt)) stack, Pass'
  else
    let on_hyp = filter_type (apply_filter_stack_one stack_element_specif not_subterm) ?evars pctxlen in
    let rec filter_stack env k p res = function
      | [] -> env, k, p, List.rev res
      | elt :: stack ->
        match kind (whd_all ?evars env p) with
        | Prod (na, ty, p) ->
          let elt = on_hyp env k ty elt in
          let env = Environ.push_rel (LocalAssum (na, ty)) env in
          filter_stack env (k+1) p (elt :: res) stack
        | _ -> env, k, p, List.rev res
    in
    let env, nhyps, codomain, stack = filter_stack env 0 p [] stack in
    stack, Test (env, nhyps, codomain)

let filter_predicate_codomain ?evars pctxlen ret spec =
  match ret with
  | Test (env, k, t) ->
    filter_type (apply_filter_spec Subterm.not_subterm) ?evars pctxlen env k t spec
  | Pass' -> spec

let filter_predicate_tree ?evars pctxlen env p elt =
  if noccur_with_meta 1 pctxlen p then
    Some elt
  else
    filter_type apply_filter_tree ?evars pctxlen env 0 p elt


(**[subterm_specif renv t] computes the recursive structure of [t] and
   compare its size with the size of the initial recursive argument of
   the fixpoint we are checking. [renv] collects such information
   about variables.
*)
let rec subterm_specif ?evars renv stack t =
  let f, l = decompose_app_list (whd_all ?evars renv.env t) in
  match kind f with
  | Rel k -> subterm_var k renv
  | Case (ci, u, pms, (p, _), _, c, brs) ->
    let specif = lookup_mind_specif renv.env ci.ci_ind in
    let pctx = expand_arity specif (ci.ci_ind, u) pms (fst p) in
    let penv = Environ.push_rel_context pctx renv.env in
    let pctxlen = List.length pctx in

    let stack = push_stack_closures renv l stack in
    let stack, ret = filter_predicate_stack stack_element_specif (lazy Subterm.not_subterm) ?evars pctxlen penv (snd p) stack in

    let c_spec = lazy_subterm_specif ?evars renv [] c in
    let constrargs_spec = Subterm.on_branches renv.env ci.ci_ind c_spec in
    let brctxs = expand_branch_contexts specif u pms brs in
    let stl =
      Array.map2_i (fun i brctx (_, br) ->
        let renv = push_branch_renv (fun renv t -> lazy_subterm_specif ?evars renv [] t) renv brctx (constrargs_spec i) in
        (* No need to lift stack as term closures were abstracted out. *)
        subterm_specif ?evars renv stack br)
        brctxs brs
    in
    let spec = Subterm.inter_spec stl in
    filter_predicate_codomain ?evars pctxlen ret spec

    | Fix ((recindxs,i),(_,typarray,bodies as recdef)) ->
      (* when proving that the fixpoint f(x)=e is less than n, it is enough
         to prove that e is less than n assuming f is less than n
         furthermore when f is applied to a term which is strictly less than
         n, one may assume that x itself is strictly less than n
      *)
    if not (check_inductive_codomain ?evars renv.env typarray.(i)) then Subterm.not_subterm
    else
      let (ctxt,clfix) = whd_decompose_prod ?evars renv.env typarray.(i) in
      let oind =
        let env' = push_rel_context ctxt renv.env in
          try Some(fst (find_inductive ?evars env' clfix))
          with Not_found -> None in
        (match oind with
        | None -> Subterm.not_subterm (* happens if fix is polymorphic *)
        | Some (ind, _) ->
        let stack = push_stack_closures renv l stack in
        let nbfix = Array.length typarray in
        let recargs = WfPaths.lookup_subterms renv.env ind in
                   (* pushing the fixpoints *)
        let renv = push_fix_renv renv recdef in
        let renv =
                     (* Why Strict here ? To be general, it could also be
                        Large... *)
          assign_var_spec renv
          (nbfix-i, lazy (Subterm.strict_subterm recargs)) in
        let decrArg = recindxs.(i) in
        let theBody = bodies.(i)   in
        let sign, strippedBody = split_struct_arg ?evars renv.env decrArg theBody in
                   (* pushing the fix parameters *)
        let renv = push_ctxt_renv renv sign in
        let renv =
          if List.length stack < decrArg + 1 then renv
          else
            let decrArg = List.nth stack decrArg in
            let arg_spec = stack_element_specif ?evars decrArg in
            assign_var_spec renv (1, arg_spec)
        in
        subterm_specif ?evars renv [] strippedBody)

    | Lambda (x,a,b) ->
      let () = assert (List.is_empty l) in
      let spec,stack' = extract_stack ?evars stack in
        subterm_specif ?evars (push_var renv (x,a,spec)) stack' b

      (* Evars are considered OK *)
    | Evar _ -> Subterm.dead_code

    | Proj (p, _, c) ->
      let subt = subterm_specif ?evars renv [] c in
      Subterm.on_projection subt (Projection.arg p)

    | Const c ->
      begin try
        let _ = Environ.constant_value_in renv.env c in Subterm.not_subterm
      with
        | NotEvaluableConst (IsPrimitive (_u,op)) when List.length l >= CPrimitives.arity op ->
          primitive_specif ?evars renv op l
        | NotEvaluableConst _ -> Subterm.not_subterm
      end

    | Meta _ -> assert false

    | Var _ | Sort _ | Cast _ | Prod _ | LetIn _ | App _ | Ind _
      | Construct _ | CoFix _ | Int _ | Float _ | String _
      | Array _ -> Subterm.not_subterm


      (* Other terms are not subterms *)

and lazy_subterm_specif ?evars renv stack t =
  lazy (subterm_specif ?evars renv stack t)

and stack_element_specif ?evars = function
  | SClosure (_, h_renv, _, h) -> lazy_subterm_specif ?evars h_renv [] h
  | SArg x -> x

and extract_stack ?evars = function
   | [] -> lazy Subterm.not_subterm, []
   | elt :: l -> stack_element_specif ?evars elt, l

and primitive_specif ?evars renv op args =
  let open CPrimitives in
  match op with
  | Arrayget | Arraydefault ->
    (* t.[i] and default t can be seen as strict subterms of t, with a
       potentially nested rectree. *)
    let arg = List.nth args 1 in (* the result is a strict subterm of the second argument *)
    let subt = subterm_specif ?evars renv [] arg in
    Subterm.on_array subt
  | _ -> Subterm.not_subterm

(************************************************************************)

exception FixGuardError of env * fix_guard_error

let illegal_rec_call renv fx = function
  | SClosure (_,arg_renv,_,arg) ->
    let le_lt_vars =
    lazy (let (_,le_vars,lt_vars) =
      List.fold_left
        (fun (i,le,lt) sbt ->
          match Lazy.force sbt with
              (Subterm.Subterm (Strict, _, _) | DeadCode) -> (i+1, le, i::lt)
            | (Subterm.Subterm (Large, _, _)) -> (i+1, i::le, lt)
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

type check_subterm_result = Subterm.check_result =
  | InvalidSubterm
  | NeedReduce of Int.Set.t (* empty = NoNeedReduce *)


let find_uniform_parameters illformed ?evars env recindx nargs bodies =
  let nbodies = Array.length bodies in
  (* Ensure that the structural argument is not uniform,
     so that it stays in [non_absorbed_stack] *)
  let min_indx = Array.fold_left min nargs recindx in
  let rec aux k nuniformparams c =
    let f, l = decompose_app_list c in
    match kind f with
    | Rel n ->
      let fold accu c = fold_constr_with_binders succ aux k accu c in
      let nuniformparams = List.fold_left fold nuniformparams l in
      (* A recursive reference to any one of the mutual fixpoints *)
      if n > k && n <= k + nbodies then
        List.fold_left_until (fun j arg ->
          if j >= nuniformparams then Stop nuniformparams else
          match kind arg with
          | Rel m when Int.equal m (k - j) ->
            (* a reference to the j-th parameter *)
            Cont (j+1)
          | _ ->
            (* not a parameter: this puts a bound on the size of an extrudable prefix of uniform arguments *)
            Stop j
          ) 0 l
      else
        nuniformparams
    | _ -> fold_constr_with_binders succ aux k nuniformparams c
  in
  Array.fold_left2_i (fun k nuniformparams recindx c ->
    let _, c = try
      split_struct_arg ?evars env recindx c
      with Invalid_argument _ -> illformed k
      (* Typing invariants are checked later for inner fixpoints *)
    in
    (* Typing invariants say no recursive call happen in prefix ctx *)
    aux (recindx + 1) nuniformparams c)
    min_indx recindx bodies

(*  Given a fixpoint [fix f x y z n {struct n} := phi(f x y u t, ..., f x y u' t')]
    with [z] not uniform we build in context [x:A, y:B(x), z:C(x,y)] a term
    [fix f z n := phi(f u t, ..., f u' t')], say [psi], of some type
    [forall (z:C(x,y)) (n:I(x,y,z)), T(x,y,z,n)], so that
    [fun x y z => psi z] is of same type as the original term *)

let drop_uniform_parameters nuniformparams bodies =
  let nbodies = Array.length bodies in
  let rec aux k c =
    let f, l = decompose_app_list c in
    match kind f with
    | Rel n ->
      let l = List.map (fun c -> aux k c) l in
      (* A recursive reference to any one of the mutual fixpoints *)
      if n > k && n <= k + nbodies then
        let new_args = List.skipn nuniformparams l in
        Term.applist (f, new_args)
      else Term.applist (f, l)
    | _ -> map_with_binders succ aux k c
  in
  Array.map (aux 0) bodies

let filter_fix_stack_domain ?evars nr decrarg stack nuniformparams =
  let rec aux i nuniformparams stack =
    match stack with
    | [] -> []
    | a :: stack ->
      let uniform, nuniformparams = if nuniformparams = 0 then false, 0 else true, nuniformparams -1 in
      let a =
        if uniform then a
        else if Int.equal i decrarg then SArg (stack_element_specif ?evars a)
        (* We forget the needreduce status of the structural argument here,
           since it's checked in [non_absorbed_stack]. *)
        else
          (* deactivate the status of non-uniform parameters since we
             cannot guarantee that they are preserve in the recursive
             calls *)
          SArg (Lazy.from_val (Subterm.internal nr)) in
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

let rec reduce_and_contract_cofix ?evars env c =
  let c = whd_all ?evars env c in
  let hd, args = decompose_app c in
  match kind hd with
  | CoFix cofix ->
    reduce_and_contract_cofix ?evars env (mkApp (contract_cofix cofix, args))
  | _ -> hd, args

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
    | App (f, args) ->
      let rs, stack =
        Array.fold_right (fun a (rs, stack) ->
          let needreduce, rs = check_rec_call renv rs a in
          let stack = push_stack_closure renv needreduce a stack in
          (rs, stack))
          args (rs, stack)
      in
      check_rec_call_stack renv stack rs f

    | Rel p ->
      let rs =
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
            match Subterm.check (Lazy.force (stack_element_specif ?evars z)) trees.(glob) with
            | NeedReduce l -> set_need_reduce renv.env l (illegal_rec_call renv glob z) rs
            | InvalidSubterm -> raise (FixGuardError (renv.env, illegal_rec_call renv glob z))
        else rs
      in
      check_rec_call_state renv NoNeedReduce stack rs (fun () ->
        match lookup_rel p renv.env with
        | LocalAssum _ -> None
        | LocalDef (_,c,_) -> Some (lift p c, []))

    | Case (ci, u, pms, (p, _), _, c, brs) -> (* iv ignored: it's just a cache *)
      let specif = lookup_mind_specif renv.env ci.ci_ind in
      let pctx = expand_arity specif (ci.ci_ind, u) pms (fst p) in
      let penv = Environ.push_rel_context pctx renv.env in
      let pctxlen = List.length pctx in

      let needreduce_c, rs = check_rec_call renv rs c in
      let renv' = push_ctxt_renv renv pctx in
      let rs = check_inert_subterm_rec_call renv' rs (snd p) in
      let rs' = NoNeedReduce :: rs in
      let nr = redex_level rs' in

      let filtered_stack, _ = filter_predicate_stack stack_element_specif ?evars (Lazy.from_val (Subterm.internal nr)) pctxlen penv (snd p) stack in

      let c_spec = Subterm.make_internal nr (lazy_subterm_specif ?evars renv [] c) in
      let constrargs_spec = Subterm.on_branches renv.env ci.ci_ind c_spec in
      let brctxs = expand_branch_contexts specif u pms brs in
      let rs' =
        Array.fold_left2_i (fun i rs' brctx (_, br) ->
          let renv = push_branch_renv (fun renv t -> lazy_subterm_specif ?evars renv [] t) renv brctx (constrargs_spec i) in
          (* No need to lift stack as term closures were abstracted out. *)
          check_rec_call_stack renv filtered_stack rs' br)
          rs' brctxs brs
      in
      let needreduce_br, rs = List.sep_first rs' in
      check_rec_call_state renv (needreduce_c ||| needreduce_br) stack rs (fun () ->
        (* we try hard to reduce the match away by looking for a
            constructor in c_0 (we unfold definitions too) *)
        let hd, args = reduce_and_contract_cofix ?evars renv.env c in
        match kind hd with
        | Construct cstr -> Some (apply_branch cstr (Array.to_list args) ci brctxs brs, [])
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
            let illformed k =
              error_ill_formed_rec_body renv.env (Type_errors.FixGuardError (NotEnoughAbstractionInFixBody recindxs.(k)))
                (pi1 recdef) k (push_rec_types recdef renv.env)
                (judgment_of_fixpoint recdef)
            in
            let nuniformparams = find_uniform_parameters illformed ?evars renv.env recindxs (List.length stack) bodies in
            let bodies = drop_uniform_parameters nuniformparams bodies in
            let fix_stack = filter_fix_stack_domain ?evars (redex_level rs) decrArg stack nuniformparams in
            let fix_stack = if List.length stack > decrArg then List.firstn (decrArg+1) fix_stack else fix_stack in
            let stack_this = lift_stack nbodies fix_stack in
            let stack_others = lift_stack nbodies (List.firstn nuniformparams fix_stack) in
            (* Check guard in the expanded fix *)

            let rs' = Array.fold_left2_i (fun j rs' recindx body ->
                let fix_stack = if Int.equal i j then stack_this else stack_others in
                check_nested_fix_body renv' (recindx+1) fix_stack rs' body) rs' recindxs bodies in
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
            assert (List.is_empty stack);
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
              let hd, args = reduce_and_contract_cofix ?evars renv.env c in
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
            assert (List.is_empty stack);
            rs

        | Array (_u,t,def,ty) ->
            assert (List.is_empty stack);
            let rs = Array.fold_left (check_inert_subterm_rec_call renv) rs t in
            let rs = check_inert_subterm_rec_call renv rs def in
            let rs = check_inert_subterm_rec_call renv rs ty in
            rs

        (* stack is not checked because it will depend on evar definition *)
        | Evar _ -> rs (* TODO: check if evar has a definition in ?evars *)

        | Meta _ -> assert false

  and check_nested_fix_body renv decr stack rs body =
    if Int.equal decr 0 then
      check_inert_subterm_rec_call renv rs body
    else
      match kind (whd_all ?evars renv.env body) with
        | Lambda (x,a,body) ->
          begin
            let rs = check_inert_subterm_rec_call renv rs a in
            match stack with
            | elt :: stack ->
              let renv', stack', body' = pop_argument NoNeedReduce renv elt stack x a body in
              check_nested_fix_body renv' (decr-1) stack' rs body'
            | [] ->
              let renv' = push_var_renv renv (redex_level rs) (x,a) in
              check_nested_fix_body renv' (decr-1) [] rs body
          end
        | _ -> assert false
        (* We know from find_uniform_parameters that they are wellformed *)

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

let raise_fix_guard_err_fn env recdef names =
  let fixenv = push_rec_types recdef env in
  let vdefj = judgment_of_fixpoint recdef in
  let raise_err env i err =
    error_ill_formed_rec_body env (Type_errors.FixGuardError err) names i fixenv vdefj in
  raise_err

let inductive_of_mutfix ?evars env ((nvect, bodynum), (names, types, bodies as recdef)) =
  let nbfix = Array.length bodies in
  if Int.equal nbfix 0
    || not (Int.equal (Array.length nvect) nbfix)
    || not (Int.equal (Array.length types) nbfix)
    || not (Int.equal (Array.length names) nbfix)
    || bodynum < 0
    || bodynum >= nbfix
  then anomaly (Pp.str "Ill-formed fix term.");
  let fixenv = push_rec_types recdef env in
  let raise_err = raise_fix_guard_err_fn env recdef names in
  (* Check the i-th definition with recarg *)
  let find_ind env i recarg def =
    let ctx, body =
      try split_struct_arg ?evars env recarg def
      with Invalid_argument _ ->
        raise_err env i (NotEnoughAbstractionInFixBody recarg)
    in
    (* check no recursive call appear in the first abstractions until recarg *)
    let initial_context = Term.it_mkLambda_or_LetIn mkProp (* dummy *) ctx in
    let () = if not (noccur_with_meta 1 nbfix initial_context) then
      anomaly ~label:"check_one_fix" (Pp.str "Bad occurrence of recursive call.")
    in
    (* ctx has size [recarg+1], top entry is recarg *)
    let ty = Context.Rel.Declaration.get_type (List.hd ctx) in
    (* get the inductive type of the fixpoint *)
    let mind, _ =
      try find_inductive ?evars env ty
      with Not_found ->
        raise_err env i (RecursionNotOnInductiveType ty)
    in
    let mib, _ = lookup_mind_specif env (out_punivs mind) in
    let () = if mib.mind_finite != Finite then
      raise_err env i (RecursionNotOnInductiveType ty)
    in
    (mind, (Environ.push_rel_context ctx env, body))
  in
  (* Do it on every fixpoint *)
  let rv = Array.map2_i (fun i recarg def -> find_ind fixenv i recarg def) nvect bodies in
  (Array.map fst rv, Array.map snd rv)

(* Returns the pairs of (inductive sort * output sort) or
 * None if any elimination constraint was ignored. *)
let sorts_of_mutfix env minds names =
  let ind_ignores_elim_constraints (ind, _) = Environ.ind_ignores_elim_constraints env ind in
  (* recursive sprop means non record with projections -> squashed *)
  if Array.exists ind_ignores_elim_constraints minds then None
  else
    Some (Array.fold_left_i (fun i sorts (ind, inst) ->
        let mib, mip = lookup_mind_specif env ind in
        let ind_sort = match mib.mind_template with
        | None -> UVars.subst_instance_sort inst mip.mind_sort
        | Some templ ->
          let () = assert (UVars.Instance.is_empty inst) in
          (* suspect, this is always Type currently *)
          UVars.subst_instance_sort templ.template_defaults mip.mind_sort
        in
        let u = Sorts.univ_of_sort ind_sort in
        (* This is an approximation: a [Relevant] variable might be of sort [Prop]
           or [Type]. As we only care about the quality, we have to be conservative
           here, i.e., every relevant sort (so, [Prop] or above) can be eliminated
           into any other relevant sort. *)
        let out_sort = match names.(i).Context.binder_relevance with
          | Irrelevant -> Sorts.sprop
          | Relevant -> Sorts.prop
          | RelevanceVar q -> Sorts.vsort q u in
        (ind_sort, out_sort) :: sorts
      ) [] minds)


let check_fix_pre_sorts ?evars env ((nvect, _), (names, _, bodies as recdef) as fix) =
(* For elaboration of elimination constraints, we need to update the evar_map with
   the possibly new constraints (see e.g. [esearch_guard] (Pretyping)). We expose this
   function to be used for this purpose, while check_fix performs the normal check,
   failing when elimination constraints are not satisfied. *)
  let minds, rdef = inductive_of_mutfix ?evars env fix in
  let sorts_opt = sorts_of_mutfix env minds names in
  let inds = Array.map fst minds in
  let flags = Environ.typing_flags env in
  let raise_err = raise_fix_guard_err_fn env recdef names in
  let () =
    if flags.check_guarded then
      let trees = Array.map (fun ind -> WfPaths.lookup_subterms env ind) inds in
      for i = 0 to Array.length bodies - 1 do
        let (fenv, body) = rdef.(i) in
        let renv = make_renv fenv nvect.(i) trees.(i) in
        try check_one_fix ?evars renv nvect trees body
        with FixGuardError (err_env, err) -> raise_err err_env i err
      done
  in
  sorts_opt

let check_fix ?evars env (_, (names, _, _ as recdef) as fix) =
  let sorts_opts = check_fix_pre_sorts ?evars env fix in
  let raise_err = raise_fix_guard_err_fn env recdef names in
  let elim_to = eliminates_to (Environ.qualities env) in
  Option.iter (List.iteri (fun i (ind_sort, out_sort) ->
      if not (is_allowed_fixpoint elim_to ind_sort out_sort) then
        raise_err env i @@ FixpointOnNonEliminable (ind_sort, out_sort)
    )) sorts_opts

(************************************************************************)
(* Co-fixpoints. *)

exception CoFixGuardError of env * cofix_guard_error

let rec codomain_is_coind ?evars env c =
  let b = whd_all ?evars env c in
  match kind b with
    | Prod (x,a,b) ->
        codomain_is_coind ?evars (push_rel (LocalAssum (x,a)) env) b
    | _ ->
        (try find_coinductive ?evars env b
        with Not_found ->
          raise (CoFixGuardError (env, CodomainNotInductiveType b)))

let check_one_cofix ?evars env nbfix def vlra =
  let rec check_rec_call env alreadygrd n tree t =
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
            let mI = inductive_of_constructor cstr_kn in
            let (mib,_mip) = lookup_mind_specif env mI in
            let realargs = List.skipn mib.mind_nparams args in
            let rec process_args_of_constr j = function
            | [] -> ()
            | t :: lr ->
              let rar = WfPaths.dest_subterm tree (i - 1) j in
              let () =
                if WfPaths.is_norec rar then
                  if noccur_with_meta n nbfix t then ()
                  else
                    raise (CoFixGuardError (env, RecCallInNonRecArgOfConstructor t))
                else
                  check_rec_call env true n rar t
              in
              process_args_of_constr (j + 1) lr
            in
            process_args_of_constr 0 realargs

        | Lambda (x,a,b) ->
            let () = assert (List.is_empty args) in
            if noccur_with_meta n nbfix a then
              let env' = push_rel (LocalAssum (x,a)) env in
              check_rec_call env' alreadygrd (n+1) tree b
            else
              raise (CoFixGuardError (env,RecCallInTypeOfAbstraction a))

        | CoFix (i, (_, varit, vdefs as recdef)) ->
          let () = if not (List.for_all (noccur_with_meta n nbfix) args) then
            raise (CoFixGuardError (env, UnguardedRecursiveCall c))
          in
          let () = if not (Array.for_all (noccur_with_meta n nbfix) varit) then
            raise (CoFixGuardError (env, RecCallInTypeOfDef c))
          in
          let nbfixinner = Array.length vdefs in
          let env' = push_rec_types recdef env in
          let () = if not (Array.for_all_i (fun j c -> Int.equal i j || noccur_with_meta (n + nbfixinner) nbfix c) 0 vdefs) then
            raise (CoFixGuardError (env, RecCallInNonMainMutual c))
          in
          check_rec_call env' alreadygrd (n + nbfixinner) tree vdefs.(i)

        | Case (ci, u, pms, (p, _), _, tm, brs) -> (* iv ignored: just a cache *)
          let specif = lookup_mind_specif env ci.ci_ind in
          let pctx = expand_arity specif (ci.ci_ind, u) pms (fst p) in
          let penv = Environ.push_rel_context pctx env in
          let pctxlen = List.length pctx in
          let tree = match filter_predicate_tree ?evars pctxlen penv (snd p) tree with
            | Some tree -> tree
            | None -> raise (CoFixGuardError (env, ReturnPredicateNotCoInductive c))
          in
          let () = if not (noccur_with_meta n nbfix tm) then
            raise (CoFixGuardError (env, RecCallInCaseArg c))
          in
          let () = if not (noccur_with_meta (n + List.length pctx) nbfix (snd p)) then
            raise (CoFixGuardError (env, RecCallInCasePred c))
          in
          let () = if not (List.for_all (noccur_with_meta n nbfix) args) then
            raise (CoFixGuardError (env, RecCallInCaseFun c))
          in
          let brctxs = expand_branch_contexts specif u pms brs in
          Array.iter2 (fun brctx (_, br) ->
            let env = Environ.push_rel_context brctx env in
            check_rec_call env alreadygrd (n + List.length brctx) tree br)
            brctxs brs

        | Meta _ -> assert false
        | Evar _ ->
            List.iter (check_rec_call env alreadygrd n tree) args
        | Rel _ | Var _ | Sort _ | Cast _ | Prod _ | LetIn _ | App _ | Const _
          | Ind _ | Fix _ | Proj _ | Int _ | Float _ | String _
          | Array _ ->
           raise (CoFixGuardError (env,NotGuardedForm t)) in

  check_rec_call env false 1 vlra def

(* The  function which checks that the whole block of definitions
   satisfies the guarded condition *)

let check_cofix ?evars env (_bodynum,(names,types,bodies as recdef)) =
  let flags = Environ.typing_flags env in
  if flags.check_guarded then
    let nbfix = Array.length bodies in
    for i = 0 to nbfix-1 do
      let fixenv = push_rec_types recdef env in
      try
        let ((mind, _),_) = codomain_is_coind ?evars env types.(i) in
        let vlra = WfPaths.lookup_subterms env mind in
        check_one_cofix ?evars fixenv nbfix bodies.(i) vlra
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

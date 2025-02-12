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
open Term
open Constr
open Context
open Environ
open EConstr
open Vars
open Reductionops
open Inductive
open Inductiveops
open Arguments_renaming
open Pretype_errors
open Context.Rel.Declaration

module GR = Names.GlobRef

let fresh_template_context env0 sigma ind (mib, mip as spec) args =
  let templ = match mib.Declarations.mind_template with
  | None -> assert false
  | Some t -> Array.of_list t.template_param_arguments
  in
  let ctx = List.rev (EConstr.of_rel_context mib.Declarations.mind_params_ctxt) in
  let rec freshen i env sigma accu sorts = function
  | [] -> sigma, List.rev sorts
  | LocalAssum (na, t) as decl :: ctx ->
    let sigma, decl, s =
      match templ.(i) with
      | Some _ ->
        let decls, s0 = Reductionops.dest_arity env sigma t in
        let sigma, s =
          if i < Array.length args then match Reductionops.sort_of_arity env sigma args.(i).uj_type with
          | s -> sigma, s
          | exception Reduction.NotArity -> Evd.new_sort_variable Evd.univ_flexible sigma
          else sigma, s0
        in
        let t = EConstr.it_mkProd_or_LetIn (mkSort s) decls in
        let s ~default = match ESorts.kind sigma s with
        | Sorts.SProp ->
          let indty = EConstr.of_constr @@
            Inductive.type_of_inductive (spec, UVars.Instance.empty)
          in
          error_cant_apply_bad_type env0 sigma
            (i+1, mkSort (ESorts.make default), args.(i).uj_type)
            (make_judge (mkIndU (ind, EInstance.empty)) indty)
            args
        | Sorts.Prop -> TemplateProp
        | Sorts.Set -> TemplateUniv Univ.Universe.type0
        | Sorts.Type u | Sorts.QSort (_, u) -> TemplateUniv u
        in
        sigma, LocalAssum (na, t), s
      | None ->
        sigma, decl, (fun ~default -> assert false)
    in
    freshen (i + 1) (push_rel decl env) sigma (decl :: accu) (s :: sorts) ctx
  | LocalDef (na, b, t) as decl :: ctx ->
    freshen i (push_rel decl env) sigma (decl :: accu) sorts ctx
  in
  freshen 0 env0 sigma [] [] ctx

let get_template_parameters env sigma ind args =
  let spec = Inductive.lookup_mind_specif env ind in
  fresh_template_context env sigma ind spec args

let type_judgment env sigma j =
  match EConstr.kind sigma (whd_all env sigma j.uj_type) with
    | Sort s -> sigma, {utj_val = j.uj_val; utj_type = s }
    | Evar ev ->
        let (sigma,s) = Evardefine.define_evar_as_sort env sigma ev in
        sigma, { utj_val = j.uj_val; utj_type = s }
    | _ -> error_not_a_type env sigma j

let assumption_of_judgment env sigma j =
  try
    let sigma, j = type_judgment env sigma j in
    sigma, j.utj_val
  with Type_errors.TypeError _ | PretypeError _ ->
    error_assumption env sigma j

let judge_of_apply_core env sigma funj argjv =
  let rec apply_rec sigma n subs typ = function
  | [] ->
    let typ = Vars.esubst Vars.lift_substituend subs typ in
    sigma, { uj_val  = mkApp (j_val funj, Array.map j_val argjv);
             uj_type = typ }
  | hj::restjl ->
    let sigma, c1, subs, c2 = match EConstr.kind sigma typ with
    | Prod (_, c1, c2) ->
      (* Fast path *)
      let c1 = Vars.esubst Vars.lift_substituend subs c1 in
      let subs = Esubst.subs_cons (Vars.make_substituend hj.uj_val) subs in
      sigma, c1, subs, c2
    | _ ->
      let typ = Vars.esubst Vars.lift_substituend subs typ in
      let subs = Esubst.subs_cons (Vars.make_substituend hj.uj_val) (Esubst.subs_id 0) in
      match EConstr.kind sigma (whd_all env sigma typ) with
      | Prod (_, c1, c2) -> sigma, c1, subs, c2
      | Evar ev ->
        let (sigma,t) = Evardefine.define_evar_as_product env sigma ev in
        let (_, c1, c2) = destProd sigma t in
        sigma, c1, subs, c2
      | _ ->
        let seen, rest = Array.chop (n-1) argjv in
        error_cant_apply_not_functional env sigma
          (make_judge (mkApp (funj.uj_val, Array.map j_val seen)) typ)
          rest
    in
    match Evarconv.unify_leq_delay env sigma hj.uj_type c1 with
    | sigma ->
      apply_rec sigma (n+1) subs c2 restjl
    | exception Evarconv.UnableToUnify (sigma,error) ->
      error_cant_apply_bad_type env sigma ~error (n, c1, hj.uj_type) funj argjv
  in
  apply_rec sigma 1 (Esubst.subs_id 0) funj.uj_type (Array.to_list argjv)

let judge_of_applied ~check env sigma funj argjv =
  let sigma =
    if check then
      let (sigma, _) = judge_of_apply_core env sigma funj argjv in
      sigma
    else sigma
  in
  let typ = hnf_prod_appvect env sigma (j_type funj) (Array.map j_val argjv) in
  sigma, { uj_val = (mkApp (j_val funj, Array.map j_val argjv)); uj_type = typ }

let judge_of_applied_inductive_knowing_parameters ~check env sigma (ind, u) argjv =
  let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
  let () = if check then Reductionops.check_hyps_inclusion env sigma (GR.IndRef ind) mib.mind_hyps in
  let sigma, paramstyp = fresh_template_context env sigma ind specif argjv in
  let u0 = EInstance.kind sigma u in
  let ty, csts = Inductive.type_of_inductive_knowing_parameters (specif, u0) paramstyp in
  let sigma = Evd.add_constraints sigma csts in
  let funj = { uj_val = mkIndU (ind, u); uj_type = EConstr.of_constr (rename_type ty (GR.IndRef ind)) } in
  judge_of_applied ~check env sigma funj argjv

let judge_of_applied_constructor_knowing_parameters ~check env sigma ((ind, _ as cstr), u) argjv =
  let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
  let () = if check then Reductionops.check_hyps_inclusion env sigma (GR.IndRef ind) mib.mind_hyps in
  let sigma, paramstyp = fresh_template_context env sigma ind specif argjv in
  let u0 = EInstance.kind sigma u in
  let ty, csts = Inductive.type_of_constructor_knowing_parameters (cstr, u0) specif paramstyp in
  let sigma = Evd.add_constraints sigma csts in
  let funj = { uj_val = mkConstructU (cstr, u); uj_type = (EConstr.of_constr (rename_type ty (GR.ConstructRef cstr))) } in
  judge_of_applied ~check env sigma funj argjv

let judge_of_apply env sigma fj args =
  match EConstr.kind sigma fj.uj_val with
  | Ind (ind, u) when EInstance.is_empty u && Environ.template_polymorphic_ind ind env ->
    judge_of_applied_inductive_knowing_parameters ~check:true env sigma (ind, u) args
  | Construct (cstr, u) when EInstance.is_empty u && Environ.template_polymorphic_ind (fst cstr) env ->
    judge_of_applied_constructor_knowing_parameters ~check:true env sigma (cstr, u) args
  | _ ->
    (* No template polymorphism *)
    judge_of_apply_core env sigma fj args

let checked_appvect env sigma f args =
  let mk c = Retyping.get_judgment_of env sigma c in
  let sigma, j = judge_of_apply env sigma (mk f) (Array.map mk args) in
  sigma, j.uj_val

let () = Hook.set Evarsolve.checked_appvect_hook checked_appvect

let checked_applist env sigma f args = checked_appvect env sigma f (Array.of_list args)

let check_branch_types env sigma (ind,u) cj (lfj,explft) =
  if not (Int.equal (Array.length lfj) (Array.length explft)) then
    error_number_branches env sigma cj (Array.length explft);
  Array.fold_left2_i (fun i sigma lfj explft ->
      match Evarconv.unify_leq_delay env sigma lfj.uj_type explft with
      | sigma -> sigma
      | exception Evarconv.UnableToUnify _ ->
        error_ill_formed_branch env sigma cj.uj_val ((ind,i+1),u) lfj.uj_type explft)
    sigma lfj explft

let is_correct_arity env sigma c pj ind specif params =
  let arsign = make_arity_signature env sigma true (make_ind_family (ind,params)) in
  let error rtnsort = Pretype_errors.error_elim_arity env sigma ind c rtnsort in
  let rec srec env sigma pt ar =
    let pt' = whd_all env sigma pt in
    match EConstr.kind sigma pt', ar with
    | Prod (na1,a1,t), (LocalAssum (_,a1'))::ar' ->
      begin match Evarconv.unify_leq_delay env sigma a1 a1' with
        | exception Evarconv.UnableToUnify _ -> error None
        | sigma ->
          srec (push_rel (LocalAssum (na1,a1)) env) sigma t ar'
      end
    | Sort s, [] ->
      begin match is_squashed sigma (specif, snd ind) with
      | None -> sigma, s
      | Some squash ->
        let sigma =
          try squash_elim_sort sigma squash s
          with UGraph.UniverseInconsistency _ -> error (Some s)
        in
        sigma, s
      end
    | Evar (ev,_), [] ->
        let sigma, s = Evd.fresh_sort_in_family sigma (elim_sort specif) in
        let sigma = Evd.define ev (mkSort s) sigma in
        sigma, s
    | _, (LocalDef _ as d)::ar' ->
        srec (push_rel d env) sigma (lift 1 pt') ar'
    | _ ->
        error None
  in
  srec env sigma pj.uj_type (List.rev arsign)

let lambda_applist_decls sigma n c l =
  let rec app n subst t l =
    if Int.equal n 0 then
      if l == [] then substl subst t
      else anomaly (Pp.str "Not enough arguments.")
    else match EConstr.kind sigma t, l with
    | Lambda(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (substl subst b::subst) c l
    | _ -> anomaly (Pp.str "Not enough lambda/let's.") in
  app n [] c l

let type_case_branches env sigma (ind,largs) specif pj c =
  let nparams = inductive_params specif in
  let (params,realargs) = List.chop nparams largs in
  let p = pj.uj_val in
  let sigma, ps = is_correct_arity env sigma c pj ind specif params in
  let ind = on_snd EConstr.Unsafe.to_instance ind in
  let params = List.map EConstr.Unsafe.to_constr params in
  let lc = build_branches_type ind specif params (EConstr.to_constr ~abort_on_undefined_evars:false sigma p) in
  let lc = Array.map EConstr.of_constr lc in
  let n = (snd specif).Declarations.mind_nrealdecls in
  let ty = whd_betaiota env sigma (lambda_applist_decls sigma (n+1) p (realargs@[c])) in
  sigma, (lc, ty, ESorts.relevance_of_sort ps)

let unify_relevance sigma r1 r2 =
  match ERelevance.kind sigma r1, ERelevance.kind sigma r2 with
  | Relevant, Relevant | Irrelevant, Irrelevant -> Some sigma
  | Relevant, Irrelevant | Irrelevant, Relevant -> None
  | Irrelevant, RelevanceVar q | RelevanceVar q, Irrelevant ->
    let sigma =
      Evd.add_quconstraints sigma
        (Sorts.QConstraints.singleton (Sorts.Quality.qsprop, Equal, QVar q),
         Univ.Constraints.empty)
    in
    Some sigma
  | Relevant, RelevanceVar q | RelevanceVar q, Relevant ->
    let sigma =
      Evd.add_quconstraints sigma
        (Sorts.QConstraints.singleton (Sorts.Quality.qprop, Leq, QVar q),
         Univ.Constraints.empty)
    in
    Some sigma
  | RelevanceVar q1, RelevanceVar q2 ->
    if Sorts.QVar.equal q1 q2 then Some sigma
    else
      let sigma =
        Evd.add_quconstraints sigma
          (Sorts.QConstraints.singleton (QVar q1, Equal, QVar q2),
           Univ.Constraints.empty)
      in
      Some sigma

let judge_of_case env sigma case ci (pj,rp) iv cj lfj =
  let ((ind, u), spec) =
    try find_mrectype env sigma cj.uj_type
    with Not_found -> error_case_not_inductive env sigma cj in
  let specif = lookup_mind_specif env ind in
  let () = if Inductive.is_private specif then Type_errors.error_case_on_private_ind env ind in
  let indspec = ((ind, u), spec) in
  let sigma, (bty,rslty,rci) = type_case_branches env sigma indspec specif pj cj.uj_val in
  (* should we have evar map aware should_invert_case? *)
  let sigma, rp =
    match unify_relevance sigma rp rci with
    | None ->
      raise_type_error (env,sigma,Type_errors.BadCaseRelevance (rp, mkCase case))
    | Some sigma -> sigma, rci
  in
  let ind = on_snd (EInstance.kind sigma) (fst indspec) in
  let () = check_case_info env ind ci in
  let sigma = check_branch_types env sigma ind cj (lfj,bty) in
  let () = if (match iv with | NoInvert -> false | CaseInvert _ -> true)
              != Typeops.should_invert_case env (ERelevance.kind sigma rp) ci
    then Type_errors.error_bad_invert env
  in
  sigma, { uj_val  = mkCase case;
           uj_type = rslty }

let check_type_fixpoint ?loc env sigma lna lar vdefj =
  let lt = Array.length vdefj in
  assert (Int.equal (Array.length lar) lt);
  Array.fold_left2_i (fun i sigma defj ar ->
      match Evarconv.unify_leq_delay env sigma defj.uj_type (lift lt ar) with
      | sigma -> sigma
      | exception Evarconv.UnableToUnify _ ->
        error_ill_typed_rec_body ?loc env sigma
          i lna vdefj lar)
    sigma vdefj lar


(* FIXME: might depend on the level of actual parameters!*)
let check_allowed_sort env sigma ind c p =
  let specif = lookup_mind_specif env (fst ind) in
  let pj = Retyping.get_judgment_of env sigma p in
  let _, s = whd_decompose_prod env sigma pj.uj_type in
  let sort =  match EConstr.kind sigma s with
    | Sort s -> s
    | _ -> error_elim_arity env sigma ind c None
  in
  match Inductiveops.make_allowed_elimination env sigma (specif, (snd ind)) sort with
  | Some sigma -> sigma, ESorts.relevance_of_sort sort
  | None ->
    error_elim_arity env sigma ind c (Some sort)

let check_actual_type env sigma cj t =
  try Evarconv.unify_leq_delay env sigma cj.uj_type t
  with Evarconv.UnableToUnify (sigma,e) -> error_actual_type env sigma cj t e

let judge_of_cast env sigma cj k tj =
  let expected_type = tj.utj_val in
  let sigma = check_actual_type env sigma cj expected_type in
  sigma, { uj_val = mkCast (cj.uj_val, k, expected_type);
           uj_type = expected_type }

let check_fix env sigma pfix =
  let inj c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  let (idx, (ids, cs, ts)) = pfix in
  let ids = Array.map EConstr.Unsafe.to_binder_annot ids in
  check_fix ~evars:(Evd.evar_handler sigma) env (idx, (ids, Array.map inj cs, Array.map inj ts))

let check_cofix env sigma pcofix =
  let inj c = EConstr.to_constr sigma c in
  let (idx, (ids, cs, ts)) = pcofix in
  let ids = Array.map EConstr.Unsafe.to_binder_annot ids in
  check_cofix ~evars:(Evd.evar_handler sigma) env (idx, (ids, Array.map inj cs, Array.map inj ts))

(* The typing machine with universes and existential variables. *)

let judge_of_sprop =
  { uj_val = EConstr.mkSProp;
    uj_type = EConstr.type1 }

let judge_of_prop =
  { uj_val = EConstr.mkProp;
    uj_type = EConstr.mkSort (ESorts.type1) }

let judge_of_set =
  { uj_val = EConstr.mkSet;
    uj_type = EConstr.mkSort (ESorts.type1) }

let judge_of_type u =
  let uu = Univ.Universe.super u in
    { uj_val = EConstr.mkType u;
      uj_type = EConstr.mkType uu }

let judge_of_sort s =
  let open Sorts in
  let u = match s with
  | Prop | SProp | Set -> Univ.Universe.type1
  | Type u | QSort (_, u) -> Univ.Universe.super u
  in
  { uj_val = EConstr.mkSort (ESorts.make s); uj_type = EConstr.mkType u }

let type_of_relative env n =
  EConstr.of_constr (Typeops.type_of_relative env n)

let judge_of_relative env v =
  { uj_val = mkRel v; uj_type = type_of_relative env v }

let type_of_variable env id =
  EConstr.of_constr (Typeops.type_of_variable env id)

let judge_of_variable env id =
  { uj_val = mkVar id; uj_type = type_of_variable env id }

let judge_of_projection env sigma p cj =
  let pr, pty = lookup_projection p env in
  let (ind,u), args =
    try find_mrectype env sigma cj.uj_type
    with Not_found -> error_case_not_inductive env sigma cj
  in
  let pr = Vars.subst_instance_relevance u (ERelevance.make pr) in
  let ty = Vars.subst_instance_constr u (EConstr.of_constr pty) in
  let ty = substl (cj.uj_val :: List.rev args) ty in
  {uj_val = EConstr.mkProj (p,pr,cj.uj_val);
   uj_type = ty}

let judge_of_abstraction env sigma name var j =
  let r = ESorts.relevance_of_sort var.utj_type in
  { uj_val = mkLambda (make_annot name r, var.utj_val, j.uj_val);
    uj_type = mkProd (make_annot name r, var.utj_val, j.uj_type) }

let judge_of_product env sigma name t1 t2 =
  let s1 = ESorts.kind sigma t1.utj_type in
  let s2 = ESorts.kind sigma t2.utj_type in
  let r = ERelevance.make @@ Sorts.relevance_of_sort s1 in
  let s = ESorts.make (Typeops.sort_of_product env s1 s2) in
  { uj_val = mkProd (make_annot name r, t1.utj_val, t2.utj_val);
    uj_type = mkSort s }

let judge_of_letin env sigma name defj typj j =
  let r = ESorts.relevance_of_sort typj.utj_type in
  { uj_val = mkLetIn (make_annot name r, defj.uj_val, typj.utj_val, j.uj_val) ;
    uj_type = subst1 defj.uj_val j.uj_type }

let type_of_constant env sigma (c,u) =
  let open Declarations in
  let cb = Environ.lookup_constant c env in
  let () = Reductionops.check_hyps_inclusion env sigma (GR.ConstRef c) cb.const_hyps in
  let u = EInstance.kind sigma u in
  let ty, csts = Environ.constant_type env (c,u) in
  let sigma = Evd.add_constraints sigma csts in
  sigma, (EConstr.of_constr (rename_type ty (GR.ConstRef c)))

let type_of_inductive env sigma (ind,u) =
  let open Declarations in
  let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
  let () = Reductionops.check_hyps_inclusion env sigma (GR.IndRef ind) mib.mind_hyps in
  let u = EInstance.kind sigma u in
  let ty, csts = Inductive.constrained_type_of_inductive (specif,u) in
  let sigma = Evd.add_constraints sigma csts in
  sigma, (EConstr.of_constr (rename_type ty (GR.IndRef ind)))

let type_of_constructor env sigma ((ind,_ as ctor),u) =
  let open Declarations in
  let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
  let () = Reductionops.check_hyps_inclusion env sigma (GR.IndRef ind) mib.mind_hyps in
  let u = EInstance.kind sigma u in
  let ty, csts = Inductive.constrained_type_of_constructor (ctor,u) specif in
  let sigma = Evd.add_constraints sigma csts in
  sigma, (EConstr.of_constr (rename_type ty (GR.ConstructRef ctor)))

let type_of_int env = EConstr.of_constr (Typeops.type_of_int env)

let judge_of_int env v =
  { uj_val = mkInt v; uj_type = type_of_int env }

let type_of_float env = EConstr.of_constr (Typeops.type_of_float env)

let judge_of_float env v =
  { uj_val = mkFloat v; uj_type = type_of_float env }

let type_of_string env = EConstr.of_constr (Typeops.type_of_string env)

let judge_of_string env v =
  { uj_val = mkString v; uj_type = type_of_string env }

let judge_of_array env sigma u tj defj tyj =
  let ulev = match UVars.Instance.to_array u with
    | [||], [|u|] -> u
    | _ -> assert false
  in
  let sigma = Evd.set_leq_sort sigma tyj.utj_type
      (ESorts.make (Sorts.sort_of_univ (Univ.Universe.make ulev)))
  in
  let check_one sigma j = check_actual_type env sigma j tyj.utj_val in
  let sigma = check_one sigma defj in
  let sigma = Array.fold_left check_one sigma tj in
  let arr = EConstr.of_constr @@ Typeops.type_of_array env u in
  let j = make_judge (mkArray(EInstance.make u, Array.map j_val tj, defj.uj_val, tyj.utj_val))
      (mkApp (arr, [|tyj.utj_val|]))
  in
  sigma, j

type ('constr,'types,'r) bad_relevance =
| BadRelevanceBinder of 'r * ('constr,'types,'r) Context.Rel.Declaration.pt
| BadRelevanceCase of 'r * 'constr

let bad_relevance_warning =
  CWarnings.create_warning ~name:"bad-relevance" ~default:CWarnings.AsError ()

let bad_relevance_msg = CWarnings.create_msg bad_relevance_warning ()
(* no need for default printer, pretyping is always linked with himsg in practice *)

let warn_bad_relevance_binder ?loc env sigma rlv bnd =
  match CWarnings.warning_status bad_relevance_warning with
| CWarnings.Disabled | CWarnings.Enabled ->
  CWarnings.warn bad_relevance_msg ?loc (env,sigma,BadRelevanceBinder (rlv, bnd))
| CWarnings.AsError ->
  Loc.raise ?loc (PretypeError (env, sigma, TypingError (Type_errors.BadBinderRelevance (rlv, bnd))))

type relevance_preunify =
  | Trivial
  | Impossible
  | DummySort of ESorts.t

let check_binder_relevance env sigma s decl =
  let preunify = match ESorts.kind sigma s, ERelevance.kind sigma (get_relevance decl) with
    | (Prop | Set | Type _), Relevant -> Trivial
    | (Prop | Set | Type _), Irrelevant -> Impossible
    | SProp, Irrelevant -> Trivial
    | SProp, Relevant -> Impossible
    | QSort (_,l), RelevanceVar q' -> DummySort (ESorts.make (Sorts.qsort q' l))
    | (SProp | Prop | Set), RelevanceVar q ->
      DummySort (ESorts.make (Sorts.qsort q Univ.Universe.type0))
    | Type l, RelevanceVar q -> DummySort (ESorts.make (Sorts.qsort q l))
    | QSort (_,l), Relevant -> DummySort (ESorts.make (Sorts.sort_of_univ l))
    | QSort _, Irrelevant -> DummySort ESorts.sprop
  in
  let unify = match preunify with
    | Trivial -> Some sigma
    | Impossible -> None
    | DummySort s' ->
      match Evd.set_leq_sort sigma s s' with
      | sigma -> Some sigma
      | exception UGraph.UniverseInconsistency _ -> None
  in
  match unify with
  | Some sigma -> sigma, decl
  | None ->
    (* TODO always anomaly *)
    let rs = ESorts.relevance_of_sort s in
    let () =
      if not (UGraph.type_in_type (Evd.universes sigma))
      then warn_bad_relevance_binder env sigma rs decl
    in
    sigma, set_annot { (get_annot decl) with binder_relevance = rs } decl

(* cstr must be in n.f. w.r.t. evars and execute returns a judgement
   where both the term and type are in n.f. *)
let rec execute env sigma cstr =
  let cstr = whd_evar sigma cstr in
  match EConstr.kind sigma cstr with
    | Meta n -> assert false (* Typing should always be performed on meta-free terms *)

    | Evar ev ->
        let ty = EConstr.existential_type sigma ev in
        let sigma, jty = execute env sigma ty in
        let sigma, jty = assumption_of_judgment env sigma jty in
        sigma, { uj_val = cstr; uj_type = jty }

    | Rel n ->
        sigma, judge_of_relative env n

    | Var id ->
        sigma, judge_of_variable env id

    | Const c ->
        let sigma, ty = type_of_constant env sigma c in
        sigma, make_judge cstr ty

    | Ind ind ->
        let sigma, ty = type_of_inductive env sigma ind in
        sigma, make_judge cstr ty

    | Construct ctor ->
        let sigma, ty = type_of_constructor env sigma ctor in
        sigma, make_judge cstr ty

    | Case (ci, u, pms, p, iv, c, lf) ->
        let case = (ci, u, pms, p, iv, c, lf) in
        let (ci, (p,rp), iv, c, lf) = EConstr.expand_case env sigma case in
        let sigma, cj = execute env sigma c in
        let sigma, pj = execute env sigma p in
        let sigma, lfj = execute_array env sigma lf in
        let sigma = match iv with
          | NoInvert -> sigma
          | CaseInvert {indices} ->
            let args = Array.append pms indices in
            let t = mkApp (mkIndU (ci.ci_ind,u), args) in
            let sigma, tj = execute env sigma t in
            let sigma, tj = type_judgment env sigma tj in
            let sigma = check_actual_type env sigma cj tj.utj_val in
            sigma
        in
        judge_of_case env sigma case ci (pj,rp) iv cj lfj

    | Fix ((vn,i as vni),recdef) ->
        let sigma, (_,tys,_ as recdef') = execute_recdef env sigma recdef in
        let fix = (vni,recdef') in
        check_fix env sigma fix;
        sigma, make_judge (mkFix fix) tys.(i)

    | CoFix (i,recdef) ->
        let sigma, (_,tys,_ as recdef') = execute_recdef env sigma recdef in
        let cofix = (i,recdef') in
        check_cofix env sigma cofix;
        sigma, make_judge (mkCoFix cofix) tys.(i)

    | Sort s ->
      begin match ESorts.kind sigma s with
        | SProp ->
          if Environ.sprop_allowed env then sigma, judge_of_sprop
          else error_disallowed_sprop env sigma
        | Prop -> sigma, judge_of_prop
        | Set -> sigma, judge_of_set
        | Type u -> sigma, judge_of_type u
        | QSort _ as s -> sigma, judge_of_sort s
      end

    | Proj (p, _, c) ->
      let sigma, cj = execute env sigma c in
      sigma, judge_of_projection env sigma p cj

    | App (f,args) ->
        let sigma, fj = execute env sigma f in
        let sigma, jl = execute_array env sigma args in
        judge_of_apply env sigma fj jl

    | Lambda (name,c1,c2) ->
        let sigma, j = execute env sigma c1 in
        let sigma, var = type_judgment env sigma j in
        let sigma, decl = check_binder_relevance env sigma var.utj_type (LocalAssum (name, var.utj_val)) in
        let env1 = push_rel decl env in
        let sigma, j' = execute env1 sigma c2 in
        sigma, judge_of_abstraction env1 sigma name.binder_name var j'

    | Prod (name,c1,c2) ->
        let sigma, j = execute env sigma c1 in
        let sigma, varj = type_judgment env sigma j in
        let sigma, decl = check_binder_relevance env sigma varj.utj_type (LocalAssum (name, varj.utj_val)) in
        let env1 = push_rel decl env in
        let sigma, j' = execute env1 sigma c2 in
        let sigma, varj' = type_judgment env1 sigma j' in
        sigma, judge_of_product env sigma name.binder_name varj varj'

     | LetIn (name,c1,c2,c3) ->
        let sigma, j1 = execute env sigma c1 in
        let sigma, j2 = execute env sigma c2 in
        let sigma, j2 = type_judgment env sigma j2 in
        let sigma, _ =  judge_of_cast env sigma j1 DEFAULTcast j2 in
        let sigma, decl = check_binder_relevance env sigma j2.utj_type (LocalDef (name, j1.uj_val, j2.utj_val)) in
        let env1 = push_rel decl env in
        let sigma, j3 = execute env1 sigma c3 in
        sigma, judge_of_letin env sigma name.binder_name j1 j2 j3

    | Cast (c,k,t) ->
        let sigma, cj = execute env sigma c in
        let sigma, tj = execute env sigma t in
        let sigma, tj = type_judgment env sigma tj in
        judge_of_cast env sigma cj k tj

    | Int i ->
        sigma, judge_of_int env i

    | Float f ->
        sigma, judge_of_float env f

    | String s ->
        sigma, judge_of_string env s

    | Array(u,t,def,ty) ->
      let sigma, tyj = execute env sigma ty in
      let sigma, tyj = type_judgment env sigma tyj in
      let sigma, defj = execute env sigma def in
      let sigma, tj = execute_array env sigma t in
      judge_of_array env sigma (EInstance.kind sigma u) tj defj tyj

and execute_recdef env sigma (names,lar,vdef) =
  let sigma, larj = execute_array env sigma lar in
  let sigma, lara = Array.fold_left_map (assumption_of_judgment env) sigma larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let sigma, vdefj = execute_array env1 sigma vdef in
  let vdefv = Array.map j_val vdefj in
  let sigma = check_type_fixpoint env1 sigma names lara vdefj in
  sigma, (names,lara,vdefv)

and execute_array env = Array.fold_left_map (execute env)

let check env sigma c t =
  let sigma, j = execute env sigma c in
  check_actual_type env sigma j t

(* Sort of a type *)

let sort_of env sigma c =
  let sigma, j = execute env sigma c in
  let sigma, a = type_judgment env sigma j in
  sigma, a.utj_type

(* Try to solve the existential variables by typing *)

let type_of ?(refresh=false) env sigma c =
  let sigma, j = execute env sigma c in
  (* side-effect on evdref *)
    if refresh then
      Evarsolve.refresh_universes ~onlyalg:true (Some false) env sigma j.uj_type
    else sigma, j.uj_type

let solve_evars env sigma c =
  let sigma, j = execute env sigma c in
  (* side-effect on evdref *)
  sigma, nf_evar sigma j.uj_val

let _ = Evarconv.set_solve_evars (fun env sigma c -> solve_evars env sigma c)

type change_kind = Same | Changed of {bodyonly : bool Lazy.t }

let merge_changes a b = match a,b with
  | Same, v | v, Same -> v
  | Changed {bodyonly=a}, Changed {bodyonly=b} ->
    Changed {bodyonly = lazy (Lazy.force a && Lazy.force b)}

let unchanged = function
  | Same -> true
  | Changed _ -> false

let bodyonly = function
  | Same -> true
  | Changed {bodyonly} -> Lazy.force bodyonly

let judge_of_apply_against env sigma changedf funj argjv =
  let rec apply_rec sigma changedf n subs typ = function
  | [] ->
    let typ = Vars.esubst Vars.lift_substituend subs typ in
    sigma,
    { uj_val  = mkApp (j_val funj, Array.map (fun (_,j) -> j_val j) argjv);
      uj_type = typ }
  | (changedh,hj)::restjl ->
    let sigma, c1, subs, c2 = match EConstr.kind sigma typ with
    | Prod (_, c1, c2) ->
      (* Fast path *)
      let c1 = Vars.esubst Vars.lift_substituend subs c1 in
      let subs = Esubst.subs_cons (Vars.make_substituend hj.uj_val) subs in
      sigma, c1, subs, c2
    | _ ->
      let typ = Vars.esubst Vars.lift_substituend subs typ in
      let subs = Esubst.subs_cons (Vars.make_substituend hj.uj_val) (Esubst.subs_id 0) in
      match EConstr.kind sigma (whd_all env sigma typ) with
      | Prod (_, c1, c2) -> sigma, c1, subs, c2
      | Evar ev ->
        let (sigma,t) = Evardefine.define_evar_as_product env sigma ev in
        let (_, c1, c2) = destProd sigma t in
        sigma, c1, subs, c2
      | _ ->
        error_cant_apply_not_functional env sigma funj (Array.map snd argjv)
    in
    if bodyonly changedf then begin match changedh with
      | Same -> apply_rec sigma changedf (n+1) subs c2 restjl
      | Changed {bodyonly=lazy true} ->
        (* TODO if non dependent product then changedf else bodyonly = false *)
        apply_rec sigma (Changed {bodyonly=lazy false}) (n+1) subs c2 restjl
      | Changed {bodyonly=lazy false} ->
        match Evarconv.unify_leq_delay env sigma hj.uj_type c1 with
        | sigma ->
          apply_rec sigma (Changed {bodyonly=lazy false}) (n+1) subs c2 restjl
        | exception Evarconv.UnableToUnify (sigma,error) ->
          error_cant_apply_bad_type env sigma ~error (n, c1, hj.uj_type) funj (Array.map snd argjv)
    end
    else
      match Evarconv.unify_leq_delay env sigma hj.uj_type c1 with
      | sigma ->
        apply_rec sigma changedf (n+1) subs c2 restjl
      | exception Evarconv.UnableToUnify (sigma,error) ->
        error_cant_apply_bad_type env sigma ~error (n, c1, hj.uj_type) funj (Array.map snd argjv)
  in
  apply_rec sigma changedf 1 (Esubst.subs_id 0) funj.uj_type (Array.to_list argjv)

(* Assuming "env |- good : some type", infer "env |- c : other type" *)
let rec recheck_against env sigma good c =
  if EConstr.eq_constr sigma good c then sigma, Same, make_judge c (Retyping.get_type_of env sigma c)
  else
    let assume_unchanged_type sigma =
      let gt = Retyping.get_type_of env sigma good in
      sigma, Changed {bodyonly=Lazy.from_val true}, make_judge c gt
    in
    let maybe_changed (sigma, j) =
      let bodyonly = lazy (EConstr.eq_constr sigma (Retyping.get_type_of env sigma good) j.uj_type) in
      let change = Changed {bodyonly} in
      sigma, change, j
    in
    let default () = maybe_changed (execute env sigma c) in
    match kind sigma good, kind sigma c with
    (* No subterms *)
    | _, (Meta _ | Rel _ | Var _ | Const _ | Ind _ | Construct _
         | Sort _ | Int _ | Float _ | String _) ->
      default ()

    (* Evar (todo deal with Evar differently??? execute recurses on its type)
       others: too annoying for now *)
    | _, (Evar _ | Fix _ | CoFix _ | LetIn _ | Array _) ->
     default ()

    | Case (gci, gu, gpms, gp, giv, gc, glf),
      Case (ci, u, pms, p, iv, c, lf) ->
      let (gci, (gp,_), giv, gc, glf) = EConstr.expand_case env sigma (gci, gu, gpms, gp, giv, gc, glf) in
      let case = (ci, u, pms, p, iv, c, lf) in
      let (ci, (p,rp), iv, c, lf) = EConstr.expand_case env sigma case in
      let sigma, changedc, cj = recheck_against env sigma gc c in
      let sigma, changedp, pj = recheck_against env sigma gp p in
      let (sigma, changedlf), lfj =
        if Array.length glf <> Array.length lf then
          Array.fold_left_map (fun (sigma,changed) c ->
              let sigma, j = execute env sigma c in
              (sigma, changed), j)
            (sigma, Changed {bodyonly=lazy false})
            lf
        else
          Array.fold_left2_map (fun (sigma,changed) good c ->
              let sigma, changed', t = recheck_against env sigma good c in
              (sigma, merge_changes changed changed'), t)
            (sigma,Same) glf lf
      in
      let sigma, changediv = match giv, iv with
        | _, NoInvert -> sigma, Same
        | NoInvert, CaseInvert {indices} ->
          (* likely bug but accept for now *)
          let args = Array.append pms indices in
          let t = mkApp (mkIndU (ci.ci_ind,u), args) in
          let sigma, tj = execute env sigma t in
          let sigma, tj = type_judgment env sigma tj in
          let sigma = check_actual_type env sigma cj tj.utj_val in
          sigma, Changed {bodyonly=Lazy.from_val false}
        | CaseInvert {indices=gindices}, CaseInvert {indices} ->
          let gargs = Array.append gpms gindices in
          let args = Array.append pms indices in
          let gt = mkApp (mkIndU (gci.ci_ind,u), gargs) in
          let t = mkApp (mkIndU (ci.ci_ind,u), args) in
          let sigma, changediv, tj = recheck_against env sigma gt t in
          let sigma, tj = type_judgment env sigma tj in
          let sigma = check_actual_type env sigma cj tj.utj_val in
          sigma, changediv
      in
      if unchanged changedc && unchanged changedp && unchanged changediv && bodyonly changedlf
      then assume_unchanged_type sigma
      else maybe_changed (judge_of_case env sigma case ci (pj,rp) iv cj lfj)

    | Proj (gp, _, gc),
      Proj (p, _, c) ->
      if not (QProjection.equal env gp p) then default ()
      else
        let sigma, changed, c = recheck_against env sigma gc c in
        maybe_changed (sigma, judge_of_projection env sigma p c)

    | App (gf, gargs),
      App (f, args) ->
      if Array.length gargs <> Array.length args then
        let sigma, _, fj = recheck_against env sigma gf f in
        let sigma, jl = execute_array env sigma args in
        (match EConstr.kind sigma f with
         | Ind (ind, u) when EInstance.is_empty u && Environ.template_polymorphic_ind ind env ->
           maybe_changed (judge_of_applied_inductive_knowing_parameters ~check:true env sigma (ind, u) jl)
         | Construct (cstr, u) when EInstance.is_empty u && Environ.template_polymorphic_ind (fst cstr) env ->
           maybe_changed (judge_of_applied_constructor_knowing_parameters ~check:true env sigma (cstr, u) jl)
         | _ ->
           (* No template polymorphism *)
           maybe_changed (judge_of_apply env sigma fj jl))
      else begin
        let (sigma, changedargs), jl =
          Array.fold_left2_map (fun (sigma,changed) good c ->
              let sigma, changed', t = recheck_against env sigma good c in
              (sigma, merge_changes changed changed'), (changed', t))
            (sigma,Same) gargs args
        in
        let sigma, changedf, fj = recheck_against env sigma gf f in
        if unchanged changedargs && bodyonly changedf
        then assume_unchanged_type sigma
        else
          (* XXX could exploit change info when template *)
          (match EConstr.kind sigma f with
           | Ind (ind, u) when EInstance.is_empty u && Environ.template_polymorphic_ind ind env ->
             let jl = Array.map snd jl in
             maybe_changed (judge_of_applied_inductive_knowing_parameters ~check:true env sigma (ind, u) jl)
           | Construct (cstr, u) when EInstance.is_empty u && Environ.template_polymorphic_ind (fst cstr) env ->
             let jl = Array.map snd jl in
             maybe_changed (judge_of_applied_constructor_knowing_parameters ~check:true env sigma (cstr, u) jl)
           | _ ->
             (* No template polymorphism *)
             maybe_changed (judge_of_apply_against env sigma changedf fj jl))
      end

    | Lambda (_, gc1, gc2),
      Lambda (name, c1, c2) ->
      let sigma, changedj, j = recheck_against env sigma gc1 c1 in
      let sigma, var = type_judgment env sigma j in
      let sigma, decl = check_binder_relevance env sigma var.utj_type (LocalAssum (name, var.utj_val)) in
      let env1 = push_rel decl env in
      let sigma, changedj', j' = if unchanged changedj then recheck_against env1 sigma gc2 c2
        else let sigma, j' = execute env1 sigma c2 in
          sigma, Changed {bodyonly=lazy false}, j'
      in
      sigma, merge_changes changedj' changedj, judge_of_abstraction env1 sigma name.binder_name var j'

    | Prod (_, gc1, gc2),
      Prod (name, c1, c2) ->
      let sigma, changedj, j = recheck_against env sigma gc1 c1 in
      let sigma, var = type_judgment env sigma j in
      let sigma, decl = check_binder_relevance env sigma var.utj_type (LocalAssum (name, var.utj_val)) in
      let env1 = push_rel decl env in
      let sigma, changedj', j' = if unchanged changedj then recheck_against env1 sigma gc2 c2
        else let sigma, j' = execute env1 sigma c2 in
          sigma, Changed {bodyonly=lazy false}, j'
      in
      let sigma, j' = type_judgment env1 sigma j' in
      sigma, merge_changes changedj' changedj, judge_of_product env1 sigma name.binder_name var j'

    | Cast (gc, _, gt),
      Cast (c, k, t) ->
      let sigma, changedc, cj = recheck_against env sigma gc c in
      let sigma, changedt, tj = recheck_against env sigma gt t in
      if unchanged changedt && bodyonly changedc
      then assume_unchanged_type sigma
      else
        let sigma, tj = type_judgment env sigma tj in
        maybe_changed (judge_of_cast env sigma cj k tj)

    | _, (Case _ | App _ | Lambda _ | Prod _ | Cast _ | Proj _) -> default ()

let recheck_against env sigma a b =
  let sigma, _, j = recheck_against env sigma a b in
  sigma, j.uj_type

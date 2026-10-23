(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Univ
open Sorts
open Constr
open Declarations
open Environ
open Names

module RelDecl = Context.Rel.Declaration

open Conversion

let warn_irrelevant_pattern = CWarnings.create ~name:"irrelevant-pattern" Fun.id

type eq_cmp = LEQ | EQ | GEQ

type rigidity = Rigid | Freestanding

type predicative_kind = Predicative | Impredicative | PredVar of QVar.t

let sort_predicativity env = function
  | Prop | SProp -> Impredicative
  | Set when Environ.is_impredicative_set env -> Impredicative
  | Set | Type _ | GSort _ -> Predicative
  | VSort (q, _) -> PredVar q


type equality = {
  lhs: constr;
  rhs : constr;
  cv_pb : conv_pb;
  ctx : rel_context
}

type blocked_on = RelVar of QVar.t | Evar of Evar.t

module QSet = QVar.Set
module EMap = Evar.Map

type evar_info = {
  name: Name.t;
  rigidity: rigidity;
  relevance: relevance;
  typ : types;
}

type state = {
  evar_index : (Evar.t * rigidity) Int.Map.t;
  nevars : int;
  evar_map : Evd.evar_map;

  qualities : (QVar.t * rigidity) Int.Map.t;
  nqualities : int;

  levels : (Level.t * rigidity) Int.Map.t;
  nlevels : int;
  ucstrs: (predicative_kind * UnivConstraint.t) list;

  pattern_relevances: QVar.Set.t;

  evar_candidates : (eq_cmp * constr) list Evar.Map.t; (* Indexed over evars *)
  delayed_equalities: (blocked_on * equality) list;
}


module State = struct

let sigma_of (evd : state) (defs : constr EMap.t) : Evd.evar_map =
  let Refl = EConstr.Unsafe.eq in
  EMap.fold Evd.define defs evd.evar_map

let make sigma = {
  evar_map = sigma; (* should only contain universe binders *)
  evar_index = Int.Map.empty;
  nevars = 0;

  qualities = Int.Map.empty;
  nqualities = 0;

  levels = Int.Map.empty;
  nlevels = 0;
  ucstrs = [];

  pattern_relevances = QSet.empty;

  evar_candidates = EMap.empty;
  delayed_equalities = [];
}

let evar_map evd = evd.evar_map

let is_rel_inst inst = List.for_all_i (fun i arg -> kind (Option.get arg) = Rel i) 1 (SList.to_list inst)

let add_evar ?loc env index evi evd : state * constr =
  let Refl = EConstr.Unsafe.eq in
  let naming = match evi.name with Name n -> Some (Namegen.IntroIdentifier n) | Anonymous -> None in
  let sigma, ev = Evarutil.new_evar
    ?naming
    ~src:(loc, RewriteRulePattern evi.name)
    ~relevance:(EConstr.ERelevance.make evi.relevance)
    env evd.evar_map (EConstr.of_constr evi.typ)
  in
  let Refl = EConstr.Unsafe.eq in
  let evk, inst = destEvar ev in
  assert (is_rel_inst inst);
  { evd with
    evar_index = Int.Map.add index (evk, evi.rigidity) evd.evar_index;
    evar_map = sigma;
    evar_candidates = if evi.rigidity == Rigid then evd.evar_candidates else EMap.add evk [] evd.evar_candidates },
  ev

let add_patvar ?loc ~name env evd typ relevance rigidity =
  let evi = { name; typ; relevance; rigidity } in
  let index = evd.nevars in
  let evd, ev = add_evar ?loc env index evi evd in
  { evd with nevars = index+1 }, (index, ev)

let create_evar ?loc ?name env evd typ relevance =
  let naming = Option.map (fun n -> Namegen.IntroIdentifier n) name in
  let sigma, ev = Evarutil.new_evar
    ?naming
    ~src:(loc, InternalHole)
    ~relevance:(EConstr.ERelevance.make relevance)
    env evd.evar_map (EConstr.of_constr typ)
  in
  let Refl = EConstr.Unsafe.eq in
  let evk, inst as ev = destEvar ev in
  assert (is_rel_inst inst);
  { evd with
    evar_map = sigma;
    evar_candidates = EMap.add evk [] evd.evar_candidates }, ev

let define_evar ev cmp t evd =
  let evar_candidates = EMap.update ev (function Some l -> Some ((cmp, t) :: l) | None -> None) evd.evar_candidates in
  { evd with evar_candidates }

let add_pattern_relevance r evd =
  match r with
  | Relevant -> evd
  | RelevanceVar q ->
    { evd with pattern_relevances = QSet.add q evd.pattern_relevances }
  | Irrelevant -> warn_irrelevant_pattern Pp.(str "Irrelevant subpattern in rewrite rules"); evd

let add_quality ?loc ?name evd =
  let evar_map, q = Evd.new_quality_variable ?loc ?name ~sort_rigid:(Option.has_some name) evd.evar_map in
  let rigidity = if Option.has_some name then Rigid else Freestanding in
  let qualities = Int.Map.add evd.nqualities (q, rigidity) evd.qualities in
  { evd with evar_map; qualities; nqualities = evd.nqualities + 1 }, (PQVar evd.nqualities, Quality.QVar q)

let bind_qvar q ~bound evd =
  assert (not @@ Int.Map.mem q evd.qualities);
  { evd with
    qualities = Int.Map.add q (QVar.make_var q, bound) evd.qualities }

let create_qvar evd =
  let evar_map, q = Evd.new_quality_variable evd.evar_map in
  { evd with evar_map }, Quality.QVar q

let add_level ?loc ?name evd =
  let evar_map, l = Evd.new_univ_level_variable ?loc ?name UnivRigid evd.evar_map in
  let rigidity = if Option.has_some name then Rigid else Freestanding in
  let levels = Int.Map.add evd.nlevels (l, rigidity) evd.levels in
  { evd with evar_map; levels; nlevels = evd.nlevels + 1 }, (evd.nlevels, l)

let bind_level l ~bound evd =
  assert (not @@ Int.Map.mem l evd.levels);
  { evd with
    levels = Int.Map.add l (Level.var l, bound) evd.levels }

let create_level evd =
  let evar_map, l = Evd.new_univ_level_variable (UnivFlexible false) evd.evar_map in
  { evd with evar_map }, l

let create_universe ?loc evd =
  let evar_map, s = Evd.new_sort_variable ?loc (UnivFlexible true) evd.evar_map in
  { evd with evar_map }, EConstr.Unsafe.to_sorts s

let check_eq_qvar evd q q' =
  UState.check_eq_quality (Evd.ustate evd.evar_map) (QVar q) (QVar q')

let check_eq_qual evd s s' =
  UState.check_eq_quality (Evd.ustate evd.evar_map) s s'

let get_constraint q q' = function
| Conversion.CONV -> UnivProblem.QEq (q, q')
| Conversion.CUMUL -> UnivProblem.QLeq (q, q')

let nf_relevance evd r =
  UState.nf_relevance (Evd.ustate evd.evar_map) r

let enforce_cmp_quality c q1 q2 evd =
  let evar_map = Evd.add_constraints evd.evar_map (UnivProblem.Set.singleton (get_constraint q1 q2 c)) in
  { evd with evar_map }

let enforce_cmp_level k p l l' cstrs =
  if Level.equal l l' then cstrs
  else (p, (l, k, l')) :: cstrs


let enforce_leq_universe p u1 u2 cstrs =
  match Universe.level u2 with
  | Some l2 ->
    List.fold_left (fun c (l, n) ->
      if Level.equal l l2 then c
      else
        let k = UnivConstraint.(if n = 0 then Le else Lt) in
        (p, (l, k, l2)) :: c)
      cstrs (Universe.repr u1)
  | None -> cstrs

let enforce_cmp_universe c p u1 u2 evd =
  let ucstrs =
    match c with
    | CUMUL -> enforce_leq_universe p u1 u2 evd.ucstrs
    | CONV ->
      match Universe.level u1, Universe.level u2 with
      | Some l, Some l' -> enforce_cmp_level UnivConstraint.Eq p l l' evd.ucstrs
      | _ -> enforce_leq_universe p u1 u2 (enforce_leq_universe p u2 u1 evd.ucstrs)
  in
  { evd with ucstrs }


let get_algebraic = function
| Prop | SProp -> Universe.type0
| GSort (_, u) | VSort (_, u) -> u
| Set -> Universe.type0
| Type u -> u

let enforce_cmp_sort env cv_pb s1 s2 evd =
  let evd = enforce_cmp_quality cv_pb (Sorts.quality s1) (Sorts.quality s2) evd in
  enforce_cmp_universe cv_pb (sort_predicativity env s1) (get_algebraic s1) (get_algebraic s2) evd

let enforce_univ_constraints evd cstrs =
  let cstrs = UnivConstraints.elements cstrs in
  let cstrs = List.map (fun c -> (Predicative, c)) cstrs in
  { evd with ucstrs = cstrs @ evd.ucstrs }

let enforce_sort_constraints evd cstrs =
  let evar_map = Evd.add_poly_constraints evd.evar_map (PConstraints.of_qualities cstrs) in
  { evd with evar_map }

let enforce_constraints evd cstrs =
  let evd = enforce_sort_constraints evd (PConstraints.qualities cstrs) in
  enforce_univ_constraints evd (PConstraints.univs cstrs)

let create_fresh_instance env evd gr =
  let auctx = Environ.universes_of_global env gr in
  let qlen, ulen = UVars.AbstractContext.size auctx in
  let evdref = ref evd in
  let fmap f = let evd, r = f !evdref in evdref := evd; r in
  let qinst = Array.init qlen (fun _ -> fmap create_qvar) in
  let uinst = Array.init ulen (fun _ -> fmap create_level) in
  let evd = !evdref in
  let inst = UVars.Instance.of_array (qinst,uinst) in
  let cstrs = UVars.AbstractContext.instantiate inst auctx in
  enforce_constraints evd cstrs, inst

let enforce_super_level env evd s u =
  enforce_cmp_universe CUMUL (sort_predicativity env s) (Universe.super (get_algebraic s)) (Universe.make u) evd

let create_super_sort env evd s =
  let evd, l = create_level evd in
  enforce_super_level env evd s l, sort_of_univ (Universe.make l)

let enforce_product_level env evd s s' u =
  let evd = enforce_cmp_universe CUMUL (sort_predicativity env s') (get_algebraic s') (Universe.make u) evd in
  enforce_cmp_universe CUMUL (sort_predicativity env s) (get_algebraic s) (Universe.make u) evd

let create_product_sort env evd s s' =
  let evd, l = create_level evd in
  enforce_product_level env evd s s' l, Sorts.make (Sorts.quality s') (Universe.make l)


let compare_instances u1 u2 evd =
  let (qcstrs, ucstrs) = UVars.enforce_eq_instances u1 u2 (UVars.QPairSet.empty, UnivConstraints.empty) in
  let evd = UVars.QPairSet.fold (fun (s, s') -> enforce_cmp_quality CONV s s') qcstrs evd in
  enforce_univ_constraints evd ucstrs

let compare_cumul_instances cv_pb variance u u' evd =
  let qucstrs = (UVars.QPairSet.empty, UnivConstraints.empty) in
  let (qcstrs, ucstrs) = match cv_pb with
    | CONV ->
      UVars.enforce_eq_variance_instances variance u u' qucstrs
    | CUMUL ->
      UVars.enforce_leq_variance_instances variance u u' qucstrs
  in
  let evd = UVars.QPairSet.fold (fun (s, s') -> enforce_cmp_quality CONV s s') qcstrs evd in
  enforce_univ_constraints evd ucstrs


let enforce_equality_relevancevar env q cv_pb lhs rhs evd =
  let equality = { lhs; rhs; cv_pb; ctx = Environ.rel_context env } in
  { evd with delayed_equalities = (RelVar q, equality) :: evd.delayed_equalities }


let enforce_equality_evar env evk cv_pb lhs rhs evd =
  let equality = { lhs; rhs; cv_pb; ctx = Environ.rel_context env } in
  { evd with delayed_equalities = (Evar evk, equality) :: evd.delayed_equalities }

end






(** Adversarial unification engine
    State gets enriched with equalities and constraints
    which hold even for substituted terms, for any substitution. *)

exception MustExpand
exception NotConvertible

let inductive_cumulativity_arguments (mind,ind) =
  mind.mind_nparams +
  mind.mind_packets.(ind).mind_nrealargs

let convert_inductives cv_pb (mind, ind) nargs u1 u2 s =
  match mind.mind_variance with
  | None -> State.compare_instances u1 u2 s
  | Some variances ->
    let num_param_arity = inductive_cumulativity_arguments (mind,ind) in
    if not (Int.equal num_param_arity nargs) then
      (* shortcut, not sure if worth doing, could use perf data *)
      if UVars.Instance.equal u1 u2 then s else raise MustExpand
    else
      State.compare_cumul_instances cv_pb variances u1 u2 s

let convert_constructors (mind, ind, cns as ctor) nargs u1 u2 s =
  match mind.mind_variance with
  | None -> State.compare_instances u1 u2 s
  | Some _ ->
    let num_cnstr_args = constructor_cumulativity_arguments ctor in
    if not (Int.equal num_cnstr_args nargs) then
      if UVars.Instance.equal u1 u2 then s else raise MustExpand
    else
      (* By invariant, both constructors have a common supertype,
          so they are convertible _at that type_. *)
      (* NB: no variance for qualities *)
      let variances = Array.make (snd (UVars.Instance.length u1)) UVars.Variance.Irrelevant in
      State.compare_cumul_instances CONV variances u1 u2 s

let identity_of_ctx (ctx : Constr.rel_context) =
  Context.Rel.instance mkRel 0 ctx

let eta_expand_ind env (ind,u as pind) =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let ctx = Vars.subst_instance_context u mip.mind_arity_ctxt in
  let args = identity_of_ctx ctx in
  let c = mkApp (mkIndU pind, args) in
  let c = Term.it_mkLambda_or_LetIn c ctx in
  c

let eta_expand_constructor env ((ind,ctor),u as pctor) =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let ctx = Vars.subst_instance_context u (fst mip.mind_nf_lc.(ctor-1)) in
  let args = identity_of_ctx ctx in
  let c = mkApp (mkConstructU pctor, args) in
  let c = Term.it_mkLambda_or_LetIn c ctx in
  c

let eta_expand_lambda t =
  mkApp (Vars.lift 1 t, [|mkRel 1|])

let eta_expand_constructor_term env (ind, u) args t' =
  let (mib, _ as specif) = Inductive.lookup_mind_specif env ind in
  (* disallow eta-exp for non-primitive records, also check postponed eta *)
  let () = if not (Declareops.is_record_with_eta specif u) then
      raise Not_found
  in
  match Declareops.inductive_make_projections ind mib with
  | None -> assert false
  | Some projs ->
    (* (Construct, pars1 .. parsm :: arg1...argn :: []) ~= (f, s') ->
           arg1..argn ~= (proj1 t...projn t) where t = zip (f,s') *)
    let pars = mib.Declarations.mind_nparams in
    (* Try to drop the params, might fail on partially applied constructors. *)
    let nargs = Array.length args in
    if pars >= nargs then raise Not_found;
    let args = Array.sub args pars (nargs - pars) in
    let projapps = Array.map (fun (p,r) -> mkProj (Projection.make p true, UVars.subst_instance_relevance u r, t')) projs in
    args, projapps

let is_rel_inst inst = List.for_all_i (fun i arg -> Option.map kind arg = Some (Rel i)) 1 (SList.to_list inst)

let cmp_of_pb = function CUMUL -> GEQ | CONV -> EQ
let cmp_of_pb_r : _ -> eq_cmp = function CUMUL -> LEQ | CONV -> EQ

let is_empty_stack = List.is_empty

let may_invert h s =
  match kind h with
  | Const _ -> false
  | Rel _ | Ind _ | Construct _ -> true
  | Sort _ | Lambda _ | Fix _ | CoFix _
  | Prod _ | Int _ | Float _ | String _
  | Array _ -> is_empty_stack s
  | Cast _ | LetIn  _| App _ | Case _ | Proj _
    (* ruled out by whd_stack *)
  | Var _ | Meta _ | Evar _ ->
    assert false

let whd_all : env -> Evd.evar_map -> constr -> constr = let Refl = EConstr.Unsafe.eq in Reductionops.whd_all ?metas:None
let whd_all_state : env -> Evd.evar_map -> (constr * _) -> (constr * _) = let Refl = EConstr.Unsafe.eq in Reductionops.whd_all_state ?metas:None
let zip : Evd.evar_map -> (constr * _) -> constr = let Refl = EConstr.Unsafe.eq in Reductionops.Stack.zip

let rec unify cv_pb env sigma t1 t2 evd =
  let Refl = EConstr.Unsafe.eq in
  let h1, s1 = whd_all_state env sigma (t1, []) in
  let h2, s2 = whd_all_state env sigma (t2, []) in
  let t1 = zip sigma (h1, s1) in
  let t2 = zip sigma (h2, s2) in

  match kind t1 with
  | Evar (ev, args) when is_rel_inst args ->
    State.define_evar ev (cmp_of_pb cv_pb) t2 evd
  | _ ->
  match kind t2 with
  | Evar (ev, args) when is_rel_inst args ->
    State.define_evar ev (cmp_of_pb_r cv_pb) t1 evd
  | _ ->

  match kind h1, kind h2 with
  | Evar (ev, _), _ | _, Evar (ev, _) ->
    State.enforce_equality_evar env ev cv_pb t1 t2 evd
  | _ ->
    if may_invert h1 s1 && may_invert h2 s2 then
      unify_in_stack cv_pb env sigma t1 t2 evd
    else
      evd

and unify_in_stack cv_pb env sigma ?(napp=0) t1 t2 evd =
  match Relevanceops.relevance_of_term env t1, Relevanceops.relevance_of_term env t2 with
  | Irrelevant, Irrelevant -> evd
  | RelevanceVar q, RelevanceVar q' when State.check_eq_qvar evd q q' ->
      State.enforce_equality_relevancevar env q cv_pb t1 t2 evd
  | RelevanceVar _, _ | _, RelevanceVar _
  | Relevant, Irrelevant | Irrelevant, Relevant ->
      CErrors.anomaly Pp.(str "tried to compare two terms with different relevances")
  | Relevant, Relevant ->
  let h1, args1 = decompose_app t1 in
  let h2, args2 = decompose_app t2 in
  match kind h1, kind h2 with
  | Fix ((op1, i1), _), Fix ((op2, i2), _) ->
    if not (Int.equal i1 i2 && Array.equal Int.equal op1 op2) then
      raise NotConvertible;
    let index = op1.(i1) in
    let evd = unify_in_stack cv_pb env sigma args1.(index) args2.(index) evd in
    let evd = unify cv_pb env sigma h1 h2 evd in
    Array.fold_left2_i (fun i u v1 v2 -> if i = index then u else unify CONV env sigma v1 v2 u) evd args1 args2

  | Construct ((ind1, j1), u1 as pctor1), Construct ((ind2, j2), u2 as pctor2) ->
    if not (Int.equal j1 j2 && QInd.equal env ind1 ind2) then
      raise NotConvertible
    else if Array.length args1 != Array.length args2 then
      raise NotConvertible;

    let evd =
      if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
        State.compare_instances u1 u2 evd
      else
        let mind = Environ.lookup_mind (fst ind1) env in
        begin match convert_constructors (mind, snd ind1, j1) napp u1 u2 evd with
        | evd -> evd
        | exception MustExpand ->
          let t1 = eta_expand_constructor env pctor1 in
          let t2 = eta_expand_constructor env pctor2 in
          unify cv_pb env sigma t1 t2 evd
        end
    in
    Array.fold_left2 (fun u v1 v2 -> unify CONV env sigma v1 v2 u) evd args1 args2

  | Construct ((ind1, _), u1), _ ->
    begin match eta_expand_constructor_term env (ind1, u1) args1 t2 with
    | args1, args2 -> Array.fold_left2 (fun u v1 v2 -> unify CONV env sigma v1 v2 u) evd args1 args2
    | exception Not_found -> raise NotConvertible
    end

  | _, Construct ((ind2, _), u2) ->
    begin match eta_expand_constructor_term env (ind2, u2) args2 t1 with
    | args2, args1 -> Array.fold_left2 (fun u v1 v2 -> unify CONV env sigma v1 v2 u) evd args1 args2
    | exception Not_found -> raise NotConvertible
    end
  | _ ->
  match kind t1, kind t2 with
  (* case of leaves *)
  | Sort s1, Sort s2 ->
    State.enforce_cmp_sort env cv_pb s1 s2 evd

  | Meta _, _ | _, Meta _ -> assert false
  | Var _, _ | _, Var _ -> assert false

  (* Inductive types:  MutInd MutConstruct Fix Cofix *)
  | Ind (ind1, u1 as pind1), Ind (ind2, u2 as pind2) ->
    if not (QInd.equal env ind1 ind2) then
      raise NotConvertible
    else if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
      State.compare_instances u1 u2 evd
    else
      let mind = Environ.lookup_mind (fst ind1) env in
      begin match convert_inductives cv_pb (mind, snd ind1) napp u1 u2 evd with
      | evd -> evd
      | exception MustExpand ->
        let t1 = eta_expand_ind env pind1 in
        let t2 = eta_expand_ind env pind2 in
        unify cv_pb env sigma t1 t2 evd
      end

  | Construct _, _ | _, Construct _ -> assert false

  | Prod (na, dom1, codom1), Prod (_, dom2, codom2) ->
    let evd = unify CONV env sigma dom1 dom2 evd in
    unify cv_pb (Environ.push_rel (LocalAssum (na, dom1)) env) sigma codom1 codom2 evd

  (* other constructors *)
  | Lambda (na, ty1, bd1), Lambda (_, ty2, bd2) ->
    let evd = unify CONV env sigma ty1 ty2 evd in
    unify CONV (Environ.push_rel (LocalAssum (na, ty1)) env) sigma bd1 bd2 evd

  (* Eta-expansion on the fly *)
  | Lambda (na, ty, bd1), _ ->
    let t2 = eta_expand_lambda t2 in
    unify CONV (Environ.push_rel (LocalAssum (na, ty)) env) sigma bd1 t2 evd

  | _, Lambda (na, ty, bd2) ->
    let t1 = eta_expand_lambda t1 in
    unify CONV (Environ.push_rel (LocalAssum (na, ty)) env) sigma t1 bd2 evd

  (* Fix as an elimination handled in FApp *)
  | Fix ((op1, i1), (na1, tys1, cl1 as recdecl)), Fix ((op2, i2), (_, tys2, cl2)) ->
    if not (Int.equal i1 i2 && Array.equal Int.equal op1 op2) then
      raise NotConvertible;

    let evd = Array.fold_left2 (fun evd t1 t2 -> unify CONV env sigma t1 t2 evd) evd tys1 tys2 in
    let env = Environ.push_rec_types recdecl env in
    Array.fold_left2 (fun evd t1 t2 -> unify CONV env sigma t1 t2 evd) evd cl1 cl2

  | CoFix (op1, (na1, tys1, cl1 as recdecl)), CoFix (op2, (_, tys2, cl2)) ->
    if not (Int.equal op1 op2) then
      raise NotConvertible;

    let evd = Array.fold_left2 (fun evd t1 t2 -> unify CONV env sigma t1 t2 evd) evd tys1 tys2 in
    let env = Environ.push_rec_types recdecl env in
    Array.fold_left2 (fun evd t1 t2 -> unify CONV env sigma t1 t2 evd) evd cl1 cl2

  | Int i1, Int i2 ->
      if Uint63.equal i1 i2 then evd
      else raise NotConvertible

  | Float f1, Float f2 ->
      if Float64.equal f1 f2 then evd
      else raise NotConvertible

  | String s1, String s2 ->
    if Pstring.equal s1 s2 then evd
    else raise NotConvertible

  | Array (u1, t1, def1, ty1), Array (u2, t2, def2, ty2) ->
    if not (Int.equal (Array.length t1) (Array.length t2)) then raise NotConvertible;
    let evd = State.compare_cumul_instances CONV [|UVars.Variance.Irrelevant|] u1 u2 evd in
    let evd = unify CONV env sigma ty1 ty2 evd in
    let evd = unify CONV env sigma def1 def2 evd in
    let evd = Array.fold_left2 (fun u v1 v2 -> unify CONV env sigma v1 v2 u) evd t1 t2 in
    evd


  (* Neutral rules *)

  (* 2 indices known to be bound to no constant *)
  | Rel n, Rel m ->
    if n = m then
      evd
    else
      raise NotConvertible

  | App (hd1, args1), App (hd2, args2) ->
    let nargs1 = Array.length args1 in
    let nargs2 = Array.length args2 in
    if nargs1 != nargs2 then raise NotConvertible;
    let evd = unify_in_stack cv_pb env ~napp:nargs1 sigma hd1 hd2 evd in
    Array.fold_left2 (fun u v1 v2 -> unify CONV env sigma v1 v2 u) evd args1 args2

  | Proj (p1, _r1, c1), Proj (p2, _r2, c2) ->
    if QProjection.Repr.equal env (Names.Projection.repr p1) (Names.Projection.repr p2) then
      unify_in_stack CONV env sigma c1 c2 evd
    else raise NotConvertible

  | Case (ci1, u1, pms1, (p1, _), iv1, c1, br1), Case (ci2, u2, pms2, (p2, _), iv2, c2, br2) ->
    if not (QInd.equal env ci1.ci_ind ci2.ci_ind) then
      raise NotConvertible;

    let specif = Inductive.lookup_mind_specif env ci1.ci_ind in

    (* FIXME: cache the presence of let-bindings in the case_info *)
    let evd =
      let ind = (fst specif, snd ci1.ci_ind) in
      let nargs = inductive_cumulativity_arguments ind in
      convert_inductives CONV ind nargs u1 u2 evd
    in

    let pctx = Inductive.expand_arity specif (ci1.ci_ind, u1) pms1 (fst p1) in
    let brctx = Inductive.expand_branch_contexts specif u1 pms1 br1 in

    let evd = unify_in_stack CONV env sigma c1 c2 evd in
    let evd = Array.fold_left2 (fun u v1 v2 -> unify CONV env sigma v1 v2 u) evd pms1 pms2 in
    let evd = convert_under_context env sigma pctx (snd p1) (snd p2) evd in
    Array.fold_left3 (fun u ctx (_, v1) (_, v2) -> convert_under_context env sigma ctx v1 v2 u) evd brctx br1 br2

  (* Dealt with in unify *)
  | (Evar _, _ | _, Evar _)
  | (Const _, _ | _, Const _) -> assert false

  (* Should not happen because both (hd1,v1) and (hd2,v2) are in whnf *)
  | ((LetIn _ | Cast _), _) | (_, (LetIn _ | Cast _)) -> assert false

  | (Rel _ | Sort _ | Ind _ | Fix _ | CoFix _
    | Prod _ | Int _ | Float _ | String _ | Array _
    | App _ | Case _ | Proj _), _ -> raise NotConvertible


and convert_under_context env sigma ctx c1 c2 cu =
  let env = Environ.push_rel_context ctx env in
  unify CONV env sigma c1 c2 cu

let cumul_lax env evd t1 t2 =
  unify CUMUL env evd.evar_map t1 t2 evd



let evar_handler_defs evd defs =
  let evar_expand (ev, inst) =
    match Evar.Map.find_opt ev defs with
    | Some def -> CClosure.EvarDefined (Vars.substl (inst |> SList.to_list |> List.map Option.get) def)
    | None -> CClosure.EvarUndefined (ev, inst |> SList.to_list |> List.map Option.get)
  in
  let qvar_irrelevant _ = assert false in (* Only used in conversion mode, but we use reduction mode here *)
  let qual_equal s s' = State.check_eq_qual evd s s' in
  let evar_irrelevant _ = false in
  let evar_repack (ev, args) = mkEvar (ev, SList.of_full_list args) in
  let abstr_const = fun _ -> assert false in
  { CClosure.evar_expand; evar_irrelevant; evar_repack; qvar_irrelevant; qual_equal; abstr_const; }

let unify_lax rels conv_pb defs env evd t1 t2 =
  unify conv_pb env (State.sigma_of evd defs) t1 t2 evd

let unify_delayed env evd defs eq =
  let env = Environ.push_rel_context eq.ctx env in
  unify eq.cv_pb env (State.sigma_of evd defs) eq.lhs eq.rhs evd











(* Adversarial typechecker, returns minimal types while checking arguments against maxiaml types *)


type names = {
  sort_names : Name.t array;
  level_names : Name.t array;
  evar_names : Name.t array;
}

let mk_univ i = Universe.make (Level.var i)

let declare_qvar names evd q =
  let nao = Array.get names.sort_names q in
  let bound = if Name.is_name nao then Rigid else Freestanding in
  State.bind_qvar q ~bound evd

let declare_level names evd lvl =
  let nao = Array.get names.level_names lvl in
  let bound = if Name.is_name nao then Rigid else Freestanding in
  State.bind_level lvl ~bound evd

let declare_evar names env evd evk relevance typ =
  let name = Array.get names.evar_names evk in
  let evi = {
    rigidity = if Name.is_name name then Rigid else Freestanding;
    name; relevance; typ
  } in
  State.add_evar env evk evi evd

let quality_of_quality_mask names evd =
  let open Sorts.Quality in
  function
  | PQConstant q -> evd, QConstant q
  | PQGlobal g -> evd, QGlobal g
  | PQVar q ->
    let evd = declare_qvar names evd q in
    evd, Sorts.Quality.var q

let sort_of_sort_pattern names evd = function
  | PSSProp -> evd, sprop
  | PSProp -> evd, prop
  | PSSet -> evd, set
  | PSType lvl ->
    let evd = declare_level names evd lvl in
    evd, Sorts.sort_of_univ (mk_univ lvl)
  | PSGlobal (g, lvl) ->
    let evd = declare_level names evd lvl in
    evd, Sorts.gsort g (mk_univ lvl)
  | PSQSort (q, lvl) ->
    let evd = declare_qvar names evd q in
    let evd = declare_level names evd lvl in
    evd, Sorts.vsort (QVar.make_var q) (mk_univ lvl)

let instance_of_instance_mask names evd (qs, us : _ instance_mask) =
  let evd, qs = Array.fold_left_map (quality_of_quality_mask names) evd qs in
  let evd, us = Array.fold_left_map (fun evd u -> declare_level names evd u, Level.var u) evd us in
  evd, UVars.Instance.of_array (qs, us)



let reduce_to_prod env evd t =
  match kind (whd_all env evd.evar_map t) with
  | Prod (na, ty, ret) ->
    evd, (ty, na.Context.binder_relevance, ret)

  | Evar (ev, inst) ->
    let evd, dom_sort = State.create_universe evd in
    let evd, evty = State.create_evar env evd (mkSort dom_sort) Relevant in
    let domty = mkEvar evty in

    let domr = Sorts.relevance_of_sort dom_sort in
    let decl = Context.(Rel.Declaration.LocalAssum (make_annot Anonymous domr, domty)) in
    let env' = Environ.push_rel decl env in

    let evd, cod_sort = State.create_universe evd in
    let evd, evret = State.create_evar env' evd (mkSort cod_sort) Relevant in

    let codty = mkEvar evret in

    let prodty = Term.mkProd_wo_LetIn decl codty in

    let evd =
      if is_rel_inst inst then
        State.define_evar ev EQ prodty evd
      else evd
    in
    evd, (domty, domr, codty)
  | _ -> CErrors.anomaly (Pp.str "Typing error in rewrite rules, application head doesn't have function type.")


let create_evar_instance env evd ar_ctx =
  let open Context.Rel.Declaration in
  let rec apply_rec evd telescope args subst =
    match telescope with
    | LocalDef (_, b, _) :: tele ->
      let b = Vars.substl subst b in
      apply_rec evd tele args (b :: subst)
    | LocalAssum (na, ty) :: tele ->
      let ty = Vars.substl subst ty in
      let evd, ev = State.create_evar env evd ty na.binder_relevance in
      let ev = mkEvar ev in
      apply_rec evd tele (ev :: args) (ev :: subst)
    | [] -> evd, Array.rev_of_list args
  in
  apply_rec evd (List.rev ar_ctx) [] []


let reduce_to_appind env evd ind t =
  match kind (whd_all env evd.evar_map t) with
  | Ind (ind', u) when QInd.equal env ind ind' ->
      evd, (u, [||])
  | App (hd, args) ->
      begin match kind hd with
      | Ind (ind', u) when QInd.equal env ind ind' ->
        evd, (u, args)
      | _ -> CErrors.anomaly (Pp.str "Typing error in rewrite rules, match head doesn't have inductive type.")
      end
  | Evar (ev, inst) ->

    let evd, u = State.create_fresh_instance env evd (GlobRef.IndRef ind) in
    let (mib, mip) = Inductive.lookup_mind_specif env ind in
    let ar_ctx = Vars.subst_instance_context u mip.mind_arity_ctxt in
    let evd, args = create_evar_instance env evd ar_ctx in
    let indargs = mkApp (mkIndU (ind, u), args) in

    let evd =
      if is_rel_inst inst then
        State.define_evar ev EQ indargs evd
      else evd
    in
    evd, (u, args)
  | _ -> CErrors.anomaly (Pp.str "Typing error in rewrite rules, match head doesn't have inductive type.")




let warn_eta_in_pattern =
  CWarnings.create ~name:"eta-in-pattern" Fun.id

let warn_redex_in_rewrite_rules =
  CWarnings.create ~name:"redex-in-rewrite-rules"
  (fun redex -> Pp.(str "This pattern contains a" ++ redex ++ str " which may prevent this rule from being triggered."))

let rec check_may_eta ?loc env evd ?tryother t =
  match kind (whd_all env evd.evar_map t) with
  | Prod _ ->
      warn_eta_in_pattern ?loc
        Pp.(str "This subpattern has a product type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")
  | Sort _ -> ()
  | Ind (ind, _) ->
      let specif = Inductive.lookup_mind_specif env ind in
      if not @@ Inductive.is_primitive_record specif then () else
        warn_eta_in_pattern ?loc
          Pp.(str "This subpattern has a primitive record type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")
  | App (i, _) -> check_may_eta ?loc env evd ?tryother i
  | Const _ -> () (* Either an axiom or a primitive type *)
  | _ ->
      match tryother with
      | Some t -> check_may_eta ?loc env evd t
      | None ->
        warn_eta_in_pattern ?loc
          Pp.(str "This subpattern has a yet unknown type, which may be a product type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")


let type_of_relative env n =
  env |> lookup_rel n |> RelDecl.get_type |> lift n

let type_of_inductive env evd (ind, u) =
  let (mib, _ as specif) = Inductive.lookup_mind_specif env ind in
  assert (List.is_empty mib.mind_hyps);
  let t, cstrs = Inductive.constrained_type_of_inductive (specif, u) in
  let evd = State.enforce_constraints evd cstrs in
  evd, t

let type_of_constructor env evd (c, _ as cu) =
  let (mib, _ as specif) = Inductive.lookup_mind_specif env (inductive_of_constructor c) in
  assert (List.is_empty mib.mind_hyps);
  let t, cstrs = Inductive.constrained_type_of_constructor cu specif in
  let evd = State.enforce_constraints evd cstrs in
  evd, t

let type_of_constant env evd (kn, _ as cst) =
  let cb = lookup_constant kn env in
  assert (List.is_empty cb.const_hyps);
  let ty, cu = constant_type env cst in
  let evd = State.enforce_constraints evd cu in
  evd, ty


let judge_of_relative env k = make_judge (mkRel k) (type_of_relative env k)

let judge_of_inductive env evd indu =
  let evd, ty = type_of_inductive env evd indu in
  evd, make_judge (mkIndU indu) ty

let judge_of_constructor env evd cu =
  let evd, ty = type_of_constructor env evd cu in
  evd, make_judge (mkConstructU cu) ty

let judge_of_constant env evd cst =
  let evd, ty = type_of_constant env evd cst in
  evd, make_judge (mkConstU cst) ty

let take_named na na' = match na with
  | Anonymous -> na'
  | na -> na

let instantiate_context u subst nas ctx =
  let open Context.Rel.Declaration in
  let open Context in
  let open Vars in
  let instantiate_relevance na =
    { na with binder_relevance = UVars.subst_instance_relevance u na.binder_relevance }
  in
  let rec instantiate i ctx = match ctx with
  | [] -> assert (Int.equal i (-1)); []
  | LocalAssum (na, ty) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    let na = instantiate_relevance na in
    let na = Context.map_annot (take_named nas.(i)) na in
    LocalAssum (na, ty) :: ctx
  | LocalDef (na, ty, bdy) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    let bdy = substnl subst i (subst_instance_constr u bdy) in
    let na = instantiate_relevance na in
    let na = Context.map_annot (take_named nas.(i)) na in
    LocalDef (na, ty, bdy) :: ctx
  in
  instantiate (List.length ctx - 1) ctx


let rec instantiate ctx args subst =
  let open Context.Rel.Declaration in
  match ctx, args with
  | [], [] -> subst
  | LocalAssum _ :: ctx, a :: args ->
    let subst = Esubst.subs_cons (Vars.make_substituend a) subst in
    instantiate ctx args subst
  | LocalDef (_, a, _) :: ctx, args ->
    let a = Vars.esubst Vars.lift_substituend subst a in
    let subst = Esubst.subs_cons (Vars.make_substituend a) subst in
    instantiate ctx args subst
  | _ -> assert false


(* Annotation for cases *)
let make_case_info env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let print_info = { style = MatchStyle } in
  (* Reasonable dummy, even if unused *)
  { ci_ind     = ind;
    ci_npar    = mib.mind_nparams;
    ci_cstr_ndecls = mip.mind_consnrealdecls;
    ci_cstr_nargs = mip.mind_consnrealargs;
    ci_pp_info = print_info }

let rec is_applied_ind_template env = function
  | PApp (f, _) -> is_applied_ind_template env f
  | PInd (ind, _) -> ignore (env, ind); false
  | _ -> false

let indtyping_helper typecheck to_pred push_rel_context (!!) env evd j_head ind ?pnas ?(pna=Anonymous) p brs =
  let evd, (u, args) = reduce_to_appind !!env evd ind (j_type j_head) in
  let (mib, mip) = Inductive.lookup_mind_specif !!env ind in

  let (params, realargs) = Array.chop mib.mind_nparams args in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in

  let pctx =
    let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
    let self =
      let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
      let inst = UVars.Instance.(abstract_instance (length u)) in
      mkApp (mkIndU (ind, inst), args)
    in
    let realdecls = Context.Rel.Declaration.LocalAssum (Context.make_annot pna mip.mind_relevance, self) :: realdecls in
    let pnas = Option.default (Array.make (mip.mind_nrealdecls + 1) Anonymous) pnas in
    instantiate_context u paramsubst pnas realdecls
  in

  let evd, ret_sort = State.create_universe evd in
  let ret_rel = Sorts.relevance_of_sort ret_sort in
  let (evd, p) =
    let pctx, p_env = push_rel_context evd pctx env in
    let evd, j_p = typecheck p_env evd (mkSort ret_sort, Relevant) p in
    (evd, (Array.map_of_list Context.Rel.Declaration.get_annot pctx, j_p))
  in
  let pred = to_pred (snd p) in
  let build_one_branch i evd (brnas, br) =
    let (ctx, cty) = mip.mind_nf_lc.(i) in

    let brnas = Option.default (Array.make mip.mind_consnrealdecls.(i) Anonymous) brnas in
    let bctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
    let bctx = instantiate_context u paramsubst brnas bctx in
    let bctx, br_env = push_rel_context evd bctx env in
    let cty = Vars.substnl paramsubst mip.mind_consnrealdecls.(i) (Vars.subst_instance_constr u cty) in

    let (_, retargs) = Inductive.find_rectype !!br_env cty in

    let params = Array.map (fun c -> lift mip.mind_consnrealdecls.(i) c) params in
    let cargs = Context.Rel.instance mkRel 0 bctx in
    let cstr = mkApp (mkConstructU ((ind, i + 1), u), Array.append params cargs) in
    let indices = List.lastn mip.mind_nrealargs retargs in
    let subst = instantiate (List.rev pctx) (indices @ [cstr]) (Esubst.subs_shft (mip.mind_consnrealdecls.(i), Esubst.subs_id 0)) in

    let brty = Vars.esubst Vars.lift_substituend subst pred in

    let evd, j_br = typecheck br_env evd (brty, ret_rel) br in
    evd, (Array.map_of_list Context.Rel.Declaration.get_annot bctx, j_br)
  in
  let evd, brs = Array.fold_left_map_i build_one_branch evd brs in

  let ci = make_case_info !!env ind in
  let body = (ci, u, params, (p, ret_rel), NoInvert, j_val j_head, brs) in

  let ty =
    let subst = Vars.subst_of_rel_context_instance_list pctx (CArray.to_list realargs @ [j_val j_head]) in
    Vars.substl subst pred
  in

  evd, body, ty


let rec typecheck_pattern env names evd = function

  | p when is_applied_ind_template env p -> assert false

  | PRel n -> evd, judge_of_relative env n
  | PSort s ->
      let evd, s = sort_of_sort_pattern names evd s in
      let evd, sup = State.create_super_sort env evd s in
      evd, make_judge (mkSort s) (mkSort sup)
  | PInd (ind, u) ->
      let evd, u = instance_of_instance_mask names evd u in
      judge_of_inductive env evd (ind, u)
  | PConstr (cstr, u) ->
      let evd, u = instance_of_instance_mask names evd u in
      judge_of_constructor env evd (cstr, u)
  | PSymbol (s, u) ->
      let evd, u = instance_of_instance_mask names evd u in
      judge_of_constant env evd (s, u)
  | PInt i ->
      evd, make_judge (mkInt i) (Typeops.type_of_int env)
  | PFloat f ->
      evd, make_judge (mkFloat f) (Typeops.type_of_float env)
  | PString s ->
      evd, make_judge (mkString s) (Typeops.type_of_string env)
  | PLambda (na, argty, bod) ->
      let evd, ty_sort = State.create_universe evd in
      let ty_rel = Sorts.relevance_of_sort ty_sort in
      let evd, argtyj = typecheck_arg_pattern env names evd (mkSort ty_sort, Relevant) argty in
      let decl = Context.(Rel.Declaration.LocalAssum (make_annot na ty_rel, j_val argtyj)) in
      let env = Environ.push_rel decl env in
      let evd, bodj = typecheck_pattern env names evd bod in
      let () = check_may_eta env evd (j_type bodj) in
      let tm = Term.mkLambda_or_LetIn decl (j_val bodj) in
      let ty = Term.mkProd_or_LetIn decl (j_type bodj) in
      evd, make_judge tm ty
  | PProd (na, domty, codty) ->
      let evd, dom_sort = State.create_universe evd in
      let domr = Sorts.relevance_of_sort dom_sort in
      let evd, domtyj = typecheck_arg_pattern env names evd (mkSort dom_sort, Relevant) domty in
      let decl = Context.(Rel.Declaration.LocalAssum (make_annot na domr, j_val domtyj)) in
      let env = Environ.push_rel decl env in

      let evd, cod_sort = State.create_universe evd in
      let evd, codj = typecheck_arg_pattern env names evd (mkSort cod_sort, Relevant) codty in

      let evd, ret_sort = State.create_product_sort env evd dom_sort cod_sort in

      let tm = Term.mkProd_or_LetIn decl (j_val codj) in
      evd, make_judge tm (mkSort ret_sort)

  | PApp (f, arg) ->

    let evd, j_head = typecheck_pattern env names evd f in

    let evd, (argty, argrel, retty) = reduce_to_prod env evd (j_type j_head) in

    let evd, j_arg = typecheck_arg_pattern env names evd (argty, argrel) arg in

    let retty = Vars.subst1 (j_val j_arg) retty in
    let head = mkApp (j_val j_head, [|j_val j_arg|]) in
    evd, make_judge head retty

  | PProj (c, p) ->

    let evd, j_head = typecheck_pattern env names evd c in

    let ind = Projection.Repr.inductive p in

    let evd, (u, args) = reduce_to_appind env evd ind (j_type j_head) in

    let p = Projection.make p true in
    let pr, pty = lookup_projection p env in
    let pr = UVars.subst_instance_relevance u pr in
    let ty = Vars.subst_instance_constr u pty in
    let bod = mkProj (p, pr, j_val j_head) in
    evd, make_judge bod (Vars.substl (j_val j_head :: CArray.rev_to_list args) ty)

  | PCase (c, ind, ret, brs) ->

    let evd, j_head = typecheck_pattern env names evd c in
    let evd = State.add_pattern_relevance (Relevanceops.relevance_of_term env (j_val j_head)) evd in
    (* There may be a relevance change here *)

    let brs = Array.map (fun (brctx, br) -> Some brctx, br) brs in

    let evd, case, ty = indtyping_helper
      (fun env -> typecheck_arg_pattern env names) j_val
      (fun _ ctx env -> ctx, Environ.push_rel_context ctx env) (fun x -> x)
      env evd j_head ind ~pnas:(fst ret) (snd ret) brs in

    let (ci, u, pms, ((pnas, p), pr), iv, c, brs) = case in
    let body = mkCase (ci, u, pms, ((pnas, j_val p), pr), iv, c, Array.map (on_snd j_val) brs) in

    evd, make_judge body ty


and typecheck_arg_pattern env names evd (typ, relevance) = function
  | PVar index ->
    let evd, ev = declare_evar names env evd index relevance typ in
    evd, make_judge ev typ

  | Pat p ->
    let evd, j = typecheck_pattern env names evd p in
    let evd = cumul_lax env evd (j_type j) typ in
    let evd = State.add_pattern_relevance (Relevanceops.relevance_of_term env (j_val j)) evd in
    let () = check_may_eta env evd ~tryother:(j_type j) typ in
    evd, make_judge (j_val j) typ


let typecheck_pattern env names pattern =
  let auctx = UVars.AbstractContext.make { quals = names.sort_names; univs = names.level_names } PConstraints.empty in
  let evar_map = Evd.from_auctx env auctx in
  typecheck_pattern env names (State.make evar_map) pattern





(* Extract info from found equalities *)

module Imitate = struct
  type 'a imitation = Same | Reconstructed of state * 'a | Impossible

  let imitate_sort env evd cmp s =
    match s with
    | Prop | SProp -> Same
    | Set when cmp = GEQ -> Same
    | Set | Type _ | GSort _ | VSort _ ->
      let pred = sort_predicativity env s in
      let uorig = State.get_algebraic s in
      let evd, l = State.create_level evd in
      let u = Universe.make l in
      let evd =
        match cmp with
        | LEQ -> State.enforce_cmp_universe CUMUL pred uorig u evd
        | GEQ -> State.enforce_cmp_universe CUMUL pred u uorig evd
        | EQ -> assert false
      in
      Reconstructed (evd, mkSort @@ Sorts.(make (quality s) u))

  let imitate_instance evd cmp variance ui =
    let open UVars in
    let qs, us = Instance.to_array ui in
    let evd, us = Array.fold_left2_map (fun evd v l ->
      match v with
      | Variance.Covariant ->
          let evd, l' = State.create_level evd in
          let u = Universe.make l and u' = Universe.make l' in
          let evd = match cmp with
            | LEQ -> State.enforce_cmp_universe CUMUL Predicative u u' evd
            | GEQ -> State.enforce_cmp_universe CUMUL Predicative u' u evd
            | EQ -> assert false
          in
          evd, l'
      | Variance.Invariant | Variance.Irrelevant -> evd, l) evd variance us
    in
    Reconstructed (evd, Instance.of_array (qs, us))

  let rec imitate env evd defs cmp t =
    let h, s = CClosure.(whd_stack (create_clos_infos ~evars:(evar_handler_defs evd defs) RedFlags.all env) (create_tab ()) (inject t) []) in
    match CClosure.fterm_of h with
    | FEvar _ -> Impossible
    | _ ->
    let t = CClosure.term_of_process h s in
    match kind t with
    | Sort s -> imitate_sort env evd cmp s
    | Prod (na, ty, cod) ->
      begin match imitate env evd defs cmp cod with
      | Same -> Same
      | Impossible -> Impossible
      | Reconstructed (evd, cod') -> Reconstructed (evd, mkProd (na, ty, cod'))
      end
    | App (f, args) when isInd f ->
      let ind, u = destInd f in
      let mind = Environ.lookup_mind (fst ind) env in
      begin match mind.mind_variance with
      | None -> Same
      | Some variances ->
        if not (Array.exists (function UVars.Variance.Covariant -> true | _ -> false) variances) then Same else
        let num_param_arity = inductive_cumulativity_arguments (mind, snd ind) in
        if not (Int.equal num_param_arity (Array.length args)) then CErrors.anomaly Pp.(str"Imitate called on non-type.")
        else
          begin match imitate_instance evd cmp variances u with
          | Same | Impossible as r -> r
          | Reconstructed (evd, ui) ->
            Reconstructed (evd, mkApp (mkIndU (ind, ui), args))
          end
      end
    (* Arrays have no covariant levels, so the result is [Same] *)
    | _ -> (* All other types are neutral *) Same
end

let rel_inst n = SList.of_full_list (List.init n (fun i -> EConstr.mkRel (i+1)))

let add_evar_definition env evd defs evk def =
  let eqs = Evar.Map.find evk evd.evar_candidates in
  let evd = { evd with evar_candidates = Evar.Map.remove evk evd.evar_candidates } in
  let sigma = State.sigma_of evd defs in
  let evi = Evd.find_undefined sigma evk in
  let context = List.map Context.Named.Declaration.to_rel_decl (Evd.evar_context evi) in
  let env = EConstr.push_rel_context context env in
  let typ = Evd.existential_type sigma (evk, rel_inst (List.length context)) in
  if not @@ Evarsolve.noccur_evar env (State.sigma_of evd defs) evk (EConstr.of_constr def) then
    CErrors.anomaly Pp.(str "looping definition in rewrite rules")
  else
  let defs = Evar.Map.add evk def defs in
  let Refl = EConstr.Unsafe.eq in
  let Refl = EConstr.Unsafe.relevance_eq in
  let defty = Retyping.get_type_of env (State.sigma_of evd defs) def in
  let rels = List.fold_right (fun decl rels -> Range.cons (RelDecl.get_relevance decl) rels) context Range.empty in
  let evd = unify_lax rels CUMUL defs env evd defty typ in

  let evd = List.fold_left (fun evd (cmp, t) ->
    match cmp with
    | LEQ -> unify_lax rels CUMUL defs env evd t def
    | EQ  -> unify_lax rels CONV  defs env evd t def
    | GEQ -> unify_lax rels CUMUL defs env evd def t
    ) evd eqs
  in
  evd, defs

let push_evar_definitions env evd defs =
  Evar.Map.fold (fun evk eqs (evd, defs, flag) ->
    let sigma = State.sigma_of evd defs in
    let evi = Evd.find_undefined sigma evk in
    let context = List.map Context.Named.Declaration.to_rel_decl (Evd.evar_context evi) in
    let env' = EConstr.push_rel_context context env in
    match List.find_opt (fun (pb, c) -> pb = EQ && Evarsolve.noccur_evar env' sigma evk (EConstr.of_constr c)) eqs with
    | Some (_, def) ->
      let evd, defs = add_evar_definition env evd defs evk def in
      evd, defs, true
    | None ->
      let filter (pb, c) =
        if pb = EQ || not @@ Evarsolve.noccur_evar env' sigma evk (EConstr.of_constr c) then None else
        begin match Imitate.imitate env evd defs pb c with
        | Same -> Some (evd, c)
        | Reconstructed (evd, c) -> Some (evd, c)
        | Impossible -> None
        end
      in
      match List.find_map filter eqs with
      | Some (evd, def) ->
          let evd, defs = add_evar_definition env evd defs evk def in
          evd, defs, true
      | None -> evd, defs, flag

    ) evd.evar_candidates (evd, defs, false)

let push_equality env evd defs (block, eq as blocked_eq) =
  match block with
  | Evar evk ->
    if EMap.mem evk defs then
      unify_delayed env evd defs eq, true
    else
      { evd with delayed_equalities = blocked_eq :: evd.delayed_equalities }, false
  | RelVar qv ->
    match State.nf_relevance evd (RelevanceVar qv) with
    | RelevanceVar q' -> { evd with delayed_equalities = blocked_eq :: evd.delayed_equalities }, false
    | Irrelevant -> evd, false
    | Relevant -> unify_delayed env evd defs eq, true

let push_equalities env evd defs =
  let evd, equalities = { evd with delayed_equalities = [] }, evd.delayed_equalities in
  List.fold_left (fun (evd, flag) eq ->
    let evd, b = push_equality env evd defs eq in
    evd, flag || b
    ) (evd, false) equalities


let push_constraints env evd =
  let rec round evd defs =
    let evd, defs, b1 = push_evar_definitions env evd defs in

    let evd, b2 = push_equalities env evd defs in

    if b1 || b2 then
      round evd defs
    else
      evd, defs
  in
  round evd Evar.Map.empty


let check_pattern_relevances ~loc evd rels r0 =
  let r0 = UState.nf_relevance (Evd.ustate evd) r0 in
  QVar.Set.iter (fun q ->
    match UState.nf_relevance (Evd.ustate evd) (RelevanceVar q) with
    | Irrelevant -> warn_irrelevant_pattern ?loc Pp.(str "Irrelevant subpattern in rewrite rules")
    | RelevanceVar q when match r0 with RelevanceVar q' -> QVar.equal q q' | _ -> false -> ()
    | RelevanceVar _ ->
        warn_irrelevant_pattern ?loc Pp.(str "Subpattern has different relevance than whole pattern in rewrite rules")
    | Relevant -> ()
    ) rels


let rec get_pconstrapp args = function
  | PApp (p, arg) -> get_pconstrapp (arg :: args) p
  | PConstr (c, _) -> Some (c, args)
  | _ -> None
let get_pconstrapp = get_pconstrapp []

let test_projection_apps ~loc env pat =
  match get_pconstrapp pat with None -> ()
  | Some (cst, args) ->
    let ind = fst cst in
  let specif = Inductive.lookup_mind_specif env ind in
  if not @@ Inductive.is_primitive_record specif then () else
  if List.for_all_i (fun i arg ->
    match arg with
    | PVar _ -> true
    | Pat PProj (_, p) -> Ind.CanOrd.equal (Projection.Repr.inductive p) ind && Projection.Repr.arg p = i
    | Pat _ -> false
  ) 0 args then
    warn_redex_in_rewrite_rules ?loc Pp.(str " subpattern compatible with an eta-long form for " ++ Id.print (snd specif).mind_typename ++ str"," )

let rec check_pattern_redex ~loc env = function
  | PApp (PLambda _, _) -> warn_redex_in_rewrite_rules ?loc (Pp.str " beta redex")
  | PCase (p, _, _, _) | PProj (p, _) when Option.has_some @@ get_pconstrapp p -> warn_redex_in_rewrite_rules ?loc (Pp.str " iota redex")
  | PLambda _ -> warn_redex_in_rewrite_rules ?loc (Pp.str " lambda pattern")
  | PApp (p, arg) -> check_pattern_redex ~loc env p; check_pattern_redex_aux ~loc env arg
  | PCase (p, _, ret, brs) -> test_projection_apps ~loc env p; check_pattern_redex ~loc env p; check_pattern_redex_aux ~loc env (snd ret); Array.iter (snd %> check_pattern_redex_aux ~loc env) brs
  | PProj (p, _) -> test_projection_apps ~loc env p; check_pattern_redex ~loc env p
  | PProd (_, ty, bod) -> check_pattern_redex_aux ~loc env ty; check_pattern_redex_aux ~loc env bod
  | PRel _ | PInt _ | PFloat _ | PString _ | PSort _ | PInd _ | PConstr _ | PSymbol _ -> ()
and check_pattern_redex_aux ~loc env = function
  | PVar _ -> ()
  | Pat p -> check_pattern_redex ~loc env p


let finalize_state evd defs =
  let sigma = State.sigma_of evd defs in
  let sigma = Evd.freeze_sort_variables sigma in
  let sigma = Evd.fix_undefined_variables sigma in
  let sigma = Int.Map.fold (fun _ (evk, _) sigma -> Evd.set_rewrite_rule_evar sigma evk) evd.evar_index sigma in

  let names =
    let name_of_idopt = function None -> Anonymous | Some id -> Name id in
    let name_of_qualidopt = function None -> Anonymous | Some fp -> Name (Libnames.basename fp) in
    let ustate = Evd.ustate sigma in
    let evar_names = Array.init evd.nevars (fun i -> name_of_qualidopt @@ Evd.evar_ident (fst (Int.Map.find i evd.evar_index)) sigma) in
    let sort_names = Array.init evd.nqualities (fun i -> name_of_idopt @@ UState.id_of_qvar ustate (fst (Int.Map.find i evd.qualities))) in
    let level_names = Array.init evd.nlevels (fun i -> name_of_idopt @@ UState.id_of_level ustate (fst (Int.Map.find i evd.levels))) in
    { evar_names; sort_names; level_names }
  in

  let subst =
    let esubst = Int.Map.fold (fun i (ev, _) esubst -> Evar.Map.add ev i esubst) evd.evar_index Evar.Map.empty in
    let qsubst = Int.Map.fold (fun i (q, _) qsubst -> QVar.Map.add q (Quality.QVar (QVar.make_var i)) qsubst) evd.qualities QVar.Map.empty in
    let usubst = Int.Map.fold (fun i (u, _) usubst -> Level.Map.add u (Level.var i) usubst) evd.levels Level.Map.empty in
    esubst, (qsubst, usubst)
  in

  let sigma, cstrs =
    List.fold_left (fun (sigma, cstrs) (pred, c) ->
      match pred with
      | Predicative -> Evd.add_univ_constraints sigma (UnivConstraints.singleton c), cstrs
      | Impredicative -> sigma, cstrs
      | PredVar q -> match UState.nf_qvar (Evd.ustate sigma) q with
        | QConstant (QProp | QSProp) -> sigma, cstrs
        | QConstant QType | QGlobal _ -> Evd.add_univ_constraints sigma (UnivConstraints.singleton c), cstrs
        | QVar q -> sigma, QVar.Map.update q (function None -> Some (UnivConstraints.singleton c) | Some cstrs -> Some (UnivConstraints.add c cstrs)) cstrs
      ) (sigma, QVar.Map.empty) evd.ucstrs
  in

  names, subst, sigma, cstrs


let typecheck_finalize ~loc env evd pat j =
  let evd, defs = push_constraints env evd in

  let names, subst, sigma, cstrs = finalize_state evd defs in

  let r = Relevanceops.relevance_of_term env (j_val j) in
  check_pattern_relevances ~loc sigma evd.pattern_relevances r;
  check_pattern_redex ~loc env pat;

  names, subst, sigma, cstrs, pat, j


type pattern_translation_error =
  | UnknownEvar of Evar.t
  | UnknownQuality of Quality.t
  | UnknownLevel of Level.t
  | NoHeadSymbol

(* exception PatternTranslationError of rewrite_rule * pattern_translation_error *)
exception LocalPatternTranslationError of pattern_translation_error

let translate_quality_pattern = function
  | PQConstant _ | PQGlobal _ as q -> q
  | PQVar i -> PQVar (Some i)

let translate_instance (s, l) =
  let s = Array.map translate_quality_pattern s in
  let l = Array.map (fun i -> Some i) l in
  s, l

let translate_sort_pattern = function
  | PSProp | PSSProp | PSSet as sp -> sp
  | PSType i -> PSType (Some i)
  | PSGlobal (g, li) ->
    PSGlobal (g, Some li)
  | PSQSort (si, li) ->
    PSQSort (Some si, Some li)


let rec translate_pattern = function
  | PRel n -> PHRel n, []
  | PSort sp -> PHSort (translate_sort_pattern sp), []
  | PSymbol (cst, mask) -> PHSymbol (cst, translate_instance mask), []
  | PInd (ind, mask) -> PHInd (ind, translate_instance mask), []
  | PConstr (cstr, mask) -> PHConstr (cstr, translate_instance mask), []
  | PInt i -> PHInt i, []
  | PFloat f -> PHFloat f, []
  | PString s -> PHString s, []
  | PLambda (_, arg, bod) ->
      let arg = translate_arg_pattern arg in
      let bod = translate_pattern bod in
      let lambda = begin match bod with PHLambda (args, bod), [] -> PHLambda (Array.append [|arg|] args, bod) | _ -> PHLambda ([|arg|], bod) end in
      lambda, []
  | PProd (_, arg, bod) ->
      let arg = translate_arg_pattern arg in
      let bod = translate_arg_pattern bod in
      let prod = begin match bod with ERigid (PHProd (args, bod), []) -> PHProd (Array.append [|arg|] args, bod) | _ -> PHProd ([|arg|], bod) end in
      prod, []
  | PApp (f, arg) ->
      let head, elims = translate_pattern f in
      let arg = translate_arg_pattern arg in
      let elims = begin match elims with PEApp args :: elims -> PEApp (Array.append args [|arg|]) :: elims | _ -> PEApp [|arg|] :: elims end in
      head, elims
  | PCase (c, ind, ret, brs) ->
      let head, elims = translate_pattern c in
      let ret = translate_arg_pattern (snd ret) in
      let brs = Array.map (fun (_, br) -> translate_arg_pattern br) brs in
      head, PECase (ind, ret, brs) :: elims
  | PProj (c, p) ->
      let head, elims = translate_pattern c in
      head, PEProj p :: elims

and translate_pattern_rev p =
  let h, e = translate_pattern p in
  h, List.rev e

and translate_arg_pattern = function
  | PVar i -> EHole i
  | Pat p ->
      let p = translate_pattern_rev p in
      ERigid p

let translate_pattern = translate_pattern_rev

(* relocation of evars into de Bruijn indices *)
let rec evar_subst evd evmap k t =
  match EConstr.kind evd t with
  | Evar (evk, inst) -> begin
    match Evar.Map.find_opt evk evmap with
    | None -> raise (LocalPatternTranslationError (UnknownEvar evk))
    | Some n ->
        let head = EConstr.mkRel (n + 1 + k) in
        let Evd.EvarInfo evi = Evd.find evd evk in
        let vars = Evd.evar_hyps evi |> Environ.named_context_of_val |> Context.Named.instance EConstr.mkVar in
        let body = EConstr.mkApp (head, vars) in
        let inst = inst |> SList.Smart.map (evar_subst evd evmap k) in
        Evd.instantiate_evar_array evd evi body inst
    end
  | _ -> EConstr.map_with_binders evd succ (evar_subst evd evmap) k t

let test_quality env nvarqs q =
  match Sorts.Quality.var_index q with
  | Some n ->
    if n < 0 || n > nvarqs then
      CErrors.anomaly Pp.(str "Unknown sort variable in rewrite rule.")
  | None ->
      match QGraph.is_declared q (Environ.qualities env) with
      | true -> ()
      | false ->
        raise (LocalPatternTranslationError (UnknownQuality q))

let test_level env nvarus lvl =
  match Univ.Level.var_index lvl with
  | Some n ->
    if n < 0 || n > nvarus then
      CErrors.anomaly Pp.(str "Unknown universe level variable in rewrite rule")
  | None ->
      match UGraph.check_declared_universes (Environ.universes env) (Univ.Level.Set.singleton lvl) with
      | Ok () -> ()
      | Error l ->
        let lvl = Univ.Level.Set.choose l in (* Subsingleton of size 1 *)
        raise (LocalPatternTranslationError (UnknownLevel lvl))



let translate_rewrite_rule env evd { rr_uctx; rr_evars; esubst; pattern; replacement } =
  (* try *)
  let nsorts = Array.length rr_uctx.quals in
  let nlvls = Array.length rr_uctx.univs in
  let nvars = Array.length rr_evars in
  let lhs_pat = translate_pattern pattern in
  let rhs = EConstr.Unsafe.to_constr (evar_subst evd esubst 0 (EConstr.of_constr replacement)) in
  let () =
    let qs, us = Vars.sort_and_universes_of_constr rhs in
    Sorts.Quality.Set.iter (test_quality env nsorts) qs;
    Univ.Level.Set.iter (test_level env nlvls) us
  in
  let symb, head_umask, elims = match lhs_pat with
    | PHSymbol (symb, mask), elims -> symb, mask, elims
    | _ -> raise (LocalPatternTranslationError NoHeadSymbol)
  in

  symb, { nvars = (nvars, nsorts, nlvls); lhs_pat = (head_umask, elims); rhs }
  (* with LocalPatternTranslationError e as exn ->
    let _, info = Exninfo.capture exn in
    Exninfo.iraise (PatternTranslationError (rule, e), info) *)

let rec head_symbol = function
  | PSymbol (cst, _) -> cst
  | PApp (f, _) -> head_symbol f
  | PCase (c, _, _, _) -> head_symbol c
  | PProj (c, _) -> head_symbol c
  | PRel _ | PSort _ | PInd _ | PConstr _ | PInt _ | PFloat _ | PString _ | PLambda _ | PProd _ ->
    invalid_arg "No head symbol"

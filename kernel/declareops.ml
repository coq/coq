(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Mod_subst
open Util

module RelDecl = Context.Rel.Declaration

let noh hcons x = snd (hcons x)

(** Operations concernings types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

let configure_enabled_native = match Coq_config.native_compiler with
  | NativeOff -> false
  | NativeOn _ -> true

let safe_flags oracle = {
  check_guarded = true;
  check_positive = true;
  check_eliminations = true;
  check_universes = true;
  conv_oracle = oracle;
  share_reduction = true;
  unfold_dep_heuristic = false;
  unfold_height_heuristic = false;
  enable_VM = Coq_config.bytecode_compiler;
  enable_native_compiler = configure_enabled_native;
  indices_matter = true;
  impredicative_set = false;
  sprop_allowed = true;
  allow_uip = false;
}

(** {6 Arities } *)

let hcons_template_universe ar =
  { template_param_arguments = List.Smart.map (Option.Smart.map (noh Sorts.hcons)) ar.template_param_arguments;
    template_concl = noh Sorts.hcons ar.template_concl;
    template_context = noh UVars.AbstractContext.hcons ar.template_context;
    template_defaults = noh UVars.Instance.hcons ar.template_defaults;
  }

let universes_context = function
  | Monomorphic -> UVars.AbstractContext.empty
  | Polymorphic ctx -> ctx

let abstract_universes = function
  | Entries.Monomorphic_entry ->
    Monomorphic
  | Entries.Polymorphic_entry auctx ->
    Polymorphic auctx

(** {6 Constants } *)

let constant_is_polymorphic cb =
  match cb.const_universes with
  | Monomorphic -> false
  | Polymorphic _ -> true


let constant_has_body cb = match cb.const_body with
  | Undef _ | Primitive _ | Symbol _ -> false
  | Def _ | OpaqueDef _ -> true

let constant_polymorphic_context cb =
  universes_context cb.const_universes

let is_opaque cb = match cb.const_body with
  | OpaqueDef _ -> true
  | Undef _ | Def _ | Primitive _ | Symbol _ -> false

(** {7 Constant substitutions } *)

let subst_rel_declaration subst =
  RelDecl.map_constr (subst_mps subst)

let subst_rel_context subst = List.Smart.map (subst_rel_declaration subst)

let subst_const_type subst arity =
  if is_empty_subst subst then arity
  else subst_mps subst arity

(** No need here to check for physical equality after substitution,
    at least for Def due to the delayed substitution [subst_constr_subst]. *)
let subst_const_def subst def = match def with
  | Undef _ | Primitive _ | Symbol _ -> def
  | Def c -> Def (subst_mps subst c)
  | OpaqueDef o -> OpaqueDef (Opaqueproof.subst_opaque subst o)

let subst_const_body subst cb =
  (* we're outside sections *)
  assert (List.is_empty cb.const_hyps && UVars.Instance.is_empty cb.const_univ_hyps);
  if is_empty_subst subst then cb
  else
    let body' = subst_const_def subst cb.const_body in
    let type' = subst_const_type subst cb.const_type in
    if body' == cb.const_body && type' == cb.const_type
    then cb
    else
      { const_hyps = [];
        const_univ_hyps = UVars.Instance.empty;
        const_body = body';
        const_type = type';
        const_body_code = Vmemitcodes.subst_body_code subst cb.const_body_code;
        const_universes = cb.const_universes;
        const_relevance = cb.const_relevance;
        const_inline_code = cb.const_inline_code;
        const_typing_flags = cb.const_typing_flags;
        (* FIXME: Does not reflect reality for functorized code. Beware when using modules and sections. *)
        const_def_height = cb.const_def_height }

(** {7 Hash-consing of constants } *)

(** This hash-consing is currently quite partial : we only
    share internal fields (e.g. constr), and not the records
    themselves. But would it really bring substantial gains ? *)

let hcons_rel_decl =
  RelDecl.map_name (noh Names.Name.hcons) %> RelDecl.map_value (noh Constr.hcons) %> RelDecl.map_type (noh Constr.hcons)

let hcons_rel_context l = List.Smart.map hcons_rel_decl l

let hcons_const_def ?(hbody=noh Constr.hcons) = function
  | Undef inl -> Undef inl
  | Primitive p -> Primitive p
  | Symbol r -> Symbol r
  | Def l_constr ->
    Def (hbody l_constr)
  | OpaqueDef _ as x -> x (* hashconsed when turned indirect *)

let hcons_universes cbu =
  match cbu with
  | Monomorphic -> Monomorphic
  | Polymorphic ctx ->
    Polymorphic (noh UVars.AbstractContext.hcons ctx)

let hcons_const_body ?hbody cb =
  { cb with
    const_body = hcons_const_def ?hbody cb.const_body;
    const_type = noh Constr.hcons cb.const_type;
    const_universes = hcons_universes cb.const_universes;
  }

(** {6 Inductive types } *)

let compare_recarg_type t1 t2 = match t1, t2 with
| RecArgInd ind1, RecArgInd ind2 -> Names.Ind.CanOrd.compare ind1 ind2
| RecArgInd _, RecArgPrim _ -> -1
| RecArgPrim c1, RecArgPrim c2 -> Names.Constant.CanOrd.compare c1 c2
| RecArgPrim _, RecArgInd _ -> 1

let compare_recarg r1 r2 = match r1, r2 with
| Norec, Norec -> 0
| Norec, Mrec _ -> -1
| Mrec t1, Mrec t2 -> compare_recarg_type t1 t2
| Mrec _, Norec -> 1

let eq_recarg r1 r2 = Int.equal (compare_recarg r1 r2) 0

let pr_recarg_type = let open Pp in function
  | RecArgInd (mind,i) ->
     str "Mrec[" ++ Names.MutInd.print mind ++ pr_comma () ++ int i ++ str "]"
  | RecArgPrim c ->
     str "Prim[" ++ Names.Constant.print c ++ str "]"

let pr_recarg = let open Pp in function
  | Declarations.Norec -> str "Norec"
  | Declarations.Mrec t -> pr_recarg_type t

let pr_wf_paths x = Rtree.pr_tree pr_recarg x

let subst_recarg_type subst ty = match ty with
| RecArgInd (kn,i) ->
  let kn' = subst_mind subst kn in
  if kn==kn' then ty else RecArgInd (kn',i)
| RecArgPrim c ->
  let c',_ = subst_con subst c in
  if c==c' then ty else RecArgPrim c'

let subst_recarg subst r = match r with
  | Norec -> r
  | Mrec ty ->
    let ty' = subst_recarg_type subst ty in
    if ty==ty' then r else Mrec ty'

let mk_norec = Rtree.mk_node Norec [||]

let mk_paths r recargs =
  Rtree.mk_node r
    (Array.map Array.of_list recargs)

let dest_recarg p = Rtree.dest_head p

(* dest_subterms returns the sizes of each argument of each constructor of
   an inductive object of size [p]. This should never be done for Norec,
   because the number of sons does not correspond to the number of
   constructors.
 *)
let dest_subterms p =
  let (ra,cstrs) = Rtree.dest_node p in
  assert (match ra with Norec -> false | _ -> true);
  Array.map Array.to_list cstrs

let subst_automaton subst a =
  Rtree.Automaton.map (fun r -> subst_recarg subst r) a

(** {7 Substitution of inductive declarations } *)

let subst_mind_record subst r = match r with
| NotRecord -> NotRecord
| FakeRecord -> FakeRecord
| PrimRecord ({ tys; _ } as infos) ->
    let tys' = Array.Smart.map (subst_mps subst) tys in
    if tys' == tys then r
    else PrimRecord { infos with tys = tys' }

let subst_mind_packet subst mbp =
  { mind_consnames = mbp.mind_consnames;
    mind_consnrealdecls = mbp.mind_consnrealdecls;
    mind_consnrealargs = mbp.mind_consnrealargs;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = Array.Smart.map (fun (ctx, c) -> Context.Rel.map (subst_mps subst) ctx, subst_mps subst c) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context subst mbp.mind_arity_ctxt;
    mind_user_arity = subst_mps subst mbp.mind_user_arity;
    mind_sort = mbp.mind_sort;
    mind_record = subst_mind_record subst mbp.mind_record;
    mind_user_lc = Array.Smart.map (subst_mps subst) mbp.mind_user_lc;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_nrealdecls = mbp.mind_nrealdecls;
    mind_squashed = mbp.mind_squashed;
    mind_automaton = subst_automaton subst mbp.mind_automaton;
    mind_relevance = mbp.mind_relevance;
    mind_relies_on_indices_not_mattering = mbp.mind_relies_on_indices_not_mattering;
    mind_nb_constant = mbp.mind_nb_constant;
    mind_nb_args = mbp.mind_nb_args;
    mind_reloc_tbl = mbp.mind_reloc_tbl }

let subst_mind_body subst mib =
  (* we're outside sections *)
  assert (List.is_empty mib.mind_hyps && UVars.Instance.is_empty mib.mind_univ_hyps);
  { mind_finite = mib.mind_finite ;
    mind_hyps = [];
    mind_univ_hyps = UVars.Instance.empty;
    mind_nparams = mib.mind_nparams;
    mind_nparams_rec = mib.mind_nparams_rec;
    mind_params_ctxt =
      Context.Rel.map (subst_mps subst) mib.mind_params_ctxt;
    mind_packets = Array.Smart.map (subst_mind_packet subst) mib.mind_packets ;
    mind_universes = mib.mind_universes;
    mind_template = mib.mind_template;
    mind_variance = mib.mind_variance;
    mind_sec_variance = mib.mind_sec_variance;
    mind_private = mib.mind_private;
    mind_typing_flags = mib.mind_typing_flags;
  }

let mind_ntypes mib = Array.length mib.mind_packets

let inductive_polymorphic_context mib =
  universes_context mib.mind_universes

let inductive_is_polymorphic mib =
  match mib.mind_universes with
  | Monomorphic -> false
  | Polymorphic _ctx -> true

let inductive_is_cumulative mib =
  Option.has_some mib.mind_variance

let inductive_make_projection ind mib ~proj_arg =
  match mib.mind_packets.(snd ind).mind_record with
  | NotRecord | FakeRecord ->
    CErrors.anomaly Pp.(str "inductive_make_projection: not a primitive record.")
  | PrimRecord { projections; relevances; _ } ->
    if proj_arg < 0 || Array.length projections <= proj_arg
    then CErrors.anomaly Pp.(str "inductive_make_projection: invalid proj_arg.");
    let p = Names.Projection.Repr.make ind
      ~proj_npars:mib.mind_nparams
      ~proj_arg
    in
    p, relevances.(proj_arg)

let inductive_make_projections ind mib =
  match mib.mind_packets.(snd ind).mind_record with
  | NotRecord | FakeRecord -> None
  | PrimRecord { relevances; _ } ->
    let projs = Array.mapi (fun proj_arg r ->
        Names.Projection.Repr.make ind ~proj_npars:mib.mind_nparams ~proj_arg, r)
        relevances
    in
    Some projs

let has_valid_relevance u ind_relevance flds =
  let ind_relevance = UVars.subst_instance_relevance u ind_relevance in
  let flds = Array.map (UVars.subst_instance_relevance u) flds in
  match ind_relevance with
  | Sorts.Irrelevant -> true
  | Sorts.Relevant -> Array.exists Sorts.is_relevant flds
  | Sorts.RelevanceVar qv ->
    Array.for_all (fun r -> match r with
        | Sorts.Relevant -> true
        | Sorts.Irrelevant -> false
        | Sorts.RelevanceVar qv' -> Sorts.QVar.equal qv qv') flds

let is_record_with_eta (_,mip) u =
  match mip.mind_record with
  | NotRecord | FakeRecord -> false
  | PrimRecord r ->
    match r.has_eta with
    | NoEta -> false
    | MaybeEta ->
      has_valid_relevance u mip.mind_relevance r.relevances
    | AlwaysEta -> true

(** {6 Hash-consing of inductive declarations } *)

(** Just as for constants, this hash-consing is quite partial *)

let hcons_mind_packet oib =
  let user = Array.Smart.map (noh Constr.hcons) oib.mind_user_lc in
  let map (ctx, c) = Context.Rel.map (noh Constr.hcons) ctx, noh Constr.hcons c in
  let nf = Array.Smart.map map oib.mind_nf_lc in
  { oib with
    mind_typename = noh Names.Id.hcons oib.mind_typename;
    mind_arity_ctxt = hcons_rel_context oib.mind_arity_ctxt;
    mind_user_arity = noh Constr.hcons oib.mind_user_arity;
    mind_sort = noh Sorts.hcons oib.mind_sort;
    mind_consnames = Array.Smart.map (noh Names.Id.hcons) oib.mind_consnames;
    mind_user_lc = user;
    mind_nf_lc = nf }

let hcons_mind mib =
  { mib with
    mind_packets = Array.Smart.map hcons_mind_packet mib.mind_packets;
    mind_params_ctxt = hcons_rel_context mib.mind_params_ctxt;
    mind_template = Option.Smart.map hcons_template_universe mib.mind_template;
    mind_universes = hcons_universes mib.mind_universes }


let smart_on_snd f (a, b as p) =
  let b' = f b in
  if b == b' then p else (a, b')

let subst_pattern subst p =
  let open Declarations in
  let rec on_pat p = match p with
    | PSymbol (cst, mask) ->
      let cst' = subst_constant subst cst in
      if cst' == cst then p else
        PSymbol (cst', mask)
    | PInd (ind, mask) ->
        let ind' = subst_ind subst ind in
        if ind'==ind then p else PInd (ind', mask)
    | PConstr (cstr, mask) ->
        let cstr' = subst_constructor subst cstr in
        if cstr'==cstr then p else PConstr (cstr', mask)
    | PCase (c, ind, r, brs) ->
      let ind' = subst_ind subst ind in
      let c' = on_pat c in
      let r' = smart_on_snd on_arg_pat r in
      let brs' = Array.Smart.map (smart_on_snd on_arg_pat) brs in
      if ind' == ind && c' == c && r' == r && brs' == brs then p else
        PCase (c', ind', r', brs')
    | PProj (c, pr) ->
        let pr' = subst_proj_repr subst pr in
        let c' = on_pat c in
        if pr' == pr && c' == c then p else
          PProj (c', pr')
    | PLambda (na, ty, bod) ->
        let ty' = on_arg_pat ty in
        let bod' = on_pat bod in
        if ty' == ty && bod' == bod then p else
          PLambda (na, ty', bod')
    | PProd (na, dom, codom) ->
        let dom' = on_arg_pat dom in
        let codom' = on_arg_pat codom in
        if dom' == dom && codom' == codom then p else
          PProd (na, dom', codom')
    | PApp (f, arg) ->
      let f' = on_pat f in
      let arg' = on_arg_pat arg in
      if f' == f && arg' == arg then p else
        PApp (f', arg')
    | PRel _ | PSort _ | PInt _ | PFloat _ | PString _ as p -> p
  and on_arg_pat = function
    | Pat pat as argpat ->
        let pat' = on_pat pat in
        if pat == pat' then argpat else Pat pat'
    | PVar _ as argpat -> argpat
  in
  on_pat p


let subst_machine_pattern subst p =
  let open Declarations in
  let rec on_head p = match p with
  | PHSymbol (cst, mask) ->
    let cst' = subst_constant subst cst in
    if cst' == cst then p else PHSymbol (cst', mask)
  | PHInd (ind, mask) ->
    let ind' = subst_ind subst ind in
    if ind'==ind then p else PHInd (ind', mask)
  | PHConstr (cstr, mask) ->
    let cstr' = subst_constructor subst cstr in
    if cstr'==cstr then p else PHConstr (cstr', mask)
  | PHLambda (tys, bod) ->
    let tys' = Array.Smart.map on_arg_pat tys in
    let bod' = on_pat bod in
    if tys' == tys && bod' == bod then p else
      PHLambda (tys', bod')
  | PHProd (doms, codom) ->
    let doms' = Array.Smart.map on_arg_pat doms in
    let codom' = on_arg_pat codom in
    if doms' == doms && codom' == codom then p else
      PHProd (doms', codom')
  | PHRel _ | PHSort _ | PHInt _ | PHFloat _ | PHString _ as p -> p
  and on_elim e = match e with
  | PEApp args ->
    let args' = Array.Smart.map on_arg_pat args in
    if args' == args then e else
      PEApp args'
  | PECase (ind, r, brs) ->
    let ind' = subst_ind subst ind in
    let r' = on_arg_pat r in
    let brs' = Array.Smart.map on_arg_pat brs in
    if ind' == ind && r' == r && brs' == brs then e else
      PECase (ind', r', brs')
  | PEProj pr ->
    let pr' = subst_proj_repr subst pr in
    if pr' == pr then e else PEProj pr'
  and on_pat (h, e as p) =
    let h' = on_head h in
    let e' = List.Smart.map on_elim e in
    if h == h' && e == e' then p else (h', e')
  and on_arg_pat ap = match ap with
  | ERigid p ->
    let p' = on_pat p in
    if p == p' then ap else ERigid p'
  | EHole _ | EHoleIgnored -> ap
  in
  on_pat p

let subst_rewrite_rules subst ({ rewrules_rules; rewrules_machine } as rules) =
  let body' = List.Smart.map (fun rule ->
      let pattern' = subst_pattern subst rule.pattern in
      let replacement' = subst_mps subst rule.replacement in
      if
        pattern' == rule.pattern &&
        replacement' == rule.replacement
      then
        rule
      else
        { rr_uctx = rule.rr_uctx; rr_evars = rule.rr_evars; esubst = rule.esubst;
          pattern=pattern'; replacement=replacement'
        })
      rewrules_rules
  in
  let machine' = List.Smart.map (fun (cst, { nvars; lhs_pat = (u, e); rhs } as rule) ->
    let lhs_pat' = subst_machine_pattern subst (PHSymbol (cst, u), e) in
    let cst', u', e' = match lhs_pat' with
    | PHSymbol (cst', u'), e' -> cst', u', e'
    | _ -> assert false
    in
    let rhs' = subst_mps subst rhs in
    if cst == cst' && u == u' && e == e' && rhs == rhs' then
      rule
    else (cst', { nvars; lhs_pat = (u', e'); rhs = rhs' })
    ) rewrules_machine
  in
  if rewrules_rules == body' && rewrules_machine == machine' then rules else
    { rewrules_rules = body'; rewrules_machine = machine' }

(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre out of V6.3 file constants.ml
   as part of the rebuilding of Coq around a purely functional
   abstract type-checker, Nov 1999 *)

(* This module implements kernel-level discharching of local
   declarations over global constants and inductive types *)

open Util
open Names
open Term
open Constr
open Declarations
open Univ
open Context

module NamedDecl = Context.Named.Declaration
module RelDecl = Context.Rel.Declaration

(*s Cooking the constants. *)

type my_global_reference =
  | ConstRef of Constant.t
  | IndRef of inductive
  | ConstructRef of constructor

module RefHash =
struct
  type t = my_global_reference
  let equal gr1 gr2 = match gr1, gr2 with
  | ConstRef c1, ConstRef c2 -> Constant.SyntacticOrd.equal c1 c2
  | IndRef i1, IndRef i2 -> Ind.SyntacticOrd.equal i1 i2
  | ConstructRef c1, ConstructRef c2 -> Construct.SyntacticOrd.equal c1 c2
  | _ -> false
  open Hashset.Combine
  let hash = function
  | ConstRef c -> combinesmall 1 (Constant.SyntacticOrd.hash c)
  | IndRef i -> combinesmall 2 (Ind.SyntacticOrd.hash i)
  | ConstructRef c -> combinesmall 3 (Construct.SyntacticOrd.hash c)
end

module RefTable = Hashtbl.Make(RefHash)

let instantiate_my_gr gr u =
  match gr with
  | ConstRef c -> mkConstU (c, u)
  | IndRef i -> mkIndU (i, u)
  | ConstructRef c -> mkConstructU (c, u)

let share cache r (cstl,knl) =
  try RefTable.find cache r
  with Not_found ->
  let inst =
    match r with
    | IndRef (kn,_i) ->
        Mindmap.find kn knl
    | ConstructRef ((kn,_i),_j) ->
        Mindmap.find kn knl
    | ConstRef cst ->
        Cmap.find cst cstl in
  RefTable.add cache r inst;
  inst

let share_univs cache r u l =
  let {abstr_uinst;abstr_inst} = share cache r l in
    mkApp (instantiate_my_gr r (Instance.append abstr_uinst u), abstr_inst)

let discharge_proj_repr r p = (* To merge with discharge_proj *)
  let newpars = r.abstr_inst in
  let map npars = npars + Array.length newpars in
  Projection.Repr.map_npars map p

let discharge_proj r p =
  let newpars = r.abstr_inst in
  let map npars = npars + Array.length newpars in
  Projection.map_npars map p

let is_empty_modlist (cm, mm) =
  Cmap.is_empty cm && Mindmap.is_empty mm

let expand_constr cache modlist c =
  let share_univs = share_univs cache in
  let rec substrec c =
    match kind c with
      | Case (ci, u, pms, p, iv, t, br) ->
        begin match share cache (IndRef ci.ci_ind) modlist with
        | {abstr_uinst;abstr_inst} ->
          let u = Instance.append abstr_uinst u in
          let pms = Array.append abstr_inst pms in
          let ci = { ci with ci_npar = ci.ci_npar + Array.length abstr_inst } in
          Constr.map substrec (mkCase (ci,u,pms,p,iv,t,br))
        | exception Not_found ->
          Constr.map substrec c
        end

      | Ind (ind,u) ->
          (try
            share_univs (IndRef ind) u modlist
           with
            | Not_found -> Constr.map substrec c)

      | Construct (cstr,u) ->
          (try
             share_univs (ConstructRef cstr) u modlist
           with
            | Not_found -> Constr.map substrec c)

      | Const (cst,u) ->
          (try
            share_univs (ConstRef cst) u modlist
           with
            | Not_found -> Constr.map substrec c)

      | Proj (p, c') ->
          let ind = Names.Projection.inductive p in
          let p' =
            try
              let exp = share cache (IndRef ind) modlist in
              discharge_proj exp p
            with Not_found -> p in
          let c'' = substrec c' in
          if p == p' && c' == c'' then c else mkProj (p', c'')

  | _ -> Constr.map substrec c

  in
  if is_empty_modlist modlist then c
  else substrec c

(** Cooking is made of 4 steps:
    1. expansion of global constants by applying them to the section
       subcontext they depend on
    2. substitution of named universe variables by de Bruijn universe variables
    3. substitution of named term variables by de Bruijn term variables
    3. generalization of terms over the section subcontext they depend on
       (note that the generalization over universe variable is implicit) *)

(** The main expanding/substitution functions, performing the three first steps *)
let expand_subst cache expand_info abstr_info c =
  let c = expand_constr cache expand_info c in
  let c = Vars.subst_univs_level_constr abstr_info.abstr_ausubst c in
  let c = Vars.subst_vars abstr_info.abstr_subst c in
  c

(** Adding the final abstraction step, term case *)
let abstract_as_type cache { expand_info; abstr_info; _ } t =
  it_mkProd_wo_LetIn (expand_subst cache expand_info abstr_info t) abstr_info.abstr_ctx

(** Adding the final abstraction step, type case *)
let abstract_as_body cache { expand_info; abstr_info; _ } c =
  it_mkLambda_or_LetIn (expand_subst cache expand_info abstr_info c) abstr_info.abstr_ctx

(** Absorb a named context in the transformation which turns a
    judgment [G, Δ ⊢ ΠΩ.J] into [⊢ ΠG.ΠΔ.((ΠΩ.J)[σ][τ])], that is,
    produces the context [Δ(Ω[σ][τ])] and substitutions [σ'] and [τ]
    that turns a judgment [G, Δ, Ω[σ][τ] ⊢ J] into [⊢ ΠG.ΠΔ.((ΠΩ.J)[σ][τ])]
    via [⊢ ΠG.ΠΔ.Π(Ω[σ][τ]).(J[σ'][τ])] *)
let abstract_named_context expand_info abstr_info hyps =
  let cache = RefTable.create 13 in
  let fold decl abstr_info =
    let id, decl = match decl with
    | NamedDecl.LocalDef (id, b, t) ->
      let b = expand_subst cache expand_info abstr_info b in
      let t = expand_subst cache expand_info abstr_info t in
      id, RelDecl.LocalDef (map_annot Name.mk_name id, b, t)
    | NamedDecl.LocalAssum (id, t) ->
      let t = expand_subst cache expand_info abstr_info t in
      id, RelDecl.LocalAssum (map_annot Name.mk_name id, t)
    in
    { abstr_info with
        abstr_ctx = decl :: abstr_info.abstr_ctx;
        abstr_subst = id.binder_name :: abstr_info.abstr_subst }
  in
  Context.Named.fold_outside fold hyps ~init:abstr_info

(** Turn a named context [Δ] (hyps) and a universe named context
    [G] (uctx) into a rel context and abstract universe context
    respectively; computing also the substitution [σ] and universe
    substitution [τ] such that if [G, Δ ⊢ J] is valid then
    [⊢ ΠG.ΠΔ.(J[σ][τ])] is too, that is, it produces the substitutions
    which turns named binders into de Bruijn binders; computing also
    the instance to apply to take the generalization into account;
    collecting the information needed to do such as a transformation
    of judgment into a [cooking_info] *)
let make_cooking_info expand_info hyps uctx =
  let abstr_inst = Named.instance mkVar hyps in
  let abstr_uinst, abstr_auctx = abstract_universes uctx in
  let abstr_ausubst = Univ.make_instance_subst abstr_uinst in
  let abstr_info = { abstr_ctx = []; abstr_subst = []; abstr_auctx; abstr_ausubst } in
  let abstr_info = abstract_named_context expand_info abstr_info hyps in
  let abstr_inst_info = { abstr_inst; abstr_uinst } in
  let names_info = Context.Named.to_vars hyps in
  { expand_info; abstr_info; abstr_inst_info; names_info }

type inline = bool

type 'opaque result = {
  cook_body : (constr, 'opaque) constant_def;
  cook_type : types;
  cook_universes : universes;
  cook_relevance : Sorts.relevance;
  cook_inline : inline;
  cook_context : Id.Set.t option;
  cook_flags : typing_flags;
}

let discharge_abstract_universe_context abstr auctx =
  (** Given a substitution [abstr.abstr_ausubst := u₀ ... uₙ₋₁] together with an abstract
      context [abstr.abstr_ctx := 0 ... n - 1 |= C{0, ..., n - 1}] of the same length,
      and another abstract context relative to the former context
      [auctx := 0 ... m - 1 |= C'{u₀, ..., uₙ₋₁, 0, ..., m - 1}],
      construct the lifted abstract universe context
      [0 ... n - 1 n ... n + m - 1 |=
        C{0, ... n - 1} ∪
        C'{0, ..., n - 1, n, ..., n + m - 1} ]
      together with the substitution
      [u₀ ↦ Var(0), ... ,uₙ₋₁ ↦ Var(n - 1), Var(0) ↦  Var(n), ..., Var(m - 1) ↦  Var (n + m - 1)].
  *)
  let open Univ in
  let n = AbstractContext.size abstr.abstr_auctx in
  if (Int.equal n 0) then
    (** Optimization: still need to take the union for the constraints between globals *)
    abstr, AbstractContext.union abstr.abstr_auctx auctx
  else
    let subst = abstr.abstr_ausubst in
    let ainst = make_abstract_instance auctx in
    let substf = Univ.lift_level_subst n (make_instance_subst ainst) in
    let substf = Univ.merge_level_subst subst substf in
    let auctx = Univ.subst_univs_level_abstract_universe_context substf auctx in
    let auctx' = AbstractContext.union abstr.abstr_auctx auctx in
    { abstr with abstr_ausubst = substf }, auctx'

let lift_poly_univs info auctx =
  (** The constant under consideration is quantified over a
      universe context [auctx]; it has to be quantified further over
      [abstr.abstr_auctx] leading to a new abstraction recipe valid
      under the quantification; that is if we had a judgment
      [G, Δ ⊢ ΠG'.J] to be turned, thanks to [abstr] =
      [{ctx:=Δ;uctx:=G;subst:=σ;usubst:=τ}], into
      [⊢ ΠG.ΠΔ.(ΠG'.J)[σ][τ])], we build the new
      [{ctx:=Δ;uctx:=G(G'[ττ']);subst:=σ;usubst:=ττ'}], for some [τ']
      built by [discharge_abstract_universe_context], that works on
      [J], that is, that allows to turn [GG'[ττ'], Δ ⊢ J] into
      [⊢ ΠG.ΠΔ.(ΠG'.J)[σ][τ]] via [⊢ ΠG(G'[ττ']).ΠΔ.(J[σ][ττ'])] *)
  let abstr_info, auctx = discharge_abstract_universe_context info.abstr_info auctx in
  { info with abstr_info }, auctx

let lift_univs info = function
  | Monomorphic ->
    assert (AbstractContext.is_empty info.abstr_info.abstr_auctx); (* No monorphic constants in a polymorphic section *)
    info, Monomorphic
  | Polymorphic auctx ->
    let info, auctx = lift_poly_univs info auctx in
    info, Polymorphic auctx

let subst_private_univs info = function
  | Opaqueproof.PrivateMonomorphic () as priv ->
    let () = assert (AbstractContext.is_empty info.abstr_info.abstr_auctx) in
    let () = assert (is_empty_level_subst info.abstr_info.abstr_ausubst) in
    priv
  | Opaqueproof.PrivatePolymorphic (inst, cstrs) ->
    let cstrs = Univ.subst_univs_level_constraints info.abstr_info.abstr_ausubst cstrs in
    Opaqueproof.PrivatePolymorphic (inst, cstrs)

(********************************)
(* Discharging opaque proof terms *)

let cook_opaque_proofterm info c =
  let fold info (c, priv) =
    let priv = subst_private_univs info priv in
    let c = abstract_as_body (RefTable.create 13) info c in
    (c, priv)
  in
  List.fold_right fold info c

(********************************)
(* Discharging constant         *)

let cook_constant env info cb =
  let cache = RefTable.create 13 in
  (* Adjust the info so that it is meaningful under the block of quantified universe binders *)
  let info, univs = lift_univs info cb.const_universes in
  let map c = abstract_as_body cache info c in
  let body = match cb.const_body with
  | Undef _ as x -> x
  | Def cs -> Def (map cs)
  | OpaqueDef o ->
    OpaqueDef (Opaqueproof.discharge_opaque info o)
  | Primitive _ -> CErrors.anomaly (Pp.str "Primitives cannot be cooked")
  in
  let tps = Vmbytegen.compile_constant_body ~fail_on_error:false env univs body in
  let typ = abstract_as_type cache info cb.const_type in
  let hyps = List.filter (fun d -> not (Id.Set.mem (NamedDecl.get_id d) info.names_info)) cb.const_hyps in
  {
    const_hyps = hyps;
    const_body = body;
    const_type = typ;
    const_body_code = tps;
    const_universes = univs;
    const_relevance = cb.const_relevance;
    const_inline_code = cb.const_inline_code;
    const_typing_flags = cb.const_typing_flags;
  }

(********************************)
(* Discharging mutual inductive *)

let cook_rel_context cache info ctx =
  (* Dealing with substitutions between contexts is too annoying, so
     we reify [ctx] into a big [forall] term and work on that. *)
  let t = it_mkProd_or_LetIn mkProp ctx in
  let t = abstract_as_type cache info t in
  let ctx, t = decompose_prod_assum t in
  assert (Constr.equal t mkProp);
  ctx

let cook_lc cache ~ntypes info t =
  (* Expand the recursive call to the inductive types *)
  let diff = List.length info.abstr_info.abstr_ctx in
  let subs = List.init ntypes (fun k -> mkApp (mkRel (k+diff+1), info.abstr_inst_info.abstr_inst)) in
  let t = Vars.substl subs t in
  (* Apply the abstraction *)
  abstract_as_type cache info t

let cook_projection cache ~params info t =
  let t = mkArrowR mkProp t in (* dummy type standing in for the inductive *)
  let t = it_mkProd_or_LetIn t params in
  let t = abstract_as_type cache info t in
  let _, t = decompose_prod_n_assum (List.length params + 1 + Context.Rel.nhyps info.abstr_info.abstr_ctx) t in
  t

let cook_one_ind cache ~ntypes info mip =
  let mind_arity = match mip.mind_arity with
    | RegularArity {mind_user_arity=arity;mind_sort=sort} ->
      let arity = abstract_as_type cache info arity in
      let sort = destSort (expand_subst cache info.expand_info info.abstr_info (mkSort sort)) in
      RegularArity {mind_user_arity=arity; mind_sort=sort}
    | TemplateArity {template_level} ->
      TemplateArity {template_level}
  in
  let mind_arity_ctxt = cook_rel_context cache info mip.mind_arity_ctxt in
  let mind_user_lc = Array.map (cook_lc cache ~ntypes info) mip.mind_user_lc in
  let mind_nf_lc = Array.map (fun (ctx,t) ->
      let lc = it_mkProd_or_LetIn t ctx in
      let lc = cook_lc cache ~ntypes info lc in
      decompose_prod_assum lc)
      mip.mind_nf_lc
  in
  { mind_typename = mip.mind_typename;
    mind_arity_ctxt;
    mind_arity;
    mind_consnames = mip.mind_consnames;
    mind_user_lc;
    mind_nrealargs = mip.mind_nrealargs;
    mind_nrealdecls = mip.mind_nrealdecls;
    mind_kelim = mip.mind_kelim;
    mind_nf_lc;
    mind_consnrealargs = mip.mind_consnrealargs;
    mind_consnrealdecls = mip.mind_consnrealdecls;
    mind_recargs = mip.mind_recargs;
    mind_relevance = mip.mind_relevance;
    mind_nb_constant = mip.mind_nb_constant;
    mind_nb_args = mip.mind_nb_args;
    mind_reloc_tbl = mip.mind_reloc_tbl;
  }

let cook_inductive info mib =
  let info, mind_universes = lift_univs info mib.mind_universes in
  let cache = RefTable.create 13 in
  let nnewparams = Context.Rel.nhyps info.abstr_info.abstr_ctx in
  let mind_params_ctxt = cook_rel_context cache info mib.mind_params_ctxt in
  let ntypes = mib.mind_ntypes in
  let mind_packets = Array.map (cook_one_ind cache ~ntypes info) mib.mind_packets in
  let mind_record = match mib.mind_record with
    | NotRecord -> NotRecord
    | FakeRecord -> FakeRecord
    | PrimRecord data ->
      let data = Array.map (fun (id,projs,relevances,tys) ->
          let tys = Array.map (cook_projection cache ~params:mib.mind_params_ctxt info) tys in
          (id,projs,relevances,tys))
          data
      in
      PrimRecord data
  in
  let mind_hyps =
    List.filter (fun d -> not (Id.Set.mem (NamedDecl.get_id d) info.names_info))
      mib.mind_hyps
  in
  let mind_variance, mind_sec_variance =
    match mib.mind_variance, mib.mind_sec_variance with
    | None, None -> None, None
    | None, Some _ | Some _, None -> assert false
    | Some variance, Some sec_variance ->
      let sec_variance, newvariance =
        Array.chop (Array.length sec_variance - AbstractContext.size info.abstr_info.abstr_auctx)
          sec_variance
      in
      Some (Array.append newvariance variance), Some sec_variance
  in
  let mind_template = match mib.mind_template with
  | None -> None
  | Some {template_param_levels=levels; template_context} ->
      let sec_levels = CList.map_filter (fun d ->
          if RelDecl.is_local_assum d then Some None
          else None)
          info.abstr_info.abstr_ctx
      in
      let levels = List.rev_append sec_levels levels in
      Some {template_param_levels=levels; template_context}
  in
  {
    mind_packets;
    mind_record;
    mind_finite = mib.mind_finite;
    mind_ntypes = mib.mind_ntypes;
    mind_hyps;
    mind_nparams = mib.mind_nparams + nnewparams;
    mind_nparams_rec = mib.mind_nparams_rec + nnewparams;
    mind_params_ctxt;
    mind_universes;
    mind_template;
    mind_variance;
    mind_sec_variance;
    mind_private = mib.mind_private;
    mind_typing_flags = mib.mind_typing_flags;
  }

let cook_rel_context info ctx =
  cook_rel_context (RefTable.create 13) info ctx

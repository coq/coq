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
  | IndRef i1, IndRef i2 -> eq_syntactic_ind i1 i2
  | ConstructRef c1, ConstructRef c2 -> eq_syntactic_constructor c1 c2
  | _ -> false
  open Hashset.Combine
  let hash = function
  | ConstRef c -> combinesmall 1 (Constant.SyntacticOrd.hash c)
  | IndRef i -> combinesmall 2 (ind_syntactic_hash i)
  | ConstructRef c -> combinesmall 3 (constructor_syntactic_hash c)
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
  let (u,l) =
    match r with
    | IndRef (kn,_i) ->
        Mindmap.find kn knl
    | ConstructRef ((kn,_i),_j) ->
        Mindmap.find kn knl
    | ConstRef cst ->
        Cmap.find cst cstl in
  let c = (u, Array.map mkVar l) in
  RefTable.add cache r c;
  c

let share_univs cache r u l =
  let (u', args) = share cache r l in
    mkApp (instantiate_my_gr r (Instance.append u' u), args)

let update_case_info cache ci modlist =
  try
    let (_u,l) = share cache (IndRef ci.ci_ind) modlist in
    { ci with ci_npar = ci.ci_npar + Array.length l }
  with Not_found ->
    ci

let is_empty_modlist (cm, mm) =
  Cmap.is_empty cm && Mindmap.is_empty mm

let expmod_constr cache modlist c =
  let share_univs = share_univs cache in
  let update_case_info = update_case_info cache in
  let rec substrec c =
    match kind c with
      | Case (ci,p,t,br) ->
          Constr.map substrec (mkCase (update_case_info ci modlist,p,t,br))

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
        let map cst npars =
          let _, newpars = Mindmap.find cst (snd modlist) in
          (cst, npars + Array.length newpars)
        in
        let p' = try Projection.map_npars map p with Not_found -> p in
        let c'' = substrec c' in
        if p == p' && c' == c'' then c else mkProj (p', c'')

  | _ -> Constr.map substrec c

  in
  if is_empty_modlist modlist then c
  else substrec c

(** Transforms a named context into a rel context. Also returns the list of
    variables [id1 ... idn] that need to be replaced by [Rel 1 ... Rel n] to
    abstract a term that lived in that context. *)
let abstract_context hyps =
  let fold decl (ctx, subst) =
    let id, decl = match decl with
    | NamedDecl.LocalDef (id, b, t) ->
      let b = Vars.subst_vars subst b in
      let t = Vars.subst_vars subst t in
      id, RelDecl.LocalDef (map_annot Name.mk_name id, b, t)
    | NamedDecl.LocalAssum (id, t) ->
      let t = Vars.subst_vars subst t in
      id, RelDecl.LocalAssum (map_annot Name.mk_name id, t)
    in
    (decl :: ctx, id.binder_name :: subst)
  in
  Context.Named.fold_outside fold hyps ~init:([], [])

let abstract_as_type t (hyps, subst) =
  let t = Vars.subst_vars subst t in
  List.fold_left (fun c d -> mkProd_wo_LetIn d c) t hyps

let abstract_as_body c (hyps, subst) =
  let c = Vars.subst_vars subst c in
  it_mkLambda_or_LetIn c hyps

type recipe = { from : Opaqueproof.opaque constant_body; info : Opaqueproof.cooking_info }
type inline = bool

type 'opaque result = {
  cook_body : (constr Mod_subst.substituted, 'opaque) constant_def;
  cook_type : types;
  cook_universes : universes;
  cook_relevance : Sorts.relevance;
  cook_inline : inline;
  cook_context : Id.Set.t option;
}

let expmod_constr_subst cache modlist subst c =
  let subst = Univ.make_instance_subst subst in
  let c = expmod_constr cache modlist c in
    Vars.subst_univs_level_constr subst c

let discharge_abstract_universe_context subst abs_ctx auctx =
  (** Given a named instance [subst := u₀ ... uₙ₋₁] together with an abstract
      context [auctx0 := 0 ... n - 1 |= C{0, ..., n - 1}] of the same length,
      and another abstract context relative to the former context
      [auctx := 0 ... m - 1 |= C'{u₀, ..., uₙ₋₁, 0, ..., m - 1}],
      construct the lifted abstract universe context
      [0 ... n - 1 n ... n + m - 1 |=
        C{0, ... n - 1} ∪
        C'{0, ..., n - 1, n, ..., n + m - 1} ]
      together with the instance
      [u₀ ... uₙ₋₁ Var(0) ... Var (m - 1)].
  *)
  if (Univ.Instance.is_empty subst) then
    (** Still need to take the union for the constraints between globals *)
    subst, (AUContext.union abs_ctx auctx)
  else
    let open Univ in
    let ainst = make_abstract_instance auctx in
    let subst = Instance.append subst ainst in
    let substf = make_instance_subst subst in
    let auctx = Univ.subst_univs_level_abstract_universe_context substf auctx in
    subst, (AUContext.union abs_ctx auctx)

let lift_univs subst auctx0 = function
  | Monomorphic ctx ->
    assert (AUContext.is_empty auctx0);
    subst, (Monomorphic ctx)
  | Polymorphic auctx ->
    let subst, auctx = discharge_abstract_universe_context subst auctx0 auctx in
    subst, (Polymorphic auctx)

let cook_constr { Opaqueproof.modlist ; abstract } (c, priv) =
  let cache = RefTable.create 13 in
  let abstract, usubst, abs_ctx = abstract in
  let usubst, priv = match priv with
  | Opaqueproof.PrivateMonomorphic () ->
    let () = assert (AUContext.is_empty abs_ctx) in
    let () = assert (Instance.is_empty usubst) in
    usubst, priv
  | Opaqueproof.PrivatePolymorphic (univs, ctx) ->
    let ainst = Instance.of_array (Array.init univs Level.var) in
    let usubst = Instance.append usubst ainst in
    let ctx = on_snd (Univ.subst_univs_level_constraints (Univ.make_instance_subst usubst)) ctx in
    let univs = univs + AUContext.size abs_ctx in
    usubst, Opaqueproof.PrivatePolymorphic (univs, ctx)
  in
  let expmod = expmod_constr_subst cache modlist usubst in
  let hyps = Context.Named.map expmod abstract in
  let hyps = abstract_context hyps in
  let c = abstract_as_body (expmod c) hyps in
  (c, priv)

let cook_constr infos c =
  let fold info c = cook_constr info c in
  List.fold_right fold infos c

let cook_constant { from = cb; info } =
  let { Opaqueproof.modlist; abstract } = info in
  let cache = RefTable.create 13 in
  let abstract, usubst, abs_ctx = abstract in
  let usubst, univs = lift_univs usubst abs_ctx cb.const_universes in
  let expmod = expmod_constr_subst cache modlist usubst in
  let hyps0 = Context.Named.map expmod abstract in
  let hyps = abstract_context hyps0 in
  let map c = abstract_as_body (expmod c) hyps in
  let body = match cb.const_body with
  | Undef _ as x -> x
  | Def cs -> Def (Mod_subst.from_val (map (Mod_subst.force_constr cs)))
  | OpaqueDef o ->
    OpaqueDef (Opaqueproof.discharge_opaque info o)
  | Primitive _ -> CErrors.anomaly (Pp.str "Primitives cannot be cooked")
  in
  let const_hyps = Id.Set.diff (Context.Named.to_vars cb.const_hyps) (Context.Named.to_vars hyps0) in
  let typ = abstract_as_type (expmod cb.const_type) hyps in
  {
    cook_body = body;
    cook_type = typ;
    cook_universes = univs;
    cook_relevance = cb.const_relevance;
    cook_inline = cb.const_inline_code;
    cook_context = Some const_hyps;
  }

(* let cook_constant_key = CProfile.declare_profile "cook_constant" *)
(* let cook_constant = CProfile.profile2 cook_constant_key cook_constant *)

(********************************)
(* Discharging mutual inductive *)

let it_mkProd_wo_LetIn = List.fold_left (fun c d -> mkProd_wo_LetIn d c)

let abstract_rel_ctx (section_decls,subst) ctx =
  (* Dealing with substitutions between contexts is too annoying, so
     we reify [ctx] into a big [forall] term and work on that. *)
  let t = it_mkProd_or_LetIn mkProp ctx in
  let t = Vars.subst_vars subst t in
  let t = it_mkProd_wo_LetIn t section_decls in
  let ctx, t = decompose_prod_assum t in
  assert (Constr.equal t mkProp);
  ctx

let abstract_lc ~ntypes expmod (newparams,subst) c =
  let args = Array.rev_of_list (CList.map_filter (fun d ->
      if RelDecl.is_local_def d then None
      else match RelDecl.get_name d with
        | Anonymous -> assert false
        | Name id -> Some (mkVar id))
      newparams)
  in
  let diff = List.length newparams in
  let subs = List.init ntypes (fun k ->
      lift diff (mkApp (mkRel (k+1), args)))
  in
  let c = Vars.substl subs c in
  let c = Vars.subst_vars subst (expmod c) in
  let c = it_mkProd_wo_LetIn c newparams in
  c

let abstract_projection ~params expmod hyps t =
  let t = it_mkProd_or_LetIn t params in
  let t = mkArrowR mkProp t in (* dummy type standing in for the inductive *)
  let t = abstract_as_type (expmod t) hyps in
  let _, t = decompose_prod_n_assum (List.length params + 1 + Context.Rel.nhyps (fst hyps)) t in
  t

let cook_one_ind ~ntypes
    hyps expmod mip =
  let mind_arity = match mip.mind_arity with
    | RegularArity {mind_user_arity=arity;mind_sort=sort} ->
      let arity = abstract_as_type (expmod arity) hyps in
      let sort = destSort (expmod (mkSort sort)) in
      RegularArity {mind_user_arity=arity; mind_sort=sort}
    | TemplateArity {template_level} ->
      TemplateArity {template_level}
  in
  let mind_arity_ctxt =
    let ctx = Context.Rel.map expmod mip.mind_arity_ctxt in
    abstract_rel_ctx hyps ctx
  in
  let mind_user_lc =
    Array.map (abstract_lc ~ntypes expmod hyps)
      mip.mind_user_lc
  in
  let mind_nf_lc = Array.map (fun (ctx,t) ->
      let lc = it_mkProd_or_LetIn t ctx in
      let lc = abstract_lc ~ntypes expmod hyps lc in
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
    mind_recargs = mip.mind_recargs; (* TODO is this correct? checker should tell us. *)
    mind_relevance = mip.mind_relevance;
    mind_nb_constant = mip.mind_nb_constant;
    mind_nb_args = mip.mind_nb_args;
    mind_reloc_tbl = mip.mind_reloc_tbl;
  }

let cook_inductive { Opaqueproof.modlist; abstract } mib =
  let (section_decls, subst, abs_uctx) = abstract in
  let subst, mind_universes = lift_univs subst abs_uctx mib.mind_universes in
  let cache = RefTable.create 13 in
  let expmod = expmod_constr_subst cache modlist subst in
  let section_decls = Context.Named.map expmod section_decls in
  let removed_vars = Context.Named.to_vars section_decls in
  let section_decls, _ as hyps = abstract_context section_decls in
  let nnewparams = Context.Rel.nhyps section_decls in
  let mind_params_ctxt =
    let ctx = Context.Rel.map expmod mib.mind_params_ctxt in
    abstract_rel_ctx hyps ctx
  in
  let ntypes = mib.mind_ntypes in
  let mind_packets =
    Array.map (cook_one_ind ~ntypes hyps expmod)
      mib.mind_packets
  in
  let mind_record = match mib.mind_record with
    | NotRecord -> NotRecord
    | FakeRecord -> FakeRecord
    | PrimRecord data ->
      let data = Array.map (fun (id,projs,relevances,tys) ->
          let tys = Array.map (abstract_projection ~params:mib.mind_params_ctxt expmod hyps) tys in
          (id,projs,relevances,tys))
          data
      in
      PrimRecord data
  in
  let mind_hyps =
    List.filter (fun d -> not (Id.Set.mem (NamedDecl.get_id d) removed_vars))
      mib.mind_hyps
  in
  let mind_variance, mind_sec_variance =
    match mib.mind_variance, mib.mind_sec_variance with
    | None, None -> None, None
    | None, Some _ | Some _, None -> assert false
    | Some variance, Some sec_variance ->
      let sec_variance, newvariance =
        Array.chop (Array.length sec_variance - AUContext.size abs_uctx)
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
          section_decls
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

let expmod_constr modlist c = expmod_constr (RefTable.create 13) modlist c

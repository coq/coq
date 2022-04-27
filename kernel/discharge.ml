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
open Names
open Constr
open Term
open Declarations
open Univ
open Cooking

module NamedDecl = Context.Named.Declaration
module RelDecl = Context.Rel.Declaration

type inline = bool

type 'opaque result = {
  cook_body : (constr, 'opaque) constant_def;
  cook_type : types;
  cook_universes : universes;
  cook_relevance : Sorts.relevance;
  cook_inline : inline;
  cook_context : Id.Set.t option;
  cook_univ_hyps : Instance.t;
  cook_flags : typing_flags;
}

let lift_univs info univ_hyps = function
  | Monomorphic ->
    assert (Univ.Instance.is_empty univ_hyps);
    info, univ_hyps, Monomorphic
  | Polymorphic auctx ->
    let info, n, auctx = lift_poly_univs info auctx in
    let univ_hyps =
      let open Univ.Instance in
      let us = to_array univ_hyps in
      let us = Array.sub us 0 (Array.length us - n) in
      of_array us
    in
    info, univ_hyps, Polymorphic auctx

(********************************)
(* Discharging opaque proof terms *)

let lift_private_univs info = function
  | Opaqueproof.PrivateMonomorphic () as priv ->
    let () = lift_private_mono_univs info () in
    priv
  | Opaqueproof.PrivatePolymorphic ctx ->
    let ctx = lift_private_poly_univs info ctx in
    Opaqueproof.PrivatePolymorphic ctx

let cook_opaque_proofterm info c =
  let fold info (c, priv) =
    let priv = lift_private_univs info priv in
    let c = abstract_as_body (create_cache info) c in
    (c, priv)
  in
  List.fold_right fold info c

(********************************)
(* Discharging constant         *)

let cook_constant env info cb =
  (* Adjust the info so that it is meaningful under the block of quantified universe binders *)
  let info, univ_hyps, univs = lift_univs info cb.const_univ_hyps cb.const_universes in
  let cache = create_cache info in
  let map c = abstract_as_body cache c in
  let body = match cb.const_body with
  | Undef _ as x -> x
  | Def cs -> Def (map cs)
  | OpaqueDef o ->
    OpaqueDef (Opaqueproof.discharge_opaque info o)
  | Primitive _ -> CErrors.anomaly (Pp.str "Primitives cannot be cooked")
  in
  let tps = Vmbytegen.compile_constant_body ~fail_on_error:false env univs body in
  let typ = abstract_as_type cache cb.const_type in
  let names = names_info info in
  let hyps = List.filter (fun d -> not (Id.Set.mem (NamedDecl.get_id d) names)) cb.const_hyps in
  {
    const_hyps = hyps;
    const_univ_hyps = univ_hyps;
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

let cook_rel_context cache ctx =
  (* Dealing with substitutions between contexts is too annoying, so
     we reify [ctx] into a big [forall] term and work on that. *)
  let t = it_mkProd_or_LetIn mkProp ctx in
  let t = abstract_as_type cache t in
  let ctx, t = decompose_prod_assum t in
  assert (Constr.equal t mkProp);
  ctx

let cook_lc cache ~ntypes t =
  (* Expand the recursive call to the inductive types *)
  let diff = Context.Rel.length (rel_context_of_cooking_cache cache) in
  let subs = List.init ntypes (fun k -> mkApp (mkRel (k+diff+1), instance_of_cooking_cache cache)) in
  let t = Vars.substl subs t in
  (* Apply the abstraction *)
  abstract_as_type cache t

let cook_projection cache ~params t =
  let t = mkArrowR mkProp t in (* dummy type standing in for the inductive *)
  let t = it_mkProd_or_LetIn t params in
  let t = abstract_as_type cache t in
  let nrels = Context.Rel.nhyps (rel_context_of_cooking_cache cache) in
  let _, t = decompose_prod_n_assum (Context.Rel.length params + 1 + nrels) t in
  t

let cook_one_ind cache ~ntypes mip =
  let mind_arity = match mip.mind_arity with
    | RegularArity {mind_user_arity=arity;mind_sort=sort} ->
      let arity = abstract_as_type cache arity in
      let sort = abstract_as_sort cache sort in
      RegularArity {mind_user_arity=arity; mind_sort=sort}
    | TemplateArity {template_level} ->
      TemplateArity {template_level}
  in
  let mind_arity_ctxt = cook_rel_context cache mip.mind_arity_ctxt in
  let mind_user_lc = Array.map (cook_lc cache ~ntypes) mip.mind_user_lc in
  let mind_nf_lc = Array.map (fun (ctx,t) ->
      let lc = it_mkProd_or_LetIn t ctx in
      let lc = cook_lc cache ~ntypes lc in
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
  let info, univ_hyps, mind_universes = lift_univs info mib.mind_univ_hyps mib.mind_universes in
  let cache = create_cache info in
  let nnewparams = Context.Rel.nhyps (rel_context_of_cooking_cache cache) in
  let mind_params_ctxt = cook_rel_context cache mib.mind_params_ctxt in
  let ntypes = mib.mind_ntypes in
  let mind_packets = Array.map (cook_one_ind cache ~ntypes) mib.mind_packets in
  let mind_record = match mib.mind_record with
    | NotRecord -> NotRecord
    | FakeRecord -> FakeRecord
    | PrimRecord data ->
      let data = Array.map (fun (id,projs,relevances,tys) ->
          let tys = Array.map (cook_projection cache ~params:mib.mind_params_ctxt) tys in
          (id,projs,relevances,tys))
          data
      in
      PrimRecord data
  in
  let names = names_info info in
  let mind_hyps =
    List.filter (fun d -> not (Id.Set.mem (NamedDecl.get_id d) names))
      mib.mind_hyps
  in
  let mind_variance, mind_sec_variance =
    match mib.mind_variance, mib.mind_sec_variance with
    | None, None -> None, None
    | None, Some _ | Some _, None -> assert false
    | Some variance, Some sec_variance ->
      let sec_variance, newvariance =
        Array.chop (Array.length sec_variance - AbstractContext.size (universe_context_of_cooking_info info))
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
          (rel_context_of_cooking_cache cache)
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
    mind_univ_hyps = univ_hyps;
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
  cook_rel_context (create_cache info) ctx

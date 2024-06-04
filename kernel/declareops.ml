(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

(** Operations concernings types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

let safe_flags oracle = {
  check_guarded = true;
  check_positive = true;
  check_universes = true;
  conv_oracle = oracle;
  share_reduction = true;
  enable_VM = true;
  enable_native_compiler = true;
  indices_matter = true;
  impredicative_set = false;
  sprop_allowed = true;
  allow_uip = false;
}

(** {6 Arities } *)

let subst_decl_arity f g subst ar =
  match ar with
  | RegularArity x ->
    let x' = f subst x in
      if x' == x then ar
      else RegularArity x'
  | TemplateArity x ->
    let x' = g subst x in
      if x' == x then ar
      else TemplateArity x'

let map_decl_arity f g = function
  | RegularArity a -> RegularArity (f a)
  | TemplateArity a -> TemplateArity (g a)

let hcons_template_arity ar =
  { template_level = Sorts.hcons ar.template_level; }

let hcons_template_universe ar =
  { template_param_levels = ar.template_param_levels;
    template_context = Univ.hcons_universe_context_set ar.template_context }

let universes_context = function
  | Monomorphic -> UVars.AbstractContext.empty
  | Polymorphic ctx -> ctx

let abstract_universes = function
  | Entries.Monomorphic_entry ->
    UVars.empty_sort_subst, Monomorphic
  | Entries.Polymorphic_entry uctx ->
    let (inst, auctx) = UVars.abstract_universes uctx in
    let inst = UVars.make_instance_subst inst in
    (inst, Polymorphic auctx)

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
  assert (List.is_empty cb.const_hyps && UVars.LevelInstance.is_empty cb.const_univ_hyps);
  if is_empty_subst subst then cb
  else
    let body' = subst_const_def subst cb.const_body in
    let type' = subst_const_type subst cb.const_type in
    if body' == cb.const_body && type' == cb.const_type
    then cb
    else
      { const_hyps = [];
        const_univ_hyps = UVars.LevelInstance.empty;
        const_body = body';
        const_type = type';
        const_body_code =
          Option.map (Vmemitcodes.subst_body_code subst) cb.const_body_code;
        const_universes = cb.const_universes;
        const_relevance = cb.const_relevance;
        const_inline_code = cb.const_inline_code;
        const_typing_flags = cb.const_typing_flags }

(** {7 Hash-consing of constants } *)

(** This hash-consing is currently quite partial : we only
    share internal fields (e.g. constr), and not the records
    themselves. But would it really bring substantial gains ? *)

let hcons_rel_decl =
  RelDecl.map_name Names.Name.hcons %> RelDecl.map_value Constr.hcons %> RelDecl.map_type Constr.hcons

let hcons_rel_context l = List.Smart.map hcons_rel_decl l

let hcons_const_def = function
  | Undef inl -> Undef inl
  | Primitive p -> Primitive p
  | Symbol r -> Symbol r
  | Def l_constr ->
    Def (Constr.hcons l_constr)
  | OpaqueDef _ as x -> x (* hashconsed when turned indirect *)

let hcons_universes cbu =
  match cbu with
  | Monomorphic -> Monomorphic
  | Polymorphic ctx ->
    Polymorphic (UVars.hcons_abstract_universe_context ctx)

let hcons_const_body cb =
  { cb with
    const_body = hcons_const_def cb.const_body;
    const_type = Constr.hcons cb.const_type;
    const_universes = hcons_universes cb.const_universes;
  }

(** {6 Inductive types } *)

let eq_recarg_type t1 t2 = match t1, t2 with
| RecArgInd ind1, RecArgInd ind2 -> Names.Ind.CanOrd.equal ind1 ind2
| RecArgPrim c1, RecArgPrim c2 -> Names.Constant.CanOrd.equal c1 c2
| (RecArgInd _ | RecArgPrim _), _ -> false

let eq_recarg r1 r2 = match r1, r2 with
| Norec, Norec -> true
| Norec, _ -> false
| Mrec t1, Mrec t2 -> eq_recarg_type t1 t2
| Mrec _, _ -> false

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

let dest_recarg p = fst (Rtree.dest_node p)

(* dest_subterms returns the sizes of each argument of each constructor of
   an inductive object of size [p]. This should never be done for Norec,
   because the number of sons does not correspond to the number of
   constructors.
 *)
let dest_subterms p =
  let (ra,cstrs) = Rtree.dest_node p in
  assert (match ra with Norec -> false | _ -> true);
  Array.map Array.to_list cstrs

let recarg_length p j =
  let (_,cstrs) = Rtree.dest_node p in
  Array.length cstrs.(j-1)

let subst_wf_paths subst p = Rtree.Smart.map (subst_recarg subst) p

(** {7 Substitution of inductive declarations } *)

let subst_regular_ind_arity subst s =
  let uar' = subst_mps subst s.mind_user_arity in
    if uar' == s.mind_user_arity then s
    else { mind_user_arity = uar'; mind_sort = s.mind_sort }

let subst_template_ind_arity _sub s = s

(* FIXME records *)
let subst_ind_arity =
  subst_decl_arity subst_regular_ind_arity subst_template_ind_arity

let subst_mind_packet subst mbp =
  { mind_consnames = mbp.mind_consnames;
    mind_consnrealdecls = mbp.mind_consnrealdecls;
    mind_consnrealargs = mbp.mind_consnrealargs;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = Array.Smart.map (fun (ctx, c) -> Context.Rel.map (subst_mps subst) ctx, subst_mps subst c) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context subst mbp.mind_arity_ctxt;
    mind_arity = subst_ind_arity subst mbp.mind_arity;
    mind_user_lc = Array.Smart.map (subst_mps subst) mbp.mind_user_lc;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_nrealdecls = mbp.mind_nrealdecls;
    mind_squashed = mbp.mind_squashed;
    mind_recargs = subst_wf_paths subst mbp.mind_recargs (*wf_paths*);
    mind_relevance = mbp.mind_relevance;
    mind_nb_constant = mbp.mind_nb_constant;
    mind_nb_args = mbp.mind_nb_args;
    mind_reloc_tbl = mbp.mind_reloc_tbl }

let subst_mind_record subst r = match r with
| NotRecord -> NotRecord
| FakeRecord -> FakeRecord
| PrimRecord infos ->
  let map (id, ps, rs, pb as info) =
    let pb' = Array.Smart.map (subst_mps subst) pb in
    if pb' == pb then info
    else (id, ps, rs, pb')
  in
  let infos' = Array.Smart.map map infos in
  if infos' == infos then r else PrimRecord infos'

let subst_mind_body subst mib =
  (* we're outside sections *)
  assert (List.is_empty mib.mind_hyps && UVars.LevelInstance.is_empty mib.mind_univ_hyps);
  { mind_record = subst_mind_record subst mib.mind_record ;
    mind_finite = mib.mind_finite ;
    mind_ntypes = mib.mind_ntypes ;
    mind_hyps = [];
    mind_univ_hyps = UVars.LevelInstance.empty;
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

let inductive_polymorphic_context mib =
  universes_context mib.mind_universes

let inductive_is_polymorphic mib =
  match mib.mind_universes with
  | Monomorphic -> false
  | Polymorphic _ctx -> true

let inductive_is_cumulative mib =
  Option.has_some mib.mind_variance

let inductive_make_projection ind mib ~proj_arg =
  match mib.mind_record with
  | NotRecord | FakeRecord ->
    CErrors.anomaly Pp.(str "inductive_make_projection: not a primitive record.")
  | PrimRecord infos ->
    let _, labs, rs, _ = infos.(snd ind) in
    if proj_arg < 0 || Array.length labs <= proj_arg
    then CErrors.anomaly Pp.(str "inductive_make_projection: invalid proj_arg.");
    let p = Names.Projection.Repr.make ind
      ~proj_npars:mib.mind_nparams
      ~proj_arg
      labs.(proj_arg)
    in
    p, rs.(proj_arg)

let inductive_make_projections ind mib =
  match mib.mind_record with
  | NotRecord | FakeRecord -> None
  | PrimRecord infos ->
    let _, labs, relevances, _ = infos.(snd ind) in
    let projs = Array.map2_i (fun proj_arg lab r ->
        Names.Projection.Repr.make ind ~proj_npars:mib.mind_nparams ~proj_arg lab, r)
        labs relevances
    in
    Some projs

(** {6 Hash-consing of inductive declarations } *)

let hcons_regular_ind_arity a =
  { mind_user_arity = Constr.hcons a.mind_user_arity;
    mind_sort = Sorts.hcons a.mind_sort }

(** Just as for constants, this hash-consing is quite partial *)

let hcons_ind_arity =
  map_decl_arity hcons_regular_ind_arity hcons_template_arity

(** Substitution of inductive declarations *)

let hcons_mind_packet oib =
  let user = Array.Smart.map Constr.hcons oib.mind_user_lc in
  let map (ctx, c) = Context.Rel.map Constr.hcons ctx, Constr.hcons c in
  let nf = Array.Smart.map map oib.mind_nf_lc in
  { oib with
    mind_typename = Names.Id.hcons oib.mind_typename;
    mind_arity_ctxt = hcons_rel_context oib.mind_arity_ctxt;
    mind_arity = hcons_ind_arity oib.mind_arity;
    mind_consnames = Array.Smart.map Names.Id.hcons oib.mind_consnames;
    mind_user_lc = user;
    mind_nf_lc = nf }

let hcons_mind mib =
  { mib with
    mind_packets = Array.Smart.map hcons_mind_packet mib.mind_packets;
    mind_params_ctxt = hcons_rel_context mib.mind_params_ctxt;
    mind_template = Option.Smart.map hcons_template_universe mib.mind_template;
    mind_universes = hcons_universes mib.mind_universes }

let subst_rewrite_rules subst ({ rewrules_rules } as rules) =
  let body' = List.Smart.map (fun (name, ({ rhs; _ } as rule) as orig) ->
      let rhs' = subst_mps subst rhs in
      if rhs == rhs' then orig else name, { rule with rhs = rhs' })
      rewrules_rules
  in
  if rewrules_rules == body' then rules else
    { rewrules_rules = body' }

(** Hashconsing of modules *)

let hcons_functorize hty he hself f = match f with
| NoFunctor e ->
  let e' = he e in
  if e == e' then f else NoFunctor e'
| MoreFunctor (mid, ty, nf) ->
  (** FIXME *)
  let mid' = mid in
  let ty' = hty ty in
  let nf' = hself nf in
  if mid == mid' && ty == ty' && nf == nf' then f
  else MoreFunctor (mid, ty', nf')

let hcons_module_alg_expr me = me

let rec hcons_module_expression me = match me with
| MENoFunctor malg ->
  let malg' = hcons_module_alg_expr malg in
  if malg == malg' then me else MENoFunctor malg'
| MEMoreFunctor mf ->
  let mf' = hcons_module_expression mf in
  if mf' == mf then me else MEMoreFunctor mf'

let rec hcons_structure_field_body sb = match sb with
| SFBconst cb ->
  let cb' = hcons_const_body cb in
  if cb == cb' then sb else SFBconst cb'
| SFBmind mib ->
  let mib' = hcons_mind mib in
  if mib == mib' then sb else SFBmind mib'
| SFBmodule mb ->
  let mb' = hcons_module_body mb in
  if mb == mb' then sb else SFBmodule mb'
| SFBmodtype mb ->
  let mb' = hcons_module_type mb in
  if mb == mb' then sb else SFBmodtype mb'
| SFBrules _ -> sb (* TODO? *)

and hcons_structure_body sb =
  (** FIXME *)
  let map (l, sfb as fb) =
    let l' = Names.Label.hcons l in
    let sfb' = hcons_structure_field_body sfb in
    if l == l' && sfb == sfb' then fb else (l', sfb')
  in
  List.Smart.map map sb

and hcons_module_signature ms =
  hcons_functorize hcons_module_type hcons_structure_body hcons_module_signature ms

and hcons_module_implementation mip = match mip with
| Abstract -> Abstract
| Algebraic me ->
  let me' = hcons_module_expression me in
  if me == me' then mip else Algebraic me'
| Struct ms ->
  let ms' = hcons_structure_body ms in
  if ms == ms' then mip else Struct ms
| FullStruct -> FullStruct

and hcons_generic_module_body :
  'a. ('a -> 'a) -> 'a generic_module_body -> 'a generic_module_body =
  fun hcons_impl mb ->
  let mp' = mb.mod_mp in
  let expr' = hcons_impl mb.mod_expr in
  let type' = hcons_module_signature mb.mod_type in
  let type_alg' = mb.mod_type_alg in
  let delta' = mb.mod_delta in
  let retroknowledge' = mb.mod_retroknowledge in

  if
    mb.mod_mp == mp' &&
    mb.mod_expr == expr' &&
    mb.mod_type == type' &&
    mb.mod_type_alg == type_alg' &&
    mb.mod_delta == delta' &&
    mb.mod_retroknowledge == retroknowledge'
  then mb
  else {
    mod_mp = mp';
    mod_expr = expr';
    mod_type = type';
    mod_type_alg = type_alg';
    mod_delta = delta';
    mod_retroknowledge = retroknowledge';
  }

and hcons_module_body mb =
  hcons_generic_module_body hcons_module_implementation mb

and hcons_module_type mb =
  hcons_generic_module_body (fun () -> ()) mb

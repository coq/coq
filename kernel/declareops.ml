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

let hcons_template_universe ar =
  { template_param_arguments = List.Smart.map (Option.Smart.map Sorts.hcons) ar.template_param_arguments;
    template_concl = Sorts.hcons ar.template_concl;
    template_context = UVars.hcons_abstract_universe_context ar.template_context;
    template_defaults = UVars.Instance.hcons ar.template_defaults;
  }

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

let hcons_const_def ?(hbody=Constr.hcons) = function
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
    Polymorphic (UVars.hcons_abstract_universe_context ctx)

let hcons_const_body ?hbody cb =
  { cb with
    const_body = hcons_const_def ?hbody cb.const_body;
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

let recarg_length p j =
  let (_,cstrs) = Rtree.dest_node p in
  Array.length cstrs.(j-1)

let subst_wf_paths subst p = Rtree.Smart.map (subst_recarg subst) p

(** {7 Substitution of inductive declarations } *)

let subst_mind_packet subst mbp =
  { mind_consnames = mbp.mind_consnames;
    mind_consnrealdecls = mbp.mind_consnrealdecls;
    mind_consnrealargs = mbp.mind_consnrealargs;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = Array.Smart.map (fun (ctx, c) -> Context.Rel.map (subst_mps subst) ctx, subst_mps subst c) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context subst mbp.mind_arity_ctxt;
    mind_user_arity = subst_mps subst mbp.mind_user_arity;
    mind_sort = mbp.mind_sort;
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
  assert (List.is_empty mib.mind_hyps && UVars.Instance.is_empty mib.mind_univ_hyps);
  { mind_record = subst_mind_record subst mib.mind_record ;
    mind_finite = mib.mind_finite ;
    mind_ntypes = mib.mind_ntypes ;
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

(** Just as for constants, this hash-consing is quite partial *)

let hcons_mind_packet oib =
  let user = Array.Smart.map Constr.hcons oib.mind_user_lc in
  let map (ctx, c) = Context.Rel.map Constr.hcons ctx, Constr.hcons c in
  let nf = Array.Smart.map map oib.mind_nf_lc in
  { oib with
    mind_typename = Names.Id.hcons oib.mind_typename;
    mind_arity_ctxt = hcons_rel_context oib.mind_arity_ctxt;
    mind_user_arity = Constr.hcons oib.mind_user_arity;
    mind_sort = Sorts.hcons oib.mind_sort;
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
